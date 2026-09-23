import Veir.Analysis.DataFlow.Domains.ConstantSoundness
import Veir.Analysis.DataFlow.Domains.ConstantDomain
import Veir.Analysis.DataFlow.SparseForwardDataFlowAnalysis
import Veir.Interfaces.FoldInterfaces
import Veir.Interfaces.FoldSoundness

public section

namespace Veir

namespace SparseConstantPropagation

instance : SparseFactSpec .sparseConstant AbstractConstant where
  payloadEq := rfl

def kind : AnalysisKind :=
  .sparseConstantPropagation

/--
Sparse constant propagation transfer function.
- operations with regions conservatively force results to `⊤`,
- any operand at `⊥` leave results as `⊥` and delay propagation,
- otherwise we try to fold and return the result (if there isn't
  a result from the fold, return `⊤`)
-/
def transfer
    (op : OperationPtr)
    (operandLatticeElements : Array AbstractConstant)
    (irCtx : WfIRContext OpCode) : Array AbstractConstant :=
  let numResults := op.getNumResults! irCtx.raw
  let opType := op.getOpType! irCtx.raw

  -- Don't try to simulate the results of an operation with regions as we
  -- can't guarantee that folding will be out-of-place. We don't allow
  -- in-place folds as the desire here is for simulated execution, and not
  -- general folding.
  if op.getNumRegions! irCtx.raw ≠ 0 then
    Array.replicate numResults ⊤

  -- Wait until every operand lattice has been initialized before trying to
  -- infer a result.
  else if operandLatticeElements.any (· = ⊥) then
    Array.replicate numResults ⊥

  -- Grab constant out of constant like operation
  else if opType.isConstantLike then
    (op.getResults! irCtx.raw).map fun result =>
      (result.constantValue irCtx.raw).map AbstractConstant.ofRuntimeValue |>.getD ⊤

  -- Attempt folding the lattice elements of the operands
  else if opInBounds : op.InBounds irCtx.raw then
    let constantOperands := operandLatticeElements.map fun
      | .constant ⟨bitwidth, value⟩ => some (.int bitwidth value)
      | _ => none
    match op.foldsTo irCtx opInBounds constantOperands with
    | some results =>
      results.map fun result => AbstractConstant.ofFoldDecision result operandLatticeElements
    | none =>
      Array.replicate numResults ⊤

  else
    Array.replicate numResults ⊤

/--
`a.Describes v` says the abstract fact `a` describes the runtime value `v`
exactly: `⊤` describes every value, `⊥` none, and `.constant c` only the
integer `c` itself — poison included, with no refinement.

Operand facts are read exactly because folding consumes them as values: a
`.constant` operand fact is handed to the folder as the operand's value.
-/
def _root_.Veir.AbstractConstant.Describes (a : AbstractConstant) (v : RuntimeValue) : Prop :=
  match a with
  | .top => True
  | .bottom => False
  | .constant c => v = .int c.bitwidth c.value

/-- Every abstract operand fact describes its concrete operand. -/
def OperandsSound (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array RuntimeValue) : Prop :=
  ∀ (j : Nat) (a : AbstractConstant) (v : RuntimeValue),
    abstractOperands[j]? = some a → concreteOperands[j]? = some v → a.Describes v

/-- An exact description is in particular a sound one. -/
theorem soundForValue_of_describes {a : AbstractConstant} {v : RuntimeValue}
    (h : a.Describes v) : a.SoundForValue v := by
  right
  cases a with
  | top =>
    cases AbstractConstant.ofTrackedValue v with
    | none => trivial
    | some c => exact AbstractConstant.γ_top_eq c
  | bottom => exact h.elim
  | constant c =>
    simp only [AbstractConstant.Describes] at h
    subst h
    show (⟨c.bitwidth, c.value⟩ : ConcreteConstant) = c
    rfl

/-- The abstraction of a runtime value is sound for that value. -/
theorem soundForValue_ofRuntimeValue (v : RuntimeValue) :
    (AbstractConstant.ofRuntimeValue v).SoundForValue v := by
  right
  cases v <;> simp [AbstractConstant.ofRuntimeValue, AbstractConstant.ofTrackedValue] <;> rfl

/-- The constants handed to the folder agree with the concrete operands. -/
theorem constOperandsAgree_of_operandsSound
    {abstractOperands : Array AbstractConstant} {concreteOperands : Array RuntimeValue}
    (hOperands : OperandsSound abstractOperands concreteOperands)
    (hSize : abstractOperands.size = concreteOperands.size) :
    ConstOperandsAgree
      (abstractOperands.map fun
        | .constant ⟨bitwidth, value⟩ => some (RuntimeValue.int bitwidth value)
        | _ => none)
      concreteOperands := by
  intro j v hConst
  simp only [Array.getElem?_map, Option.map_eq_some_iff] at hConst
  obtain ⟨a, ha, hv⟩ := hConst
  have hj : j < concreteOperands.size := by
    have := (Array.getElem?_eq_some_iff.mp ha).1
    omega
  obtain ⟨w, hw⟩ : ∃ w, concreteOperands[j]? = some w := ⟨_, Array.getElem?_eq_getElem hj⟩
  have hDescribes := hOperands j a w ha hw
  cases a with
  | constant c =>
    simp only [Option.some.injEq] at hv
    simp only [AbstractConstant.Describes] at hDescribes
    rw [hw, hDescribes, ← hv]
  | top => simp at hv
  | bottom => simp at hv

/-- A sound fold decision yields a sound abstract fact. -/
theorem ofFoldDecision_soundFor
    (decision : FoldDecision) (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array RuntimeValue) (outcome : Interp (Array RuntimeValue)) (i : Nat)
    (hOperands : OperandsSound abstractOperands concreteOperands)
    (hDecision : decision.SoundFor concreteOperands outcome i) :
    (AbstractConstant.ofFoldDecision decision abstractOperands).SoundFor outcome i := by
  cases outcome with
  | fail => trivial
  | ub => trivial
  | ok results =>
    simp only [AbstractConstant.SoundFor]
    simp only [FoldDecision.SoundFor] at hDecision
    cases hResult : results[i]? with
    | none => trivial
    | some actual =>
      simp only [hResult] at hDecision
      rcases hDecision with hPoison | hValue
      · exact Or.inl hPoison
      · cases decision with
        | useConstant value =>
          simp only [FoldDecision.valueFor, Option.some.injEq] at hValue
          subst hValue
          exact soundForValue_ofRuntimeValue value
        | useOperand j =>
          simp only [FoldDecision.valueFor] at hValue
          simp only [AbstractConstant.ofFoldDecision]
          cases ha : abstractOperands[j]? with
          | none => exact AbstractConstant.soundForValue_top actual
          | some a => exact soundForValue_of_describes (hOperands j a actual ha hValue)

/--
Local soundness of the constant-propagation transfer function.

Every result fact `transfer` produces is sound, in the refinement sense of
`AbstractConstant.SoundFor`, for the interpretation of the operation on its
concrete operands. UB and interpreter failure constrain nothing.

The hypotheses:
* `hTable`, `hHonest` — the per-opcode obligations of `foldsTo_sound`;
* `hOperands`, `hSize` — the operand facts describe the concrete operands
  exactly (`AbstractConstant.Describes`). This also rules out `⊥` operand facts,
  so the `⊥` branch of `transfer` needs no separate premise;
* `hArity` — the concrete operands are as many as the operation has;
* `hConstSuccessors` — a constant-like operation has no successors, so the
  interpretation `ValuePtr.constantValue` runs agrees with `interpretPure`.

Note the asymmetry: operand facts are read exactly, result facts only up to
refinement. A result fact may claim a value where the execution produced poison
(`arith.addui_extended x, 0` with poison `x`), and such a fact does not describe
the value exactly. Chaining this theorem across operations therefore needs a
refinement argument about the whole program, not a pointwise induction.
-/
theorem transfer_sound
    (op : OperationPtr) (irCtx : WfIRContext OpCode)
    (abstractOperands : Array AbstractConstant) (concreteOperands : Array RuntimeValue)
    (hTable : FoldTableSound (op.getOpType! irCtx.raw))
    (hHonest : PropagatesPoisonHonestly (op.getOpType! irCtx.raw))
    (hOperands : OperandsSound abstractOperands concreteOperands)
    (hSize : abstractOperands.size = concreteOperands.size)
    (hArity : concreteOperands.size = op.getNumOperands! irCtx.raw)
    (hConstSuccessors : (op.getOpType! irCtx.raw).isConstantLike = true →
      op.getSuccessors! irCtx.raw = #[])
    (i : Nat) :
    ((transfer op abstractOperands irCtx)[i]?.getD ⊤).SoundFor
      (interpretPure (op.getOpType! irCtx.raw)
        (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw))
        (op.getResultTypes! irCtx.raw) concreteOperands) i := by
  have hTop : ∀ n, ((Array.replicate n (⊤ : AbstractConstant))[i]?.getD ⊤) = ⊤ := by
    intro n
    rw [Array.getElem?_replicate]
    split <;> rfl
  by_cases hRegions : op.getNumRegions! irCtx.raw ≠ 0
  · rw [show transfer op abstractOperands irCtx =
        Array.replicate (op.getNumResults! irCtx.raw) ⊤ by simp [transfer, hRegions], hTop]
    exact AbstractConstant.soundFor_top _ i
  have hRegions0 : op.getNumRegions! irCtx.raw = 0 := by simpa using hRegions
  by_cases hBot : abstractOperands.any (· = ⊥)
  · exfalso
    obtain ⟨j, hj, hjBot⟩ := Array.any_eq_true.mp hBot
    have hjConcrete : j < concreteOperands.size := by omega
    have := hOperands j _ _ (Array.getElem?_eq_getElem hj) (Array.getElem?_eq_getElem hjConcrete)
    simp only [decide_eq_true_eq] at hjBot
    rw [hjBot] at this
    exact this
  by_cases hConst : (op.getOpType! irCtx.raw).isConstantLike = true
  · have hSuccessors := hConstSuccessors hConst
    rw [show transfer op abstractOperands irCtx = (op.getResults! irCtx.raw).map (fun result =>
        (result.constantValue irCtx.raw).map AbstractConstant.ofRuntimeValue |>.getD ⊤) by
          simp [transfer, hRegions0, hBot, hConst]]
    by_cases hi : ¬ i < op.getNumResults! irCtx.raw
    · have hNone : (op.getResults! irCtx.raw)[i]? = none := by simp; omega
      simp [Array.getElem?_map, hNone]
    simp only [Decidable.not_not] at hi
    rw [Array.getElem?_map, Array.getElem?_eq_getElem (by simpa using hi), Option.map_some,
      Option.getD_some, OperationPtr.getResults!.getElem_eq_getResult hi]
    have hConstOp : op.isConstantLike irCtx.raw = true := hConst
    by_cases hNum : op.getNumOperands! irCtx.raw ≠ 0
    · simp [ValuePtr.constantValue, OperationPtr.getResult, hNum]
    simp only [Decidable.not_not] at hNum
    have hEmpty : concreteOperands = #[] := Array.eq_empty_of_size_eq_zero (by omega)
    subst hEmpty
    simp only [ValuePtr.constantValue, OperationPtr.getResult, hConstOp, hNum,
      OperationPtr.interpret, hSuccessors, interpretPure, not_true_eq_false, ite_false,
      ne_eq]
    cases interpretOp' (op.getOpType! irCtx.raw) (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw))
        (op.getResultTypes! irCtx.raw) #[] #[] MemoryState.empty with
    | fail => exact AbstractConstant.soundFor_fail _ i
    | ub => exact AbstractConstant.soundFor_ub _ i
    | ok triple =>
      obtain ⟨results, _, action⟩ := triple
      cases action with
      | some _ => exact AbstractConstant.soundFor_top _ i
      | none =>
        simp only [Interp.map_ok, AbstractConstant.SoundFor]
        cases hResult : results[i]? with
        | none => trivial
        | some actual =>
          simp only [Option.map_some, Option.getD_some]
          exact soundForValue_ofRuntimeValue actual
  by_cases hInBounds : op.InBounds irCtx.raw
  · let constOperands :=
      abstractOperands.map fun
        | .constant ⟨bitwidth, value⟩ => some (RuntimeValue.int bitwidth value)
        | _ => none
    cases hFold : op.foldsTo irCtx hInBounds constOperands with
    | none =>
      rw [show transfer op abstractOperands irCtx =
          Array.replicate (op.getNumResults! irCtx.raw) ⊤ by
            simp [transfer, hRegions0, hBot, hConst, hInBounds, hFold, constOperands], hTop]
      exact AbstractConstant.soundFor_top _ i
    | some decisions =>
      rw [show transfer op abstractOperands irCtx =
          decisions.map (fun decision => AbstractConstant.ofFoldDecision decision abstractOperands) by
            simp [transfer, hRegions0, hBot, hConst, hInBounds, hFold, constOperands]]
      cases hDecision : decisions[i]? with
      | none => simp [hDecision]
      | some decision =>
        simp only [Array.getElem?_map, hDecision, Option.map_some, Option.getD_some]
        apply ofFoldDecision_soundFor decision abstractOperands concreteOperands _ i hOperands
        simp only [OperationPtr.foldsTo] at hFold
        simp [guard, Option.bind_eq_some_iff] at hFold
        obtain ⟨_, hFold⟩ := hFold
        rw [← OperationPtr.getProperties!_eq_getProperties hInBounds (by grind),
          ← OperationPtr.getResultTypes!_eq_getResultTypes hInBounds,
          ← OperationPtr.getOpType!_eq_getOpType hInBounds] at hFold
        exact foldsTo_sound _ _ _ concreteOperands constOperands decisions i decision
          hTable hHonest (constOperandsAgree_of_operandsSound hOperands hSize)
          (by simp [constOperands, hSize]) hFold hDecision
  · rw [show transfer op abstractOperands irCtx =
        Array.replicate (op.getNumResults! irCtx.raw) ⊤ by
          simp [transfer, hRegions0, hBot, hConst, hInBounds], hTop]
    exact AbstractConstant.soundFor_top _ i

end SparseConstantPropagation

def SparseConstantPropagationAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .sparseConstant
    SparseConstantPropagation.kind
    SparseConstantPropagation.transfer

end Veir
