import Veir.Analysis.DataFlow.Domains.ConstantSoundness
import Veir.Analysis.DataFlow.Domains.ConstantDomain
import Veir.Analysis.DataFlow.SparseForwardDataFlowAnalysis
import Veir.Interfaces.FoldInterfaces
import Veir.Interfaces.FoldSoundness
import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas

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
`a.DescribesExactly v` says the abstract fact `a` describes the runtime value `v`
exactly: `⊤` describes every value, `⊥` none, and `.constant c` only the
integer `c` itself — poison included, with no refinement. It is
`AbstractConstant.Refines` with `⊒` strengthened to `=`.

`transfer_sound_exact` reads operand facts this way because folding consumes
them as values: a `.constant` operand fact is handed to the folder as the
operand's value.
-/
def _root_.Veir.AbstractConstant.DescribesExactly (a : AbstractConstant) (v : RuntimeValue) : Prop :=
  match a with
  | .top => True
  | .bottom => False
  | .constant c => v = .int c.bitwidth c.value

/-- Every abstract operand fact describes its concrete operand exactly. -/
def OperandsExact (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array RuntimeValue) : Prop :=
  ∀ (j : Nat) (a : AbstractConstant) (v : RuntimeValue),
    abstractOperands[j]? = some a → concreteOperands[j]? = some v → a.DescribesExactly v

/--
Every abstract operand fact refines its concrete operand
(`AbstractConstant.Refines`). This is the relation `transfer_sound` establishes
for results, so it is the one that composes along an execution.
-/
def OperandsRefine (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array RuntimeValue) : Prop :=
  ∀ (j : Nat) (a : AbstractConstant) (v : RuntimeValue),
    abstractOperands[j]? = some a → concreteOperands[j]? = some v → a.Refines v

/-- An exact description is in particular a refinement. -/
theorem refines_of_describesExactly {a : AbstractConstant} {v : RuntimeValue}
    (h : a.DescribesExactly v) : a.Refines v := by
  cases a with
  | top => trivial
  | bottom => exact h.elim
  | constant c =>
    simp only [AbstractConstant.DescribesExactly] at h
    subst h
    show RuntimeValue.int c.bitwidth c.value ⊒ RuntimeValue.int c.bitwidth c.value
    exact RuntimeValue.isRefinedBy_refl _

/-- The abstraction of a runtime value refines that value. -/
theorem refines_ofRuntimeValue (v : RuntimeValue) :
    (AbstractConstant.ofRuntimeValue v).Refines v := by
  cases v with
  | int bitwidth value =>
    show RuntimeValue.int bitwidth value ⊒ RuntimeValue.int bitwidth value
    exact RuntimeValue.isRefinedBy_refl _
  | _ => trivial

/-- The constants handed to the folder agree with the concrete operands. -/
theorem constOperandsAgree_of_operandsExact
    {abstractOperands : Array AbstractConstant} {concreteOperands : Array RuntimeValue}
    (hOperands : OperandsExact abstractOperands concreteOperands)
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
  have hExact := hOperands j a w ha hw
  cases a with
  | constant c =>
    simp only [Option.some.injEq] at hv
    simp only [AbstractConstant.DescribesExactly] at hExact
    rw [hw, hExact, ← hv]
  | top => simp at hv
  | bottom => simp at hv

/-- A sound fold decision yields a sound abstract fact. -/
theorem ofFoldDecision_soundFor
    (decision : FoldDecision) (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array RuntimeValue) (outcome : Interp (Array RuntimeValue)) (i : Nat)
    (hOperands : OperandsExact abstractOperands concreteOperands)
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
      obtain ⟨claimed, hValue, hRefines⟩ := hDecision
      apply AbstractConstant.refines_of_isRefinedBy hRefines
      cases decision with
      | useConstant value =>
        simp only [FoldDecision.valueFor, Option.some.injEq] at hValue
        subst hValue
        exact refines_ofRuntimeValue value
      | useOperand j =>
        simp only [FoldDecision.valueFor] at hValue
        simp only [AbstractConstant.ofFoldDecision]
        cases ha : abstractOperands[j]? with
        | none => exact AbstractConstant.refines_top claimed
        | some a => exact refines_of_describesExactly (hOperands j a claimed ha hValue)

/--
Local soundness of the transfer function for exactly described operands.

This is the core step of `transfer_sound`. Every result fact `transfer` produces
refines the result of interpreting the operation on its concrete operands
(`AbstractConstant.SoundFor`, built on `AbstractConstant.Refines`). UB and
interpreter failure constrain nothing.

The hypotheses:
* `hTable`, `hHonest` — the per-opcode obligations of `foldsTo_sound`;
* `hOperands`, `hSize` — the operand facts describe the concrete operands
  exactly (`OperandsExact`, built on `AbstractConstant.DescribesExactly`). This
  also rules out `⊥` operand facts, so the `⊥` branch of `transfer` needs no
  separate premise;
* `hArity` — the concrete operands are as many as the operation has;
* `hConstSuccessors` — a constant-like operation has no successors, so the
  interpretation `ValuePtr.constantValue` runs agrees with `interpretPure`.

On its own this theorem is asymmetric: operand facts must describe their
operands exactly, result facts are only guaranteed to refine theirs. A result fact may claim a value where the execution
produced poison (`arith.addui_extended x, 0` with poison `x`), and such a fact
does not describe the value exactly, so this theorem does not chain across
operations. `transfer_sound` removes the asymmetry by relaxing the operands to
refinement as well, via `interpretOp'_monotone`; use that theorem for composition.
-/
theorem transfer_sound_exact
    (op : OperationPtr) (irCtx : WfIRContext OpCode)
    (abstractOperands : Array AbstractConstant) (concreteOperands : Array RuntimeValue)
    (hTable : FoldTableSound (op.getOpType! irCtx.raw))
    (hHonest : PropagatesPoisonHonestly (op.getOpType! irCtx.raw))
    (hOperands : OperandsExact abstractOperands concreteOperands)
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
          exact refines_ofRuntimeValue actual
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
          hTable hHonest (constOperandsAgree_of_operandsExact hOperands hSize)
          (by simp [constOperands, hSize]) hFold hDecision
  · rw [show transfer op abstractOperands irCtx =
        Array.replicate (op.getNumResults! irCtx.raw) ⊤ by
          simp [transfer, hRegions0, hBot, hConst, hInBounds], hTop]
    exact AbstractConstant.soundFor_top _ i

/--
The operands the folder effectively sees: every operand with a `.constant c`
fact is replaced by `c` itself, and the rest are left as they are.
-/
def refineOperands (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array RuntimeValue) : Array RuntimeValue :=
  concreteOperands.mapIdx fun j v =>
    match abstractOperands[j]? with
    | some (.constant c) => .int c.bitwidth c.value
    | _ => v

@[simp]
theorem refineOperands_size (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array RuntimeValue) :
    (refineOperands abstractOperands concreteOperands).size = concreteOperands.size := by
  simp [refineOperands]

/-- The operand facts describe the refined operands exactly. -/
theorem operandsExact_refineOperands
    {abstractOperands : Array AbstractConstant} {concreteOperands : Array RuntimeValue}
    (hOperands : OperandsRefine abstractOperands concreteOperands) :
    OperandsExact abstractOperands (refineOperands abstractOperands concreteOperands) := by
  intro j a w ha hw
  simp only [refineOperands, Array.getElem?_mapIdx, Option.map_eq_some_iff] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  cases a with
  | top => trivial
  | bottom => exact hOperands j .bottom v ha hv
  | constant c => simp [ha, AbstractConstant.DescribesExactly]

/-- Each concrete operand is refined by its counterpart in `refineOperands`. -/
theorem isRefinedBy_refineOperands
    {abstractOperands : Array AbstractConstant} {concreteOperands : Array RuntimeValue}
    (hOperands : OperandsRefine abstractOperands concreteOperands) :
    concreteOperands ⊒ refineOperands abstractOperands concreteOperands := by
  refine ⟨(refineOperands_size _ _).symm, fun j hj => ?_⟩
  have hRefined : (refineOperands abstractOperands concreteOperands)[j]! =
      match abstractOperands[j]? with
      | some (.constant c) => .int c.bitwidth c.value
      | _ => concreteOperands[j]! := by
    simp [refineOperands, hj]
  rw [hRefined]
  cases ha : abstractOperands[j]? with
  | none => exact RuntimeValue.isRefinedBy_refl _
  | some a =>
    cases a with
    | constant c =>
      exact hOperands j (.constant c) _ ha (by simp [hj])
    | top => exact RuntimeValue.isRefinedBy_refl _
    | bottom => exact RuntimeValue.isRefinedBy_refl _

/--
If interpreting `operands` is refined by interpreting `operands'`, a fact sound
for the latter outcome is sound for the former: the fact's claim refines the
refined result, which in turn refines the original result.
-/
theorem soundFor_of_interp_isRefinedBy
    {a : AbstractConstant} {i : Nat}
    {source target : Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction)}
    (hRefines : Interp.isRefinedBy
      (fun (r₁ r₂ : Array RuntimeValue × MemoryState × Option ControlFlowAction) =>
        RuntimeValue.arrayIsRefinedBy r₁.1 r₂.1 ∧ r₁.2.1 = r₂.2.1 ∧
        ControlFlowAction.optionIsRefinedBy r₁.2.2 r₂.2.2) source target)
    (hSound : a.SoundFor (target.map (fun (results, _, _) => results)) i) :
    a.SoundFor (source.map (fun (results, _, _) => results)) i := by
  cases source with
  | fail => trivial
  | ub => trivial
  | ok sourceResult =>
    cases target with
    | fail => exact hRefines.elim
    | ub => exact hRefines.elim
    | ok targetResult =>
      obtain ⟨⟨hSizeEq, hPointwise⟩, -, -⟩ := hRefines
      simp only [Interp.map_ok, AbstractConstant.SoundFor] at hSound ⊢
      cases hv : sourceResult.1[i]? with
      | none => trivial
      | some v =>
        have hi : i < sourceResult.1.size := (Array.getElem?_eq_some_iff.mp hv).1
        have hi' : i < targetResult.1.size := by omega
        have hTarget : targetResult.1[i]? = some targetResult.1[i]! := by
          simp [hi']
        rw [hTarget] at hSound
        have hvEq : v = sourceResult.1[i]! := by simp_all
        subst hvEq
        exact AbstractConstant.refines_of_isRefinedBy (hPointwise i hi) hSound

/--
Local soundness of the constant-propagation transfer function.

Every result fact `transfer` produces refines the result of interpreting the
operation on its concrete operands (`AbstractConstant.SoundFor`, built on
`AbstractConstant.Refines`), provided every operand fact refines its concrete
operand (`OperandsRefine`). Because operands and results are related by the same
relation, `Refines`, the theorem composes along an execution.

The proof reduces to `transfer_sound_exact`. The operands the folder is told
about, `refineOperands`, are described exactly by the operand facts
(`OperandsExact`) and refine the concrete operands, and interpretation is
monotone under refinement.

That last step is the project axiom `interpretOp'_monotone`
(`Veir/Interpreter/Lemmas.lean`), so this theorem is sound relative to it.

The remaining hypotheses are those of `transfer_sound_exact`:
* `hTable`, `hHonest` — the per-opcode obligations of `foldsTo_sound`;
* `hSize` — one fact per concrete operand;
* `hArity` — the concrete operands are as many as the operation has;
* `hConstSuccessors` — a constant-like operation has no successors.
-/
theorem transfer_sound
    (op : OperationPtr) (irCtx : WfIRContext OpCode)
    (abstractOperands : Array AbstractConstant) (concreteOperands : Array RuntimeValue)
    (hTable : FoldTableSound (op.getOpType! irCtx.raw))
    (hHonest : PropagatesPoisonHonestly (op.getOpType! irCtx.raw))
    (hOperands : OperandsRefine abstractOperands concreteOperands)
    (hSize : abstractOperands.size = concreteOperands.size)
    (hArity : concreteOperands.size = op.getNumOperands! irCtx.raw)
    (hConstSuccessors : (op.getOpType! irCtx.raw).isConstantLike = true →
      op.getSuccessors! irCtx.raw = #[])
    (i : Nat) :
    ((transfer op abstractOperands irCtx)[i]?.getD ⊤).SoundFor
      (interpretPure (op.getOpType! irCtx.raw)
        (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw))
        (op.getResultTypes! irCtx.raw) concreteOperands) i := by
  have hExact := transfer_sound_exact op irCtx abstractOperands
    (refineOperands abstractOperands concreteOperands) hTable hHonest
    (operandsExact_refineOperands hOperands) (by simp [hSize])
    (by simp [hArity]) hConstSuccessors i
  have hMono := interpretOp'_monotone (op.getOpType! irCtx.raw)
    (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw)) (op.getResultTypes! irCtx.raw)
    concreteOperands (refineOperands abstractOperands concreteOperands) #[] MemoryState.empty
    (isRefinedBy_refineOperands hOperands)
  exact soundFor_of_interp_isRefinedBy hMono hExact

end SparseConstantPropagation

def SparseConstantPropagationAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .sparseConstant
    SparseConstantPropagation.kind
    SparseConstantPropagation.transfer

end Veir
