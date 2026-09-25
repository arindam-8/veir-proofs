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
What `transfer` tells the folder about the operands: a `.constant c` fact
becomes "this operand is `c`", every other fact "unknown". This is the only
place the analysis turns facts into runtime values.
-/
def foldInputs (facts : Array AbstractConstant) : Array (Option RuntimeValue) :=
  facts.map fun
    | .constant ⟨bitwidth, value⟩ => some (.int bitwidth value)
    | _ => none

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
    match op.foldsTo irCtx opInBounds (foldInputs operandLatticeElements) with
    | some results =>
      results.map fun result => AbstractConstant.ofFoldDecision result operandLatticeElements
    | none =>
      Array.replicate numResults ⊤

  else
    Array.replicate numResults ⊤

/--
Every operand lies in `γ` of its fact. This is `γ` pointwise: the relation
`transfer_sound` assumes of the operands and establishes for the results, so it
composes along an execution.
-/
def OperandsInGamma (facts : Array AbstractConstant) (vs : Array RuntimeValue) : Prop :=
  ∀ (j : Nat) (a : AbstractConstant) (v : RuntimeValue),
    facts[j]? = some a → vs[j]? = some v → v ∈ AbstractConstant.γ a

/--
The operands the folder's inputs describe: `c` where `foldInputs` tells the
folder the operand is `c`, the real operand elsewhere. The folder's contract
(`foldsTo_sound`) is about exactly these operands.
-/
def foldedOperands (facts : Array AbstractConstant) (vs : Array RuntimeValue) :
    Array RuntimeValue :=
  vs.mapIdx fun j v =>
    match facts[j]? with
    | some (.constant c) => .int c.bitwidth c.value
    | _ => v

@[simp]
theorem foldedOperands_size (facts : Array AbstractConstant) (vs : Array RuntimeValue) :
    (foldedOperands facts vs).size = vs.size := by
  simp [foldedOperands]

/-- The folder's inputs agree with `foldedOperands`, by construction. -/
theorem constOperandsAgree_foldedOperands (facts : Array AbstractConstant)
    (vs : Array RuntimeValue) (hSize : facts.size = vs.size) :
    ConstOperandsAgree (foldInputs facts) (foldedOperands facts vs) := by
  intro j v hConst
  simp only [foldInputs, Array.getElem?_map, Option.map_eq_some_iff] at hConst
  obtain ⟨a, ha, hv⟩ := hConst
  have hj : j < vs.size := by
    have := (Array.getElem?_eq_some_iff.mp ha).1
    omega
  cases a with
  | constant c =>
    obtain ⟨bitwidth, value⟩ := c
    simp only [Option.some.injEq] at hv
    simp [foldedOperands, hj, ha, ← hv]
  | top => simp at hv
  | bottom => simp at hv

/-- The facts still hold of `foldedOperands`. -/
theorem operandsInGamma_foldedOperands {facts : Array AbstractConstant} {vs : Array RuntimeValue}
    (hOperands : OperandsInGamma facts vs) : OperandsInGamma facts (foldedOperands facts vs) := by
  intro j a w ha hw
  simp only [foldedOperands, Array.getElem?_mapIdx, Option.map_eq_some_iff] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  cases a with
  | top => trivial
  | bottom => exact hOperands j .bottom v ha hv
  | constant c =>
    simp only [ha]
    exact AbstractConstant.mem_γ_constant.mpr (RuntimeValue.isRefinedBy_refl _)

/-- The real operands refine `foldedOperands`: this is `γ` at the `.constant` facts. -/
theorem isRefinedBy_foldedOperands {facts : Array AbstractConstant} {vs : Array RuntimeValue}
    (hOperands : OperandsInGamma facts vs) : vs ⊒ foldedOperands facts vs := by
  refine ⟨(foldedOperands_size _ _).symm, fun j hj => ?_⟩
  have hFolded : (foldedOperands facts vs)[j]! =
      match facts[j]? with
      | some (.constant c) => .int c.bitwidth c.value
      | _ => vs[j]! := by
    simp [foldedOperands, hj]
  rw [hFolded]
  cases ha : facts[j]? with
  | none => exact RuntimeValue.isRefinedBy_refl _
  | some a =>
    cases a with
    | constant c => exact hOperands j (.constant c) _ ha (by simp [hj])
    | top => exact RuntimeValue.isRefinedBy_refl _
    | bottom => exact RuntimeValue.isRefinedBy_refl _

/-- A fold decision that is sound for `operands` yields a fact that is sound. -/
theorem ofFoldDecision_soundFor
    (decision : FoldDecision) (facts : Array AbstractConstant)
    (operands : Array RuntimeValue) (outcome : Interp (Array RuntimeValue)) (i : Nat)
    (hOperands : OperandsInGamma facts operands)
    (hDecision : decision.SoundFor operands outcome i) :
    (AbstractConstant.ofFoldDecision decision facts).SoundFor outcome i := by
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
      apply AbstractConstant.mem_γ_of_isRefinedBy hRefines
      cases decision with
      | useConstant value =>
        simp only [FoldDecision.valueFor, Option.some.injEq] at hValue
        subst hValue
        exact AbstractConstant.mem_γ_ofRuntimeValue value
      | useOperand j =>
        simp only [FoldDecision.valueFor] at hValue
        simp only [AbstractConstant.ofFoldDecision]
        cases ha : facts[j]? with
        | none => exact AbstractConstant.mem_γ_top claimed
        | some a => exact hOperands j a claimed ha hValue

/--
If interpreting `operands` is refined by interpreting `operands'`, a fact sound
for the latter outcome is sound for the former: `γ` is closed under refinement.
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
        exact AbstractConstant.mem_γ_of_isRefinedBy (hPointwise i hi) hSound

/--
Soundness of a fold decision for the real operands.

The folder decided on `foldInputs facts`, and its contract (`foldsTo_sound`) is
about the operands those inputs describe, `foldedOperands facts vs`. The real
operands only lie in `γ` of the facts: at a `.constant c` fact the real operand
may be poison where the folder assumed `c`. The real operands refine the folded
ones (`isRefinedBy_foldedOperands`), so if interpretation is monotone the real
run refines the folded run, and a fact sound for the folded run is sound for the
real one (`soundFor_of_interp_isRefinedBy`).

This is the only lemma that relates the folder's run to the real run, and the
only use of monotonicity. It currently takes it from the project axiom
`interpretOp'_monotone` (`Veir/Interpreter/Lemmas.lean`), which is false for
`llvm.freeze`; see `InterpretMonotone` in
`Veir/Interpreter/Refinement/OpMonotone.lean`.
-/
theorem fold_sound
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (facts : Array AbstractConstant) (vs : Array RuntimeValue)
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hTable : FoldTableSound opType) (hPoison : PropagatesPoisonSound opType)
    (hOperands : OperandsInGamma facts vs) (hSize : facts.size = vs.size)
    (hFold : OpCode.foldsTo opType properties resultTypes (foldInputs facts) = some decisions)
    (hDecision : decisions[i]? = some decision) :
    (AbstractConstant.ofFoldDecision decision facts).SoundFor
      (interpretPure opType properties resultTypes vs) i := by
  have hFolded := foldsTo_sound opType properties resultTypes (foldedOperands facts vs)
    (foldInputs facts) decisions i decision hTable hPoison
    (constOperandsAgree_foldedOperands facts vs hSize) (by simp [foldInputs, hSize])
    hFold hDecision
  have hFact := ofFoldDecision_soundFor decision facts (foldedOperands facts vs) _ i
    (operandsInGamma_foldedOperands hOperands) hFolded
  have hMono := interpretOp'_monotone opType properties resultTypes vs
    (foldedOperands facts vs) #[] MemoryState.empty (isRefinedBy_foldedOperands hOperands)
  exact soundFor_of_interp_isRefinedBy hMono hFact

/--
Local soundness of the constant-propagation transfer function.

If every operand lies in `γ` of its fact (`OperandsInGamma`), every result lies
in `γ` of the fact `transfer` produces (`AbstractConstant.SoundFor`), whenever
interpretation succeeds; UB and interpreter failure constrain nothing. Operands
and results use the same relation, `γ`, so the theorem composes along an
execution.

Folding is justified by `fold_sound`, the one place where the folder's run is
related to the real run.

Hypotheses:
* `hTable`, `hPoison` — per-opcode obligations of `foldsTo_sound`;
* `hSize`, `hArity` — one fact per operand, as many operands as the op has;
* `hConstSuccessors` — a constant-like operation has no successors, so the
  interpretation `ValuePtr.constantValue` runs agrees with `interpretPure`.
-/
theorem transfer_sound
    (op : OperationPtr) (irCtx : WfIRContext OpCode)
    (abstractOperands : Array AbstractConstant) (concreteOperands : Array RuntimeValue)
    (hTable : FoldTableSound (op.getOpType! irCtx.raw))
    (hPoison : PropagatesPoisonSound (op.getOpType! irCtx.raw))
    (hOperands : OperandsInGamma abstractOperands concreteOperands)
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
    exact AbstractConstant.not_mem_γ_bot _ this
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
          exact AbstractConstant.mem_γ_ofRuntimeValue actual
  by_cases hInBounds : op.InBounds irCtx.raw
  · cases hFold : op.foldsTo irCtx hInBounds (foldInputs abstractOperands) with
    | none =>
      rw [show transfer op abstractOperands irCtx =
          Array.replicate (op.getNumResults! irCtx.raw) ⊤ by
            simp [transfer, hRegions0, hBot, hConst, hInBounds, hFold], hTop]
      exact AbstractConstant.soundFor_top _ i
    | some decisions =>
      rw [show transfer op abstractOperands irCtx =
          decisions.map (fun decision => AbstractConstant.ofFoldDecision decision abstractOperands) by
            simp [transfer, hRegions0, hBot, hConst, hInBounds, hFold]]
      cases hDecision : decisions[i]? with
      | none => simp [hDecision]
      | some decision =>
        simp only [Array.getElem?_map, hDecision, Option.map_some, Option.getD_some]
        simp only [OperationPtr.foldsTo] at hFold
        simp [guard, Option.bind_eq_some_iff] at hFold
        obtain ⟨_, hFold⟩ := hFold
        rw [← OperationPtr.getProperties!_eq_getProperties hInBounds (by grind),
          ← OperationPtr.getResultTypes!_eq_getResultTypes hInBounds,
          ← OperationPtr.getOpType!_eq_getOpType hInBounds] at hFold
        exact fold_sound _ _ _ abstractOperands concreteOperands decisions i decision
          hTable hPoison hOperands hSize hFold hDecision
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
