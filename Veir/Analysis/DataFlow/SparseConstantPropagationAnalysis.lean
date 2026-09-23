import Veir.Analysis.DataFlow.Domains.ConstantSoundness
import Veir.Analysis.DataFlow.Domains.ConstantDomain
import Veir.Analysis.DataFlow.SparseForwardDataFlowAnalysis
import Veir.Interfaces.FoldInterfaces

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
An indexed fold result is abstractly sound whenever a concrete output is
actually realized by the corresponding fold decision.
-/
theorem foldResult_realizes_sound
    (results : Array FoldDecision)
    (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array ConcreteConstant)
    (hOperands : ∀ (index : Nat) (c : ConcreteConstant) (a : AbstractConstant),
      concreteOperands[index]? = some c →
      abstractOperands[index]? = some a → c ∈ AbstractConstant.γ a)
    (i : Nat) (result : FoldDecision) (output : ConcreteConstant)
    (hResult : results[i]? = some result)
    (hRealizes : AbstractConstant.foldDecisionRealizes result concreteOperands output) :
    output ∈ AbstractConstant.γ
      ((results.map (fun decision => AbstractConstant.ofFoldDecision decision abstractOperands))[i]?.getD ⊤) := by
  have hDecision :
      (results.map (fun decision => AbstractConstant.ofFoldDecision decision abstractOperands))[i]? =
        some (AbstractConstant.ofFoldDecision result abstractOperands) := by
    simp [hResult]
  rw [hDecision]
  simp only [Option.getD_some]
  exact AbstractConstant.ofFoldDecision_realizes_sound result abstractOperands concreteOperands output
    hOperands hRealizes

/--
Concrete soundness of the successful fold branch of `transfer`. The
`hRealizes` premise is the semantic obligation supplied by the concrete
operation evaluator or by a dialect fold proof.
-/
theorem transfer_foldCase_realizes_sound
    (op : OperationPtr)
    (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array ConcreteConstant)
    (hOperands : ∀ (index : Nat) (c : ConcreteConstant) (a : AbstractConstant),
      concreteOperands[index]? = some c →
      abstractOperands[index]? = some a → c ∈ AbstractConstant.γ a)
    (irCtx : WfIRContext OpCode) (opInBounds : op.InBounds irCtx.raw)
    (hRegions : op.getNumRegions! irCtx.raw = 0)
    (hBot : ¬ abstractOperands.any (· = ⊥))
    (hConst : ¬ (op.getOpType! irCtx.raw).isConstantLike)
    (results : Array FoldDecision)
    (hFold : op.foldsTo irCtx opInBounds
      (abstractOperands.map fun
        | .constant ⟨bitwidth, value⟩ => some (.int bitwidth value)
        | _ => none) = some results)
    (i : Nat) (result : FoldDecision) (output : ConcreteConstant)
    (hResult : results[i]? = some result)
    (hRealizes : AbstractConstant.foldDecisionRealizes result concreteOperands output) :
    output ∈ AbstractConstant.γ ((transfer op abstractOperands irCtx)[i]?.getD ⊤) := by
  have hTransfer :
      transfer op abstractOperands irCtx =
        results.map (fun decision => AbstractConstant.ofFoldDecision decision abstractOperands) := by
    simp [transfer, hRegions, hBot, hConst, opInBounds, hFold]
  rw [hTransfer]
  exact foldResult_realizes_sound results abstractOperands concreteOperands hOperands i result output
    hResult hRealizes

/--
Array-level local soundness for the successful fold branch. This is the
transfer theorem needed by the dataflow proof once the concrete evaluator has
shown that each concrete result is realized by its corresponding fold
decision.
-/
theorem transfer_foldCase_concrete_sound
    (op : OperationPtr)
    (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array ConcreteConstant)
    (hOperands : ∀ (index : Nat) (c : ConcreteConstant) (a : AbstractConstant),
      concreteOperands[index]? = some c →
      abstractOperands[index]? = some a → c ∈ AbstractConstant.γ a)
    (irCtx : WfIRContext OpCode) (opInBounds : op.InBounds irCtx.raw)
    (hRegions : op.getNumRegions! irCtx.raw = 0)
    (hBot : ¬ abstractOperands.any (· = ⊥))
    (hConst : ¬ (op.getOpType! irCtx.raw).isConstantLike)
    (results : Array FoldDecision)
    (hFold : op.foldsTo irCtx opInBounds
      (abstractOperands.map fun
        | .constant ⟨bitwidth, value⟩ => some (.int bitwidth value)
        | _ => none) = some results)
    (concreteResults : Array ConcreteConstant)
    (hRealizes : ∀ (i : Nat) (output : ConcreteConstant),
      concreteResults[i]? = some output →
      ∃ result, results[i]? = some result ∧
        AbstractConstant.foldDecisionRealizes result concreteOperands output) :
    ∀ (i : Nat) (output : ConcreteConstant), concreteResults[i]? = some output →
      output ∈ AbstractConstant.γ ((transfer op abstractOperands irCtx)[i]?.getD ⊤) := by
  intro i output hOutput
  obtain ⟨result, hResult, hDecision⟩ := hRealizes i output hOutput
  exact transfer_foldCase_realizes_sound op abstractOperands concreteOperands hOperands irCtx opInBounds
    hRegions hBot hConst results hFold i result output hResult hDecision

/--
Conditional concrete soundness of the complete constant-propagation transfer.
For every concrete result, the theorem proves membership in the concretization
of the abstract result returned by `transfer`.

The hypotheses expose the semantic obligations that are not determined by the
transfer definition itself:
* `hOperands` says that any concrete operand paired with an abstract operand is
  represented by that abstract fact;
* `hConstantResults` identifies `constantResults` with the array used by the
  constant-like branch;
* `hBottomSound` says that no concrete result exists when an operand is bottom;
* `hConstantSound` says that constant-like operation results belong to their
  materialized abstract constants; and
* `hFoldSound` says that every successful fold decision realizes its concrete
  result.

The region, failed-fold, and out-of-bounds branches need no semantic premise:
they return `top`, which contains every tracked concrete value.
-/
theorem transfer_conditional_sound
    (op : OperationPtr)
    (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array ConcreteConstant)
    (hOperands : ∀ (index : Nat) (c : ConcreteConstant) (a : AbstractConstant),
      concreteOperands[index]? = some c →
      abstractOperands[index]? = some a → c ∈ AbstractConstant.γ a)
    (irCtx : WfIRContext OpCode)
    (concreteResults : Array ConcreteConstant)
    (constantResults : Array AbstractConstant)
    (hConstantResults : constantResults = (op.getResults! irCtx.raw).map fun result =>
      (result.constantValue irCtx.raw).map AbstractConstant.ofRuntimeValue |>.getD
        (⊤ : AbstractConstant))
    (hBottomSound : ∀ (hBot : abstractOperands.any (· = ⊥) = true)
      (i : Nat) (output : ConcreteConstant),
      concreteResults[i]? = some output → False)
    (hConstantSound : ∀ (hConst : (op.getOpType! irCtx.raw).isConstantLike = true)
      (i : Nat) (output : ConcreteConstant),
      concreteResults[i]? = some output →
      output ∈ AbstractConstant.γ (constantResults[i]?.getD (⊤ : AbstractConstant)))
    (hFoldSound : ∀ (results : Array FoldDecision) (i : Nat) (output : ConcreteConstant),
      op.getNumRegions! irCtx.raw = 0 →
      ¬ abstractOperands.any (· = ⊥) →
      ¬ (op.getOpType! irCtx.raw).isConstantLike →
      (opInBounds : op.InBounds irCtx.raw) →
      op.foldsTo irCtx opInBounds
        (abstractOperands.map fun
          | .constant ⟨bitwidth, value⟩ => some (.int bitwidth value)
          | _ => none) = some results →
      concreteResults[i]? = some output →
      ∃ result, results[i]? = some result ∧
        AbstractConstant.foldDecisionRealizes result concreteOperands output) :
    ∀ (i : Nat) (output : ConcreteConstant), concreteResults[i]? = some output →
      output ∈ AbstractConstant.γ ((transfer op abstractOperands irCtx)[i]?.getD ⊤) := by
  intro i output hOutput
  by_cases hRegions : op.getNumRegions! irCtx.raw ≠ 0
  · have hTop : ((Array.replicate (op.getNumResults! irCtx.raw) ⊤)[i]?.getD
      (⊤ : AbstractConstant)) = ⊤ := by
      rw [Array.getElem?_replicate]
      split <;> rfl
    rw [show transfer op abstractOperands irCtx = Array.replicate (op.getNumResults! irCtx.raw) ⊤ by
      simp [transfer, hRegions]]
    rw [hTop]
    exact AbstractConstant.γ_top_eq output
  · have hRegions0 : op.getNumRegions! irCtx.raw = 0 := by simpa using hRegions
    by_cases hBot : abstractOperands.any (· = ⊥)
    · exact False.elim (hBottomSound hBot i output hOutput)
    · by_cases hConst : ((op.getOpType! irCtx.raw).isConstantLike = true)
      · simpa [transfer, hRegions0, hBot, hConst, hConstantResults] using
          hConstantSound hConst i output hOutput
      · by_cases hInBounds : op.InBounds irCtx.raw
        · let constOperands :=
            abstractOperands.map fun
              | .constant ⟨bitwidth, value⟩ => some (RuntimeValue.int bitwidth value)
              | _ => none
          cases hFold : op.foldsTo irCtx hInBounds constOperands with
          | none =>
              have hTop : ((Array.replicate (op.getNumResults! irCtx.raw) ⊤)[i]?.getD
                  (⊤ : AbstractConstant)) = ⊤ := by
                rw [Array.getElem?_replicate]
                split <;> rfl
              rw [show transfer op abstractOperands irCtx = Array.replicate (op.getNumResults! irCtx.raw) ⊤ by
                simp [transfer, hRegions0, hBot, hConst, hInBounds, hFold, constOperands]]
              rw [hTop]
              exact AbstractConstant.γ_top_eq output
          | some results =>
              exact transfer_foldCase_concrete_sound op abstractOperands concreteOperands hOperands
                irCtx hInBounds hRegions0 hBot hConst results hFold concreteResults
                (fun j result hResult => hFoldSound results j result hRegions0 hBot hConst
                  hInBounds hFold hResult) i output hOutput
        · have hTop : ((Array.replicate (op.getNumResults! irCtx.raw) ⊤)[i]?.getD
              (⊤ : AbstractConstant)) = ⊤ := by
            rw [Array.getElem?_replicate]
            split <;> rfl
          rw [show transfer op abstractOperands irCtx = Array.replicate (op.getNumResults! irCtx.raw) ⊤ by
            simp [transfer, hRegions0, hBot, hConst, hInBounds]]
          rw [hTop]
          exact AbstractConstant.γ_top_eq output


end SparseConstantPropagation

def SparseConstantPropagationAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .sparseConstant
    SparseConstantPropagation.kind
    SparseConstantPropagation.transfer

end Veir
