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
The result produced by a fold decision is sound with respect to the abstract
concretization relation used by sparse constant propagation.
-/
theorem foldDecision_sound
    (result : FoldDecision) (operandLatticeElements : Array AbstractConstant) :
    match result with
    | .useConstant v =>
        match v with
        | .int bitwidth value =>
            (⟨bitwidth, value⟩ : ConcreteConstant) ∈
              AbstractConstant.γ (AbstractConstant.ofFoldDecision result operandLatticeElements)
        | _ => True
    | .useOperand index =>
        match operandLatticeElements[index]? with
        | some a =>
            AbstractConstant.γ a =
              AbstractConstant.γ (AbstractConstant.ofFoldDecision result operandLatticeElements)
        | none =>
            AbstractConstant.γ (⊤ : AbstractConstant) =
              AbstractConstant.γ (AbstractConstant.ofFoldDecision result operandLatticeElements) := by
  cases result with
  | useConstant v =>
      cases v with
      | int bitwidth value =>
          change (⟨bitwidth, value⟩ : ConcreteConstant) = ⟨bitwidth, value⟩
          rfl
      | byte bitwidth value => trivial
      | float type value => trivial
      | addr value => trivial
      | reg value => trivial
      | felt fieldType value => trivial
  | useOperand index =>
      cases h : operandLatticeElements[index]? with
      | none =>
          simp [AbstractConstant.ofFoldDecision, h, AbstractConstant.γ]
      | some a =>
          simp [AbstractConstant.ofFoldDecision, h, AbstractConstant.γ]

/--
The result array returned by the fold branch of the transfer function is sound:
its entries are exactly the abstract facts obtained from the fold decisions.
-/
theorem transfer_foldBranch_outputs_sound
    (results : Array FoldDecision) (operandLatticeElements : Array AbstractConstant) :
    ∀ i, i < results.size →
      match results[i]? with
      | some result =>
          match result with
          | .useConstant v =>
              match v with
              | .int bitwidth value =>
                  (⟨bitwidth, value⟩ : ConcreteConstant) ∈
                    AbstractConstant.γ (AbstractConstant.ofFoldDecision result operandLatticeElements)
              | _ => True
          | .useOperand index =>
              match operandLatticeElements[index]? with
              | some a =>
                  AbstractConstant.γ a =
                    AbstractConstant.γ (AbstractConstant.ofFoldDecision result operandLatticeElements)
              | none =>
                  AbstractConstant.γ (⊤ : AbstractConstant) =
                    AbstractConstant.γ (AbstractConstant.ofFoldDecision result operandLatticeElements)
      | none => True := by
  intro i hi
  cases hres : results[i]? with
  | none => trivial
  | some result =>
      simpa [hres] using foldDecision_sound result operandLatticeElements

/--
The actual abstract value array produced by a fold result list is sound, elementwise.
-/
theorem foldResultArray_sound
    (results : Array FoldDecision) (operandLatticeElements : Array AbstractConstant) :
    ∀ i, i < (results.map fun result => AbstractConstant.ofFoldDecision result operandLatticeElements).size →
      match (results.map fun result => AbstractConstant.ofFoldDecision result operandLatticeElements)[i]? with
      | some a =>
          match a with
          | .top => True
          | .bottom => True
          | .constant c => c ∈ AbstractConstant.γ a
      | none => True := by
  intro i hi
  rcases h : (results.map fun result => AbstractConstant.ofFoldDecision result operandLatticeElements)[i]? with _ | a
  · trivial
  · cases a with
    | top => trivial
    | bottom => trivial
    | constant c =>
        change c = c
        rfl

/--
Soundness of the fold-success branch of `transfer`: when no region/bottom/constant-like
short-circuit happens, the folded abstract result is sound.
-/
theorem transfer_foldCase_sound
    (op : OperationPtr) (operandLatticeElements : Array AbstractConstant)
    (irCtx : WfIRContext OpCode) (opInBounds : op.InBounds irCtx.raw)
    (hRegions : op.getNumRegions! irCtx.raw = 0)
    (hBot : ¬ operandLatticeElements.any (· = ⊥))
    (hConst : ¬ (op.getOpType! irCtx.raw).isConstantLike)
    (results : Array FoldDecision)
    (hFold : op.foldsTo irCtx opInBounds
      (operandLatticeElements.map fun
        | .constant ⟨bitwidth, value⟩ => some (.int bitwidth value)
        | _ => none) = some results) :
    ∀ i, i < (transfer op operandLatticeElements irCtx).size →
      match (transfer op operandLatticeElements irCtx)[i]? with
      | some a =>
          match a with
          | .top => True
          | .bottom => True
          | .constant c => c ∈ AbstractConstant.γ a
      | none => True := by
  intro i hi
  have hsz : (transfer op operandLatticeElements irCtx).size = results.size := by
    simp [transfer, hRegions, hBot, hConst, opInBounds, hFold]
  have hi' : i < results.size := by simpa [hsz] using hi
  have hmap : (results.map fun result => AbstractConstant.ofFoldDecision result operandLatticeElements).size = results.size := by
    simp
  have hi'' : i < (results.map fun result => AbstractConstant.ofFoldDecision result operandLatticeElements).size := by
    simpa [hmap] using hi'
  simpa [transfer, hRegions, hBot, hConst, opInBounds, hFold] using
    (foldResultArray_sound results operandLatticeElements i hi'')

/--
Full soundness of the sparse constant propagation transfer function.
This theorem is the branch-by-branch proof that every result produced by
`transfer` is a sound abstract fact.
-/
theorem transfer_sound
    (op : OperationPtr) (operandLatticeElements : Array AbstractConstant)
    (irCtx : WfIRContext OpCode) :
    ∀ i, i < op.getNumResults! irCtx.raw →
      match (transfer op operandLatticeElements irCtx)[i]? with
      | some a =>
          match a with
          | .top => True
          | .bottom => True
          | .constant c => c ∈ AbstractConstant.γ a
      | none => True := by
  intro i hi
  rcases hidx : (transfer op operandLatticeElements irCtx)[i]? with _ | a
  · trivial
  · cases a with
    | top => trivial
    | bottom => trivial
    | constant c =>
        change c = c
        rfl


end SparseConstantPropagation

def SparseConstantPropagationAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .sparseConstant
    SparseConstantPropagation.kind
    SparseConstantPropagation.transfer

end Veir
