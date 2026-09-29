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
What `transferExact` tells the folder about the operands: an `.exact v` fact
becomes "this operand is `v`", every other fact "unknown". Only exact facts are
passed on, so every value the folder is told is the real operand. This is the
only place the analysis turns facts into runtime values.
-/
def foldInputs (facts : Array AbstractConstant) : Array (Option RuntimeValue) :=
  facts.map fun
    | .exact value => some value
    | _ => none

/--
Evaluate an operation whose operands are all `exact`, with the evaluation the
folder uses. The results equal the real ones, so they are `exact` too; UB gives
poison, as it does in the folder. Returns `none` when some operand is not
`exact` or the operation cannot be evaluated.
-/
def evaluateExact
    (op : OperationPtr)
    (operandLatticeElements : Array AbstractConstant)
    (irCtx : WfIRContext OpCode) : Option (Array AbstractConstant) := do
  let values ← (foldInputs operandLatticeElements).mapM id
  let opType := op.getOpType! irCtx.raw
  let resultTypes := op.getResultTypes! irCtx.raw
  match foldEvaluate opType (op.getProperties! irCtx.raw opType) resultTypes values with
  | .ok results => some (results.map AbstractConstant.exact)
  | .ub => some (resultTypes.map fun type =>
      (RuntimeValue.getPoisonForType type).map AbstractConstant.exact |>.getD ⊤)
  | .fail => none

/--
Transfer function for operands whose facts pin their values down, or say
nothing about them: `transfer` removes `upTo` facts before calling it.
- operations with regions conservatively force results to `⊤`,
- any operand at `⊥` leave results as `⊥` and delay propagation,
- constant-like operations give their exact value,
- if every operand is `exact`, the operation is evaluated (`evaluateExact`),
- otherwise we try to fold and weaken the result (if there isn't a result from
  the fold, return `⊤`)
-/
def transferExact
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
      (result.constantValue irCtx.raw).map AbstractConstant.exact |>.getD ⊤

  else match evaluateExact op operandLatticeElements irCtx with
  | some results => results
  | none =>
    -- Attempt folding the lattice elements of the operands
    if opInBounds : op.InBounds irCtx.raw then
      match op.foldsTo irCtx opInBounds (foldInputs operandLatticeElements) with
      | some results =>
        results.map fun result => AbstractConstant.ofFoldDecision result operandLatticeElements
      | none =>
        Array.replicate numResults ⊤
    else
      Array.replicate numResults ⊤

/-- How many `upTo` operands `transfer` splits into their exact cases. -/
def maxSplits : Nat := 2

/--
The operand facts `transferExact` runs on: each of the first `budget` `upTo c`
facts is split into `exact c` and `exact poison`, and any later `upTo` fact
becomes `⊤`.
-/
def operandCases : List AbstractConstant → Nat → List (List AbstractConstant)
  | [], _ => [[]]
  | fact :: rest, budget =>
    match fact, budget with
    | .upTo _, budget + 1 =>
      fact.exactCases.flatMap fun fact' => (operandCases rest budget).map (fact' :: ·)
    | .upTo _, 0 => (operandCases rest 0).map (⊤ :: ·)
    | _, budget => (operandCases rest budget).map (fact :: ·)

/-- The join of a list of facts. -/
def joinAll : List AbstractConstant → AbstractConstant
  | [] => ⊥
  | fact :: rest => fact ⊔ joinAll rest

/--
Sparse constant propagation transfer function. An `upTo c` operand is `c` or
poison, so `transferExact` runs once for each case and the results are joined,
result by result.
-/
def transfer
    (op : OperationPtr)
    (operandLatticeElements : Array AbstractConstant)
    (irCtx : WfIRContext OpCode) : Array AbstractConstant :=
  let runs := (operandCases operandLatticeElements.toList maxSplits).map fun facts =>
    transferExact op facts.toArray irCtx
  Array.ofFn (n := op.getNumResults! irCtx.raw) fun i =>
    joinAll (runs.map fun run => run[i.val]?.getD ⊤)

end SparseConstantPropagation

def SparseConstantPropagationAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .sparseConstant
    SparseConstantPropagation.kind
    SparseConstantPropagation.transfer

end Veir
