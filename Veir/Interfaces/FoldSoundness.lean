module

public import Veir.Interfaces.FoldInterfaces
public import Veir.Interpreter.Purity

import all Veir.Interfaces.FoldInterfaces
import all Veir.Interpreter.Evaluate

/-!
# Fold soundness contract

`OpCode.foldsTo` decides that an operation folds. This file relates that
decision to `interpretOp'`, which is the project's only concrete semantics,
states the contract, and discharges it leg by leg.

The contract is stated against an interpreter *outcome* rather than a value.
`foldByEvaluation` converts `Interp.ub` into poison, and `ValuePtr.constantValue`
does the same (`Veir/Interfaces/ConstantLikeInterfaces.lean`). Neither can be
described by an equation between values, because in the UB case the interpreter
produces no value at all.
-/

public section

namespace Veir

/-- The runtime value a fold decision claims for a result. -/
def FoldDecision.valueFor (decision : FoldDecision) (operands : Array RuntimeValue)
    : Option RuntimeValue :=
  match decision with
  | .useOperand j => operands[j]?
  | .useConstant value => some value

/-- Interpret an operation at empty memory, keeping only the result values. -/
def interpretPure (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    : Interp (Array RuntimeValue) :=
  (interpretOp' opType properties resultTypes operands #[] MemoryState.empty).map
    (fun (results, _, _) => results)

/-- `constOperands` agrees with the real operands wherever it claims a value. -/
def ConstOperandsAgree (constOperands : Array (Option RuntimeValue))
    (operands : Array RuntimeValue) : Prop :=
  ∀ (i : Nat) (v : RuntimeValue), constOperands[i]? = some (some v) → operands[i]? = some v

/--
The fold-soundness contract for one result.

A decision must name the value the interpreter actually produces, whenever the
interpreter produces one. `.ub` and `.fail` impose no constraint: the source
program's behaviour is unconstrained there, so replacing it with any value —
poison included — is a refinement rather than a claim about a value.
-/
def FoldDecision.SoundFor (decision : FoldDecision) (operands : Array RuntimeValue)
    (outcome : Interp (Array RuntimeValue)) (i : Nat) : Prop :=
  match outcome with
  | .ok results =>
      match results[i]? with
      | some actual => decision.valueFor operands = some actual
      | none => True
  | .ub => True
  | .fail => True

@[simp]
theorem FoldDecision.soundFor_ub (decision : FoldDecision) (operands : Array RuntimeValue)
    (i : Nat) : decision.SoundFor operands .ub i := by
  simp [FoldDecision.SoundFor]

@[simp]
theorem FoldDecision.soundFor_fail (decision : FoldDecision) (operands : Array RuntimeValue)
    (i : Nat) : decision.SoundFor operands .fail i := by
  simp [FoldDecision.SoundFor]

/-- A successful `mapM` in `Option` computes each entry by `f`. -/
theorem List.getElem?_of_mapM_eq_some {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ∀ (i : Nat), xs[i]?.bind f = ys[i]?
  | [], ys, h, i => by
      simp at h; subst h; simp
  | x :: xs, ys, h, i => by
      cases hx : f x with
      | none => simp [hx] at h
      | some y =>
        cases hRest : xs.mapM f with
        | none => simp [hx, hRest] at h
        | some zs =>
          simp [hx, hRest] at h
          subst h
          cases i with
          | zero => simp [hx]
          | succ i => simpa using List.getElem?_of_mapM_eq_some hRest i

/-- A successful `mapM` in `Option` preserves length. -/
theorem List.length_of_mapM_eq_some {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
  | [], ys, h => by
      simp at h; subst h; rfl
  | x :: xs, ys, h => by
      cases hx : f x with
      | none => simp [hx] at h
      | some y =>
        cases hRest : xs.mapM f with
        | none => simp [hx, hRest] at h
        | some zs =>
          simp [hx, hRest] at h
          subst h
          simp [List.length_of_mapM_eq_some hRest]

/-- A successful `mapM` in `Option` preserves size. -/
theorem Array.size_of_mapM_eq_some {α β : Type} {f : α → Option β}
    {xs : Array α} {ys : Array β} (h : xs.mapM f = some ys) : ys.size = xs.size := by
  have hList := congrArg (·.map Array.toList) h
  simp only [Array.mapM_eq_mapM_toList, Functor.map, Option.map_map] at hList
  simp at hList
  simpa using List.length_of_mapM_eq_some hList

/-- A successful `mapM` in `Option` computes each entry by `f`. -/
theorem Array.getElem?_of_mapM_eq_some {α β : Type} {f : α → Option β}
    {xs : Array α} {ys : Array β} (h : xs.mapM f = some ys) (i : Nat) :
    xs[i]?.bind f = ys[i]? := by
  have hList := congrArg (·.map Array.toList) h
  simp only [Array.mapM_eq_mapM_toList, Functor.map, Option.map_map] at hList
  simp at hList
  simpa using List.getElem?_of_mapM_eq_some hList i

/--
When every entry of `constOperands` is known, and each agrees with `operands`,
the sequenced array is exactly `operands`.
-/
theorem ConstOperandsAgree.mapM_id_eq
    {constOperands : Array (Option RuntimeValue)} {operands values : Array RuntimeValue}
    (hAgree : ConstOperandsAgree constOperands operands)
    (hSize : constOperands.size = operands.size)
    (hValues : constOperands.mapM id = some values) :
    values = operands := by
  apply Array.ext_getElem?
  intro i
  have hEntry := Array.getElem?_of_mapM_eq_some hValues i
  cases hv : values[i]? with
  | none =>
      have hValuesSize := Array.size_of_mapM_eq_some hValues
      have hLt : ¬ i < operands.size := by
        intro hLt
        have : i < values.size := by omega
        simp [this] at hv
      simp [hLt]
  | some v =>
      refine (hAgree i v ?_).symm
      cases hc : constOperands[i]? with
      | none => simp [hc, hv] at hEntry
      | some c => simp_all

/-- A successful `foldEvaluate` agrees with the empty-memory interpretation. -/
theorem interpretPure_of_foldEvaluate_ok {opType : OpCode} {properties : propertiesOf opType}
    {resultTypes : Array TypeAttr} {operands results : Array RuntimeValue}
    (h : foldEvaluate opType properties resultTypes operands = .ok results) :
    interpretPure opType properties resultTypes operands = .ok results := by
  simp only [foldEvaluate] at h
  split at h
  · simp [liftM, monadLift, MonadLift.monadLift] at h
  · simp only [interpretPure]
    cases hInterp : interpretOp' opType properties resultTypes operands #[] MemoryState.empty with
    | fail => simp [hInterp, bind] at h
    | ub => simp [hInterp, bind] at h
    | ok triple =>
      obtain ⟨rs, mem, action⟩ := triple
      cases action <;> simp_all [bind, liftM, monadLift, MonadLift.monadLift]

/-- `foldEvaluate` reports UB only when the empty-memory interpretation does. -/
theorem interpretPure_of_foldEvaluate_ub {opType : OpCode} {properties : propertiesOf opType}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue}
    (h : foldEvaluate opType properties resultTypes operands = .ub) :
    interpretPure opType properties resultTypes operands = .ub := by
  simp only [foldEvaluate] at h
  split at h
  · simp [liftM, monadLift, MonadLift.monadLift] at h
  · simp only [interpretPure]
    cases hInterp : interpretOp' opType properties resultTypes operands #[] MemoryState.empty with
    | fail => simp [hInterp, bind] at h
    | ub => rfl
    | ok triple =>
      obtain ⟨rs, mem, action⟩ := triple
      cases action <;> simp_all [bind, liftM, monadLift, MonadLift.monadLift]

/-- The evaluation leg: decisions produced by interpreting the operation are sound. -/
private theorem foldByEvaluation_sound
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hAgree : ConstOperandsAgree constOperands operands)
    (hSize : constOperands.size = operands.size)
    (hFold : foldByEvaluation opType properties resultTypes constOperands = some decisions)
    (hDecision : decisions[i]? = some decision) :
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i := by
  simp only [foldByEvaluation, bind, Option.bind] at hFold
  cases hValues : constOperands.mapM id with
  | none => simp [hValues] at hFold
  | some values =>
    have hEq := ConstOperandsAgree.mapM_id_eq hAgree hSize hValues
    subst hEq
    simp only [hValues] at hFold
    cases hEval : foldEvaluate opType properties resultTypes values with
    | fail => simp [hEval] at hFold
    | ub => simp [interpretPure_of_foldEvaluate_ub hEval]
    | ok results =>
      simp only [hEval, pure] at hFold
      cases hFold
      have hDecisionEq : decision = .useConstant results[i]! := by
        grind
      rw [interpretPure_of_foldEvaluate_ok hEval]
      simp only [FoldDecision.SoundFor]
      cases hResult : results[i]? with
      | none => trivial
      | some actual =>
        subst hDecisionEq
        simp [FoldDecision.valueFor]
        grind

/--
The `propagatesPoison` flag is honest for `opType`: whenever some operand is
wholly poison, interpretation either fails, is UB, or produces wholly poison
results of the declared types.

This is the semantic content the flag asserts. It is a per-opcode obligation:
nothing in `Veir/IR/OpInfo.lean` enforces it.
-/
def PropagatesPoisonHonestly (opType : OpCode) : Prop :=
  opType.propagatesPoison = true →
  ∀ (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (results : Array RuntimeValue),
    operands.any RuntimeValue.isPoison = true →
    interpretPure opType properties resultTypes operands = .ok results →
    ∀ (i : Nat) (actual : RuntimeValue), results[i]? = some actual →
      resultTypes[i]?.bind RuntimeValue.getPoisonForType = some actual

/-- The poison leg: poison-propagating folds are sound when the flag is honest. -/
private theorem foldPoisonedOperand_sound
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hHonest : PropagatesPoisonHonestly opType)
    (hAgree : ConstOperandsAgree constOperands operands)
    (hFold : foldPoisonedOperand opType resultTypes constOperands = some decisions)
    (hDecision : decisions[i]? = some decision) :
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i := by
  simp only [foldPoisonedOperand] at hFold
  simp [guard, Option.bind_eq_some_iff] at hFold
  obtain ⟨hPropagates, ⟨j, hj, hPoison⟩, hFold⟩ := hFold
  have hOperandPoison : operands.any RuntimeValue.isPoison = true := by
    cases hc : constOperands[j] with
    | none => simp [hc] at hPoison
    | some value =>
      simp only [hc] at hPoison
      have hOp := hAgree j value (by simp [hj, hc])
      obtain ⟨hjOp, hOpEq⟩ := Array.getElem?_eq_some_iff.mp hOp
      exact Array.any_eq_true.mpr ⟨j, hjOp, by simp [hOpEq, hPoison]⟩
  simp only [allResultsPoison, bind, Option.bind, pure] at hFold
  cases hPoisons : resultTypes.mapM RuntimeValue.getPoisonForType with
  | none => simp [hPoisons] at hFold
  | some poisons =>
    simp only [hPoisons, Option.some.injEq] at hFold
    subst hFold
    have hEntry := Array.getElem?_of_mapM_eq_some hPoisons i
    simp only [Array.getElem?_map, Option.map_eq_some_iff] at hDecision
    obtain ⟨poison, hPoisonAt, rfl⟩ := hDecision
    cases hInterp : interpretPure opType properties resultTypes operands with
    | fail => trivial
    | ub => trivial
    | ok results =>
      simp only [FoldDecision.SoundFor]
      cases hResult : results[i]? with
      | none => trivial
      | some actual =>
        have := hHonest hPropagates properties resultTypes operands results hOperandPoison
          hInterp i actual hResult
        simp only [FoldDecision.valueFor]
        rw [← this, hEntry, hPoisonAt]

end Veir
