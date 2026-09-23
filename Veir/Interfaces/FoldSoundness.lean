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

/-- Sequencing a list of options succeeds only with the list of their contents. -/
theorem List.getElem?_of_mapM_id_eq_some {α : Type} :
    ∀ {xs : List (Option α)} {ys : List α}, xs.mapM id = some ys →
      ∀ (i : Nat), xs[i]? = ys[i]?.map some
  | [], ys, h, i => by
      simp at h; subst h; simp
  | x :: xs, ys, h, i => by
      cases x with
      | none => simp at h
      | some y =>
        cases hRest : xs.mapM id with
        | none => simp [hRest] at h
        | some zs =>
          simp [hRest] at h
          subst h
          cases i with
          | zero => simp
          | succ i => simpa using List.getElem?_of_mapM_id_eq_some hRest i

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
  have hList := congrArg (·.map Array.toList) hValues
  simp only [Array.mapM_eq_mapM_toList, Functor.map, Option.map_map] at hList
  simp at hList
  apply Array.ext_getElem?
  intro i
  have hEntry := List.getElem?_of_mapM_id_eq_some hList i
  simp only [Array.getElem?_toList] at hEntry
  cases hv : values[i]? with
  | none =>
      have hLt : ¬ i < operands.size := by
        intro hLt
        have : (constOperands[i]?).isSome := by simp; omega
        simp [hEntry, hv] at this
      simp [hLt]
  | some v =>
      exact (hAgree i v (by simp [hEntry, hv])).symm


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

end Veir
