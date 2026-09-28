import Veir.Analysis.DataFlow.Domains.ConstantSoundness
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis
import Veir.Interfaces.FoldSoundness

/-!
# Soundness of sparse constant propagation

Local soundness of `SparseConstantPropagation.transfer`: if every operand lies in
`γ` of its fact, every result lies in `γ` of the fact `transfer` produces
(`transfer_sound`).

The folder is only ever told values that `exact` facts pin down, so its inputs
agree with the real operands and its contract (`foldsTo_sound`,
`Veir/Interfaces/FoldSoundness.lean`) applies to the real run directly
(`fold_sound`). An `upTo` operand is handled by case analysis: the real operand
is one of the cases `transfer` runs (`exists_operandCase`), and the join is
above each case (`le_joinAll`). No monotonicity of the interpreter is needed.
-/

public section

namespace Veir

namespace SparseConstantPropagation

/-- Every value lies in `γ` of the fact at the same position, and there are as many of each. -/
def AllInGamma : List AbstractConstant → List RuntimeValue → Prop
  | [], [] => True
  | fact :: facts, v :: vs => v ∈ AbstractConstant.γ fact ∧ AllInGamma facts vs
  | _, _ => False

/--
Every operand lies in `γ` of its fact, one fact per operand. This is `γ`
pointwise: the relation `transfer_sound` assumes of the operands and establishes
for the results, so it composes along an execution.
-/
def OperandsInGamma (facts : Array AbstractConstant) (vs : Array RuntimeValue) : Prop :=
  AllInGamma facts.toList vs.toList

theorem AllInGamma.length_eq :
    ∀ {facts : List AbstractConstant} {vs : List RuntimeValue},
      AllInGamma facts vs → facts.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [AllInGamma.length_eq h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem AllInGamma.mem :
    ∀ {facts : List AbstractConstant} {vs : List RuntimeValue} {j : Nat}
      {a : AbstractConstant} {v : RuntimeValue},
      AllInGamma facts vs → facts[j]? = some a → vs[j]? = some v → v ∈ AbstractConstant.γ a
  | _ :: _, _ :: _, 0, _, _, h, ha, hv => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hv
    subst ha; subst hv; exact h.1
  | _ :: _, _ :: _, _ + 1, _, _, h, ha, hv => by
    simp only [List.getElem?_cons_succ] at ha hv
    exact AllInGamma.mem h.2 ha hv
  | [], _, _, _, _, _, ha, _ => by simp at ha
  | _ :: _, [], _, _, _, _, _, hv => by simp at hv

theorem OperandsInGamma.size_eq {facts : Array AbstractConstant} {vs : Array RuntimeValue}
    (h : OperandsInGamma facts vs) : facts.size = vs.size := by
  simpa using AllInGamma.length_eq h

theorem OperandsInGamma.mem {facts : Array AbstractConstant} {vs : Array RuntimeValue}
    (h : OperandsInGamma facts vs) {j : Nat} {a : AbstractConstant} {v : RuntimeValue}
    (ha : facts[j]? = some a) (hv : vs[j]? = some v) : v ∈ AbstractConstant.γ a :=
  AllInGamma.mem h (by simpa using ha) (by simpa using hv)

/-- The folder's inputs agree with the real operands: an `exact` fact pins its operand. -/
theorem constOperandsAgree_foldInputs {facts : Array AbstractConstant} {vs : Array RuntimeValue}
    (hOperands : OperandsInGamma facts vs) : ConstOperandsAgree (foldInputs facts) vs := by
  intro j v hConst
  simp only [foldInputs, Array.getElem?_map, Option.map_eq_some_iff] at hConst
  obtain ⟨a, ha, hv⟩ := hConst
  have hj : j < vs.size := by
    have := (Array.getElem?_eq_some_iff.mp ha).1
    have := hOperands.size_eq
    omega
  have hMem := hOperands.mem ha (Array.getElem?_eq_getElem hj)
  cases a with
  | exact c =>
    obtain ⟨bitwidth, value⟩ := c
    simp only [Option.some.injEq] at hv
    rw [Array.getElem?_eq_getElem hj, AbstractConstant.mem_γ_exact.mp hMem, hv]
  | top => simp at hv
  | bottom => simp at hv
  | upTo c => simp at hv

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
      cases decision with
      | useConstant value =>
        simp only [FoldDecision.valueFor, Option.some.injEq] at hValue
        subst hValue
        exact AbstractConstant.mem_γ_weaken_of_isRefinedBy hRefines
          (AbstractConstant.mem_γ_ofRuntimeValue value)
      | useOperand j =>
        simp only [FoldDecision.valueFor] at hValue
        simp only [AbstractConstant.ofFoldDecision]
        apply AbstractConstant.mem_γ_weaken_of_isRefinedBy hRefines
        cases ha : facts[j]? with
        | none => exact AbstractConstant.mem_γ_top claimed
        | some a => exact hOperands.mem ha hValue

/--
Soundness of a fold decision for the real operands. The folder's inputs agree
with the real operands (`constOperandsAgree_foldInputs`), so its contract
(`foldsTo_sound`) is about the real run itself.
-/
theorem fold_sound
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (facts : Array AbstractConstant) (vs : Array RuntimeValue)
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hTable : FoldTableSound opType) (hPoison : PropagatesPoisonSound opType)
    (hOperands : OperandsInGamma facts vs)
    (hFold : OpCode.foldsTo opType properties resultTypes (foldInputs facts) = some decisions)
    (hDecision : decisions[i]? = some decision) :
    (AbstractConstant.ofFoldDecision decision facts).SoundFor
      (interpretPure opType properties resultTypes vs) i :=
  ofFoldDecision_soundFor decision facts vs _ i hOperands
    (foldsTo_sound opType properties resultTypes vs (foldInputs facts) decisions i decision
      hTable hPoison (constOperandsAgree_foldInputs hOperands)
      (by simp [foldInputs, hOperands.size_eq]) hFold hDecision)

/-- Evaluating an operation whose operands are all `exact` gives sound, exact facts. -/
theorem evaluateExact_sound
    (op : OperationPtr) (irCtx : WfIRContext OpCode)
    (facts : Array AbstractConstant) (vs : Array RuntimeValue) (results : Array AbstractConstant)
    (hOperands : OperandsInGamma facts vs)
    (hEval : evaluateExact op facts irCtx = some results) (i : Nat) :
    (results[i]?.getD ⊤).SoundFor
      (interpretPure (op.getOpType! irCtx.raw)
        (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw))
        (op.getResultTypes! irCtx.raw) vs) i := by
  simp only [evaluateExact] at hEval
  cases hValues : (foldInputs facts).mapM id with
  | none => simp [hValues] at hEval
  | some values =>
    have hEq : values = vs :=
      ConstOperandsAgree.mapM_id_eq (constOperandsAgree_foldInputs hOperands)
        (by simp [foldInputs, hOperands.size_eq]) hValues
    subst hEq
    simp only [hValues, Option.bind_eq_bind, Option.bind_some] at hEval
    cases hRun : foldEvaluate (op.getOpType! irCtx.raw)
        (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw)) (op.getResultTypes! irCtx.raw)
        values with
    | fail => simp [hRun] at hEval
    | ub =>
      rw [interpretPure_of_foldEvaluate_ub hRun]
      exact AbstractConstant.soundFor_ub _ i
    | ok rs =>
      simp only [hRun, Option.some.injEq] at hEval
      subst hEval
      rw [interpretPure_of_foldEvaluate_ok hRun]
      simp only [AbstractConstant.SoundFor]
      cases hResult : rs[i]? with
      | none => trivial
      | some actual =>
        simp only [Array.getElem?_map, hResult, Option.map_some, Option.getD_some]
        exact AbstractConstant.mem_γ_ofRuntimeValue actual

/--
Local soundness of `transferExact`, the transfer function for one case of the
operand facts.

Hypotheses:
* `hTable`, `hPoison` — per-opcode obligations of `foldsTo_sound`;
* `hArity` — as many operands as the op has;
* `hConstSuccessors` — a constant-like operation has no successors, so the
  interpretation `ValuePtr.constantValue` runs agrees with `interpretPure`.
-/
theorem transferExact_sound
    (op : OperationPtr) (irCtx : WfIRContext OpCode)
    (abstractOperands : Array AbstractConstant) (concreteOperands : Array RuntimeValue)
    (hTable : FoldTableSound (op.getOpType! irCtx.raw))
    (hPoison : PropagatesPoisonSound (op.getOpType! irCtx.raw))
    (hOperands : OperandsInGamma abstractOperands concreteOperands)
    (hArity : concreteOperands.size = op.getNumOperands! irCtx.raw)
    (hConstSuccessors : (op.getOpType! irCtx.raw).isConstantLike = true →
      op.getSuccessors! irCtx.raw = #[])
    (i : Nat) :
    ((transferExact op abstractOperands irCtx)[i]?.getD ⊤).SoundFor
      (interpretPure (op.getOpType! irCtx.raw)
        (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw))
        (op.getResultTypes! irCtx.raw) concreteOperands) i := by
  have hSize := hOperands.size_eq
  have hTop : ∀ n, ((Array.replicate n (⊤ : AbstractConstant))[i]?.getD ⊤) = ⊤ := by
    intro n
    rw [Array.getElem?_replicate]
    split <;> rfl
  by_cases hRegions : op.getNumRegions! irCtx.raw ≠ 0
  · rw [show transferExact op abstractOperands irCtx =
        Array.replicate (op.getNumResults! irCtx.raw) ⊤ by simp [transferExact, hRegions], hTop]
    exact AbstractConstant.soundFor_top _ i
  have hRegions0 : op.getNumRegions! irCtx.raw = 0 := by simpa using hRegions
  by_cases hBot : abstractOperands.any (· = ⊥)
  · exfalso
    obtain ⟨j, hj, hjBot⟩ := Array.any_eq_true.mp hBot
    have hjConcrete : j < concreteOperands.size := by omega
    have := hOperands.mem (Array.getElem?_eq_getElem hj) (Array.getElem?_eq_getElem hjConcrete)
    simp only [decide_eq_true_eq] at hjBot
    rw [hjBot] at this
    exact AbstractConstant.not_mem_γ_bot _ this
  by_cases hConst : (op.getOpType! irCtx.raw).isConstantLike = true
  · have hSuccessors := hConstSuccessors hConst
    rw [show transferExact op abstractOperands irCtx =
        (op.getResults! irCtx.raw).map (fun result =>
          (result.constantValue irCtx.raw).map AbstractConstant.ofRuntimeValue |>.getD ⊤) by
          simp [transferExact, hRegions0, hBot, hConst]]
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
  cases hEval : evaluateExact op abstractOperands irCtx with
  | some results =>
    rw [show transferExact op abstractOperands irCtx = results by
      simp [transferExact, hRegions0, hBot, hConst, hEval]]
    exact evaluateExact_sound op irCtx abstractOperands concreteOperands results hOperands hEval i
  | none =>
  by_cases hInBounds : op.InBounds irCtx.raw
  · cases hFold : op.foldsTo irCtx hInBounds (foldInputs abstractOperands) with
    | none =>
      rw [show transferExact op abstractOperands irCtx =
          Array.replicate (op.getNumResults! irCtx.raw) ⊤ by
            simp [transferExact, hRegions0, hBot, hConst, hEval, hInBounds, hFold], hTop]
      exact AbstractConstant.soundFor_top _ i
    | some decisions =>
      rw [show transferExact op abstractOperands irCtx =
          decisions.map (fun decision => AbstractConstant.ofFoldDecision decision abstractOperands) by
            simp [transferExact, hRegions0, hBot, hConst, hEval, hInBounds, hFold]]
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
          hTable hPoison hOperands hFold hDecision
  · rw [show transferExact op abstractOperands irCtx =
        Array.replicate (op.getNumResults! irCtx.raw) ⊤ by
          simp [transferExact, hRegions0, hBot, hConst, hEval, hInBounds], hTop]
    exact AbstractConstant.soundFor_top _ i

/-- The real operands lie in `γ` of one of the cases `transfer` runs. -/
theorem exists_operandCase :
    ∀ (facts : List AbstractConstant) (vs : List RuntimeValue) (budget : Nat),
      AllInGamma facts vs → ∃ facts' ∈ operandCases facts budget, AllInGamma facts' vs
  | [], [], _, _ => ⟨[], by simp [operandCases], trivial⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | fact :: facts, v :: vs, budget, ⟨hv, hRest⟩ => by
    cases fact with
    | upTo c =>
      cases budget with
      | zero =>
        obtain ⟨facts', hMem, hAll⟩ := exists_operandCase facts vs 0 hRest
        refine ⟨⊤ :: facts', ?_, ⟨trivial, hAll⟩⟩
        simp only [operandCases, List.mem_map]
        exact ⟨facts', hMem, rfl⟩
      | succ budget =>
        obtain ⟨fact', hCase, hv'⟩ := AbstractConstant.exists_exactCase hv
        obtain ⟨facts', hMem, hAll⟩ := exists_operandCase facts vs budget hRest
        refine ⟨fact' :: facts', ?_, ⟨hv', hAll⟩⟩
        simp only [operandCases, List.mem_flatMap, List.mem_map]
        exact ⟨fact', hCase, facts', hMem, rfl⟩
    | top | bottom | exact =>
      obtain ⟨facts', hMem, hAll⟩ := exists_operandCase facts vs budget hRest
      refine ⟨_ :: facts', ?_, ⟨hv, hAll⟩⟩
      simp only [operandCases, List.mem_map]
      exact ⟨facts', hMem, rfl⟩

theorem le_joinAll : ∀ {facts : List AbstractConstant} {fact : AbstractConstant},
    fact ∈ facts → fact ≤ joinAll facts
  | _ :: _, _, .head _ => AbstractConstant.le_join_left _ _
  | fact' :: _, _, .tail _ h =>
    AbstractConstant.le_trans _ _ _ (le_joinAll h) (AbstractConstant.le_join_right fact' _)

/--
Local soundness of the constant-propagation transfer function.

If every operand lies in `γ` of its fact (`OperandsInGamma`), every result lies
in `γ` of the fact `transfer` produces (`AbstractConstant.SoundFor`), whenever
interpretation succeeds; UB and interpreter failure constrain nothing. Operands
and results use the same relation, `γ`, so the theorem composes along an
execution.

The real operands match one of the cases `transfer` runs (`exists_operandCase`),
`transferExact` is sound for that case (`transferExact_sound`), and the joined
fact is above it (`le_joinAll`).
-/
theorem transfer_sound
    (op : OperationPtr) (irCtx : WfIRContext OpCode)
    (abstractOperands : Array AbstractConstant) (concreteOperands : Array RuntimeValue)
    (hTable : FoldTableSound (op.getOpType! irCtx.raw))
    (hPoison : PropagatesPoisonSound (op.getOpType! irCtx.raw))
    (hOperands : OperandsInGamma abstractOperands concreteOperands)
    (hArity : concreteOperands.size = op.getNumOperands! irCtx.raw)
    (hConstSuccessors : (op.getOpType! irCtx.raw).isConstantLike = true →
      op.getSuccessors! irCtx.raw = #[])
    (i : Nat) :
    ((transfer op abstractOperands irCtx)[i]?.getD ⊤).SoundFor
      (interpretPure (op.getOpType! irCtx.raw)
        (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw))
        (op.getResultTypes! irCtx.raw) concreteOperands) i := by
  obtain ⟨facts, hMem, hAll⟩ :=
    exists_operandCase abstractOperands.toList concreteOperands.toList maxSplits hOperands
  have hCase := transferExact_sound op irCtx facts.toArray concreteOperands hTable hPoison
    (by simpa [OperandsInGamma] using hAll) hArity hConstSuccessors i
  by_cases hi : i < op.getNumResults! irCtx.raw
  · simp only [transfer, Array.getElem?_ofFn, hi, dite_true, Option.getD_some]
    refine AbstractConstant.soundFor_mono _ _ _ _ (le_joinAll ?_) hCase
    simp only [List.map_map, List.mem_map]
    exact ⟨facts, hMem, rfl⟩
  · simp only [transfer, Array.getElem?_ofFn, hi, dite_false, Option.getD_none]
    exact AbstractConstant.soundFor_top _ i

end SparseConstantPropagation

end Veir
