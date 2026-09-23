module

public import Veir.Interfaces.FoldSoundness

import all Veir.Dialects.Arith.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Interpreter.Basic
import all Veir.RuntimeValue.Basic
import all Veir.GlobalOpInfo

/-!
# Soundness of the `arith` fold table

`Arith.tryFold` fires for exactly two opcodes, `arith.addi` and
`arith.addui_extended`, both on the rewrite `x + 0 = x`. This file discharges
the fold-soundness contract of `Veir/Interfaces/FoldSoundness.lean` for them.
-/

public section

namespace Veir

/-- Adding zero is the identity, and cannot set either overflow flag. -/
theorem Data.LLVM.Int.add_zero_eq {w : Nat} (x : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.add x (.val 0#w) nsw nuw = x := by
  cases x with
  | poison => rfl
  | val bits =>
    have hSigned : ¬ (2 ^ (w - 1) ≤ bits.toInt ∨ bits.toInt < -2 ^ (w - 1)) := by
      have := BitVec.toInt_lt (x := bits)
      have := BitVec.le_toInt bits
      omega
    have hUnsigned : ¬ 2 ^ w ≤ bits.toNat := by
      have := bits.isLt
      omega
    simp [Data.LLVM.Int.add, BitVec.saddOverflow, BitVec.uaddOverflow, hSigned, hUnsigned]
    rfl

/-- Adding zero never carries, so the overflow flag of a defined sum is `0`. -/
theorem Data.LLVM.Int.uaddOverflowFlag_zero {w : Nat} (bits : BitVec w) :
    Data.LLVM.Int.uaddOverflowFlag (.val bits) (.val 0#w) = .val 0#1 := by
  have hUnsigned : ¬ 2 ^ w ≤ bits.toNat := by
    have := bits.isLt
    omega
  simp [Data.LLVM.Int.uaddOverflowFlag, BitVec.uaddOverflow, hUnsigned]
  rfl

/-- `arith.addi` folds only on a literal zero right operand, to its left operand. -/
theorem Arith.tryFold_addi_eq_some {properties : Arith.propertiesOf .addi}
    {resultTypes : Array TypeAttr} {constOperands : Array (Option RuntimeValue)}
    {decisions : Array FoldDecision}
    (h : Arith.tryFold .addi properties resultTypes constOperands = some decisions) :
    ∃ head bw, constOperands.toList = [head, some (.int bw (.val 0#bw))] ∧
      decisions = #[.useOperand 0] := by
  obtain ⟨l⟩ := constOperands
  rcases l with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;> simp [Arith.tryFold] at h
  rcases c1 with _ | c1
  · simp at h
  cases c1 <;> try simp at h
  rename_i bw v
  cases v <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨c0, bw, rfl, rfl⟩

/--
`arith.addui_extended` folds only on a literal zero right operand, to its left
operand and a clear carry flag.
-/
theorem Arith.tryFold_addui_extended_eq_some {properties : Arith.propertiesOf .addui_extended}
    {resultTypes : Array TypeAttr} {constOperands : Array (Option RuntimeValue)}
    {decisions : Array FoldDecision}
    (h : Arith.tryFold .addui_extended properties resultTypes constOperands = some decisions) :
    ∃ head bw, constOperands.toList = [head, some (.int bw (.val 0#bw))] ∧
      decisions = #[.useOperand 0, .useConstant (.int 1 (.val 0#1))] := by
  obtain ⟨l⟩ := constOperands
  rcases l with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;> simp [Arith.tryFold] at h
  rcases c1 with _ | c1
  · simp at h
  cases c1 <;> try simp at h
  rename_i bw v
  cases v <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨c0, bw, rfl, rfl⟩

/-- The table leg, for `arith`. -/
theorem Arith.tryFold_sound
    (op : Veir.Arith) (properties : Veir.propertiesOf (OpCode.arith op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hAgree : ConstOperandsAgree constOperands operands)
    (hFold : Arith.tryFold op properties resultTypes constOperands = some decisions)
    (hDecision : decisions[i]? = some decision) :
    decision.SoundFor operands (interpretPure (.arith op) properties resultTypes operands) i := by
  cases op
  case addi =>
    obtain ⟨head, bw, hConst, rfl⟩ := Arith.tryFold_addi_eq_some hFold
    have hOperand₁ : operands[1]? = some (.int bw (.val 0#bw)) :=
      hAgree 1 _ (by simp [← Array.getElem?_toList, hConst])
    have hDecisionEq : i = 0 ∧ decision = .useOperand 0 := by
      cases i <;> simp_all
    obtain ⟨rfl, rfl⟩ := hDecisionEq
    obtain ⟨operands⟩ := operands
    rcases operands with _ | ⟨lhs, _ | ⟨rhs, _ | ⟨extra, rest⟩⟩⟩ <;> simp at hOperand₁ <;>
      subst hOperand₁ <;> cases lhs <;>
      simp [interpretPure, Veir.interpretOp', Arith.interpretOp', bind, FoldDecision.SoundFor]
    rename_i w x
    by_cases hbw : bw = w
    · subst hbw
      simp [Data.LLVM.Int.cast, Data.LLVM.Int.add_zero_eq, FoldDecision.valueFor]
    · simp [hbw]
  case addui_extended =>
    obtain ⟨head, bw, hConst, rfl⟩ := Arith.tryFold_addui_extended_eq_some hFold
    have hOperand₁ : operands[1]? = some (.int bw (.val 0#bw)) :=
      hAgree 1 _ (by simp [← Array.getElem?_toList, hConst])
    obtain ⟨operands⟩ := operands
    rcases operands with _ | ⟨lhs, _ | ⟨rhs, _ | ⟨extra, rest⟩⟩⟩ <;> simp at hOperand₁ <;>
      subst hOperand₁ <;> cases lhs <;>
      simp [interpretPure, Veir.interpretOp', Arith.interpretOp', bind, FoldDecision.SoundFor]
    rename_i w x
    by_cases hbw : bw = w
    · subst hbw
      rcases i with _ | _ | i
      · simp at hDecision
        subst hDecision
        simp [Data.LLVM.Int.cast, Data.LLVM.Int.add_zero_eq, FoldDecision.valueFor]
      · simp at hDecision
        subst hDecision
        -- A poison `x` gives a poison flag, which the constant `0` refines.
        cases x with
        | poison =>
          simp [Data.LLVM.Int.cast, Data.LLVM.Int.uaddOverflowFlag]
          exact Or.inl rfl
        | val bits =>
          simp [Data.LLVM.Int.cast, Data.LLVM.Int.uaddOverflowFlag_zero, FoldDecision.valueFor]
      · simp at hDecision
    · simp [hbw]
  all_goals simp [Arith.tryFold] at hFold

/-- The `arith` fold table satisfies the fold-soundness contract. -/
theorem Arith.foldTableSound (op : Veir.Arith) : FoldTableSound (.arith op) := by
  intro properties resultTypes operands constOperands decisions i decision hAgree hFold hDecision
  exact Arith.tryFold_sound op properties resultTypes operands constOperands decisions i decision
    hAgree hFold hDecision

end Veir
