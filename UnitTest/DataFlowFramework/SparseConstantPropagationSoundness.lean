import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.Domains.ConstantDomain
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis

/-!
Regression tests pinning the constant-propagation behaviour that
`SparseConstantPropagation.transfer_sound` describes: well-defined evaluation,
UB folded to poison, the `arith` fold table, and the refinement case that
motivated stating soundness up to refinement.
-/

open Veir

private def constInt (bitwidth : Nat) (value : Int) : AbstractConstant :=
  .constant ⟨bitwidth, Data.LLVM.Int.constant bitwidth value⟩

private def poisonInt (bitwidth : Nat) : AbstractConstant :=
  .constant ⟨bitwidth, .poison⟩

private def run (mlir : String) (expected : Array (String × AbstractConstant)) : String :=
  runWithAnalyses mlir #[Veir.SparseConstantPropagationAnalysis]
    (fun top dfCtx parserState => Id.run do
      match recoverNames top parserState.ctx mlir with
      | .error err => return #[err]
      | .ok recovered => checkNamedConstants dfCtx recovered.values expected)

/-- A well-defined division folds to its interpreted value. -/
private def testWellDefinedDivisionFolds : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = 10 : i32 }> : () -> i32
  %b = "arith.constant"() <{ value = 2 : i32 }> : () -> i32
  %d = "arith.divui"(%a, %b) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("a", constInt 32 10), ("b", constInt 32 2), ("d", constInt 32 5) ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testWellDefinedDivisionFolds

/--
Division by zero is UB in the interpreter, and `foldByEvaluation` turns that into
poison. `AbstractConstant.SoundFor` is what makes this fact statable: the
interpreter produces no value, so no equation between values could describe it.
-/
private def testDivisionByZeroFoldsToPoison : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = 10 : i32 }> : () -> i32
  %z = "arith.constant"() <{ value = 0 : i32 }> : () -> i32
  %d = "arith.divui"(%a, %z) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("a", constInt 32 10), ("z", constInt 32 0), ("d", poisonInt 32) ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testDivisionByZeroFoldsToPoison

/-- The `arith.addi x, 0` table entry. -/
private def testAddZeroUsesOperand : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = 7 : i32 }> : () -> i32
  %z = "arith.constant"() <{ value = 0 : i32 }> : () -> i32
  %s = "arith.addi"(%a, %z) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("a", constInt 32 7), ("z", constInt 32 0), ("s", constInt 32 7) ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testAddZeroUsesOperand

/--
`arith.addui_extended x, 0` folds the carry flag to `0` even when `x` is unknown.
When `x` is poison the interpreted flag is poison, so this fact is sound only as
a refinement — the case that fixed the shape of `FoldDecision.SoundFor`.
-/
private def testAddUIExtendedZeroClearsCarry : String :=
  run
    r#""builtin.module"() ({
^module:
  "func.func"() <{function_type = (i8) -> (), sym_name = "f"}> ({
  ^entry(%x : i8):
    %z = "arith.constant"() <{ value = 0 : i8 }> : () -> i8
    %s, %c = "arith.addui_extended"(%x, %z) : (i8, i8) -> (i8, i1)
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#
    #[ ("x", ⊤), ("z", constInt 8 0), ("s", ⊤), ("c", constInt 1 0) ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testAddUIExtendedZeroClearsCarry

/--
`γ` is the one relation between facts and runtime values. A `.constant c` fact
allows `c`, and also poison of that width, since replacing poison by `c` is a
refinement. It allows nothing else.
-/
private def zero8 : AbstractConstant := .constant ⟨8, .val 0#8⟩

example : RuntimeValue.int 8 (.val 0#8) ∈ AbstractConstant.γ zero8 :=
  AbstractConstant.mem_γ_constant.mpr (RuntimeValue.isRefinedBy_refl _)

example : RuntimeValue.int 8 .poison ∈ AbstractConstant.γ zero8 :=
  AbstractConstant.mem_γ_constant.mpr (RuntimeValue.int_poison_isRefinedBy 8 _)

example : RuntimeValue.int 8 (.val 1#8) ∉ AbstractConstant.γ zero8 := by
  simp [zero8, AbstractConstant.mem_γ_constant, RuntimeValue.isRefinedBy, Data.LLVM.Int.cast,
    _root_.isRefinedBy]
