import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.Domains.ConstantDomain
import Veir.Analysis.DataFlow.SparseConstantPropagationSoundness

/-!
Regression tests pinning the constant-propagation behaviour that
`SparseConstantPropagation.transfer_sound` describes: well-defined evaluation,
UB folded to poison, the `arith` fold table, and the refinement case that
motivated stating soundness up to refinement.
-/

open Veir

private def constInt (bitwidth : Nat) (value : Int) : AbstractConstant :=
  .exact ⟨bitwidth, Data.LLVM.Int.constant bitwidth value⟩

private def poisonInt (bitwidth : Nat) : AbstractConstant :=
  .exact ⟨bitwidth, .poison⟩

private def upToInt (bitwidth : Nat) (value : Int) : AbstractConstant :=
  .upTo ⟨bitwidth, Data.LLVM.Int.constant bitwidth value⟩

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
When `x` is poison the interpreted flag is poison, so the fact is `upTo 0`, not
`exact 0`: the folder's answer only holds up to refinement.
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
    #[ ("x", ⊤), ("z", constInt 8 0), ("s", ⊤), ("c", upToInt 1 0) ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testAddUIExtendedZeroClearsCarry

/--
Joining a constant with poison gives `upTo`, which the old domain could only
express as `⊤`. An `upTo` operand is split into its two cases: `%next` is `6` or
poison, while `freeze` of `5` and of poison differ, so `%frozen` is `⊤`.
-/
private def testUpToFromJoinWithPoison : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %five = "arith.constant"() <{ value = 5 : i32 }> : () -> i32
  "cf.br"(%five) [^bb2] : (i32) -> ()
^bb1:
  %poison = "llvm.mlir.poison"() : () -> i32
  "cf.br"(%poison) [^bb2] : (i32) -> ()
^bb2(%joined : i32):
  %one = "arith.constant"() <{ value = 1 : i32 }> : () -> i32
  %next = "arith.addi"(%joined, %one) : (i32, i32) -> i32
  %frozen = "llvm.freeze"(%joined) : (i32) -> i32
}) : () -> ()"#
    #[ ("joined", upToInt 32 5), ("next", upToInt 32 6), ("frozen", ⊤) ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testUpToFromJoinWithPoison

/--
With every operand `exact`, the operation is evaluated and the result is
`exact`, even for `freeze`, which is not monotone.
-/
private def testFreezeOfExactIsExact : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %five = "arith.constant"() <{ value = 5 : i32 }> : () -> i32
  %frozen = "llvm.freeze"(%five) : (i32) -> i32
  %poison = "llvm.mlir.poison"() : () -> i32
  %frozenPoison = "llvm.freeze"(%poison) : (i32) -> i32
}) : () -> ()"#
    #[ ("frozen", constInt 32 5), ("frozenPoison", constInt 32 0) ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testFreezeOfExactIsExact

/--
`γ` is the one relation between facts and runtime values, and it uses equality
only. An `.exact c` fact allows `c`; an `.upTo c` fact allows `c` and poison of
the same width.
-/
private def zero8 : AbstractConstant := .exact ⟨8, .val 0#8⟩

private def upToZero8 : AbstractConstant := .upTo ⟨8, .val 0#8⟩

example : RuntimeValue.int 8 (.val 0#8) ∈ AbstractConstant.γ zero8 :=
  AbstractConstant.mem_γ_exact.mpr rfl

example : RuntimeValue.int 8 .poison ∉ AbstractConstant.γ zero8 := by
  simp [zero8, AbstractConstant.mem_γ_exact]

example : RuntimeValue.int 8 .poison ∈ AbstractConstant.γ upToZero8 :=
  AbstractConstant.mem_γ_upTo.mpr (Or.inr rfl)

example : RuntimeValue.int 8 (.val 1#8) ∉ AbstractConstant.γ upToZero8 := by
  simp [upToZero8, AbstractConstant.mem_γ_upTo]

/-- The constant domain compares runtime values of every kind. -/
example : (RuntimeValue.reg ⟨5#64⟩ == RuntimeValue.reg ⟨5#64⟩) = true := by decide
