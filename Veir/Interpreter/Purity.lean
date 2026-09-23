module

public import Veir.Interpreter.Basic

import all Veir.Interpreter.Basic

/-!
# Structural purity of `interpretOp'`

Most dialect arms of `interpretOp'` thread the incoming memory through
untouched: they call a dialect interpreter that takes no memory argument at all
and re-attach the caller's memory to the result. For those opcodes,
memory-independence holds by the shape of the definition and needs no reasoning
about `getEffects`.

This matters because `foldEvaluate` (`Veir/Interpreter/Evaluate.lean`) only ever
interprets at `MemoryState.empty`, so any fold-soundness statement must know that
the choice of memory is irrelevant.

`.llvm`, `.riscv` and `.riscv_stack` genuinely consume and produce memory and are
not covered here.
-/

public section

namespace Veir

/--
Interpreting an `arith` operation does not depend on, or modify, memory.

This is the `OperationPtr.Pure` property of `Veir/Interpreter/EquationLemma.lean`
specialised to `arith` and stated directly on the opcode, so that it applies
without an `OperationPtr` in hand.
-/
theorem interpretOp'_arith_memory_irrelevant
    (op : Veir.Arith) (properties : propertiesOf (OpCode.arith op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (memory₁ memory₂ : MemoryState)
    (layout : DataLayout) :
    interpretOp' (.arith op) properties resultTypes operands blockOperands memory₁ layout =
      (interpretOp' (.arith op) properties resultTypes operands blockOperands memory₂ layout).map
        (fun (results, _, cf) => (results, memory₁, cf)) := by
  simp only [interpretOp']
  cases Arith.interpretOp' op properties resultTypes operands blockOperands <;> rfl

/--
The empty-memory interpretation determines the interpretation at any memory, for
`arith`. This is the form the fold proofs use: `foldEvaluate` runs at
`MemoryState.empty`, and this says nothing was lost by that choice.
-/
theorem interpretOp'_arith_eq_empty
    (op : Veir.Arith) (properties : propertiesOf (OpCode.arith op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) (layout : DataLayout) :
    interpretOp' (.arith op) properties resultTypes operands blockOperands memory layout =
      (interpretOp' (.arith op) properties resultTypes operands blockOperands
        MemoryState.empty layout).map (fun (results, _, cf) => (results, memory, cf)) :=
  interpretOp'_arith_memory_irrelevant op properties resultTypes operands blockOperands
    memory MemoryState.empty layout

end Veir
