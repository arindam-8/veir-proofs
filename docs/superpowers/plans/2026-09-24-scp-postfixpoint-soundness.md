# Sparse Constant Propagation Post-Fixpoint Soundness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that any fact assignment satisfying the constant-propagation constraints (a post-fixpoint) is sound for every terminating execution of a function body's CFG: every SSA value the execution defines holds a value its fact refines.

**Architecture:** The theorem is stated over an arbitrary fact map `F : ValuePtr → AbstractConstant`, never over the solver's output, so the `partial def` solver (`DataFlowFramework.run`) is not involved. The proof is an induction along the execution carrying the invariant `StateRefines F state`. The per-operation step is `SparseConstantPropagation.transfer_sound`, lifted from `interpretPure` to the real interpreter by a purity obligation. Block arguments are handled by a branch-forwarding obligation per terminator. Executions are described by an explicit inductive relation `CFGExec`, because `interpretBlockCFG` cannot support a partial-correctness argument (see Design note 1).

**Tech Stack:** Lean 4.35 (`lean-toolchain`), `lake build`, `#print axioms` for trust-base checks.

**Spec:** This plan's "Design" section below, and the explanation doc "Soundness of VeIR constant propagation: the proof explained" (https://claude.ai/code/artifact/8c01d9bd-99a3-4e83-81d8-e406026c520a), section "Why there is no whole-analysis proof yet", theorem 1. Builds on `docs/superpowers/plans/2026-09-22-scp-fold-soundness.md` (completed).

## Global Constraints

- `Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean` is **not** a `module` file. Any new file that imports it must also be a non-module file: no `module` line, plain `import` lines, then `public section`, exactly as that file's header does. Files that do not import it (`Veir/Interpreter/CFGExec.lean`) are `module` files, per `CLAUDE.md`.
- Every new `.lean` file must be reachable from a `lakefile.toml` root. Add each to the `-- FIXME: These modules are otherwise orphans` block in `Veir.lean` unless another reachable file imports it.
- No `sorry` survives a task. Each proof task ends with `#print axioms`, which must show only `propext`, `Classical.choice`, `Quot.sound`, the existing `Veir.MemoryState.loadByte64._native.bv_decide.ax_5`, and, where `transfer_sound` is used, `Veir.interpretOp'_monotone`.
- Commits use conventional-commit style with a scope and end with the line `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- Naming: relations between facts and values use `Refines` / `DescribesExactly` (see `ConstantSoundness.lean`); per-opcode obligations are `UpperCamelCase` `Prop`s (`PureResults`, `BranchForwards`); theorems are `snake_case`.
- Build a single module with `lake build <Module.Name>`; full check `lake build && lake test`. A full build takes up to ~10 minutes; run it in the background if a tool timeout applies.

## Design

**Note 1: why `CFGExec` instead of `interpretBlockCFG`.** `interpretBlockCFG` (`Veir/Interpreter/Basic.lean`) is defined with `partial_fixpoint`. `Interp` has no `Lean.Order.CCPO` instance, so Lean used the flat order with bottom `Classical.ofNonempty` (confirmed with `set_option pp.explicit true in #check @interpretBlockCFG.fixpoint_induct`). A diverging run is therefore logically equal to an unknown `Interp` value, which may be `.ok junk`, so "`interpretBlockCFG … = .ok r` implies the invariant" is not provable. `CFGExec` is an inductive relation whose derivations are exactly the terminating runs; `CFGExec.interpretBlockCFG_eq` shows each is a genuine `interpretBlockCFG` result. Giving `Interp` a CCPO instance with bottom `.fail` would allow stating the theorem on `interpretBlockCFG` itself, but that changes shared interpreter code and is out of scope.

**Note 2: the specification.** `F` is a post-fixpoint relative to liveness predicates `BlockLive` and `EdgeLive` (the dead-code analysis's facts, abstracted). The constraints mirror the solver in `Veir/Analysis/DataFlow/SparseForwardDataFlowAnalysis.lean`:
- `visitOperation` joins `transfer`'s output into each result, but only in live blocks → `OpConstraint` for ops whose parent block is live;
- `visitBlock` joins each forwarded successor operand into the matching block argument over live edges, and uses the entry state `⊤` when an operand is missing → `EdgeConstraint`;
- a live edge leads to a live block → `liveTargets`.

**Note 3: the per-opcode and per-analysis obligations** are taken as hypotheses, like `hTable` / `hPoison` before:

| Obligation | Meaning | Discharged in this plan |
|---|---|---|
| `OpSoundAt ctx op` | `transfer_sound` holds against the real interpreter, not only `interpretPure` | from `PureResults` (Task 3) |
| `PureResults opType` | results do not depend on memory or successors | `arith` (Task 7) |
| `BranchForwards ctx op` | a branch passes the forwarded operands' values | `cf.br` (Task 8) |
| `TakenEdgesLive` | every edge the execution takes is live (dead-code analysis soundness) | no, hypothesis |

## Scope

In scope: one CFG (a function body region), terminating executions, invariant over all SSA values the execution defines.

Out of scope, recorded in Task 9: the solver producing a post-fixpoint (`run` is `partial def`); dead-code analysis soundness (`TakenEdgesLive`); `BranchForwards` for `cf.cond_br`, `llvm`, `riscv_cf` terminators; `PureResults` beyond `arith`; facts about returned values; nested regions and calls; statements on `interpretBlockCFG` / `interpretFunction` directly (Design note 1).

## File Structure

| File | Kind | Responsibility |
|---|---|---|
| `Veir/Interpreter/CFGExec.lean` (new) | module | `CFGExec` relation and its agreement with `interpretBlockCFG` |
| `Veir/Interfaces/FoldSoundness.lean` (modify) | module | add `PureResults` next to `interpretPure` |
| `Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean` (new) | non-module | specification (`IsPostFixpoint`), obligations, invariant, step/block/CFG theorems |
| `Veir/Dialects/Arith/FoldProofs.lean` (modify) | module | `Arith.pureResults` |
| `Veir/Dialects/Cf/BranchProofs.lean` (new) | non-module | `Cf.br_branchForwards` |
| `Veir.lean` (modify) | | reachability |

---

### Task 1: Terminating CFG executions (`CFGExec`)

**Files:**
- Create: `Veir/Interpreter/CFGExec.lean`
- Modify: `Veir.lean` (FIXME import block)

**Interfaces:**
- Consumes: `interpretBlock`, `interpretBlockCFG`, `interpretBlockCFG.eq_1` (`Veir/Interpreter/Basic.lean`)
- Produces: `Veir.CFGExec`, `Veir.CFGExec.interpretBlockCFG_eq`

- [ ] **Step 1: Write the file with the statement stubbed**

```lean
module

public import Veir.Interpreter.Basic

import all Veir.Interpreter.Basic

/-!
# Terminating CFG executions

`interpretBlockCFG` is defined with `partial_fixpoint`. `Interp` has no
`Lean.Order.CCPO` instance, so its fixpoint lives in the flat order whose bottom
is `Classical.ofNonempty`: a diverging execution is logically equal to an
unknown `Interp` value, possibly `.ok _`. No partial-correctness statement of the
form "if `interpretBlockCFG` returns `.ok`, then …" is provable from its
induction principle.

`CFGExec` describes the terminating executions directly, as an inductive
relation, so properties of them can be proved by ordinary induction.
`CFGExec.interpretBlockCFG_eq` shows every such execution is a genuine result of
`interpretBlockCFG`.
-/

public section

namespace Veir

/--
`CFGExec block values state state' results`: starting at `block` with argument
values `values` and interpreter state `state`, the CFG terminates by returning
`results` in state `state'`, after finitely many branches.
-/
inductive CFGExec {ctx : WfIRContext OpCode} :
    BlockPtr → Array RuntimeValue → InterpreterState ctx →
    InterpreterState ctx → Array RuntimeValue → Prop where
  | ret {block : BlockPtr} {values : Array RuntimeValue} {state state' : InterpreterState ctx}
      {results : Array RuntimeValue} (hBlock : block.InBounds ctx.raw)
      (hRun : interpretBlock block values state hBlock = .ok (state', .return results)) :
      CFGExec block values state state' results
  | branch {block dest : BlockPtr} {values values' : Array RuntimeValue}
      {state mid state' : InterpreterState ctx} {results : Array RuntimeValue}
      (hBlock : block.InBounds ctx.raw)
      (hRun : interpretBlock block values state hBlock = .ok (mid, .branch values' dest))
      (hDest : dest.InBounds ctx.raw)
      (hRest : CFGExec dest values' mid state' results) :
      CFGExec block values state state' results

/-- Every terminating execution described by `CFGExec` is what `interpretBlockCFG` computes. -/
theorem CFGExec.interpretBlockCFG_eq {ctx : WfIRContext OpCode} {block : BlockPtr}
    {values results : Array RuntimeValue} {state state' : InterpreterState ctx}
    (hExec : CFGExec block values state state' results) (hBlock : block.InBounds ctx.raw) :
    interpretBlockCFG block values state hBlock = .ok (state', results) := by
  sorry

end Veir
```

- [ ] **Step 2: Register the module and confirm the red state**

In `Veir.lean`, add `import Veir.Interpreter.CFGExec` to the FIXME block.

Run: `lake build Veir.Interpreter.CFGExec`
Expected: builds with one `declaration uses 'sorry'` warning.

- [ ] **Step 3: Prove it**

Induct on `hExec`. In each case rewrite with the unfolding equation and the constructor's `hRun`; the `InBounds` proofs agree by proof irrelevance.

```lean
  induction hExec with
  | ret hBlock' hRun =>
    rw [interpretBlockCFG.eq_1]
    rw [hRun]
  | branch hBlock' hRun hDest hRest ih =>
    rw [interpretBlockCFG.eq_1, hRun]
    simp only [hDest, dite_true]
    exact ih hDest
```

If `rw [hRun]` fails because the goal's `interpretBlock` carries the theorem's `hBlock` rather than the constructor's `hBlock'`, first `have : hBlock = hBlock' := rfl` is not available for `Prop`s; use `simp only [hRun]` (simp rewrites up to proof irrelevance) instead of `rw`.

- [ ] **Step 4: Verify**

Run: `lake build Veir.Interpreter.CFGExec`
Expected: `Build completed successfully`, no warnings.

Append `#print axioms Veir.CFGExec.interpretBlockCFG_eq`, run `lake env lean Veir/Interpreter/CFGExec.lean`, check the axiom list (Global Constraints), remove the line.

- [ ] **Step 5: Commit**

```bash
git add Veir/Interpreter/CFGExec.lean Veir.lean
git commit -m "feat(interpreter): add CFGExec, a relation for terminating CFG executions

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 2: Specification and obligations

**Files:**
- Create: `Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean`
- Modify: `Veir/Interfaces/FoldSoundness.lean` (add `PureResults` after `interpretPure`)
- Modify: `Veir.lean` (FIXME import block)

**Interfaces:**
- Consumes: `transfer`, `OperandsRefine`, `AbstractConstant.Refines` (`SparseConstantPropagationAnalysis.lean`, `ConstantSoundness.lean`); `BranchOpInterface.getSuccessorOperands?` (`Veir/Interfaces/ControlFlowInterfaces.lean`); `interpretOp`, `OperationPtr.interpret` (`Veir/Interpreter/Basic.lean`)
- Produces: `Veir.PureResults`; in namespace `Veir.SparseConstantPropagation`: `StateRefines`, `ArgsRefine`, `OpConstraint`, `EdgeConstraint`, `IsPostFixpoint`, `OpSoundAt`, `BranchForwards`, `TakenEdgesLive`, and the lemma `argsRefine_of_top`

- [ ] **Step 1: Add `PureResults` to `FoldSoundness.lean`**

Insert directly after the definition of `interpretPure`:

```lean
/--
The results of `opType` do not depend on memory or on successor blocks: whenever
the real interpretation succeeds, `interpretPure` succeeds with the same results.

This is what lets `transfer_sound`, which is stated against `interpretPure`,
speak about real executions. It is a per-opcode obligation; it fails for
operations that read memory.
-/
@[expose]
def PureResults (opType : OpCode) : Prop :=
  ∀ (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState)
    (results : Array RuntimeValue) (mem' : MemoryState) (cf : Option ControlFlowAction),
    interpretOp' opType properties resultTypes operands blockOperands mem = .ok (results, mem', cf) →
    interpretPure opType properties resultTypes operands = .ok results
```

- [ ] **Step 2: Write the specification file**

Header copied from `SparseConstantPropagationAnalysis.lean` (non-module):

```lean
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis
import Veir.Interfaces.ControlFlowInterfaces
import Veir.Interpreter.CFGExec
import Veir.Interpreter.Lemmas

/-!
# Post-fixpoint soundness of sparse constant propagation

A fact map `F` that satisfies the analysis's local constraints (a post-fixpoint)
is sound for every terminating execution of a CFG: every SSA value the execution
defines holds a value its fact refines.

The statement is over an arbitrary `F`, not over the solver's output, so it does
not depend on the `partial def` solver. Executions are `CFGExec` derivations;
see `Veir/Interpreter/CFGExec.lean` for why `interpretBlockCFG` itself is not
used.
-/

public section

namespace Veir

namespace SparseConstantPropagation

variable {ctx : WfIRContext OpCode}

/-- Every SSA value defined in `state` holds a value its fact refines. -/
def StateRefines (F : ValuePtr → AbstractConstant) (state : InterpreterState ctx) : Prop :=
  ∀ (v : ValuePtr) (r : RuntimeValue),
    state.variables.getVar? v = some r → (F v).Refines r

/-- The values passed to `block`'s arguments are refined by the arguments' facts. -/
def ArgsRefine (F : ValuePtr → AbstractConstant) (ctx : WfIRContext OpCode)
    (block : BlockPtr) (values : Array RuntimeValue) : Prop :=
  ∀ i, i < block.getNumArguments! ctx.raw →
    (F (block.getArgument i)).Refines values[i]!

/-- The solver's operation rule: `transfer`'s output is below each result's fact. -/
def OpConstraint (F : ValuePtr → AbstractConstant) (ctx : WfIRContext OpCode)
    (op : OperationPtr) : Prop :=
  ∀ i, i < op.getNumResults! ctx.raw →
    (transfer op ((op.getOperands! ctx.raw).map F) ctx)[i]?.getD ⊤ ≤ F (op.getResult i)

/--
The solver's edge rule for successor `k` of `op`, leading to `dest`: each
forwarded operand's fact is below the matching block argument's fact, and an
argument with no forwarded operand has fact `⊤` (the entry state).
-/
def EdgeConstraint (F : ValuePtr → AbstractConstant) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (k : Nat) (dest : BlockPtr) : Prop :=
  ∀ so, BranchOpInterface.getSuccessorOperands? op k ctx.raw = some so →
    ∀ i, i < dest.getNumArguments! ctx.raw →
      match so[i]? with
      | some v => F v ≤ F (dest.getArgument i)
      | none => F (dest.getArgument i) = ⊤

/--
`F` satisfies the analysis's constraints on live code. `BlockLive` and `EdgeLive`
abstract the dead-code analysis's facts.
-/
structure IsPostFixpoint (F : ValuePtr → AbstractConstant) (ctx : WfIRContext OpCode)
    (BlockLive : BlockPtr → Prop) (EdgeLive : BlockPtr → BlockPtr → Prop) : Prop where
  ops : ∀ block op, BlockLive block → (op.get! ctx.raw).parent = some block →
    OpConstraint F ctx op
  edges : ∀ block op k dest, BlockLive block → EdgeLive block dest →
    (op.get! ctx.raw).parent = some block →
    (op.getSuccessors! ctx.raw)[k]? = some dest → EdgeConstraint F ctx op k dest
  liveTargets : ∀ block dest, EdgeLive block dest → BlockLive dest

/--
`transfer` is sound for `op` against the real interpreter: with refinement-sound
operand facts, every result fact refines the result the interpreter produces,
at any memory and with `op`'s real successors.
-/
def OpSoundAt (ctx : WfIRContext OpCode) (op : OperationPtr) : Prop :=
  ∀ (abstractOperands : Array AbstractConstant) (operands : Array RuntimeValue)
    (mem : MemoryState) (results : Array RuntimeValue) (mem' : MemoryState)
    (cf : Option ControlFlowAction),
    OperandsRefine abstractOperands operands →
    abstractOperands.size = operands.size →
    operands.size = op.getNumOperands! ctx.raw →
    op.interpret ctx.raw operands mem = .ok (results, mem', cf) →
    ∀ i v, results[i]? = some v → ((transfer op abstractOperands ctx)[i]?.getD ⊤).Refines v

/--
When `op` branches to `dest`, it does so through some successor index `k` whose
forwarded operands (`getSuccessorOperands?`) hold exactly the passed values.
-/
def BranchForwards (ctx : WfIRContext OpCode) (op : OperationPtr) : Prop :=
  ∀ (state state' : InterpreterState ctx) (h : op.InBounds ctx.raw)
    (values : Array RuntimeValue) (dest : BlockPtr),
    interpretOp op state h = .ok (state', some (.branch values dest)) →
    ∃ k so, (op.getSuccessors! ctx.raw)[k]? = some dest ∧
      BranchOpInterface.getSuccessorOperands? op k ctx.raw = some so ∧
      ∀ i v, so[i]? = some v → state.variables.getVar? v = some values[i]!

/-- Every edge an execution takes out of a live block is live (dead-code analysis soundness). -/
def TakenEdgesLive (ctx : WfIRContext OpCode) (BlockLive : BlockPtr → Prop)
    (EdgeLive : BlockPtr → BlockPtr → Prop) : Prop :=
  ∀ block op (state state' : InterpreterState ctx) (h : op.InBounds ctx.raw)
    (values : Array RuntimeValue) (dest : BlockPtr),
    BlockLive block → (op.get! ctx.raw).parent = some block →
    interpretOp op state h = .ok (state', some (.branch values dest)) →
    EdgeLive block dest

/-- Entry arguments with fact `⊤`, as the solver assigns them, accept any values. -/
theorem argsRefine_of_top (F : ValuePtr → AbstractConstant) (block : BlockPtr)
    (values : Array RuntimeValue)
    (hTop : ∀ i, i < block.getNumArguments! ctx.raw → F (block.getArgument i) = ⊤) :
    ArgsRefine F ctx block values := by
  sorry

end SparseConstantPropagation

end Veir
```

- [ ] **Step 3: Register and confirm the red state**

Add `import Veir.Analysis.DataFlow.SparseConstantPropagationFixpoint` to the FIXME block in `Veir.lean`.

Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationFixpoint`
Expected: builds with one `sorry` warning (`argsRefine_of_top`). If `(op.getResult i)` or `(block.getArgument i)` does not coerce to `ValuePtr`, write `(.opResult (op.getResult i))` / `(.blockArgument (block.getArgument i))`; `Veir/Interpreter/Lemmas.lean` uses the coercion (`varState'.getVar? (op.getResult i)`), so it should exist.

- [ ] **Step 4: Prove `argsRefine_of_top`**

```lean
  intro i hi
  rw [hTop i hi]
  exact AbstractConstant.refines_top _
```

- [ ] **Step 5: Verify and commit**

Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationFixpoint Veir.Interfaces.FoldSoundness`
Expected: `Build completed successfully`, no warnings.

```bash
git add Veir/Interfaces/FoldSoundness.lean Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean Veir.lean
git commit -m "feat(dataflow): specify post-fixpoints of constant propagation and their obligations

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 3: `OpSoundAt` from purity

**Files:**
- Modify: `Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean`

**Interfaces:**
- Consumes: `transfer_sound`, `FoldTableSound`, `PropagatesPoisonSound`, `PureResults`, `OpSoundAt`
- Produces: `opSoundAt_of_pureResults`, `opSoundAt_of_transfer_top`

- [ ] **Step 1: State both lemmas with `sorry`**

Add before `end SparseConstantPropagation`:

```lean
/-- A pure operation is sound against the real interpreter, by `transfer_sound`. -/
theorem opSoundAt_of_pureResults (op : OperationPtr)
    (hTable : FoldTableSound (op.getOpType! ctx.raw))
    (hPoison : PropagatesPoisonSound (op.getOpType! ctx.raw))
    (hConstSuccessors : (op.getOpType! ctx.raw).isConstantLike = true →
      op.getSuccessors! ctx.raw = #[])
    (hPure : PureResults (op.getOpType! ctx.raw)) :
    OpSoundAt ctx op := by
  sorry

/-- An operation whose facts are always `⊤` is trivially sound (e.g. memory reads). -/
theorem opSoundAt_of_transfer_top (op : OperationPtr)
    (hTop : ∀ (abstractOperands : Array AbstractConstant) i,
      (transfer op abstractOperands ctx)[i]?.getD ⊤ = ⊤) :
    OpSoundAt ctx op := by
  sorry
```

- [ ] **Step 2: Confirm the red state**

Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationFixpoint`
Expected: two `sorry` warnings.

- [ ] **Step 3: Prove them**

`op.interpret` is an `abbrev` for `interpretOp'` with `op`'s successors, so `hPure` applies to it directly.

```lean
-- opSoundAt_of_pureResults
  intro abstractOperands operands mem results mem' cf hRef hSize hArity hRun i v hv
  have hPureRun := hPure _ _ operands _ mem results mem' cf hRun
  have hSound := transfer_sound op ctx abstractOperands operands hTable hPoison hRef hSize
    hArity hConstSuccessors i
  rw [hPureRun] at hSound
  simpa [AbstractConstant.SoundFor, hv] using hSound

-- opSoundAt_of_transfer_top
  intro abstractOperands _ _ _ _ _ _ _ _ _ i v _
  rw [hTop abstractOperands i]
  exact AbstractConstant.refines_top v
```

If `hPure _ _ operands _ mem …` does not unify with `hRun` because `OperationPtr.interpret` is not unfolded, add `simp only [OperationPtr.interpret] at hRun` first.

- [ ] **Step 4: Verify and commit**

Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationFixpoint`
Expected: no warnings. Check `#print axioms …opSoundAt_of_pureResults` (expect `interpretOp'_monotone`).

```bash
git add Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean
git commit -m "feat(dataflow): lift transfer soundness to the real interpreter for pure operations

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 4: One operation preserves the invariant

**Files:**
- Modify: `Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean`

**Interfaces:**
- Consumes: `interpretOp_some_iff`, `VariableState.getOperandValues_eq_some_iff`, `VariableState.getVar?_setResultValues?`, `VariableState.setResultValues?.getNumRseults!_eq_size` (`Veir/Interpreter/Lemmas.lean`); `AbstractConstant.refines_mono`
- Produces: `interpretOp_stateRefines`

- [ ] **Step 1: State it with `sorry`**

```lean
/--
Interpreting one operation preserves `StateRefines`, given that the solver's
constraint holds at the operation and `transfer` is sound for it.
-/
theorem interpretOp_stateRefines {F : ValuePtr → AbstractConstant} {op : OperationPtr}
    {state state' : InterpreterState ctx} {h : op.InBounds ctx.raw}
    {cf : Option ControlFlowAction}
    (hConstraint : OpConstraint F ctx op) (hSound : OpSoundAt ctx op)
    (hRun : interpretOp op state h = .ok (state', cf)) (hState : StateRefines F state) :
    StateRefines F state' := by
  sorry
```

- [ ] **Step 2: Confirm the red state**

Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationFixpoint`
Expected: one `sorry` warning.

- [ ] **Step 3: Prove it**

Proof outline, in order:
1. `obtain ⟨operands, results, mem', vars', hOps, hInterp, hSet, rfl⟩ := interpretOp_some_iff.mp hRun`.
2. From `VariableState.getOperandValues_eq_some_iff.mp hOps`, get `hNum : op.getNumOperands! ctx.raw = operands.size` and `hVals : ∀ i < …, state.variables.getVar? (op.getOperand! ctx.raw i) = some operands[i]!`.
3. Operand facts `(op.getOperands! ctx.raw).map F` refine `operands`: for index `j`, the fact is `F (op.getOperand! ctx.raw j)` (relate `getOperands!` and `getOperand!` with `simp [OperationPtr.getOperands!, OperationPtr.getOperand!]` or the existing `getOperands!` lemmas in `Veir/IR/Basic.lean`); apply `hState` to `hVals j`.
4. Apply `hSound` with `mem := state.memory` and `hInterp` to get, for each result `i`, `((transfer …)[i]?.getD ⊤).Refines results[i]`.
5. For the goal `StateRefines F ⟨vars', mem'⟩`, take `v r hv`. Rewrite `hv` with `VariableState.getVar?_setResultValues? hSet`. If `v = .opResult {op, index}` with `index < numResults`, then `r = results[index]!`; combine step 4 with `hConstraint index` via `AbstractConstant.refines_mono`. Otherwise `hv` is a lookup in the old state; use `hState`.

```lean
  intro v r hv
  obtain ⟨operands, results, mem', vars', hOps, hInterp, hSet, rfl⟩ := interpretOp_some_iff.mp hRun
  have hOpsSpec := VariableState.getOperandValues_eq_some_iff.mp hOps
  have hRefOperands : OperandsRefine ((op.getOperands! ctx.raw).map F) operands := by
    intro j a w ha hw
    -- a = F (op.getOperand! ctx.raw j), w = operands[j]
    sorry -- replaced in this step: see outline point 3
  have hResultsSize := VariableState.setResultValues?.getNumRseults!_eq_size hSet
  simp only [VariableState.getVar?_setResultValues? hSet] at hv
  split at hv
  · -- v is a result of op
    rename_i index hIdx
    sorry -- outline point 5, first case
  · exact hState v r hv
```

Replace each inner `sorry` following the outline; the final file must contain none. Look up the exact statement of `setResultValues?.getNumRseults!_eq_size` (note the misspelling in its name) at `Veir/Interpreter/Lemmas.lean:353` before using it.

- [ ] **Step 4: Verify and commit**

Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationFixpoint`
Expected: no warnings.

```bash
git add Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean
git commit -m "feat(dataflow): prove one operation preserves constant-fact refinement

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 5: One block preserves the invariant and passes sound arguments

**Files:**
- Modify: `Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean`

**Interfaces:**
- Consumes: `interpretOp_stateRefines` (Task 4); `interpretOpList_cons`, `interpretOpChain_eq_interpretTerminatedOpList_of_firstOp`, `VariableState.getVar?_setArgumentValues?` (`Veir/Interpreter/Lemmas.lean`); `BlockPtr.operationListWF`, `BlockPtr.OpChain.opParent` (`Veir/IR/WellFormed.lean`)
- Produces: `interpretOpList_stateRefines`, `interpretBlock_stateRefines`

- [ ] **Step 1: State both with `sorry`**

```lean
/--
Interpreting a list of operations of a live block preserves `StateRefines`. If
it stops at a branch, the branching operation, its pre-state (still satisfying
the invariant), and the run are returned, for use by the edge rule.
-/
theorem interpretOpList_stateRefines {F : ValuePtr → AbstractConstant}
    {BlockLive : BlockPtr → Prop} {EdgeLive : BlockPtr → BlockPtr → Prop}
    (hFix : IsPostFixpoint F ctx BlockLive EdgeLive)
    (hOps : ∀ block op, BlockLive block → (op.get! ctx.raw).parent = some block →
      OpSoundAt ctx op)
    {block : BlockPtr} (hLive : BlockLive block) :
    ∀ (ops : List OperationPtr) (inBounds : ∀ op ∈ ops, op.InBounds ctx.raw)
      (state state' : InterpreterState ctx) (cf : Option ControlFlowAction),
      (∀ op ∈ ops, (op.get! ctx.raw).parent = some block) →
      interpretOpList ops state inBounds = .ok (state', cf) →
      StateRefines F state →
      StateRefines F state' ∧
      ∀ values dest, cf = some (.branch values dest) →
        ∃ op ∈ ops, ∃ (pre : InterpreterState ctx) (h : op.InBounds ctx.raw),
          StateRefines F pre ∧
          interpretOp op pre h = .ok (state', some (.branch values dest)) := by
  sorry

/--
Interpreting a live block, entered with sound arguments, preserves
`StateRefines`; if it branches, the target is live and receives sound arguments.
-/
theorem interpretBlock_stateRefines {F : ValuePtr → AbstractConstant}
    {BlockLive : BlockPtr → Prop} {EdgeLive : BlockPtr → BlockPtr → Prop}
    (hFix : IsPostFixpoint F ctx BlockLive EdgeLive)
    (hOps : ∀ block op, BlockLive block → (op.get! ctx.raw).parent = some block →
      OpSoundAt ctx op)
    (hBranches : ∀ block op, BlockLive block → (op.get! ctx.raw).parent = some block →
      BranchForwards ctx op)
    (hTaken : TakenEdgesLive ctx BlockLive EdgeLive)
    {block : BlockPtr} {values : Array RuntimeValue} {state state' : InterpreterState ctx}
    {action : ControlFlowAction} (hBlock : block.InBounds ctx.raw)
    (hRun : interpretBlock block values state hBlock = .ok (state', action))
    (hLive : BlockLive block) (hState : StateRefines F state)
    (hArgs : ArgsRefine F ctx block values) :
    StateRefines F state' ∧
    ∀ values' dest, action = .branch values' dest →
      BlockLive dest ∧ ArgsRefine F ctx dest values' := by
  sorry
```

- [ ] **Step 2: Confirm the red state**

Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationFixpoint`
Expected: two `sorry` warnings.

- [ ] **Step 3: Prove `interpretOpList_stateRefines`**

Induction on `ops`, generalizing `state`:
- `[]`: `interpretOpList_nil` gives `state' = state`, `cf = none`; the branch clause is vacuous.
- `op :: rest`: rewrite with `interpretOpList_cons`, case on `hFirst : interpretOp op state _`.
  - `.ok (s₁, none)`: `interpretOp_stateRefines (hFix.ops block op hLive hParent) (hOps block op hLive hParent) hFirst hState` gives `StateRefines F s₁`; apply the induction hypothesis to `rest`, and lift its witness `op' ∈ rest` to `op' ∈ op :: rest`.
  - `.ok (s₁, some cf')`: then `state' = s₁`, `cf = some cf'`. The invariant is as above; for the branch clause the witness is `op` itself with `pre := state`.
  - `.ub`, `.fail`: contradict `.ok`.

```lean
  intro ops
  induction ops with
  | nil =>
    intro inBounds state state' cf _ hRun hState
    simp only [interpretOpList_nil, Interp.ok.injEq, Prod.mk.injEq] at hRun
    obtain ⟨rfl, rfl⟩ := hRun
    exact ⟨hState, by simp⟩
  | cons op rest ih =>
    intro inBounds state state' cf hParents hRun hState
    rw [interpretOpList_cons] at hRun
    have hParent := hParents op (by simp)
    have hStep := fun s cf' (h : interpretOp op state _ = .ok (s, cf')) =>
      interpretOp_stateRefines (hFix.ops block op hLive hParent) (hOps block op hLive hParent) h hState
    split at hRun
    all_goals sorry -- one goal per `interpretOp` outcome, as described above
```

Replace the final `sorry` with the four cases; if `split` names the equations differently, use `rename_i` after inspecting the goal.

- [ ] **Step 4: Prove `interpretBlock_stateRefines`**

1. Unfold `interpretBlock` in `hRun`: it sets arguments with `setArgumentValues?`, reads `firstOp`, and runs `interpretOpChain`. Destructure the `Option`/`Interp` binds with `simp only [interpretBlock, bind, …] at hRun` and `split at hRun`.
2. The state after `setArgumentValues?` satisfies `StateRefines F`: for `v r hv`, rewrite with `VariableState.getVar?_setArgumentValues?`; a block argument `index` gets `values[index]!`, sound by `hArgs`; other values come from `hState`.
3. Rewrite `interpretOpChain` with `interpretOpChain_eq_interpretTerminatedOpList_of_firstOp` (it needs `(block.get! ctx.raw).firstOp = some op`; convert from the non-bang `get` with `BlockPtr.get!_eq_get` or `grind`). Unfold `interpretTerminatedOpList` into `interpretOpList` plus a match.
4. Every op of `(block.operationList ctx.raw).toList` has parent `block`: `(BlockPtr.operationListWF ctx.raw block hBlock ctx.wellFormed).opParent`.
5. Apply `interpretOpList_stateRefines` for the invariant.
6. For `action = .branch values' dest`: take the witness `op`, `pre`, `hPreRun`. Then:
   - `hTaken block op pre state' h values' dest hLive hParent hPreRun : EdgeLive block dest`;
   - `hFix.liveTargets` gives `BlockLive dest`;
   - `hBranches … hPreRun` gives `k`, `so`, `hSucc`, `hSo`, `hForward`;
   - `hFix.edges block op k dest hLive hEdge hParent hSucc so hSo i hi` gives the edge rule for argument `i`. In the `some v` case, `hForward i v` gives `pre.variables.getVar? v = some values'[i]!`, the invariant for `pre` gives `(F v).Refines values'[i]!`, and `AbstractConstant.refines_mono` lifts it to `F (dest.getArgument i)`. In the `none` case the fact is `⊤`; use `AbstractConstant.refines_top`.

- [ ] **Step 5: Verify and commit**

Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationFixpoint`
Expected: no warnings.

```bash
git add Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean
git commit -m "feat(dataflow): prove blocks preserve constant-fact refinement across branches

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 6: The CFG theorem

**Files:**
- Modify: `Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean`

**Interfaces:**
- Consumes: `interpretBlock_stateRefines` (Task 5), `CFGExec`, `CFGExec.interpretBlockCFG_eq` (Task 1)
- Produces: `postFixpoint_sound`

- [ ] **Step 1: State it with `sorry`**

```lean
/--
**Post-fixpoint soundness.** Let `F` satisfy the constant-propagation constraints
on live code (`IsPostFixpoint`). Every terminating execution of the CFG that
starts in a live block, from a state and with arguments whose facts refine their
values, ends in a state where every defined SSA value holds a value its fact
refines.

The execution is a genuine interpreter run: `CFGExec.interpretBlockCFG_eq`.

Assumptions beyond `IsPostFixpoint`:
* `hOps` — `transfer` is sound against the real interpreter for every live
  operation (`opSoundAt_of_pureResults`, `opSoundAt_of_transfer_top`);
* `hBranches` — every live terminator forwards its successor operands
  (`BranchForwards`; proved for `cf.br`);
* `hTaken` — the liveness facts cover every edge the execution takes
  (dead-code analysis soundness).
-/
theorem postFixpoint_sound {F : ValuePtr → AbstractConstant}
    {BlockLive : BlockPtr → Prop} {EdgeLive : BlockPtr → BlockPtr → Prop}
    (hFix : IsPostFixpoint F ctx BlockLive EdgeLive)
    (hOps : ∀ block op, BlockLive block → (op.get! ctx.raw).parent = some block →
      OpSoundAt ctx op)
    (hBranches : ∀ block op, BlockLive block → (op.get! ctx.raw).parent = some block →
      BranchForwards ctx op)
    (hTaken : TakenEdgesLive ctx BlockLive EdgeLive)
    {block : BlockPtr} {values results : Array RuntimeValue}
    {state state' : InterpreterState ctx}
    (hExec : CFGExec block values state state' results)
    (hLive : BlockLive block) (hState : StateRefines F state)
    (hArgs : ArgsRefine F ctx block values) :
    StateRefines F state' := by
  sorry
```

- [ ] **Step 2: Confirm the red state**

Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationFixpoint`
Expected: one `sorry` warning.

- [ ] **Step 3: Prove it**

Induction on `hExec`, generalizing nothing else (the invariant hypotheses become induction arguments).

```lean
  induction hExec with
  | ret hBlock hRun =>
    exact (interpretBlock_stateRefines hFix hOps hBranches hTaken hBlock hRun hLive hState hArgs).1
  | branch hBlock hRun hDest hRest ih =>
    obtain ⟨hMid, hNext⟩ :=
      interpretBlock_stateRefines hFix hOps hBranches hTaken hBlock hRun hLive hState hArgs
    obtain ⟨hDestLive, hDestArgs⟩ := hNext _ _ rfl
    exact ih hDestLive hMid hDestArgs
```

If `induction` complains that `hLive`, `hState`, `hArgs` depend on the indices, move them after the colon (`… : BlockLive block → StateRefines F state → ArgsRefine F ctx block values → StateRefines F state'`) and `intro` them in each case.

- [ ] **Step 4: Verify**

Run: `lake build && lake test`
Expected: both succeed.

Append `#print axioms Veir.SparseConstantPropagation.postFixpoint_sound` to the file, run `lake env lean Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean`, expect the Global Constraints list including `Veir.interpretOp'_monotone` and no `sorryAx`, then remove the line.

- [ ] **Step 5: Commit**

```bash
git add Veir/Analysis/DataFlow/SparseConstantPropagationFixpoint.lean
git commit -m "feat(dataflow): prove every post-fixpoint of constant propagation is sound

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 7: `arith` operations are pure

**Files:**
- Modify: `Veir/Dialects/Arith/FoldProofs.lean`

**Interfaces:**
- Consumes: `PureResults`, `interpretPure` (`FoldSoundness.lean`); `interpretOp'_arith_eq_empty` (`Veir/Interpreter/Purity.lean`)
- Produces: `Veir.Arith.pureResults`

- [ ] **Step 1: State it with `sorry`**

Add before `end Veir`:

```lean
/-- `arith` results depend neither on memory nor on successor blocks. -/
theorem Arith.pureResults (op : Veir.Arith) : PureResults (.arith op) := by
  sorry
```

- [ ] **Step 2: Confirm the red state**

Run: `lake build Veir.Dialects.Arith.FoldProofs`
Expected: one `sorry` warning.

- [ ] **Step 3: Prove it**

`Arith.interpretOp'` ignores its block-operand argument (its parameter is `_blockOperands`), and `interpretOp'_arith_eq_empty` removes the memory.

```lean
  intro properties resultTypes operands blockOperands mem results mem' cf hRun
  have hBlocks : ∀ (b : Array BlockPtr),
      Arith.interpretOp' op properties resultTypes operands b =
        Arith.interpretOp' op properties resultTypes operands #[] := by
    intro b; cases op <;> rfl
  simp only [interpretPure, Veir.interpretOp', bind] at hRun ⊢
  rw [hBlocks blockOperands] at hRun
  cases hA : Arith.interpretOp' op properties resultTypes operands #[] with
  | fail => simp [hA] at hRun
  | ub => simp [hA] at hRun
  | ok pair => obtain ⟨vals, act⟩ := pair; simp_all
```

If `cases op <;> rfl` is slow or fails for some constructor, use `cases op <;> simp [Arith.interpretOp']`.

- [ ] **Step 4: Verify and commit**

Run: `lake build Veir.Dialects.Arith.FoldProofs`
Expected: no warnings.

```bash
git add Veir/Dialects/Arith/FoldProofs.lean
git commit -m "feat(arith): prove arith results are independent of memory and successors

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 8: `cf.br` forwards its operands

**Files:**
- Create: `Veir/Dialects/Cf/BranchProofs.lean` (non-module, imports the Task 2 file)
- Modify: `Veir.lean` (FIXME import block)

**Interfaces:**
- Consumes: `BranchForwards` (Task 2); `interpretOp_some_iff`, `VariableState.getOperandValues_eq_some_iff`; `Cf.interpretOp'` (`Veir/Interpreter/Basic.lean`: `.br` returns `.branch operands dest` with `[dest] := blockOperands`); `BranchOpInterface.getSuccessorOperands?` (`.cf .br` forwards `getOperands!`)
- Produces: `Veir.Cf.br_branchForwards`

- [ ] **Step 1: Write the file with the statement stubbed**

```lean
import Veir.Analysis.DataFlow.SparseConstantPropagationFixpoint

/-!
# `cf.br` forwards its operands

`cf.br` passes all its operands to its single successor, which is what
`BranchOpInterface.getSuccessorOperands?` reports for it.
-/

public section

namespace Veir

open SparseConstantPropagation

theorem Cf.br_branchForwards {ctx : WfIRContext OpCode} (op : OperationPtr)
    (hType : op.getOpType! ctx.raw = .cf .br) :
    BranchForwards ctx op := by
  sorry

end Veir
```

Add `import Veir.Dialects.Cf.BranchProofs` to the FIXME block in `Veir.lean`.

- [ ] **Step 2: Confirm the red state**

Run: `lake build Veir.Dialects.Cf.BranchProofs`
Expected: one `sorry` warning.

- [ ] **Step 3: Prove it**

1. `intro state state' h values dest hRun`, then `obtain ⟨operands, results, mem', vars', hOps, hInterp, _, _⟩ := interpretOp_some_iff.mp hRun`.
2. Unfold `hInterp` (`OperationPtr.interpret`, `interpretOp'` with `hType`, `Cf.interpretOp'`): the successors are `[dest]` (so `(op.getSuccessors! ctx.raw)[0]? = some dest`) and `values = operands`.
3. Take `k := 0` and `so := { forwardedOperands := op.getOperands! ctx.raw }`; `getSuccessorOperands?` reduces to it by `simp [BranchOpInterface.getSuccessorOperands?, hType]`.
4. For `so[i]? = some v`: `v = op.getOperand! ctx.raw i` with `i < numOperands`; `VariableState.getOperandValues_eq_some_iff.mp hOps` gives `state.variables.getVar? v = some operands[i]!`.

Rewriting `hInterp` by `hType` inside the dependent `properties` argument may need the same technique as `transfer_sound_exact`'s fold branch: rewrite `hType` only in `OperationPtr.getOpType!` occurrences via `simp only [hType]`, or `generalize` the properties first.

- [ ] **Step 4: Verify and commit**

Run: `lake build Veir.Dialects.Cf.BranchProofs`
Expected: no warnings.

```bash
git add Veir/Dialects/Cf/BranchProofs.lean Veir.lean
git commit -m "feat(cf): prove cf.br forwards its successor operands

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 9: Record what is proved and what remains

**Files:**
- Modify: `Constant-propagation-analysis.tex` (status paragraph in "Transfer soundness"; the file is untracked, do not `git add` it)
- Modify: `Veir/Analysis/DataFlow/SparseForwardDataFlowAnalysis.lean` (TODO comment near the top)

- [ ] **Step 1: Update the solver TODO**

Replace the sentence beginning "Lifting `SparseConstantPropagation.transfer_sound` to a fixpoint statement" with:

```lean
-- `SparseConstantPropagation.postFixpoint_sound` proves that any post-fixpoint of the
-- constant-propagation constraints is sound for terminating executions. What remains is
-- showing this solver returns a post-fixpoint, which needs `run` and
-- `initializeRecursively` to stop being `partial def` (`partial_fixpoint` suffices for
-- partial correctness).
```

- [ ] **Step 2: Update the writeup's status paragraph**

Add a paragraph stating that `postFixpoint_sound` is proved, and list the open obligations: the solver producing a post-fixpoint; `TakenEdgesLive` (dead-code analysis soundness); `BranchForwards` beyond `cf.br`; `PureResults` beyond `arith`; returned values; and statements on `interpretBlockCFG` directly, which need a CCPO instance for `Interp` with bottom `.fail`.

- [ ] **Step 3: Verify and commit**

Run: `lake build`
Expected: `Build completed successfully`.

```bash
git add Veir/Analysis/DataFlow/SparseForwardDataFlowAnalysis.lean
git commit -m "docs(dataflow): record post-fixpoint soundness and remaining obligations

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

## What this plan does not buy you

- **Not the solver's output.** The theorem covers any post-fixpoint. That `fixpointSolve` returns one is still unproved.
- **Not diverging runs, and not `interpretFunction` directly.** Only terminating executions (`CFGExec`). Stating it on `interpretBlockCFG` needs an order on `Interp` with a known bottom.
- **Conditional on the dead-code analysis** (`TakenEdgesLive`) and on per-opcode obligations. For a real function using `cf.cond_br` or memory operations, `BranchForwards` and `OpSoundAt` must be discharged for those opcodes first.
