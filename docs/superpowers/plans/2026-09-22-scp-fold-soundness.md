# Sparse Constant Propagation Fold Soundness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give `SparseConstantPropagation.transfer` an unconditional local soundness theorem stated against the interpreter's concrete semantics, with UB and interpreter failure representable so the poison-producing fold branches carry real content instead of discharging vacuously.

**Architecture:** The blocker today is not missing semantics — `interpretOp'` models poison and UB completely. The blocker is that the concretization function `γ : AbstractConstant → Set ConcreteConstant` has a concrete domain of bare values, so no soundness relation built on it can describe an execution that had UB, and every fold that turns UB into poison discharges vacuously. We widen the concrete side from `ConcreteConstant` to `Interp (Array RuntimeValue)`, introduce an explicit fold-soundness contract phrased against `interpretOp'`, discharge that contract for the `arith` dialect, and then restate the transfer theorem so only one structural hypothesis (operands initialized) remains.

**A note on terminology,** since this plan introduces a second relation alongside γ and the two are easy to conflate:

- **γ (concretization)** — `AbstractConstant → Set ConcreteConstant`, already in `ConstantDomain.lean:89`. Maps an abstract element to the set of concrete values it denotes. Unchanged by this plan.
- **α (abstraction)** — does not exist in this codebase, and this plan does not add one. `AbstractDomain` (`Veir/Analysis/DataFlow/Domains/AbstractDomain.lean:106`) requires only γ plus `γ_monotone`, so VeIR uses a concretization-based framework rather than a Galois connection. That is deliberate and sufficient: soundness needs only γ and monotonicity, not a best abstraction.
- **Soundness relation** — `AbstractConstant.SoundFor : AbstractConstant → Interp (Array RuntimeValue) → Nat → Prop`, added in Task 2. This is the relation between an abstract fact and a concrete *outcome*. It is defined in terms of γ on the `.ok` branch and is not itself a concretization: its right-hand side is an interpreter outcome, not a value, and it has no set-valued reading. Call it the soundness relation, never "γ" and never "the abstraction relation".

**Tech Stack:** Lean 4.33 module system, `lake build`, compile-time `#guard_msgs` unit tests, `#print axioms` for sorry-freedom checks.

**Spec:** `Constant-propagation-analysis.tex` (sections "Properties that should be proved next" and "Recommended proof plan") and `CONSTANT-PROPAGATION-ANALYSIS.md` in the repository root.

## Revision (2026-09-23): refinement semantics

Both soundness relations were changed from exact equality to refinement (commit `fe1ab2f73`). The exact form rejected `arith.addui_extended x, 0`: the table folds the carry flag to `0` even when `x` is poison, where the interpreter's flag is poison. Poison may be refined to any value of its type, so the fold is correct, but it does not *equal* the interpreted value. Design discussion: https://claude.ai/code/artifact/6d7c6ec2-a4df-495a-a789-ff21f6bf160b

- `FoldDecision.SoundFor` (Task 4): on `.ok`, `actual.isPoison = true ∨ decision.valueFor operands = some actual`.
- `AbstractConstant.SoundFor` (Task 2): on `.ok`, delegates to the new `AbstractConstant.SoundForValue a actual := actual.isPoison = true ∨ (match ofTrackedValue actual with | some c => c ∈ γ a | none => True)`.
- `PropagatesPoisonHonestly` (Task 5) is unchanged and still demands exact poison results.

The code snippets in Tasks 2 and 4 below have been updated to match. Proof sketches elsewhere predate the change; the committed proofs are authoritative.

## Global Constraints

- Every new `.lean` file under `Veir/` begins with `module`, then `public import` / `import` lines, then `public section`.
- Every new `.lean` file must be transitively reachable from a `lakefile.toml` root, or `Tools/check-orphan-modules` fails CI. Add to the `-- FIXME: These modules are otherwise orphans` block in `Veir.lean` only if there is no natural importer.
- Commits follow conventional-commit style with a scope: `feat(dataflow): ...`, `feat(interpreter): ...`, `refactor(dataflow): ...`.
- No `sorry` may survive a task. Every proof task ends with a `#print axioms` check showing only `[propext, Classical.choice, Quot.sound]`.
- Do not weaken or delete `Veir/Analysis/DataFlow/Domains/ConstantDomain.lean`'s existing lattice lemmas — they are load-bearing and already correct.
- Build command throughout: `lake build <Module.Name>`. Full check: `lake build && lake test`.

## Scope

This plan covers **local transfer soundness only**. Two things are explicitly out of scope and need their own plans:

1. **Solver fixpoint soundness.** `visitOperation`, `initializeRecursively` (`Veir/Analysis/DataFlow/SparseForwardDataFlowAnalysis.lean:222,262`) and `DataFlowFramework.run` (`Veir/Analysis/DataFlowFramework.lean:162`) are `partial def`, so they have no equation lemmas and nothing can be proved about them by induction. Lifting local soundness to "every execution reaching a live SSA value is represented by its final fact" requires converting the solver to a structurally- or well-founded-recursive definition first. That is a framework change, not an analysis change.
2. **The `llvm` and `riscv` fold tables.** Only three dialects override `tryFold` (`Veir/IR/OpInfo.lean:77` defaults it to `fun _ _ _ _ => none`): `Arith` (`Veir/Dialects/Arith/OpInfo.lean:143`), `Llvm` (`Veir/Dialects/LLVM/OpInfo.lean:536`), `Riscv` (`Veir/Dialects/RISCV/OpInfo.lean:253`). This plan discharges `Arith` only. Tasks 6 repeats verbatim for the other two once the contract is settled; `Llvm.tryFold` is substantially larger and deserves its own plan.

## File Structure

| File | Responsibility |
|---|---|
| `Veir/Analysis/DataFlow/Domains/ConstantSoundness.lean` (new) | `Interp`-valued soundness relation for `AbstractConstant`; the widened concrete side |
| `Veir/Interpreter/Purity.lean` (new) | Memory-independence of `interpretOp'` for the structurally pure dialect cases |
| `Veir/Interfaces/FoldSoundness.lean` (new) | The fold-soundness contract and its three legs, assembled into `foldsTo_sound` |
| `Veir/Dialects/Arith/FoldProofs.lean` (new) | `Arith.tryFold` satisfies the contract |
| `Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean` (modify) | Restate transfer soundness against the new relation |
| `UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean` (new) | Regression tests pinning the UB/poison behaviour the proofs now describe |

---

### Task 1: Commit the vacuous-theorem removal

Five theorems in `SparseConstantPropagationAnalysis.lean` had conclusions that reduced to `True` or `c = c` regardless of what `transfer` returns. They have been removed from the working tree already; this task commits that. Their content, where it was real, survives as `ofFoldDecision_useConstant_sound` and `ofFoldDecision_useOperand_sound` in `ConstantDomain.lean:204,222`.

**Files:**
- Modify: `Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean` (already edited)

**Interfaces:**
- Consumes: nothing
- Produces: a file whose remaining theorems are `foldResult_realizes_sound`, `transfer_foldCase_realizes_sound`, `transfer_foldCase_concrete_sound`, `transfer_conditional_sound`

- [ ] **Step 1: Confirm the removals are the only working-tree change to the file**

Run: `git diff --stat Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean`
Expected: one file changed, deletions dominating.

- [ ] **Step 2: Confirm the module still builds**

Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis`
Expected: `Build completed successfully`, with only the two pre-existing `hBot` / `hConst` unused-variable warnings.

- [ ] **Step 3: Confirm nothing downstream referenced the removed names**

Run: `lake build UnitTest.DataFlowFramework.SparseConstantPropagation`
Expected: `Build completed successfully`.

- [ ] **Step 4: Commit**

```bash
git add Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean
git commit -m "refactor(dataflow): remove vacuous constant-propagation soundness theorems

transfer_sound, transfer_foldCase_sound, foldResultArray_sound,
transfer_foldBranch_outputs_sound and foldDecision_sound all had conclusions
that reduced to True or c = c independently of the transfer function, so they
constrained nothing. The genuine content is retained in ConstantDomain's
ofFoldDecision_useConstant_sound and ofFoldDecision_useOperand_sound."
```

---

### Task 2: The `Interp`-valued soundness relation

`γ` maps an abstract fact to a set of `ConcreteConstant`, which is a bare `⟨bitwidth, value⟩` pair with no way to say "this execution had UB". This task widens the concrete side.

**Files:**
- Create: `Veir/Analysis/DataFlow/Domains/ConstantSoundness.lean`

**Interfaces:**
- Consumes: `AbstractConstant`, `ConcreteConstant`, `γ`, `γ_top_eq`, `γ_monotone` from `Veir/Analysis/DataFlow/Domains/ConstantDomain.lean`; `Interp` from `Veir/Interpreter/Interp.lean`
- Produces: `AbstractConstant.ofTrackedValue : RuntimeValue → Option ConcreteConstant`, `AbstractConstant.SoundFor : AbstractConstant → Interp (Array RuntimeValue) → Nat → Prop`, and the lemmas `soundFor_top`, `soundFor_ub`, `soundFor_fail`, `soundFor_mono`

- [ ] **Step 1: Write the file with the definitions and the theorem statements stubbed with `sorry`**

```lean
module

public import Veir.Analysis.DataFlow.Domains.ConstantDomain
public import Veir.Interpreter.Interp

/-!
# Soundness relation for the constant domain

`AbstractConstant.γ` concretizes to bare `ConcreteConstant` values, which cannot
describe an execution that triggered undefined behaviour or that the interpreter
could not model. Folding turns both of those outcomes into ordinary values (see
`foldByEvaluation` in `Veir/Interfaces/FoldInterfaces.lean`), so a soundness
statement phrased over bare values discharges vacuously on exactly the cases
where the analysis makes its strongest claims.

`SoundFor` widens the concrete side to an interpreter outcome.
-/

public section

namespace Veir

namespace AbstractConstant

/-- The constant this domain tracks for a runtime value, if it tracks one. -/
def ofTrackedValue : RuntimeValue → Option ConcreteConstant
  | .int bitwidth value => some ⟨bitwidth, value⟩
  | _ => none

/--
`a.SoundFor outcome i` says the abstract fact `a` does not over-claim about
result `i` of an operation whose interpretation produced `outcome`.

Only a successful interpretation constrains the fact:
* `.ub` means the source program's behaviour is unconstrained, so every fact is
  sound — this is what makes a UB-to-poison fold statable;
* `.fail` means the interpreter cannot model the operation, which likewise
  constrains nothing;
* a result outside the tracked integer domain constrains nothing.
-/
def SoundFor (a : AbstractConstant) (outcome : Interp (Array RuntimeValue)) (i : Nat) : Prop :=
  match outcome with
  | .ok results =>
      match results[i]? with
      | some actual => SoundForValue a actual
      | none => True
  | .ub => True
  | .fail => True

@[simp]
theorem soundFor_top (outcome : Interp (Array RuntimeValue)) (i : Nat) :
    SoundFor ⊤ outcome i := by
  sorry

@[simp]
theorem soundFor_ub (a : AbstractConstant) (i : Nat) :
    SoundFor a .ub i := by
  sorry

@[simp]
theorem soundFor_fail (a : AbstractConstant) (i : Nat) :
    SoundFor a .fail i := by
  sorry

/-- A sound fact stays sound when weakened up the lattice. -/
theorem soundFor_mono (a b : AbstractConstant) (outcome : Interp (Array RuntimeValue)) (i : Nat)
    (hab : a ≤ b) : SoundFor a outcome i → SoundFor b outcome i := by
  sorry

end AbstractConstant

end Veir
```

- [ ] **Step 2: Make the file reachable and confirm the statements elaborate but are unproved**

Add `public import Veir.Analysis.DataFlow.Domains.ConstantSoundness` to `Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean`'s import block.

Run: `lake build Veir.Analysis.DataFlow.Domains.ConstantSoundness`
Expected: builds, with four `declaration uses 'sorry'` warnings. This is the red state — the statements typecheck, nothing is proved.

- [ ] **Step 3: Prove the four lemmas**

```lean
@[simp]
theorem soundFor_top (outcome : Interp (Array RuntimeValue)) (i : Nat) :
    SoundFor ⊤ outcome i := by
  unfold SoundFor
  cases outcome with
  | fail => trivial
  | ub => trivial
  | ok results =>
      cases results[i]? >>= ofTrackedValue with
      | none => trivial
      | some c => exact γ_top_eq c

@[simp]
theorem soundFor_ub (a : AbstractConstant) (i : Nat) :
    SoundFor a .ub i := by
  unfold SoundFor; trivial

@[simp]
theorem soundFor_fail (a : AbstractConstant) (i : Nat) :
    SoundFor a .fail i := by
  unfold SoundFor; trivial

theorem soundFor_mono (a b : AbstractConstant) (outcome : Interp (Array RuntimeValue)) (i : Nat)
    (hab : a ≤ b) : SoundFor a outcome i → SoundFor b outcome i := by
  unfold SoundFor
  cases outcome with
  | fail => intro _; trivial
  | ub => intro _; trivial
  | ok results =>
      cases results[i]? >>= ofTrackedValue with
      | none => intro _; trivial
      | some c => exact fun hc => γ_monotone a b hab hc
```

- [ ] **Step 4: Verify the proofs land and are sorry-free**

Run: `lake build Veir.Analysis.DataFlow.Domains.ConstantSoundness`
Expected: `Build completed successfully`, no `sorry` warnings.

Add to the bottom of the file, temporarily:
```lean
#print axioms Veir.AbstractConstant.soundFor_mono
```
Run: `lake env lean Veir/Analysis/DataFlow/Domains/ConstantSoundness.lean`
Expected: `'Veir.AbstractConstant.soundFor_mono' depends on axioms: [propext, Classical.choice, Quot.sound]` — no `sorryAx`. Remove the `#print axioms` line afterwards.

- [ ] **Step 5: Commit**

```bash
git add Veir/Analysis/DataFlow/Domains/ConstantSoundness.lean \
        Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean
git commit -m "feat(dataflow): add Interp-valued soundness relation for the constant domain"
```

---

### Task 3: Memory independence for the structurally pure dialects

`foldEvaluate` runs at `MemoryState.empty` (`Veir/Interpreter/Evaluate.lean:34`), guarded by `getEffects == .none`. Any statement relating a fold to "the" interpretation needs to know the choice of memory does not matter. `OperationPtr.Pure` (`Veir/Interpreter/EquationLemma.lean:38`) already captures memory-independence and has two lemmas proved about it, but nothing connects `getEffects = .none` to it.

The full connection requires a case analysis over every opcode. This task takes the cheap and sufficient part: in `interpretOp'` (`Veir/Interpreter/Basic.lean:1042`), eleven of the fourteen dialect arms have the shape `let (vals, act) ← D.interpretOp' ...; return (vals, mem, act)` and never touch `mem` at all. `arith` is one of them. Only `.llvm`, `.riscv` and `.riscv_stack` thread memory genuinely. So for `arith` the property is structural and needs no effect reasoning.

**Files:**
- Create: `Veir/Interpreter/Purity.lean`

**Interfaces:**
- Consumes: `interpretOp'` from `Veir/Interpreter/Basic.lean:1042`; `Interp.map` from `Veir/Interpreter/Interp.lean:22`
- Produces: `Veir.interpretOp'_arith_memory_irrelevant`

- [ ] **Step 1: Write the failing statement**

```lean
module

public import Veir.Interpreter.Basic

/-!
# Structural purity of `interpretOp'`

Most dialect arms of `interpretOp'` thread the incoming memory through
untouched. For those opcodes, memory-independence holds by the shape of the
definition and needs no reasoning about `getEffects`. This matters because
`foldEvaluate` only ever interprets at `MemoryState.empty`, so any fold
soundness statement must know the choice of memory is irrelevant.

`.llvm`, `.riscv` and `.riscv_stack` genuinely use memory and are not covered
here.
-/

public section

namespace Veir

/-- Interpreting an `arith` operation does not depend on, or modify, memory. -/
theorem interpretOp'_arith_memory_irrelevant
    (op : Veir.Arith) (properties : propertiesOf (OpCode.arith op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (memory₁ memory₂ : MemoryState)
    (layout : DataLayout) :
    interpretOp' (.arith op) properties resultTypes operands blockOperands memory₁ layout =
      (interpretOp' (.arith op) properties resultTypes operands blockOperands memory₂ layout).map
        (fun (results, _, cf) => (results, memory₁, cf)) := by
  sorry

end Veir
```

- [ ] **Step 2: Run to confirm it elaborates and is unproved**

Run: `lake build Veir.Interpreter.Purity`
Expected: builds with `declaration uses 'sorry'`.

- [ ] **Step 3: Prove it**

The `.arith` arm of `interpretOp'` is `do let (vals, act) ← Arith.interpretOp' ...; return (vals, mem, act)`, so both sides reduce to a case split on the same `Arith.interpretOp'` call, which takes no memory argument at all.

```lean
    interpretOp' (.arith op) properties resultTypes operands blockOperands memory₁ layout =
      (interpretOp' (.arith op) properties resultTypes operands blockOperands memory₂ layout).map
        (fun (results, _, cf) => (results, memory₁, cf)) := by
  simp only [interpretOp']
  cases Arith.interpretOp' op properties resultTypes operands blockOperands <;> rfl
```

If `simp only [interpretOp']` does not unfold (the definition is a large `match`), replace it with `show` spelling out the `.arith` arm, or add `unfold interpretOp'` followed by `split`.

- [ ] **Step 4: Verify**

Run: `lake build Veir.Interpreter.Purity`
Expected: `Build completed successfully`, no sorry warning.

Run: `lake env lean Veir/Interpreter/Purity.lean` with `#print axioms Veir.interpretOp'_arith_memory_irrelevant` appended temporarily.
Expected: no `sorryAx`. Remove the line afterwards.

- [ ] **Step 5: Commit**

```bash
git add Veir/Interpreter/Purity.lean
git commit -m "feat(interpreter): prove arith interpretation is memory-independent"
```

---

### Task 4: The fold-soundness contract and its evaluation leg

`OpCode.foldsTo` (`Veir/Interfaces/FoldInterfaces.lean:77`) draws from three sources and today has **zero** lemmas of any kind. This task names the contract and discharges the one leg that already goes through the interpreter.

**Files:**
- Create: `Veir/Interfaces/FoldSoundness.lean`

**Interfaces:**
- Consumes: `OpCode.foldsTo`, `foldEvaluate` (`Veir/Interpreter/Evaluate.lean:29`), `FoldDecision` (`Veir/FoldDecision.lean:18`), `interpretOp'_arith_memory_irrelevant` from Task 3
- Produces: `FoldDecision.valueFor`, `Veir.interpretPure`, `Veir.ConstOperandsAgree`, `FoldDecision.SoundFor`, `Veir.foldByEvaluation_sound`

- [ ] **Step 1: Write the definitions and the evaluation-leg statement with `sorry`**

Note that `foldByEvaluation` is `private` in `FoldInterfaces.lean`. Either remove `private` from `foldByEvaluation`, `foldByTable`, `foldPoisonedOperand` and `preferredFold`, or use `import all Veir.Interfaces.FoldInterfaces` here (the pattern `Veir/Verifier.lean` uses). Prefer `import all` so the public surface of `FoldInterfaces` is unchanged.

```lean
module

public import Veir.Interfaces.FoldInterfaces
public import Veir.Interpreter.Purity

import all Veir.Interfaces.FoldInterfaces

/-!
# Fold soundness contract

`OpCode.foldsTo` decides that an operation folds. Nothing today relates that
decision to `interpretOp'`, which is the project's only concrete semantics.
This file states the contract and discharges it leg by leg.

The contract is stated against an interpreter *outcome* rather than a value.
`foldByEvaluation` converts `Interp.ub` into poison, and `ValuePtr.constantValue`
does the same at `Veir/Interfaces/ConstantLikeInterfaces.lean:41`. Neither can be
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
      | some actual => actual.isPoison = true ∨ decision.valueFor operands = some actual
      | none => True
  | .ub => True
  | .fail => True

/-- The evaluation leg: decisions produced by interpreting the operation are sound. -/
theorem foldByEvaluation_sound
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hAgree : ConstOperandsAgree constOperands operands)
    (hSize : constOperands.size = operands.size)
    (hFold : foldByEvaluation opType properties resultTypes constOperands = some decisions)
    (hDecision : decisions[i]? = some decision) :
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i := by
  sorry

end Veir
```

- [ ] **Step 2: Run to confirm the red state**

Run: `lake build Veir.Interfaces.FoldSoundness`
Expected: builds with one `declaration uses 'sorry'`.

- [ ] **Step 3: Prove the evaluation leg**

`foldByEvaluation` first does `let values ← constOperands.mapM id`, so it only fires when every operand is known; with `hAgree` and `hSize` that array is exactly `operands`. Then it splits on `foldEvaluate`:

- `.fail` → `foldByEvaluation` returns `none`, contradicting `hFold`.
- `.ok results` → decisions are `results.map .useConstant`, so `decision.valueFor operands = some results[i]!`, which is the interpreted value. Note `foldEvaluate` also returns `none` when `action.isSome`, so the control-flow component is `none` and `interpretPure` agrees.
- `.ub` → decisions are `allResultsPoison resultTypes`, and `interpretPure` is `.ub`, so `SoundFor` is `True` by definition.

```lean
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i := by
  unfold foldByEvaluation at hFold
  -- `constOperands.mapM id = some operands`
  have hValues : constOperands.mapM id = some operands := by
    apply Array.mapM_id_eq_some_of_agree hAgree hSize
  rw [hValues] at hFold
  unfold foldEvaluate interpretPure at *
  split at hFold
  case isTrue =>
    -- `isFoldEvaluationCandidate` false: `foldByEvaluation` returned `none`
    simp at hFold
  case isFalse =>
    cases hInterp : interpretOp' opType properties resultTypes operands #[] MemoryState.empty with
    | fail => simp [hInterp] at hFold
    | ub => simp [FoldDecision.SoundFor, hInterp, Interp.map]
    | ok triple =>
        obtain ⟨results, mem, action⟩ := triple
        cases hAction : action with
        | some _ => simp [hInterp, hAction] at hFold
        | none =>
            simp only [hInterp, hAction] at hFold
            simp only [FoldDecision.SoundFor, Interp.map, hInterp]
            have : decision = .useConstant results[i]! := by
              simpa [← hFold] using hDecision
            subst this
            simp [FoldDecision.valueFor]
            grind
```

The helper `Array.mapM_id_eq_some_of_agree` does not exist. Prove it in the same file, above the theorem:

```lean
/-- When every entry of `constOperands` is known and agrees with `operands`, the
    sequenced array is exactly `operands`. -/
theorem Array.mapM_id_eq_some_of_agree
    {constOperands : Array (Option RuntimeValue)} {operands : Array RuntimeValue}
    (hAgree : ConstOperandsAgree constOperands operands)
    (hSize : constOperands.size = operands.size)
    (hKnown : ∀ (i : Nat), i < constOperands.size → (constOperands[i]?).isSome) :
    constOperands.mapM id = some operands := by
  sorry
```

`hKnown` is not available as a hypothesis — it is a *consequence* of `foldByEvaluation` having succeeded. Restructure: split on `constOperands.mapM id` first, discharge the `none` case against `hFold`, and in the `some values` case prove `values = operands` from `hAgree` and `hSize` by `Array.ext`. Adjust the proof above accordingly rather than introducing `hKnown` as a premise.

- [ ] **Step 4: Verify**

Run: `lake build Veir.Interfaces.FoldSoundness`
Expected: `Build completed successfully`, no sorry warnings.

Append `#print axioms Veir.foldByEvaluation_sound`, run `lake env lean Veir/Interfaces/FoldSoundness.lean`, expect no `sorryAx`, remove the line.

- [ ] **Step 5: Commit**

```bash
git add Veir/Interfaces/FoldSoundness.lean
git commit -m "feat(interpreter): state fold soundness contract and prove the evaluation leg"
```

---

### Task 5: The poison-propagation leg

`foldPoisonedOperand` (`Veir/Interfaces/FoldInterfaces.lean:63`) fires when `opType.propagatesPoison` and some known operand is poison, and folds every result to poison. Unlike the evaluation leg this never consults the interpreter, so soundness rests entirely on the `propagatesPoison` flag being honest.

**Files:**
- Modify: `Veir/Interfaces/FoldSoundness.lean`

**Interfaces:**
- Consumes: `FoldDecision.SoundFor`, `interpretPure`, `ConstOperandsAgree` from Task 4; `OpCode.propagatesPoison` (`Veir/GlobalOpInfo.lean:291`); `RuntimeValue.isPoison`, `RuntimeValue.getPoisonForType` (`Veir/RuntimeValue/Basic.lean:37,50`)
- Produces: `Veir.PropagatesPoisonHonestly`, `Veir.foldPoisonedOperand_sound`

- [ ] **Step 1: State the honesty property and the leg, with `sorry`**

```lean
/--
The `propagatesPoison` flag is honest for `opType`: whenever a wholly-poison
operand is supplied, interpretation either fails, is UB, or produces wholly
poison results of the declared types.

This is the semantic content the flag asserts. It is a per-opcode obligation:
nothing in `Veir/IR/OpInfo.lean` enforces it.
-/
def PropagatesPoisonHonestly (opType : OpCode) : Prop :=
  opType.propagatesPoison = true →
  ∀ (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue),
    (operands.any RuntimeValue.isPoison) = true →
    ∀ (i : Nat) (actual : RuntimeValue),
      (match interpretPure opType properties resultTypes operands with
       | .ok results => results[i]?
       | _ => none) = some actual →
      resultTypes[i]?.bind RuntimeValue.getPoisonForType = some actual

/-- The poison leg: poison-propagating folds are sound when the flag is honest. -/
theorem foldPoisonedOperand_sound
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hHonest : PropagatesPoisonHonestly opType)
    (hAgree : ConstOperandsAgree constOperands operands)
    (hFold : foldPoisonedOperand opType resultTypes constOperands = some decisions)
    (hDecision : decisions[i]? = some decision) :
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i := by
  sorry
```

- [ ] **Step 2: Run to confirm the red state**

Run: `lake build Veir.Interfaces.FoldSoundness`
Expected: builds with one `declaration uses 'sorry'`.

- [ ] **Step 3: Prove the leg**

`foldPoisonedOperand` guards on `opType.propagatesPoison` and on some entry of `constOperands` being `some value` with `value.isPoison`. Via `hAgree` that operand is also in `operands`, giving `operands.any RuntimeValue.isPoison = true`. The decisions are `allResultsPoison resultTypes`, i.e. `.useConstant` of `getPoisonForType` per result type. `hHonest` then says the interpreter's result at `i`, when it has one, is exactly that value.

```lean
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i := by
  unfold foldPoisonedOperand at hFold
  simp only [Option.guard_eq_some, bind] at hFold
  obtain ⟨hPropagates, hSomePoison, hDecisions⟩ := hFold
  have hOperandPoison : (operands.any RuntimeValue.isPoison) = true := by
    obtain ⟨j, value, hConst, hPoison⟩ := Array.any_eq_true.mp hSomePoison
    exact Array.any_eq_true.mpr ⟨j, value, hAgree j value hConst, hPoison⟩
  unfold FoldDecision.SoundFor
  cases hInterp : interpretPure opType properties resultTypes operands with
  | fail => trivial
  | ub => trivial
  | ok results =>
      cases hResult : results[i]? with
      | none => trivial
      | some actual =>
          have hPoisonValue := hHonest hPropagates properties resultTypes operands
            hOperandPoison i actual (by simp [hInterp, hResult])
          have : decision = .useConstant actual := by
            simpa [← hDecisions, allResultsPoison, hPoisonValue] using hDecision
          subst this
          simp [FoldDecision.valueFor]
```

The `hSomePoison` destructuring depends on how `guard` elaborates in the `Option` monad; if `simp only [Option.guard_eq_some]` does not fire, use `split at hFold` twice instead and read the guards off the resulting hypotheses.

- [ ] **Step 4: Verify**

Run: `lake build Veir.Interfaces.FoldSoundness`
Expected: `Build completed successfully`, no sorry warnings.

- [ ] **Step 5: Commit**

```bash
git add Veir/Interfaces/FoldSoundness.lean
git commit -m "feat(interpreter): prove the poison-propagation leg of fold soundness"
```

---

### Task 6: The `arith` fold table satisfies the contract

`Arith.tryFold` (`Veir/Dialects/Arith/OpInfo.lean:143-152`) is small — it handles exactly two opcodes:

```lean
| .addi, [_, some (.int _ (.val bits))] =>
  if bits = 0 then some #[.useOperand 0] else none
| .addui_extended, [_, some (.int _ (.val bits))] =>
  if bits = 0 then some #[.useOperand 0, .useConstant (.int 1 (.val 0#1))] else none
| _, _ => none
```

Both claim `x + 0 = x`. The supporting arithmetic fact is that adding zero cannot overflow, so the `nsw`/`nuw` flags never force poison.

**Files:**
- Create: `Veir/Dialects/Arith/FoldProofs.lean`
- Modify: `Veir.lean` (add the import if `FoldSoundness` does not import it)

**Interfaces:**
- Consumes: `FoldDecision.SoundFor`, `interpretPure`, `ConstOperandsAgree` from Task 4; `Arith.interpretOp'` (`Veir/Dialects/Arith/OpInfo.lean:258`); `LLVM.Int.add` (`Veir/Data/LLVM/Int/Basic.lean:118`)
- Produces: `Veir.LLVM.Int.add_zero_eq`, `Veir.Arith.tryFold_sound`

- [ ] **Step 1: Write the supporting arithmetic lemma and the table leg, with `sorry`**

```lean
module

public import Veir.Interfaces.FoldSoundness
public import Veir.Dialects.Arith.OpInfo

/-!
# Soundness of the `arith` fold table

`Arith.tryFold` fires for exactly two opcodes, both on the rewrite `x + 0 = x`.
This file discharges the fold-soundness contract for them.
-/

public section

namespace Veir

/-- Adding zero is the identity, and cannot set either overflow flag. -/
theorem LLVM.Int.add_zero_eq {w : Nat} (x : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.add x (.val 0#w) nsw nuw = x := by
  sorry

/-- The table leg, for `arith`. -/
theorem Arith.tryFold_sound
    (op : Veir.Arith) (properties : propertiesOf (OpCode.arith op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hAgree : ConstOperandsAgree constOperands operands)
    (hFold : Arith.tryFold op properties resultTypes constOperands = some decisions)
    (hDecision : decisions[i]? = some decision) :
    decision.SoundFor operands (interpretPure (.arith op) properties resultTypes operands) i := by
  sorry

end Veir
```

- [ ] **Step 2: Run to confirm the red state**

Run: `lake build Veir.Dialects.Arith.FoldProofs`
Expected: builds with two `declaration uses 'sorry'`.

- [ ] **Step 3: Prove the arithmetic lemma**

`LLVM.Int.add` (`Veir/Data/LLVM/Int/Basic.lean:118-125`) destructures both operands, returning `poison` if either is, then checks the flags. With `y = .val 0#w` the sum is `x'`, and neither signed nor unsigned overflow can occur.

```lean
theorem LLVM.Int.add_zero_eq {w : Nat} (x : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.add x (.val 0#w) nsw nuw = x := by
  cases x with
  | poison => rfl
  | val bits =>
      unfold Data.LLVM.Int.add
      simp only [BitVec.add_zero]
      -- discharge the two overflow guards
      split <;> split <;> simp_all <;> bv_decide
```

If `bv_decide` is unavailable or times out, replace the final tactic with explicit rewriting of the carry predicates; check whether `Veir/Data/LLVM/Int/` already carries `uaddOverflow`/`saddOverflow` simp lemmas for a zero addend and reuse them.

- [ ] **Step 4: Prove the table leg**

Case on `op`. All constructors except `.addi` and `.addui_extended` make `Arith.tryFold` return `none`, contradicting `hFold`. For the two that remain, the guard gives operand 1 = `.int w (.val 0#w)`; `hAgree` transfers that to `operands`; `Arith.interpretOp'` on `.addi` then computes `LLVM.Int.add lhs (.val 0#w) nsw nuw`, which `add_zero_eq` collapses to `lhs`, which is exactly what `.useOperand 0` names.

```lean
    decision.SoundFor operands (interpretPure (.arith op) properties resultTypes operands) i := by
  cases op <;> simp [Arith.tryFold] at hFold
  case addi =>
    obtain ⟨w, bits, hConst₁, hZero, hDecisions⟩ := hFold
    have hOperand₁ : operands[1]? = some (.int w (.val 0#w)) := by
      simpa [hZero] using hAgree 1 _ hConst₁
    have : decision = .useOperand 0 := by simpa [← hDecisions] using hDecision
    subst this
    unfold FoldDecision.SoundFor interpretPure interpretOp'
    cases hOperands : operands.toList with
    | nil => simp [Arith.interpretOp', hOperands]
    | cons lhsValue rest =>
        cases lhsValue <;> simp [Arith.interpretOp', hOperands, hOperand₁, Interp.map] <;>
          simp [FoldDecision.valueFor, LLVM.Int.add_zero_eq]
  case addui__extended =>
    -- identical shape; result 0 is `useOperand 0`, result 1 is the constant `false` i1,
    -- which is sound because adding zero cannot carry.
    sorry
```

Finish `addui__extended` the same way, using the `.addui_extended` arm of `Arith.interpretOp'` and a companion lemma `LLVM.Int.add_zero_no_carry` proved alongside `add_zero_eq` if the extended arm computes the carry flag separately. Do not leave the `sorry`.

Confirm the constructor name: `#generate_dialect` maps `addui_extended` to the Lean constructor `addui__extended` (double underscore). Check with `#check Veir.Arith.addui__extended` before writing the case.

- [ ] **Step 5: Verify**

Run: `lake build Veir.Dialects.Arith.FoldProofs`
Expected: `Build completed successfully`, no sorry warnings.

Run: `python3 Tools/check-orphan-modules` (needs Python 3.11+, not the repo `.venv`).
Expected: no orphan reported for `Veir/Dialects/Arith/FoldProofs.lean`. If it is reported, add `public import Veir.Dialects.Arith.FoldProofs` to the FIXME block in `Veir.lean`.

- [ ] **Step 6: Commit**

```bash
git add Veir/Dialects/Arith/FoldProofs.lean Veir.lean
git commit -m "feat(arith): prove the arith fold table satisfies fold soundness"
```

---

### Task 7: Assemble `foldsTo_sound`

`OpCode.foldsTo` combines the three legs through `preferredFold`, which ranks outcomes and **returns the table decision on ties** (`Veir/Interfaces/FoldInterfaces.lean:28-30`). So the assembled theorem cannot lean on the evaluation leg alone — it must case on which source won.

**Files:**
- Modify: `Veir/Interfaces/FoldSoundness.lean`

**Interfaces:**
- Consumes: `foldByEvaluation_sound` (Task 4), `foldPoisonedOperand_sound` (Task 5), `Arith.tryFold_sound` (Task 6)
- Produces: `Veir.FoldTableSound`, `Veir.foldsTo_sound`

- [ ] **Step 1: State the table hypothesis and the assembled theorem, with `sorry`**

Because `Arith.tryFold_sound` lives downstream of this file, take the table leg as a hypothesis rather than importing it, and instantiate it at the call site in Task 8.

```lean
/-- The dialect fold table for `opType` satisfies the contract. -/
def FoldTableSound (opType : OpCode) : Prop :=
  ∀ (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision),
    ConstOperandsAgree constOperands operands →
    foldByTable opType properties resultTypes constOperands = some decisions →
    decisions[i]? = some decision →
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i

/--
Fold soundness for `OpCode.foldsTo`: every decision it returns names the value
the interpreter produces, whenever the interpreter produces one.
-/
theorem foldsTo_sound
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hTable : FoldTableSound opType)
    (hHonest : PropagatesPoisonHonestly opType)
    (hAgree : ConstOperandsAgree constOperands operands)
    (hSize : constOperands.size = operands.size)
    (hFold : OpCode.foldsTo opType properties resultTypes constOperands = some decisions)
    (hDecision : decisions[i]? = some decision) :
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i := by
  sorry
```

- [ ] **Step 2: Run to confirm the red state**

Run: `lake build Veir.Interfaces.FoldSoundness`
Expected: builds with one `declaration uses 'sorry'`.

- [ ] **Step 3: Prove it**

`OpCode.foldsTo` first guards `!opType.isConstantLike`, then short-circuits on `foldPoisonedOperand`, then computes `preferredFold tableDecision evaluationDecision`. `preferredFold` returns either its first or its second argument verbatim, so every outcome is one of the three legs.

```lean
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i := by
  unfold OpCode.foldsTo at hFold
  split at hFold
  case isTrue => simp at hFold          -- constant-like: foldsTo returns none
  case isFalse =>
    cases hPoison : foldPoisonedOperand opType resultTypes constOperands with
    | some poisonDecisions =>
        have : decisions = poisonDecisions := by simpa [hPoison] using hFold
        subst this
        exact foldPoisonedOperand_sound opType properties resultTypes operands constOperands
          decisions i decision hHonest hAgree hPoison hDecision
    | none =>
        simp only [hPoison] at hFold
        unfold preferredFold at hFold
        split at hFold
        · -- the evaluation decision won
          exact foldByEvaluation_sound opType properties resultTypes operands constOperands
            decisions i decision hAgree hSize (by simpa using hFold) hDecision
        · -- the table decision won (this is the tie case too)
          exact hTable properties resultTypes operands constOperands decisions i decision
            hAgree (by simpa using hFold) hDecision
```

The two `by simpa using hFold` steps need `preferredFold`'s branches to be reduced to `tableDecision = some decisions` and `evaluationDecision = some decisions` respectively. If `split` leaves the `foldPreference` comparison in the way, `rcases` on `foldPreference tableDecision < foldPreference evaluationDecision` first.

- [ ] **Step 4: Verify**

Run: `lake build Veir.Interfaces.FoldSoundness`
Expected: `Build completed successfully`, no sorry warnings.

Append `#print axioms Veir.foldsTo_sound`, run `lake env lean Veir/Interfaces/FoldSoundness.lean`, expect no `sorryAx`, remove the line.

- [ ] **Step 5: Commit**

```bash
git add Veir/Interfaces/FoldSoundness.lean
git commit -m "feat(interpreter): assemble fold soundness across table, evaluation and poison legs"
```

---

### Task 8: Restate transfer soundness

`transfer_conditional_sound` currently carries three semantic hypotheses (`hBottomSound`, `hConstantSound`, `hFoldSound`) and one bookkeeping one (`hConstantResults`). Tasks 4–7 discharge `hFoldSound`. The constant-like branch is discharged directly, because `ValuePtr.constantValue` already interprets the operation (`Veir/Interfaces/ConstantLikeInterfaces.lean:39`). What remains is the `⊥` branch, which is genuinely a solver invariant, not a local fact: `transfer` returns `⊥` for every result when any operand is `⊥`, and `γ ⊥ = ∅`, so the branch is sound only when no reachable operand is still uninitialised.

**Files:**
- Modify: `Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean`

**Interfaces:**
- Consumes: `AbstractConstant.SoundFor` (Task 2), `foldsTo_sound`, `FoldTableSound`, `PropagatesPoisonHonestly`, `ConstOperandsAgree`, `interpretPure` (Tasks 4–7)
- Produces: `SparseConstantPropagation.OperandsSound`, `SparseConstantPropagation.transfer_sound`

- [ ] **Step 1: State the new theorem with `sorry`, keeping the old one alongside**

```lean
/-- Every abstract operand fact describes its concrete operand. -/
def OperandsSound (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array RuntimeValue) : Prop :=
  ∀ (i : Nat) (v : RuntimeValue) (a : AbstractConstant),
    concreteOperands[i]? = some v → abstractOperands[i]? = some a →
    ∀ c, AbstractConstant.ofTrackedValue v = some c → c ∈ AbstractConstant.γ a

/--
Local soundness of the constant-propagation transfer function.

Every result fact `transfer` produces describes the value the interpreter
actually produces for that result. UB and interpreter failure constrain nothing,
which is what lets the poison-producing fold branches carry content.

`hInitialized` is the one remaining obligation and it is structural, not
semantic: `transfer` returns `⊥` when an operand fact is still `⊥`, and `γ ⊥` is
empty, so the branch is sound exactly when the solver has initialised every
operand of a reachable operation. Discharging it belongs to the sparse solver,
which cannot be reasoned about today — see the scope note in
`docs/superpowers/plans/2026-09-22-scp-fold-soundness.md`.
-/
theorem transfer_sound
    (op : OperationPtr) (irCtx : WfIRContext OpCode) (opInBounds : op.InBounds irCtx.raw)
    (abstractOperands : Array AbstractConstant) (concreteOperands : Array RuntimeValue)
    (hTable : FoldTableSound (op.getOpType! irCtx.raw))
    (hHonest : PropagatesPoisonHonestly (op.getOpType! irCtx.raw))
    (hOperands : OperandsSound abstractOperands concreteOperands)
    (hSize : abstractOperands.size = concreteOperands.size)
    (hInitialized : ¬ abstractOperands.any (· = ⊥))
    (i : Nat) :
    AbstractConstant.SoundFor ((transfer op abstractOperands irCtx)[i]?.getD ⊤)
      (interpretPure (op.getOpType! irCtx.raw)
        (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw))
        (op.getResultTypes! irCtx.raw) concreteOperands) i := by
  sorry
```

- [ ] **Step 2: Run to confirm the red state**

Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis`
Expected: builds with one `declaration uses 'sorry'`.

- [ ] **Step 3: Prove it, reusing the branch skeleton from `transfer_conditional_sound`**

The branch structure is already proved in `transfer_conditional_sound` — lift it. The three `⊤`-returning branches (regions, failed fold, out of bounds) close with `AbstractConstant.soundFor_top`, which is strictly easier than the old `γ_top_eq` plumbing. The `⊥` branch closes by `hInitialized`. The constant-like branch unfolds `ValuePtr.constantValue` and matches its `.ok` / `.ub` arms against `SoundFor`'s. The fold branch applies `foldsTo_sound` and then transports through `ofFoldDecision`.

The transport step needs one new bridging lemma; prove it in `ConstantSoundness.lean` and re-run Task 2's verification afterwards:

```lean
/-- A decision sound for the semantics yields an abstract fact sound for it too. -/
theorem AbstractConstant.ofFoldDecision_soundFor
    (decision : FoldDecision) (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array RuntimeValue) (outcome : Interp (Array RuntimeValue)) (i : Nat)
    (hOperands : OperandsSound abstractOperands concreteOperands)
    (hDecision : decision.SoundFor concreteOperands outcome i) :
    SoundFor (AbstractConstant.ofFoldDecision decision abstractOperands) outcome i
```

- [ ] **Step 4: Delete the superseded conditional theorems**

Once `transfer_sound` is proved, `transfer_conditional_sound`, `transfer_foldCase_concrete_sound`, `transfer_foldCase_realizes_sound` and `foldResult_realizes_sound` are all subsumed. Delete them, along with `foldDecisionRealizes` and `ofFoldDecision_realizes_sound` in `ConstantDomain.lean:81,240` if nothing else references them.

Run: `grep -rn "foldDecisionRealizes\|transfer_conditional_sound" --include=*.lean . | grep -v '^./.lake'`
Expected: no hits outside the deletions.

- [ ] **Step 5: Verify**

Run: `lake build && lake test`
Expected: `Build completed successfully` for both.

Append `#print axioms Veir.SparseConstantPropagation.transfer_sound`, run `lake env lean Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean`, expect no `sorryAx`, remove the line.

- [ ] **Step 6: Commit**

```bash
git add Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean \
        Veir/Analysis/DataFlow/Domains/ConstantSoundness.lean \
        Veir/Analysis/DataFlow/Domains/ConstantDomain.lean
git commit -m "feat(dataflow): prove local soundness of the constant-propagation transfer"
```

---

### Task 9: Pin the UB and poison behaviour with regression tests

The proofs now describe what the analysis does on division by zero. Lock that behaviour in so a later change to `preferredFold` or to `Arith.tryFold` cannot silently alter it.

**Files:**
- Create: `UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean`
- Modify: `UnitTest.lean` (add the import)

**Interfaces:**
- Consumes: `runWithAnalyses`, `recoverNames`, `checkNamedConstants` from `UnitTest/DataFlowFramework/Helpers.lean:160,172`
- Produces: nothing downstream

- [ ] **Step 1: Write the tests**

These expectations are the behaviour observed on the current tree, confirmed by running the analysis: `10 / 2` yields `const(0x00000005#32)` and `10 / 0` yields `const(poison : i32)`.

```lean
import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.Domains.ConstantDomain
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis

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

/-- The `arith.addi x, 0` table entry, the one rewrite `Arith.tryFold` claims. -/
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
```

- [ ] **Step 2: Register the test module**

Add `import UnitTest.DataFlowFramework.SparseConstantPropagationSoundness` to `UnitTest.lean`.

- [ ] **Step 3: Run the tests**

Run: `lake test`
Expected: `Build completed successfully`. A `#guard_msgs` mismatch is a build error, so a green build is a passing suite.

- [ ] **Step 4: Commit**

```bash
git add UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean UnitTest.lean
git commit -m "test(dataflow): pin UB-to-poison and add-zero constant propagation behaviour"
```

---

### Task 10: Record the remaining obligations

Three things remain open after Task 9. Write them down where the next person will find them rather than leaving them implicit.

**Files:**
- Modify: `Constant-propagation-analysis.tex` (the "Properties that should be proved next" section)
- Modify: `Veir/Analysis/DataFlow/SparseForwardDataFlowAnalysis.lean` (extend the TODO at line 15)

**Interfaces:**
- Consumes: nothing
- Produces: nothing

- [ ] **Step 1: Update the writeup**

Replace the "Transfer soundness" subsection's closing paragraph with a statement of what is now proved (`transfer_sound`, unconditional except for `hInitialized`, `hTable`, `hHonest`) and what is not:

1. `FoldTableSound` holds only for `arith`. `Llvm.tryFold` (`Veir/Dialects/LLVM/OpInfo.lean:536`) and `Riscv.tryFold` (`Veir/Dialects/RISCV/OpInfo.lean:253`) are undischarged.
2. `PropagatesPoisonHonestly` is undischarged for every opcode. It is a per-opcode obligation that nothing in `Veir/IR/OpInfo.lean:97` enforces.
3. `hInitialized` is a solver invariant. It cannot be discharged until the sparse solver is provable.

- [ ] **Step 2: Extend the solver TODO**

At `Veir/Analysis/DataFlow/SparseForwardDataFlowAnalysis.lean:15`, replace:

```lean
-- TODO: When this is verified, we will need something stronger than this for `Domain`
```

with:

```lean
-- TODO: When this is verified, we will need something stronger than this for `Domain`.
-- Verification is currently blocked: `visitOperation` and `initializeRecursively` below,
-- and `DataFlowFramework.run`, are `partial def` and so have no equation lemmas to induct
-- on. Lifting `SparseConstantPropagation.transfer_sound` to a fixpoint statement — every
-- execution reaching a live SSA value is described by that value's final fact — requires
-- converting them to well-founded recursion first. That change also has to establish the
-- `hInitialized` hypothesis of `transfer_sound`: no operand of a reachable operation is
-- still `⊥` at fixpoint.
```

- [ ] **Step 3: Verify nothing broke**

Run: `lake build`
Expected: `Build completed successfully`.

- [ ] **Step 4: Commit**

```bash
git add Constant-propagation-analysis.tex Veir/Analysis/DataFlow/SparseForwardDataFlowAnalysis.lean
git commit -m "docs(dataflow): record remaining constant-propagation proof obligations"
```

---

## What this plan does not buy you

Worth being blunt, because the shape of the result is easy to oversell:

- **Not end-to-end soundness.** After Task 9 you have a theorem about one operation in isolation. The statement "the analysis's final facts describe every real execution" needs the solver, which is out of scope for the structural reason in Task 10.
- **Not full dialect coverage.** `arith` only. An `llvm.udiv` folding through `Llvm.tryFold` is still unverified, and `FoldTableSound (.llvm _)` will simply be an unprovable hypothesis at the call site until someone discharges it.
- **`PropagatesPoisonHonestly` is a real obligation, not a formality.** It quantifies over every opcode with the flag set. If any dialect has set `propagatesPoison := true` on an opcode whose interpretation does not in fact propagate poison, this plan surfaces that as an unprovable goal — which is the point, but expect it to find something.

## Self-review notes

- **Spec coverage.** Against `Constant-propagation-analysis.tex` §"Recommended proof plan": step 1 (lattice/conversion lemmas) was already done before this plan; step 2 (concrete evaluation relation) is Task 2; step 3 (fold-soundness interface) is Tasks 4–7; steps 4–5 (transfer soundness for constant-like, fallback, and arithmetic) are Task 8; step 6 (fixpoint soundness) is explicitly out of scope with the reason recorded in Task 10; step 7 (rewrite pass) is downstream of all of it.
- **Known soft spots.** Task 4 Step 3 and Task 6 Step 4 both contain proof sketches whose tactic details depend on how Lean elaborates `Option`-monad `guard` and the generated `Arith` constructor names. Each carries an explicit fallback instruction. Task 6's `addui__extended` case is sketched rather than written out; the task says not to leave the `sorry`, and the executor should expect to prove a small carry lemma there.
- **Type consistency.** `SoundFor` appears in two namespaces deliberately — `AbstractConstant.SoundFor` (fact vs. outcome, Task 2) and `FoldDecision.SoundFor` (decision vs. outcome, Task 4). They are bridged by `AbstractConstant.ofFoldDecision_soundFor` in Task 8 Step 3. Do not merge them; they have different left-hand types.
