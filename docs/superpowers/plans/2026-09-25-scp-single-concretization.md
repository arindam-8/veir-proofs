# Constant Propagation: One Concretization, Per-Opcode Monotonicity — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `AbstractConstant.γ` the only function that relates a constant-propagation fact to a runtime value, and make `SparseConstantPropagation.transfer_sound` independent of the inconsistent axiom `interpretOp'_monotone`.

**Architecture:** `γ` moves from `ConcreteConstant` to `RuntimeValue` and absorbs the meaning of `Refines` (`.constant c` denotes every value refined by `c`: `c` itself, or poison of that width). `Refines`, `DescribesExactly`, `OperandsExact`, `transfer_sound_exact` and `refineOperands` are deleted. The gap between "the folder evaluated on `c`" and "the program ran on poison" is confined to one bridge lemma, `fold_sound`, which uses a per-opcode monotonicity hypothesis `InterpretMonotone` instead of the global axiom. `InterpretMonotone` is proved for every `arith` opcode, and shown false for `llvm.freeze`.

**Tech Stack:** Lean 4 (`lean-toolchain`), `lake build`, `lake test`, `#print axioms`.

**Spec:** the "Design" section below. Context: the worked example "Why transfer_sound needs refinement" (https://claude.ai/code/artifact/41a414b8-6774-486a-a04c-ed6a4a2d34de), whose last section shows `interpretOp'_monotone` is inconsistent (`llvm.freeze`) and that the analysis yields an unsound fact through `freeze`.

## Global Constraints

- `Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean` is **not** a `module` file (plain `import`s, then `public section`). Keep it that way. Every other file touched here is a `module` file; new files under `Veir/` must start with `module`.
- Every new `.lean` file must be reachable from a `lakefile.toml` root (`Veir.lean` / `UnitTest.lean`).
- Do not modify or delete the axiom `interpretOp'_monotone` (`Veir/Interpreter/Lemmas.lean:648`) or its users in `Veir/Interpreter/Refinement/Monotonicity.lean`. They are shared infrastructure owned by another author; this plan only stops the analysis from depending on it.
- No `sorry` survives a task. `#print axioms SparseConstantPropagation.transfer_sound` must end up **without** `Veir.interpretOp'_monotone`.
- Naming: `γ` is the only fact–value relation; pointwise lifts are named after it (`OperandsInGamma`). Per-opcode obligations are `UpperCamelCase` `Prop`s (`InterpretMonotone`, like `FoldTableSound`). Theorems are `snake_case`.
- Commits: conventional-commit style with a scope, ending with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- Build a module: `lake build <Module.Name>`. Full check: `lake build && lake test`. A full build can take ~10 minutes.

## Design

**One comparison.** Today three functions compare a fact with a value: `γ` (exact, over `ConcreteConstant`, used by no soundness theorem), `Refines` (up to refinement) and `DescribesExactly` (exact, over `RuntimeValue`). After this plan there is one:

```lean
@[expose] def γ (absVal : AbstractConstant) : Set RuntimeValue :=
  match absVal with
  | .top => fun _ => True
  | .bottom => fun _ => False
  | .constant c => fun v => v ⊒ .int c.bitwidth c.value
```

`SoundFor` (facts vs interpreter outcomes) delegates to `γ` on `.ok`, and `OperandsInGamma` is `γ` pointwise.

**What `⊒` remains, and why it is not a second comparison.** Two concrete-vs-concrete refinements stay, because they are about semantics, not about the abstraction: `FoldDecision.SoundFor` (the folder's claimed replacement refines the actual value; shared with canonicalization) and `InterpretMonotone` (refined operands give refined results).

**The one bridge.** `transfer` hands the folder `foldInputs facts` (a named version of today's `let constantOperands`). The folder's contract (`foldsTo_sound`) is about operands that *equal* those inputs. `foldedOperands facts vs` is exactly that array (the input where known, the real operand otherwise). `fold_sound` is the only lemma that relates a run on `foldedOperands` to the real run, via `InterpretMonotone`.

**Why per-opcode monotonicity.** `interpretOp'_monotone` claims every opcode is monotone; `llvm.freeze` is not (`freeze poison = 0`, `freeze 5 = 5`), so `False` is derivable. As a hypothesis of `transfer_sound`, `InterpretMonotone` excludes exactly the ops on which the analysis is unsound.

## Review Focus

- **The axiom creeping back.** A proof step that reaches `interpretOp'_monotone` through a lemma (e.g. `interpretOp_monotone`) would silently restore the inconsistency. Pinned by the `#print axioms` guard in Task 3.
- **Weakened statement.** `transfer_sound`'s conclusion must stay `SoundFor … (interpretPure … concreteOperands) i` for the *real* operands, not the folded ones. Checked by Task 3's `example` in the unit test.
- **`γ` changes meaning for `ConcreteConstant` users.** Any code relying on `γ (.constant c) = {c}` breaks; there is none outside `ConstantDomain.lean` today (checked with grep in Task 2 Step 1).
- **Analysis behaviour must not change.** Only proofs and a `let`-to-`def` refactor of `transfer`. Pinned by the existing `UnitTest/DataFlowFramework/SparseConstantPropagation*.lean` `#guard_msgs` tests, which must pass unchanged.
- **`freeze` stays excluded.** Pinned by `¬ InterpretMonotone (.llvm .freeze)` in Task 1.

## File Structure

| File | Change | Responsibility |
|---|---|---|
| `Veir/Interpreter/Refinement/OpMonotone.lean` | Create | `InterpretMonotone` definition |
| `Veir/Interpreter/Refinement.lean` | Modify | re-export `OpMonotone` |
| `Veir/Analysis/DataFlow/Domains/ConstantDomain.lean` | Modify | `γ` over `RuntimeValue`; lemmas about it; `AbstractDomain AbstractConstant RuntimeValue` |
| `Veir/Analysis/DataFlow/Domains/ConstantSoundness.lean` | Modify | `SoundFor` via `γ`; delete `Refines`, `ofTrackedValue` |
| `Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean` | Modify | `foldInputs`, `foldedOperands`, `fold_sound`, one `transfer_sound` |
| `Veir/Dialects/Arith/MonotoneProofs.lean` | Create | `Arith.interpretMonotone : InterpretMonotone (.arith op)` |
| `Veir.lean` | Modify | import `MonotoneProofs` in the orphan block |
| `UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean` | Modify | freeze counterexample; axiom guard; arith instance check |
| `docs/superpowers/plans/2026-09-24-scp-postfixpoint-soundness.md` | Modify | rename `Refines` → `γ`, add `InterpretMonotone` obligation |

---

### Task 1: `InterpretMonotone`, and `freeze` does not satisfy it

**Files:**
- Create: `Veir/Interpreter/Refinement/OpMonotone.lean`
- Modify: `Veir/Interpreter/Refinement.lean`
- Test: `UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean`

**Interfaces:**
- Produces: `Veir.InterpretMonotone (opType : OpCode) : Prop` — exactly the statement of `interpretOp'_monotone` for one opcode.

- [ ] **Step 1: Write the failing test.** Append to `UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean`, and add `import Veir.Interpreter.Refinement.OpMonotone` and `import Veir.Interfaces.FoldSoundness` to its imports:

```lean
/--
`llvm.freeze` is not monotone: the interpreter maps poison to `0`, so refining a
poison operand to `5` changes the result from `0` to `5`. This is why
`transfer_sound` takes `InterpretMonotone` per opcode instead of relying on a
global axiom.
-/
example : ¬ InterpretMonotone (.llvm .freeze) := by
  intro hMono
  have hOps : #[RuntimeValue.int 8 .poison] ⊒ #[RuntimeValue.int 8 (.val 5#8)] := by
    refine ⟨rfl, fun i hi => ?_⟩
    have : i = 0 := by simp at hi; omega
    subst this
    exact RuntimeValue.int_poison_isRefinedBy 8 _
  have h := hMono default #[] _ _ #[] MemoryState.empty hOps
  simp [interpretOp', Llvm.interpretOp', Interp.isRefinedBy, Data.LLVM.Int.freeze,
    RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy, Data.LLVM.Int.cast,
    _root_.isRefinedBy, pure, Id.run] at h
```

- [ ] **Step 2: Run it to verify it fails.** Run: `lake build UnitTest.DataFlowFramework.SparseConstantPropagationSoundness`. Expected: FAIL, `unknown module prefix` / `Unknown identifier InterpretMonotone`.

- [ ] **Step 3: Implement.** Create `Veir/Interpreter/Refinement/OpMonotone.lean`:

```lean
module

public import Veir.Interpreter.Basic
public import Veir.Interpreter.Refinement.Basic

public section

/-!
# Per-opcode monotonicity of the interpreter

`InterpretMonotone opType` says interpreting `opType` on refined operands yields a
refined outcome. It is the per-opcode form of the axiom `interpretOp'_monotone`
(`Veir/Interpreter/Lemmas.lean`), which does not hold for every opcode: the
interpreter's `llvm.freeze` maps poison to `0`, so `freeze poison = 0` is not
refined by `freeze 5 = 5`. Theorems that need monotonicity take it as a
hypothesis for the opcodes they cover; it is proved for `arith` in
`Veir/Dialects/Arith/MonotoneProofs.lean`.
-/

namespace Veir

/-- Interpreting `opType` is monotone under operand refinement. -/
@[expose]
def InterpretMonotone (opType : OpCode) : Prop :=
  ∀ (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands operands' : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState),
    operands ⊒ operands' →
    Interp.isRefinedBy (α := Array RuntimeValue × MemoryState × Option ControlFlowAction)
      (fun r₁ r₂ => r₁.1 ⊒ r₂.1 ∧ r₁.2.1 = r₂.2.1 ∧
        ControlFlowAction.optionIsRefinedBy r₁.2.2 r₂.2.2)
      (interpretOp' opType properties resultTypes operands blockOperands mem)
      (interpretOp' opType properties resultTypes operands' blockOperands mem)

end Veir
```

Add `public import Veir.Interpreter.Refinement.OpMonotone` to `Veir/Interpreter/Refinement.lean`.

- [ ] **Step 4: Run the test to verify it passes.** Run: `lake build UnitTest.DataFlowFramework.SparseConstantPropagationSoundness`. Expected: success, no errors.

- [ ] **Step 5: Commit.**

```bash
git add Veir/Interpreter/Refinement/OpMonotone.lean Veir/Interpreter/Refinement.lean \
  UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean
git commit -m "feat(interpreter): per-opcode monotonicity obligation, false for llvm.freeze

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 2: `γ` over `RuntimeValue` replaces `Refines`

**Files:**
- Modify: `Veir/Analysis/DataFlow/Domains/ConstantDomain.lean`
- Modify: `Veir/Analysis/DataFlow/Domains/ConstantSoundness.lean`
- Modify: `Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean` (mechanical renames only)

**Interfaces:**
- Produces (namespace `Veir.AbstractConstant`):
  - `γ : AbstractConstant → Set RuntimeValue` (definition in Design)
  - `mem_γ_top (v) : v ∈ γ ⊤`
  - `not_mem_γ_bot (v) : v ∉ γ ⊥`
  - `mem_γ_constant {c v} : v ∈ γ (.constant c) ↔ v ⊒ .int c.bitwidth c.value`
  - `mem_γ_of_isRefinedBy {a v v'} (h : v ⊒ v') (hv' : v' ∈ γ a) : v ∈ γ a`
  - `mem_γ_ofRuntimeValue (v) : v ∈ γ (ofRuntimeValue v)`
  - `γ_monotone`, `ofFoldDecision_useOperand_sound` (restated over `RuntimeValue`)
  - `instance : AbstractDomain AbstractConstant RuntimeValue`
  - `SoundFor` unchanged in name and signature; `.ok` branch uses `actual ∈ γ a`
- Produces (namespace `Veir.SparseConstantPropagation`): `OperandsInGamma` (renamed from `OperandsRefine`, body `v ∈ AbstractConstant.γ a`)
- Deleted: `AbstractConstant.Refines`, `refines_top`, `refines_mono`, `refines_of_isRefinedBy`, `ofTrackedValue`, `γ_top_eq`, `γ_bot_eq_empty`, `γ_constant`, `γ_constant_eq_singleton`, `ofRuntimeValue_sound`, `ofFoldDecision_useConstant_sound`; `refines_ofRuntimeValue` moves to `mem_γ_ofRuntimeValue`.

- [ ] **Step 1: Confirm nothing else depends on the old names.**

Run: `grep -rn "Refines\b\|refines_top\|refines_mono\|refines_of_isRefinedBy\|refines_ofRuntimeValue\|ofTrackedValue\|γ_top_eq\|γ_bot_eq_empty\|γ_constant\|ofRuntimeValue_sound\|ofFoldDecision_useConstant_sound\|OperandsRefine" --include=*.lean Veir UnitTest`
Expected: hits only in `ConstantDomain.lean`, `ConstantSoundness.lean`, `SparseConstantPropagationAnalysis.lean`, plus `Veir/PatternRewriter/Puddle/Validity.lean` (`RefinesRoot`, unrelated — leave it).

- [ ] **Step 2: Redefine `γ` in `ConstantDomain.lean`.** Add `public import Veir.Interpreter.Refinement.Basic` and `import Veir.Interpreter.Refinement.Lemmas`. Replace the `γ` definition with the one in Design, with this docstring:

```lean
/--
Concretization: the runtime values a fact allows. This is the only relation
between facts and values in the soundness proofs.

`.constant c` allows every value that `c` refines — `c` itself, or poison of the
same width — because the analysis's facts justify *replacing* a value by `c`,
and replacing poison by `c` is a refinement.
-/
```

Restate the lemmas that survive:

```lean
theorem γ_monotone (a b : AbstractConstant) : a ≤ b → γ a ⊆ γ b := by
  intro hab v hv
  cases a <;> cases b <;> simp_all [γ, LE.le, le]

@[simp] theorem mem_γ_top (v : RuntimeValue) : v ∈ γ (.top : AbstractConstant) := trivial
theorem not_mem_γ_bot (v : RuntimeValue) : v ∉ γ (.bottom : AbstractConstant) := id
theorem mem_γ_constant {c : ConcreteConstant} {v : RuntimeValue} :
    v ∈ γ (.constant c) ↔ v ⊒ .int c.bitwidth c.value := Iff.rfl

/-- `γ` is closed under refinement: if `v'` is allowed, so is any `v` it refines. -/
theorem mem_γ_of_isRefinedBy {a : AbstractConstant} {v v' : RuntimeValue}
    (h : v ⊒ v') (hv' : v' ∈ γ a) : v ∈ γ a := by
  cases a with
  | top => trivial
  | bottom => exact hv'.elim
  | constant c => exact RuntimeValue.isRefinedBy_trans h hv'

theorem mem_γ_ofRuntimeValue (v : RuntimeValue) : v ∈ γ (ofRuntimeValue v) := by
  cases v with
  | int bitwidth value => exact RuntimeValue.isRefinedBy_refl _
  | _ => trivial
```

Keep `γ_join_left_subset`, `γ_join_right_subset`, `γ_join_overapprox` and `ofFoldDecision_useOperand_sound` (their proofs are order-only and should compile unchanged; if a `simp [γ]` breaks, replace it with `rfl`). Delete the lemmas listed as deleted. Change the instance header to `instance : AbstractDomain AbstractConstant RuntimeValue where`.

If Step 5 reports an import cycle, move `γ`, its lemmas and the instance into `ConstantSoundness.lean` instead and keep `ConstantDomain.lean` interpreter-free.

- [ ] **Step 3: Update `ConstantSoundness.lean`.** Delete `ofTrackedValue`, `Refines`, `refines_top`, `refines_mono`, `refines_of_isRefinedBy`. In `SoundFor`, replace `| some actual => Refines a actual` by `| some actual => actual ∈ γ a`, and its docstring bullet "on `.ok`, the fact must refine the result, in the sense of `Refines`" by "on `.ok`, the result must lie in `γ a`". Replace the module docstring with:

```lean
/-!
# Soundness relation for the constant domain

`SoundFor` lifts `AbstractConstant.γ` from values to interpreter outcomes. UB and
interpreter failure constrain nothing; on `.ok`, the result must lie in `γ`.
It is not a second concretization: its `.ok` branch is `γ`.
-/
```

Fix `soundFor_top` (`exact mem_γ_top actual`) and `soundFor_mono` (`exact fun h => γ_monotone a b hab h`).

- [ ] **Step 4: Mechanical renames in the analysis file.** In `SparseConstantPropagationAnalysis.lean`: rename `OperandsRefine` → `OperandsInGamma` (definition body `a.Refines v` → `v ∈ AbstractConstant.γ a`); `AbstractConstant.refines_of_isRefinedBy` → `AbstractConstant.mem_γ_of_isRefinedBy`; `AbstractConstant.refines_top` → `AbstractConstant.mem_γ_top`; `refines_ofRuntimeValue` → `AbstractConstant.mem_γ_ofRuntimeValue` (delete the local theorem); `refines_of_describesExactly` keeps its name but its conclusion becomes `v ∈ AbstractConstant.γ a`. Update docstrings that say `Refines` to say `γ`. No proof restructuring in this task.

- [ ] **Step 5: Build.** Run: `lake build Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis UnitTest.DataFlowFramework.SparseConstantPropagationSoundness UnitTest.DataFlowFramework.SparseConstantPropagation`. Expected: success. The `#guard_msgs` tests print `"ok"` unchanged.

- [ ] **Step 6: Commit.**

```bash
git add Veir/Analysis/DataFlow/Domains/ConstantDomain.lean \
  Veir/Analysis/DataFlow/Domains/ConstantSoundness.lean \
  Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean
git commit -m "refactor(dataflow): make γ over runtime values the only fact-value relation

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 3: One `transfer_sound`, one bridge to the folder, no global axiom

**Files:**
- Modify: `Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean`
- Test: `UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean`

**Interfaces:**
- Consumes: `InterpretMonotone` (Task 1); `γ`, `mem_γ_*`, `OperandsInGamma`, `SoundFor` (Task 2); `foldsTo_sound`, `ConstOperandsAgree`, `FoldDecision.SoundFor` (`Veir/Interfaces/FoldSoundness.lean`, unchanged).
- Produces (namespace `Veir.SparseConstantPropagation`):
  - `foldInputs (facts : Array AbstractConstant) : Array (Option RuntimeValue)` — used by `transfer`
  - `foldedOperands (facts : Array AbstractConstant) (vs : Array RuntimeValue) : Array RuntimeValue`
  - `fold_sound` (statement in Step 3)
  - `transfer_sound` with an added hypothesis `(hMono : InterpretMonotone (op.getOpType! irCtx.raw))` placed after `hPoison`, hypothesis `hOperands : OperandsInGamma …`, conclusion unchanged
- Deleted: `DescribesExactly`, `OperandsExact`, `refines_of_describesExactly`, `constOperandsAgree_of_operandsExact`, `transfer_sound_exact`, `refineOperands`, `refineOperands_size`, `operandsExact_refineOperands`, `isRefinedBy_refineOperands`, and the explanatory comment inside `transfer_sound` added on 2026-09-24.

- [ ] **Step 1: Write the failing tests.** Append to `UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean`:

```lean
/-- `transfer_sound` no longer depends on the global monotonicity axiom. -/
/--
info: 'Veir.SparseConstantPropagation.transfer_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SparseConstantPropagation.transfer_sound

/-- The conclusion is about the real operands, and monotonicity is per opcode. -/
example (op : OperationPtr) (irCtx : WfIRContext OpCode)
    (facts : Array AbstractConstant) (vs : Array RuntimeValue)
    (hTable : FoldTableSound (op.getOpType! irCtx.raw))
    (hPoison : PropagatesPoisonSound (op.getOpType! irCtx.raw))
    (hMono : InterpretMonotone (op.getOpType! irCtx.raw))
    (hOperands : SparseConstantPropagation.OperandsInGamma facts vs)
    (hSize : facts.size = vs.size) (hArity : vs.size = op.getNumOperands! irCtx.raw)
    (hConstSuccessors : (op.getOpType! irCtx.raw).isConstantLike = true →
      op.getSuccessors! irCtx.raw = #[]) (i : Nat) :
    ((SparseConstantPropagation.transfer op facts irCtx)[i]?.getD ⊤).SoundFor
      (interpretPure (op.getOpType! irCtx.raw)
        (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw))
        (op.getResultTypes! irCtx.raw) vs) i :=
  SparseConstantPropagation.transfer_sound op irCtx facts vs hTable hPoison hMono
    hOperands hSize hArity hConstSuccessors i
```

If the axiom list printed after Step 4 also contains `Veir.MemoryState.loadByte64._native.bv_decide.ax_5✝` (inherited from existing interpreter lemmas), paste the exact printed list into the `info:` block — the requirement is only that `Veir.interpretOp'_monotone` is absent.

- [ ] **Step 2: Run it to verify it fails.** Run: `lake build UnitTest.DataFlowFramework.SparseConstantPropagationSoundness`. Expected: FAIL — the `#print axioms` output lists `Veir.interpretOp'_monotone`, and the `example` has too many arguments.

- [ ] **Step 3: Implement the bridge.** In `SparseConstantPropagationAnalysis.lean`:

(a) Name the conversion `transfer` already does, and use it in `transfer`:

```lean
/--
What `transfer` tells the folder about the operands: `.constant c` facts become
"this operand is `c`", every other fact "unknown". This is the only place the
analysis turns facts into runtime values.
-/
def foldInputs (facts : Array AbstractConstant) : Array (Option RuntimeValue) :=
  facts.map fun
    | .constant ⟨bitwidth, value⟩ => some (.int bitwidth value)
    | _ => none
```

In `transfer`, replace the `let constantOperands := …` block by `let constantOperands := foldInputs operandLatticeElements`. (`foldInputs` must be defined above `transfer`.)

(b) Replace `refineOperands` and its three lemmas by:

```lean
/--
The operands the folder's inputs describe: `foldInputs facts` where it names a
value, the real operand elsewhere. The folder's contract (`foldsTo_sound`) is
about exactly these operands.
-/
def foldedOperands (facts : Array AbstractConstant) (vs : Array RuntimeValue) :
    Array RuntimeValue :=
  vs.mapIdx fun j v => ((foldInputs facts)[j]?.join).getD v

@[simp] theorem foldedOperands_size (facts vs) : (foldedOperands facts vs).size = vs.size := by
  simp [foldedOperands]

/-- The folder's inputs agree with `foldedOperands` (by construction). -/
theorem constOperandsAgree_foldedOperands (facts : Array AbstractConstant)
    (vs : Array RuntimeValue) (hSize : facts.size = vs.size) :
    ConstOperandsAgree (foldInputs facts) (foldedOperands facts vs)

/-- The facts still hold of `foldedOperands`. -/
theorem operandsInGamma_foldedOperands {facts vs} (h : OperandsInGamma facts vs) :
    OperandsInGamma facts (foldedOperands facts vs)

/-- The real operands refine `foldedOperands`: this is `γ` at `.constant` facts. -/
theorem isRefinedBy_foldedOperands {facts vs} (h : OperandsInGamma facts vs) :
    vs ⊒ foldedOperands facts vs
```

Prove each by `intro`/`simp [foldedOperands, foldInputs, Array.getElem?_mapIdx, Array.getElem?_map]` and a case split on `facts[j]?` — the proofs of the deleted `operandsExact_refineOperands` / `isRefinedBy_refineOperands` / `constOperandsAgree_of_operandsExact` are the templates; in the `.constant c` case `mem_γ_constant` gives `v ⊒ .int c`, and `c ∈ γ (.constant c)` is `RuntimeValue.isRefinedBy_refl`.

(c) Change `ofFoldDecision_soundFor`'s hypothesis from `OperandsExact` to `OperandsInGamma`. In its `useOperand j` case the claim is `operands[j]`, and `hDecision` gives `actual ⊒ claimed`; close with `AbstractConstant.mem_γ_of_isRefinedBy hRefines (hOperands j a claimed ha hValue)`.

(d) The bridge — the only lemma that relates the folder's run to the real run:

```lean
/--
Soundness of a fold decision for the real operands.

The folder decided on `foldInputs facts`, and its contract (`foldsTo_sound`) is
about the operands those inputs describe, `foldedOperands facts vs`. The real
operands only lie in `γ` of the facts: at a `.constant c` fact the real operand
may be poison where the folder assumed `c`. The real operands refine the folded
ones (`isRefinedBy_foldedOperands`), so by `InterpretMonotone` the real run
refines the folded run, and a fact sound for the folded run is sound for the real
one (`soundFor_of_interp_isRefinedBy`).
-/
theorem fold_sound
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (facts : Array AbstractConstant) (vs : Array RuntimeValue)
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hTable : FoldTableSound opType) (hPoison : PropagatesPoisonSound opType)
    (hMono : InterpretMonotone opType)
    (hOperands : OperandsInGamma facts vs) (hSize : facts.size = vs.size)
    (hFold : OpCode.foldsTo opType properties resultTypes (foldInputs facts) = some decisions)
    (hDecision : decisions[i]? = some decision) :
    (AbstractConstant.ofFoldDecision decision facts).SoundFor
      (interpretPure opType properties resultTypes vs) i := by
  have hFolded := foldsTo_sound opType properties resultTypes (foldedOperands facts vs)
    (foldInputs facts) decisions i decision hTable hPoison
    (constOperandsAgree_foldedOperands facts vs hSize) (by simp [foldInputs, hSize])
    hFold hDecision
  have hFact := ofFoldDecision_soundFor decision facts (foldedOperands facts vs) _ i
    (operandsInGamma_foldedOperands hOperands) hFolded
  exact soundFor_of_interp_isRefinedBy
    (hMono properties resultTypes vs (foldedOperands facts vs) #[] MemoryState.empty
      (isRefinedBy_foldedOperands hOperands))
    hFact
```

(`interpretPure` is `(interpretOp' … #[] MemoryState.empty).map (·.1)`, so `hFact`'s outcome is definitionally `target.map …` as `soundFor_of_interp_isRefinedBy` expects; if elaboration needs it, `simpa [interpretPure] using …`.)

(e) Rewrite `transfer_sound`: take the body of `transfer_sound_exact` (the case split on regions / `⊥` / constant-like / in-bounds fold), with these changes:
- hypotheses: `hOperands : OperandsInGamma abstractOperands concreteOperands`, add `hMono` after `hPoison`;
- `⊥` case: `hOperands j _ _ … : _ ∈ γ ⊥` closes by `AbstractConstant.not_mem_γ_bot _ this`;
- constant-like case: unchanged (it never uses the operand facts beyond arity);
- fold case: after rewriting `transfer` to `decisions.map (ofFoldDecision · abstractOperands)`, close the `some decision` branch with `fold_sound … hTable hPoison hMono hOperands hSize hFold hDecision`, where `hFold` is massaged exactly as the old proof does (`OperationPtr.foldsTo` unfolding and the `getProperties!` / `getResultTypes!` / `getOpType!` rewrites).

Docstring for `transfer_sound`:

```lean
/--
Local soundness of the constant-propagation transfer function.

If every operand lies in `γ` of its fact (`OperandsInGamma`), every result lies
in `γ` of the fact `transfer` produces (`SoundFor`), whenever interpretation
succeeds. Operands and results use the same relation, `γ`, so the theorem
composes along an execution.

Folding is justified by `fold_sound`, the one place where the folder's run on
`foldedOperands` is related to the real run.

Hypotheses:
* `hTable`, `hPoison` — per-opcode obligations of `foldsTo_sound`;
* `hMono` — the opcode is interpreted monotonically (`InterpretMonotone`);
  proved for `arith`, false for `llvm.freeze`;
* `hSize`, `hArity` — one fact per operand, as many operands as the op has;
* `hConstSuccessors` — a constant-like operation has no successors.
-/
```

Delete everything listed under "Deleted" above.

- [ ] **Step 4: Run the tests to verify they pass.** Run: `lake build UnitTest.DataFlowFramework.SparseConstantPropagationSoundness UnitTest.DataFlowFramework.SparseConstantPropagation`. Expected: success; `#print axioms` shows no `Veir.interpretOp'_monotone` (adjust the `info:` block per Step 1's note only for `bv_decide` axioms). Also run `grep -n "DescribesExactly\|OperandsExact\|refineOperands\|transfer_sound_exact\|interpretOp'_monotone" Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean` — expected: no output except the docstring mention of the axiom in `InterpretMonotone`'s rationale, if any.

- [ ] **Step 5: Commit.**

```bash
git add Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean \
  UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean
git commit -m "refactor(dataflow): one transfer_sound with a single folder bridge

transfer_sound now states and proves soundness with γ alone. The folder's run
on foldedOperands is related to the real run only in fold_sound, via the
per-opcode InterpretMonotone hypothesis, so the analysis no longer depends on
the inconsistent axiom interpretOp'_monotone.

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 4: `InterpretMonotone` for every `arith` opcode

**Files:**
- Create: `Veir/Dialects/Arith/MonotoneProofs.lean`
- Modify: `Veir.lean` (orphan block: `import Veir.Dialects.Arith.MonotoneProofs`)
- Test: `UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean`

**Interfaces:**
- Consumes: `InterpretMonotone` (Task 1); `Data.LLVM.Int.*_mono` lemmas (`Veir/Data/LLVM/Int/Bitblast.lean:729+`); `RuntimeValue.int_of_isRefinedBy` (`Veir/Interpreter/Refinement/Lemmas.lean:142`).
- Produces: `theorem Arith.interpretMonotone (op : Veir.Arith) : InterpretMonotone (.arith op)`.

- [ ] **Step 1: Write the failing test.** Append to the unit test file (and import `Veir.Dialects.Arith.MonotoneProofs`):

```lean
/-- Every `arith` opcode meets `transfer_sound`'s monotonicity obligation. -/
example : InterpretMonotone (.arith .addi) := Arith.interpretMonotone .addi
example : InterpretMonotone (.arith .extui) := Arith.interpretMonotone .extui
```

- [ ] **Step 2: Run it to verify it fails.** Run: `lake build UnitTest.DataFlowFramework.SparseConstantPropagationSoundness`. Expected: FAIL, unknown module / identifier.

- [ ] **Step 3: Implement.** Create `Veir/Dialects/Arith/MonotoneProofs.lean` with the same header style as `Veir/Dialects/Arith/FoldProofs.lean` (`module`; `public import Veir.Interpreter.Refinement.OpMonotone`; `import all Veir.Dialects.Arith.OpInfo`, `import all Veir.Data.LLVM.Int.Basic`, `import all Veir.Interpreter.Basic`, `import all Veir.GlobalOpInfo`, `import Veir.Data.LLVM.Int.Bitblast`, `import Veir.Interpreter.Refinement.Lemmas`). Structure the proof as:

1. Operand shape lemma: if `ops ⊒ ops'` and `ops.toList = [.int w₁ a₁, …, .int wₙ aₙ]`, then `ops'.toList = [.int w₁ b₁, …, .int wₙ bₙ]` with `aₖ ⊒ bₖ` (use `RuntimeValue.int_of_isRefinedBy`). State it for lists of length 1, 2 and 3, the arities `arith` uses.
2. Missing monotonicity lemmas for `Data.LLVM.Int` functions not yet in `Bitblast.lean`, each by `grind` or `cases <;> simp [f, Id.run]` in the style of `add_mono`: `zext_mono`, `sext_mono`, `select_mono`, `icmp_mono`, `smax_mono`, `smin_mono`, `umax_mono`, `umin_mono`, `uaddOverflowFlag_mono`, `usubOverflowFlag_mono`, `smulHigh_mono`, `umulHigh_mono`. Check `Bitblast.lean` first; reuse any that exist.
3. UB guards: `isUnsignedDivisionUB b = false → b ⊒ b' → b' = b` and the signed analogue (a non-UB divisor is a value, and a value is refined only by itself).
4. `theorem Arith.interpretMonotone (op : Veir.Arith) : InterpretMonotone (.arith op)`: `intro properties resultTypes ops ops' bo mem h; cases op`, then per case: if `ops` does not match the op's pattern the source is `.fail` and `Interp.isRefinedBy` is `True`; otherwise rewrite `ops'` with the shape lemma, split on the width check (same widths on both sides), and close the result refinement with the matching `_mono` lemma. The per-case skeleton, already checked to elaborate for `addi`:

```lean
  | addi =>
    obtain ⟨hsz, hpt⟩ := h
    rcases ops with ⟨l⟩; rcases ops' with ⟨l'⟩
    match l, l', hsz with
    | [.int bw a, .int bw' b], [v1, v2], _ =>
      -- v1 = .int bw a', v2 = .int bw' b' with a ⊒ a', b ⊒ b' (shape lemma)
      by_cases hbw : bw' = bw
      · subst hbw
        simp [interpretOp', Arith.interpretOp', bind, pure, Interp.isRefinedBy,
          RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy,
          ControlFlowAction.optionIsRefinedBy]
        -- close with Data.LLVM.Int.add_mono
      · simp [interpretOp', Arith.interpretOp', hbw, bind, Interp.isRefinedBy]
    | _, _, _ => -- source pattern fails: `.fail`, refinement is `True`
```

For the division-like ops (`divui`, `divsi`, `remui`, `remsi`, `ceildivui`, `ceildivsi`, `floordivsi`): if the source hits UB the refinement is `True`; otherwise the UB-guard lemmas show the target's divisor equals the source's, so the target takes the same branch. `constant` has no operands: both sides are identical (`Interp.isRefinedBy_refl_of_ne_fail` or direct `simp`).

Add `import Veir.Dialects.Arith.MonotoneProofs` to the `-- FIXME: These modules are otherwise orphans` block in `Veir.lean`.

- [ ] **Step 4: Run the test to verify it passes.** Run: `lake build Veir.Dialects.Arith.MonotoneProofs UnitTest.DataFlowFramework.SparseConstantPropagationSoundness`, then add `#print axioms Arith.interpretMonotone` temporarily and check it lists no `sorryAx` and no `interpretOp'_monotone`. Remove the `#print`.

- [ ] **Step 5: Commit.**

```bash
git add Veir/Dialects/Arith/MonotoneProofs.lean Veir.lean \
  UnitTest/DataFlowFramework/SparseConstantPropagationSoundness.lean
git commit -m "feat(arith): prove interpretation of every arith opcode is monotone

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 5: Full build, and keep the post-fixpoint plan consistent

**Files:**
- Modify: `docs/superpowers/plans/2026-09-24-scp-postfixpoint-soundness.md`

- [ ] **Step 1: Update the post-fixpoint plan.** Replace every `Refines` / `.Refines` / `StateRefines` meaning "fact vs value" with `γ` membership (`StateRefines F state` becomes "every defined value `v` of `x` has `v ∈ γ (F x)`"; keep the name `StateRefines` only if renaming it would ripple, and say so in one sentence). Add `InterpretMonotone opType` to Design note 3's obligation table ("per opcode; `arith` proved in `Veir/Dialects/Arith/MonotoneProofs.lean`; false for `llvm.freeze`"), and remove `Veir.interpretOp'_monotone` from its Global Constraints' allowed-axiom list.

- [ ] **Step 2: Full build and tests.** Run: `lake build && lake test` (in the background if the tool timeout applies). Expected: success. Then run the orphan check with a Python ≥ 3.11 interpreter: `python3.11 Tools/check-orphan-modules` (or whichever `python3.1[1-9]` exists). Expected: no orphans.

- [ ] **Step 3: Commit.**

```bash
git add docs/superpowers/plans/2026-09-24-scp-postfixpoint-soundness.md
git commit -m "docs(dataflow): align post-fixpoint plan with γ and InterpretMonotone

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```
