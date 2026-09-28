module

public import Veir.Analysis.DataFlow.Domains.ConstantDomain
public import Veir.Interpreter.Interp
public import Veir.Interpreter.Refinement.Basic

import Veir.Interpreter.Refinement.Lemmas
import all Veir.Data.Refinement

public section

namespace Veir

/-!
# Soundness relation for the constant domain

`SoundFor` lifts `AbstractConstant.γ` from runtime values to interpreter
outcomes. UB and interpreter failure constrain nothing; on `.ok`, the result
must lie in `γ`. It is not a second relation between facts and values: its
`.ok` branch is `γ`.

The lemmas here connect `γ`, which uses equality only, to the refinement the
folder's contract is stated in: `weaken` turns a fact whose values are only
refined into one that allows them (`mem_γ_weaken_of_isRefinedBy`).
-/

namespace AbstractConstant

open ConcreteConstant

/-- A runtime value lies in `γ` of its own abstraction. -/
theorem mem_γ_ofRuntimeValue (v : RuntimeValue) : v ∈ γ (ofRuntimeValue v) := by
  cases v <;> first | rfl | trivial

/-- The values refining an integer are the integer itself and poison of its width. -/
theorem isRefinedBy_int_iff {w : Nat} {x : Data.LLVM.Int w} {v : RuntimeValue} :
    v ⊒ .int w x ↔ v = .int w x ∨ v = .int w .poison := by
  constructor
  · intro h
    cases v with
    | int bw s =>
      obtain ⟨rfl, hs⟩ := h
      simp only [Data.LLVM.Int.cast_self] at hs
      cases s <;> cases x <;> simp_all [_root_.isRefinedBy]
    | _ => exact h.elim
  · rintro (rfl | rfl)
    · exact RuntimeValue.isRefinedBy_refl _
    · exact ⟨rfl, by simp [Data.LLVM.Int.cast_self, _root_.isRefinedBy]⟩

/-- Only poison refines poison. -/
theorem eq_poison_of_isRefinedBy_poison {w : Nat} {v : RuntimeValue}
    (h : v ⊒ .int w .poison) : v = .int w .poison := by
  rcases isRefinedBy_int_iff.mp h with h | h <;> exact h

/--
Weakening makes `γ` closed under refinement: if `v'` is allowed by `a`, any `v`
that `v'` refines is allowed by `a.weaken`.
-/
theorem mem_γ_weaken_of_isRefinedBy {a : AbstractConstant} {v v' : RuntimeValue}
    (h : v ⊒ v') (hv' : v' ∈ γ a) : v ∈ γ a.weaken := by
  cases a with
  | top => trivial
  | bottom => exact hv'.elim
  | exact c =>
    obtain ⟨w, x⟩ := c
    rw [mem_γ_exact.mp hv'] at h
    cases x with
    | poison => exact eq_poison_of_isRefinedBy_poison h
    | val bits => exact isRefinedBy_int_iff.mp h
  | upTo c =>
    rcases hv' with rfl | rfl
    · exact isRefinedBy_int_iff.mp h
    · exact Or.inr (eq_poison_of_isRefinedBy_poison h)

/-- A value allowed by `upTo c` is allowed by one of the exact cases it covers. -/
theorem exists_exactCase {a : AbstractConstant} {v : RuntimeValue} (hv : v ∈ γ a) :
    ∃ a' ∈ exactCases a, v ∈ γ a' := by
  cases a with
  | upTo c =>
    rcases hv with rfl | rfl
    · exact ⟨.exact c, by simp [exactCases], rfl⟩
    · exact ⟨.exact (poison c.bitwidth), by simp [exactCases], rfl⟩
  | _ => exact ⟨_, by simp [exactCases], hv⟩

/--
`a.SoundFor outcome i` says the abstract fact `a` does not over-claim about
result `i` of an operation whose interpretation produced `outcome`.

Only a successful interpretation constrains the fact:
* `.ub` means the source program's behaviour is unconstrained, so every fact is
  sound — this is what makes a UB-to-poison fold statable;
* `.fail` means the interpreter cannot model the operation, which likewise
  constrains nothing;
* on `.ok`, the result must lie in `γ a`.

Note that `.ub` and `.fail` are justified differently. `.ub` is a semantic claim
about the source program. `.fail` is a statement about VeIR's own coverage, so
soundness is relative to the operations the interpreter models.
-/
@[expose]
def SoundFor (a : AbstractConstant) (outcome : Interp (Array RuntimeValue)) (i : Nat) : Prop :=
  match outcome with
  | .ok results =>
      match results[i]? with
      | some actual => actual ∈ γ a
      | none => True
  | .ub => True
  | .fail => True

@[simp]
theorem soundFor_top (outcome : Interp (Array RuntimeValue)) (i : Nat) :
    SoundFor ⊤ outcome i := by
  cases outcome with
  | fail => trivial
  | ub => trivial
  | ok results =>
      simp only [SoundFor]
      cases results[i]? with
      | none => trivial
      | some actual => exact mem_γ_top actual

@[simp]
theorem soundFor_ub (a : AbstractConstant) (i : Nat) :
    SoundFor a .ub i := by
  unfold SoundFor; trivial

@[simp]
theorem soundFor_fail (a : AbstractConstant) (i : Nat) :
    SoundFor a .fail i := by
  unfold SoundFor; trivial

/-- A sound fact stays sound when weakened up the lattice. -/
theorem soundFor_mono (a b : AbstractConstant) (outcome : Interp (Array RuntimeValue)) (i : Nat)
    (hab : a ≤ b) : SoundFor a outcome i → SoundFor b outcome i := by
  cases outcome with
  | fail => intro _; trivial
  | ub => intro _; trivial
  | ok results =>
      simp only [SoundFor]
      cases results[i]? with
      | none => intro _; trivial
      | some actual => exact fun h => γ_monotone a b hab h

end AbstractConstant

end Veir
