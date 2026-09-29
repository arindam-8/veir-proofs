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

/-- Outside bytes, the values that refine `v` are `v` and its poison. -/
theorem RuntimeValue.isRefinedBy_iff {v x : RuntimeValue} (hv : v.isByte = false) :
    x ⊒ v ↔ x = v ∨ x = v.poisonOf := by
  constructor
  · intro h
    cases v with
    | byte => simp [RuntimeValue.isByte] at hv
    | int w t =>
      cases x with
      | int bw s =>
        obtain ⟨rfl, hs⟩ := h
        simp only [Data.LLVM.Int.cast_self] at hs
        cases s <;> cases t <;> simp_all [_root_.isRefinedBy, RuntimeValue.poisonOf]
      | _ => exact h.elim
    | addr t =>
      cases x with
      | addr s =>
        cases s <;> cases t <;>
          simp_all [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy, RuntimeValue.poisonOf]
      | _ => exact h.elim
    | reg t =>
      cases x with
      | reg s => exact Or.inl (congrArg _ h)
      | _ => exact h.elim
    | felt ft t =>
      cases x with
      | felt fs s => obtain ⟨rfl, rfl⟩ := h; exact Or.inl rfl
      | _ => exact h.elim
    | float ty t =>
      cases x with
      | float ty' s =>
        simp only [RuntimeValue.isRefinedBy] at h
        split at h
        · next hty => subst hty; subst h; exact Or.inl rfl
        · exact h.elim
      | _ => exact h.elim
  · rintro (rfl | rfl)
    · exact RuntimeValue.isRefinedBy_refl _
    · cases v with
      | int w t => exact ⟨rfl, by simp [Data.LLVM.Int.cast_self, _root_.isRefinedBy]⟩
      | addr t => show Data.LLVM.Ptr.poison ⊒ t; trivial
      | byte => simp [RuntimeValue.isByte] at hv
      | _ => exact RuntimeValue.isRefinedBy_refl _

namespace AbstractConstant

/--
Weakening makes `γ` closed under refinement: if `x'` is allowed by `a`, any `x`
that `x'` refines is allowed by `a.weaken`.
-/
theorem mem_γ_weaken_of_isRefinedBy {a : AbstractConstant} {x x' : RuntimeValue}
    (h : x ⊒ x') (hx' : x' ∈ γ a) : x ∈ γ a.weaken := by
  cases a with
  | top => trivial
  | bottom => exact hx'.elim
  | exact v =>
    rw [mem_γ_exact.mp hx'] at h
    simp only [weaken]
    split
    · trivial
    · next hb =>
      have hx := (RuntimeValue.isRefinedBy_iff (by simpa using hb)).mp h
      split
      · next hp => rw [hp] at hx; rcases hx with rfl | rfl <;> rfl
      · exact hx
  | upTo v =>
    simp only [weaken]
    split
    · trivial
    · next hb =>
      have hb : v.isByte = false := by simpa using hb
      rcases hx' with rfl | rfl
      · exact (RuntimeValue.isRefinedBy_iff hb).mp h
      · have hx := (RuntimeValue.isRefinedBy_iff (by simpa using hb)).mp h
        rw [RuntimeValue.poisonOf_poisonOf] at hx
        exact Or.inr (by rcases hx with hx | hx <;> exact hx)

/-- A value allowed by `upTo v` is allowed by one of the exact cases it covers. -/
theorem exists_exactCase {a : AbstractConstant} {x : RuntimeValue} (hx : x ∈ γ a) :
    ∃ a' ∈ exactCases a, x ∈ γ a' := by
  cases a with
  | upTo v =>
    rcases hx with rfl | rfl
    · exact ⟨.exact x, by simp [exactCases], rfl⟩
    · exact ⟨.exact v.poisonOf, by simp [exactCases], rfl⟩
  | _ => exact ⟨_, by simp [exactCases], hx⟩

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
