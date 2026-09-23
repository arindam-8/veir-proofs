module

public import Veir.Analysis.DataFlow.Domains.ConstantDomain
public import Veir.Interpreter.Interp
public import Veir.Interpreter.Refinement.Basic

import Veir.Interpreter.Refinement.Lemmas
public import Veir.Interpreter.Refinement.Basic

import Veir.Interpreter.Refinement.Lemmas

/-!
# Soundness relation for the constant domain

`AbstractConstant.γ` concretizes to bare `ConcreteConstant` values, which cannot
describe an execution that triggered undefined behaviour or that the interpreter
could not model. Folding turns both of those outcomes into ordinary values (see
`foldByEvaluation` in `Veir/Interfaces/FoldInterfaces.lean` and the `.ub` arm of
`ValuePtr.constantValue` in `Veir/Interfaces/ConstantLikeInterfaces.lean`), so a
soundness statement phrased over bare values discharges vacuously on exactly the
cases where the analysis makes its strongest claims.

`SoundFor` widens the concrete side to an interpreter outcome. It is a soundness
relation, not a concretization: its right-hand side is an `Interp` outcome rather
than a value, so it has no set-valued reading. The `.ok` branch delegates to `γ`
unchanged.
-/

public section

namespace Veir

namespace AbstractConstant

/-- The constant this domain tracks for a runtime value, if it tracks one. -/
def ofTrackedValue : RuntimeValue → Option ConcreteConstant
  | .int bitwidth value => some ⟨bitwidth, value⟩
  | _ => none

/--
`a.SoundForValue actual` says the abstract fact `a` is a sound claim about the
runtime value `actual`, read as a refinement: `⊤` claims nothing, `⊥` claims the
value does not exist, and `.constant c` claims that the integer `c` refines
`actual` (`actual ⊒ .int c`). Since a poison integer is refined by any integer of
its width, a wholly poison result accepts every constant claim of that width.

The same relation is used for operands and results, which is what lets local
transfer soundness compose along an execution.
-/
@[expose]
def SoundForValue (a : AbstractConstant) (actual : RuntimeValue) : Prop :=
  match a with
  | .top => True
  | .bottom => False
  | .constant c => actual ⊒ .int c.bitwidth c.value

/--
`a.SoundFor outcome i` says the abstract fact `a` does not over-claim about
result `i` of an operation whose interpretation produced `outcome`.

Only a successful interpretation constrains the fact:
* `.ub` means the source program's behaviour is unconstrained, so every fact is
  sound — this is what makes a UB-to-poison fold statable;
* `.fail` means the interpreter cannot model the operation, which likewise
  constrains nothing;
* on `.ok`, the fact must be sound for the result in the refinement sense of
  `SoundForValue`.

Note that `.ub` and `.fail` are justified differently. `.ub` is a semantic claim
about the source program. `.fail` is a statement about VeIR's own coverage, so
soundness is relative to the operations the interpreter models.
-/
@[expose]
def SoundFor (a : AbstractConstant) (outcome : Interp (Array RuntimeValue)) (i : Nat) : Prop :=
  match outcome with
  | .ok results =>
      match results[i]? with
      | some actual => SoundForValue a actual
      | none => True
  | .ub => True
  | .fail => True

@[simp]
theorem soundForValue_top (actual : RuntimeValue) : SoundForValue ⊤ actual := by
  trivial

/-- A sound fact stays sound when weakened up the lattice. -/
theorem soundForValue_mono (a b : AbstractConstant) (actual : RuntimeValue) (hab : a ≤ b) :
    SoundForValue a actual → SoundForValue b actual := by
  intro h
  cases b with
  | top => trivial
  | bottom =>
    -- only `⊥` is below `⊥`
    have : a = .bottom := le_antisymm a .bottom hab (bot_le a)
    subst this
    exact h
  | constant d =>
    cases a with
    | top => exact absurd (le_antisymm _ _ hab (le_top _)) (by simp)
    | bottom => exact h.elim
    | constant c =>
      -- `γ (.constant c) ⊆ γ (.constant d)` forces `c = d`
      have hcd : c = d := γ_monotone _ _ hab (show c ∈ γ (.constant c) from rfl)
      subst hcd
      exact h

/-- Soundness is preserved when the actual value is itself refined away from. -/
theorem soundForValue_of_isRefinedBy {a : AbstractConstant} {v v' : RuntimeValue}
    (hRefines : v ⊒ v') (h : SoundForValue a v') : SoundForValue a v := by
  cases a with
  | top => trivial
  | bottom => exact h.elim
  | constant c => exact RuntimeValue.isRefinedBy_trans hRefines h

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
      | some actual => exact soundForValue_top actual

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
      | some actual => exact soundForValue_mono a b actual hab

end AbstractConstant

end Veir
