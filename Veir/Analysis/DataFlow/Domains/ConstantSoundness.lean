module

public import Veir.Analysis.DataFlow.Domains.ConstantDomain
public import Veir.Interpreter.Interp
public import Veir.Interpreter.Refinement.Basic

import Veir.Interpreter.Refinement.Lemmas

/-!
# Soundness relation for the constant domain

`SoundFor` lifts `AbstractConstant.γ` from runtime values to interpreter
outcomes. UB and interpreter failure constrain nothing; on `.ok`, the result
must lie in `γ`. It is not a second relation between facts and values: its
`.ok` branch is `γ`.
-/

public section

namespace Veir

namespace AbstractConstant

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
