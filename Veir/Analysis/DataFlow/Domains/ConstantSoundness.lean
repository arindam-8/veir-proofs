module

public import Veir.Analysis.DataFlow.Domains.ConstantDomain
public import Veir.Interpreter.Interp

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
`a.SoundFor outcome i` says the abstract fact `a` does not over-claim about
result `i` of an operation whose interpretation produced `outcome`.

Only a successful interpretation constrains the fact:
* `.ub` means the source program's behaviour is unconstrained, so every fact is
  sound — this is what makes a UB-to-poison fold statable;
* `.fail` means the interpreter cannot model the operation, which likewise
  constrains nothing;
* a result outside the tracked integer domain constrains nothing.

Note that `.ub` and `.fail` are justified differently. `.ub` is a semantic claim
about the source program. `.fail` is a statement about VeIR's own coverage, so
soundness is relative to the operations the interpreter models.
-/
def SoundFor (a : AbstractConstant) (outcome : Interp (Array RuntimeValue)) (i : Nat) : Prop :=
  match outcome with
  | .ok results =>
      match results[i]? >>= ofTrackedValue with
      | some c => c ∈ γ a
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
      show match results[i]? >>= ofTrackedValue with
        | some c => c ∈ γ (⊤ : AbstractConstant)
        | none => True
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

/-- A sound fact stays sound when weakened up the lattice. -/
theorem soundFor_mono (a b : AbstractConstant) (outcome : Interp (Array RuntimeValue)) (i : Nat)
    (hab : a ≤ b) : SoundFor a outcome i → SoundFor b outcome i := by
  cases outcome with
  | fail => intro _; trivial
  | ub => intro _; trivial
  | ok results =>
      show (match results[i]? >>= ofTrackedValue with
              | some c => c ∈ γ a
              | none => True) →
           (match results[i]? >>= ofTrackedValue with
              | some c => c ∈ γ b
              | none => True)
      cases results[i]? >>= ofTrackedValue with
      | none => intro _; trivial
      | some c => exact fun hc => γ_monotone a b hab hc

end AbstractConstant

end Veir
