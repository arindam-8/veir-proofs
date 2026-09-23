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
`a.SoundForValue actual` says the abstract fact `a` is a sound claim about the
runtime value `actual`, read as a refinement: a wholly poison value may be
replaced by anything, so it accepts every fact; otherwise, a tracked value must
lie in `γ a`, and an untracked one constrains nothing.
-/
@[expose]
def SoundForValue (a : AbstractConstant) (actual : RuntimeValue) : Prop :=
  actual.isPoison = true ∨
    match ofTrackedValue actual with
    | some c => c ∈ γ a
    | none => True

/--
`a.SoundFor outcome i` says the abstract fact `a` does not over-claim about
result `i` of an operation whose interpretation produced `outcome`.

Only a successful interpretation constrains the fact:
* `.ub` means the source program's behaviour is unconstrained, so every fact is
  sound — this is what makes a UB-to-poison fold statable;
* `.fail` means the interpreter cannot model the operation, which likewise
  constrains nothing;
* on `.ok`, the fact must be sound for the result in the refinement sense of
  `SoundForValue`: poison results accept any fact.

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
  right
  cases ofTrackedValue actual with
  | none => trivial
  | some c => exact γ_top_eq c

/-- A sound fact stays sound when weakened up the lattice. -/
theorem soundForValue_mono (a b : AbstractConstant) (actual : RuntimeValue) (hab : a ≤ b) :
    SoundForValue a actual → SoundForValue b actual := by
  rintro (hPoison | hTracked)
  · exact Or.inl hPoison
  · right
    revert hTracked
    cases ofTrackedValue actual with
    | none => intro _; trivial
    | some c => exact fun hc => γ_monotone a b hab hc

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
