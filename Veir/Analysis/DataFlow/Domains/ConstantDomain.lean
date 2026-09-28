module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Analysis.DataFlow.Domains.AbstractDomain
public import Veir.FoldDecision
public import Veir.Interpreter.Interp
public import Veir.Interpreter.Refinement.Basic

import Veir.Interpreter.Refinement.Lemmas

public section

namespace Veir

/-!
# Constant domain

Instantiation of `AbstractDomain` with a constant propagation lattice whose
elements are `bottom`, a constant, or `top`.

`γ` concretizes a fact to the runtime values it allows, and `SoundFor` lifts `γ`
from runtime values to interpreter outcomes. UB and interpreter failure
constrain nothing; on `.ok`, the result must lie in `γ`. `SoundFor` is not a
second relation between facts and values: its `.ok` branch is `γ`.
-/

/-- Concrete integer values tracked by the constant domain. -/
structure ConcreteConstant where
  bitwidth : Nat
  value : Data.LLVM.Int bitwidth
deriving BEq, DecidableEq

/-- Abstract values used by sparse constant propagation. -/
inductive AbstractConstant where
  | top
  | bottom
  | constant (value : ConcreteConstant)
deriving BEq, DecidableEq, TypeName

instance : ToString AbstractConstant where
  toString
    | .top => "top"
    | .bottom => "bottom"
    | .constant constant => s!"const({constant.value} : i{constant.bitwidth})"

namespace AbstractConstant

/-- Defines the ordering of abstract values in the constant domain. -/
def le (x y : AbstractConstant) : Prop :=
  match x, y with
  | .bottom, _ => True
  | _, .top => True
  | .constant c, .constant d => c = d
  | _, _ => False

instance : LE AbstractConstant where
  le := le

theorem le_def (a b : AbstractConstant) : (a ≤ b) ↔ le a b := Iff.rfl

@[simp, grind .]
theorem le_top (a : AbstractConstant) : a ≤ .top := by
  cases a <;> trivial

@[simp, grind .]
theorem bot_le (a : AbstractConstant) : .bottom ≤ a := by
  cases a <;> trivial

instance : BoundedOrder AbstractConstant where
  top := .top
  bot := .bottom
  le_top := le_top
  bot_le := bot_le

def ofRuntimeValue : RuntimeValue → AbstractConstant
  | .int bitwidth value => .constant ⟨bitwidth, value⟩
  | _ => ⊤

def ofFoldDecision
    (result : FoldDecision) (operands : Array AbstractConstant) : AbstractConstant :=
  match result with
  | .useOperand index => operands[index]?.getD ⊤
  | .useConstant value => .ofRuntimeValue value

/--
Concretization: the runtime values a fact allows. This is the only relation
between facts and runtime values in the soundness proofs.

`.constant c` allows every value that `c` refines: `c` itself, or poison of the
same width. The analysis's facts justify *replacing* a value by `c`, and
replacing poison by `c` is a refinement.
-/
@[expose] def γ (absVal : AbstractConstant) : Set RuntimeValue :=
  match absVal with
  | .top => fun _ => True
  | .bottom => fun _ => False
  | .constant c => fun v => v ⊒ .int c.bitwidth c.value

def join (lhs rhs : AbstractConstant) : AbstractConstant :=
  match lhs, rhs with
  | .bottom, y => y
  | x, .bottom => x
  | .top, _ => ⊤
  | _, .top => ⊤
  | .constant c, .constant d => if c = d then .constant c else ⊤

instance : Join AbstractConstant where
  join := join

theorem γ_monotone (a b : AbstractConstant) : a ≤ b → γ a ⊆ γ b := by
  intro hab v hv
  cases a <;> cases b <;> simp only [LE.le, le] at hab
  all_goals first | trivial | exact hab.elim | exact hv.elim | (subst hab; exact hv)

@[simp]
theorem mem_γ_top (v : RuntimeValue) : v ∈ γ (.top : AbstractConstant) := trivial

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

/-- A runtime value lies in `γ` of its own abstraction. -/
theorem mem_γ_ofRuntimeValue (v : RuntimeValue) : v ∈ γ (ofRuntimeValue v) := by
  cases v with
  | int bitwidth value =>
    show RuntimeValue.int bitwidth value ⊒ RuntimeValue.int bitwidth value
    exact RuntimeValue.isRefinedBy_refl _
  | _ => trivial

@[simp, grind .]
theorem le_refl (a : AbstractConstant) : a ≤ a := by
  cases a <;> simp [le, le_def]

@[grind →]
theorem le_trans (a b c : AbstractConstant) : a ≤ b → b ≤ c → a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all [le, le_def]

@[grind →]
theorem le_antisymm (a b : AbstractConstant) : a ≤ b → b ≤ a → a = b := by
  cases a <;> cases b <;> simp_all [le, le_def]

@[simp, grind .]
theorem le_join_left (a b : AbstractConstant) : a ≤ a ⊔ b := by
  cases a <;> cases b <;> try simp [le, le_def, join]
  case constant.constant c d =>
    by_cases h : c = d <;> simp [h]

@[simp, grind .]
theorem le_join_right (a b : AbstractConstant) : b ≤ a ⊔ b := by
  cases a <;> cases b <;> try simp [le, le_def, join]
  case constant.constant c d =>
    by_cases h : c = d <;> simp [h]

theorem join_le (a b c : AbstractConstant) : a ≤ c → b ≤ c → a ⊔ b ≤ c := by
  intros
  cases a <;> cases b <;> cases c <;>
    simp [join] <;> (try split) <;> simp_all [le, le_def]

instance : JoinSemilattice AbstractConstant where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  join := join
  le_join_left := le_join_left
  le_join_right := le_join_right
  join_le := join_le

@[simp]
theorem γ_join_left_subset (a b : AbstractConstant) : γ a ⊆ γ (a ⊔ b) := by
  exact γ_monotone a (a ⊔ b) (le_join_left a b)

@[simp]
theorem γ_join_right_subset (a b : AbstractConstant) : γ b ⊆ γ (a ⊔ b) := by
  exact γ_monotone b (a ⊔ b) (le_join_right a b)

/-- The join is a sound over-approximation of either input fact. -/
theorem γ_join_overapprox (a b : AbstractConstant) :
    (∀ x, x ∈ γ a → x ∈ γ (a ⊔ b)) ∧ (∀ x, x ∈ γ b → x ∈ γ (a ⊔ b)) := by
  constructor
  · intro x hx
    exact γ_join_left_subset a b hx
  · intro x hx
    exact γ_join_right_subset a b hx

theorem join_self (a : AbstractConstant) : a ⊔ a = a := by
  apply le_antisymm
  · exact join_le a a a (le_refl a) (le_refl a)
  · exact le_join_left a a

theorem join_comm (a b : AbstractConstant) : a ⊔ b = b ⊔ a := by
  apply le_antisymm
  · exact join_le a b (b ⊔ a) (le_join_right b a) (le_join_left b a)
  · exact join_le b a (a ⊔ b) (le_join_right a b) (le_join_left a b)

theorem join_assoc (a b c : AbstractConstant) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) := by
  apply le_antisymm
  · exact join_le (a ⊔ b) c (a ⊔ (b ⊔ c))
      (join_le a b (a ⊔ (b ⊔ c))
        (le_join_left a (b ⊔ c))
        (le_trans b (b ⊔ c) (a ⊔ (b ⊔ c))
          (le_join_left b c) (le_join_right a (b ⊔ c))))
      (le_trans c (b ⊔ c) (a ⊔ (b ⊔ c))
        (le_join_right b c) (le_join_right a (b ⊔ c)))
  · exact join_le a (b ⊔ c) ((a ⊔ b) ⊔ c)
      (le_trans a (a ⊔ b) ((a ⊔ b) ⊔ c)
        (le_join_left a b) (le_join_left (a ⊔ b) c))
      (join_le b c ((a ⊔ b) ⊔ c)
        (le_trans b (a ⊔ b) ((a ⊔ b) ⊔ c)
          (le_join_right a b) (le_join_left (a ⊔ b) c))
        (le_join_right (a ⊔ b) c))

instance : AbstractDomain AbstractConstant RuntimeValue where
  toJoinSemilattice := inferInstance
  toBoundedOrder := inferInstance
  γ := γ
  γ_top := rfl
  γ_bot := rfl
  γ_monotone := γ_monotone

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
