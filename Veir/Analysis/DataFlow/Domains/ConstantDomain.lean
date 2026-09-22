module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Analysis.DataFlow.Domains.AbstractDomain
public import Veir.FoldDecision

public section

namespace Veir

/-!
# Constant domain

Instantiation of `AbstractDomain` with a constant propagation lattice whose
elements are `bottom`, a constant, or `top`.
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
When a fold decision is applied to concrete operands, this is the concrete
result it is claiming to produce.  Non-integer runtime constants are outside
the tracked constant domain, so they impose no constraint here.
-/
def foldDecisionRealizes
    (result : FoldDecision) (operands : Array ConcreteConstant)
    (output : ConcreteConstant) : Prop :=
  match result with
  | .useOperand index => operands[index]? = some output
  | .useConstant (.int bitwidth value) => output = ⟨bitwidth, value⟩
  | .useConstant _ => True

@[expose] def γ (absVal : AbstractConstant) : Set ConcreteConstant :=
  match absVal with
  | .top => fun _ => True
  | .bottom => fun _ => False
  | .constant a => fun concVal => concVal = a

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
  intro hab x hx
  cases a <;> cases b <;> simp [γ] at hab hx ⊢
  all_goals first | trivial | exact hx.trans hab

@[simp]
theorem γ_top_eq (x : ConcreteConstant) : x ∈ γ (.top : AbstractConstant) := by
  change (γ (.top : AbstractConstant)) x
  simp [γ]

@[simp]
theorem γ_bot_eq_empty : γ (.bottom : AbstractConstant) = (fun _ : ConcreteConstant => False) := by
  ext x
  simp [γ]

@[simp]
theorem γ_constant (c : ConcreteConstant) : γ (.constant c) = (fun x => x = c) := by
  ext x
  simp [γ]

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

/-- A concrete runtime integer value is represented exactly by the matching constant abstract value. -/
theorem ofRuntimeValue_sound (v : RuntimeValue) :
    match v with
    | .int bitwidth value =>
        (⟨bitwidth, value⟩ : ConcreteConstant) ∈ γ (AbstractConstant.ofRuntimeValue v)
    | _ => True := by
  cases v with
  | int bitwidth value =>
      change (⟨bitwidth, value⟩ : ConcreteConstant) = ⟨bitwidth, value⟩
      rfl
  | byte bitwidth value => trivial
  | float type value => trivial
  | addr value => trivial
  | reg value => trivial
  | felt fieldType value => trivial

/-- The constant case of the concretization map is exactly the singleton set at that value. -/
theorem γ_constant_eq_singleton (c : ConcreteConstant) :
    γ (.constant c) = (fun x => x = c) := by
  ext x
  simp [γ]

/-- A fold decision that returns a concrete constant is sound with respect to the abstract concretization. -/
theorem ofFoldDecision_useConstant_sound
    (v : RuntimeValue) (operands : Array AbstractConstant) :
    match v with
    | .int bitwidth value =>
        (⟨bitwidth, value⟩ : ConcreteConstant) ∈
          γ (AbstractConstant.ofFoldDecision (.useConstant v) operands)
    | _ => True := by
  cases v with
  | int bitwidth value =>
      change (⟨bitwidth, value⟩ : ConcreteConstant) = ⟨bitwidth, value⟩
      rfl
  | byte bitwidth value => trivial
  | float type value => trivial
  | addr value => trivial
  | reg value => trivial
  | felt fieldType value => trivial

/-- A fold decision that reuses an operand is sound when that operand is itself sound. -/
theorem ofFoldDecision_useOperand_sound
    (operands : Array AbstractConstant) (index : Nat) :
    match operands[index]? with
    | some a =>
        γ a = γ (AbstractConstant.ofFoldDecision (.useOperand index) operands)
    | none =>
        γ (⊤ : AbstractConstant) = γ (AbstractConstant.ofFoldDecision (.useOperand index) operands) := by
  cases h : operands[index]? with
  | none =>
      simp [AbstractConstant.ofFoldDecision, h, γ]
  | some a =>
      simp [AbstractConstant.ofFoldDecision, h, γ]

/--
The abstract result of a fold contains every concrete result justified by the
fold decision, provided the selected concrete operand is represented by its
abstract operand fact.
-/
theorem ofFoldDecision_realizes_sound
    (result : FoldDecision) (abstractOperands : Array AbstractConstant)
    (concreteOperands : Array ConcreteConstant) (output : ConcreteConstant)
    (hOperands : ∀ (index : Nat) (c : ConcreteConstant) (a : AbstractConstant),
      concreteOperands[index]? = some c →
      abstractOperands[index]? = some a → c ∈ γ a)
    (hRealizes : foldDecisionRealizes result concreteOperands output) :
    output ∈ γ (ofFoldDecision result abstractOperands) := by
  cases result with
  | useOperand index =>
      cases hAbstract : abstractOperands[index]? with
      | none =>
          have hTop : ofFoldDecision (.useOperand index) abstractOperands = ⊤ := by
            simp [ofFoldDecision, hAbstract]
          rw [hTop]
          exact γ_top_eq output
      | some a =>
          have hConcrete : concreteOperands[index]? = some output := hRealizes
          have hMem : output ∈ γ a := hOperands index output a hConcrete hAbstract
          simpa [ofFoldDecision, hAbstract] using hMem
  | useConstant value =>
      cases value with
      | int bitwidth value =>
          change output = ⟨bitwidth, value⟩
          exact hRealizes
      | byte bitwidth value => trivial
      | float type value => trivial
      | addr value => trivial
      | reg value => trivial
      | felt fieldType value => trivial

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

instance : AbstractDomain AbstractConstant ConcreteConstant where
  toJoinSemilattice := inferInstance
  toBoundedOrder := inferInstance
  γ := γ
  γ_top := rfl
  γ_bot := rfl
  γ_monotone := γ_monotone

end AbstractConstant

end Veir
