module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Analysis.DataFlow.Domains.AbstractDomain
public import Veir.FoldDecision

public section

namespace Veir

/-!
# Constant domain

Instantiation of `AbstractDomain` with a constant propagation lattice whose
elements are `bottom`, `exact c` (the value is `c`), `upTo c` (the value is `c`
or poison of the same width), or `top`.

`γ` concretizes a fact to the runtime values it allows, using equality only.
The relation to interpreter outcomes and refinement lives in
`Veir/Analysis/DataFlow/Domains/ConstantSoundness.lean`.
-/

/-- Concrete integer values tracked by the constant domain. -/
structure ConcreteConstant where
  bitwidth : Nat
  value : Data.LLVM.Int bitwidth
deriving BEq, DecidableEq

namespace ConcreteConstant

/-- Poison of width `w`. -/
@[expose] def poison (w : Nat) : ConcreteConstant := ⟨w, .poison⟩

/--
`c ≼ d`: `c` is `d`, or poison of `d`'s width. Every value `d` allows is
allowed by `c` too, so `upTo c` sits below `upTo d`.
-/
@[expose] def Below (c d : ConcreteConstant) : Prop := c = d ∨ c = poison d.bitwidth

@[inherit_doc] infix:50 " ≼ " => Below

instance (c d : ConcreteConstant) : Decidable (c ≼ d) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem below_refl (c : ConcreteConstant) : c ≼ c := Or.inl rfl

theorem below_trans {c d e : ConcreteConstant} (hcd : c ≼ d) (hde : d ≼ e) : c ≼ e := by
  rcases hde with rfl | rfl
  · exact hcd
  · rcases hcd with rfl | rfl <;> exact Or.inr rfl

theorem below_antisymm {c d : ConcreteConstant} (hcd : c ≼ d) (hdc : d ≼ c) : c = d := by
  rcases hcd with rfl | rfl
  · rfl
  · rcases hdc with h | h <;> exact h.symm

/-- Two constants below a common one are comparable. -/
theorem below_total_of_below {c d e : ConcreteConstant} (hce : c ≼ e) (hde : d ≼ e) :
    c ≼ d ∨ d ≼ c := by
  rcases hce with rfl | rfl <;> rcases hde with rfl | rfl <;>
    first
      | exact Or.inl (Or.inl rfl)
      | exact Or.inl (Or.inr rfl)
      | exact Or.inr (Or.inr rfl)

end ConcreteConstant

/-- Abstract values used by sparse constant propagation. -/
inductive AbstractConstant where
  | top
  | bottom
  /-- The value is exactly `value`. -/
  | exact (value : ConcreteConstant)
  /-- The value is `value`, or poison of the same width. -/
  | upTo (value : ConcreteConstant)
deriving BEq, DecidableEq, TypeName

instance : ToString AbstractConstant where
  toString
    | .top => "top"
    | .bottom => "bottom"
    | .exact c => s!"exact({c.value} : i{c.bitwidth})"
    | .upTo c => s!"upTo({c.value} : i{c.bitwidth})"

namespace AbstractConstant

open ConcreteConstant

/-- Defines the ordering of abstract values in the constant domain. -/
def le (x y : AbstractConstant) : Prop :=
  match x, y with
  | .bottom, _ => True
  | _, .top => True
  | .exact c, .exact d => c = d
  | .exact c, .upTo d => c ≼ d
  | .upTo c, .upTo d => c ≼ d
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

/--
Drop the claim that the value is not poison. A fold's answer is sound only up
to refinement, which is what `upTo` allows. `exact poison` is kept, since only
poison refines poison.
-/
@[expose] def weaken : AbstractConstant → AbstractConstant
  | .exact ⟨w, .poison⟩ => .exact ⟨w, .poison⟩
  | .exact c => .upTo c
  | a => a

@[expose] def ofRuntimeValue : RuntimeValue → AbstractConstant
  | .int bitwidth value => .exact ⟨bitwidth, value⟩
  | _ => ⊤

/--
The fact for a result the folder decided on. The folder's contract only gives
refinement, so the fact is weakened.
-/
@[expose] def ofFoldDecision
    (result : FoldDecision) (operands : Array AbstractConstant) : AbstractConstant :=
  match result with
  | .useOperand index => (operands[index]?.getD ⊤).weaken
  | .useConstant value => (ofRuntimeValue value).weaken

/-- The exactly-known facts an `upTo` fact covers; every other fact covers itself. -/
@[expose] def exactCases : AbstractConstant → List AbstractConstant
  | .upTo c => [.exact c, .exact (poison c.bitwidth)]
  | a => [a]

/--
Concretization: the runtime values a fact allows. This is the only relation
between facts and runtime values in the soundness proofs, and it uses equality
only.
-/
@[expose] def γ (absVal : AbstractConstant) : Set RuntimeValue :=
  match absVal with
  | .top => fun _ => True
  | .bottom => fun _ => False
  | .exact c => fun v => v = .int c.bitwidth c.value
  | .upTo c => fun v => v = .int c.bitwidth c.value ∨ v = .int c.bitwidth .poison

/-- The least `upTo` fact above both `c` and `d`, or `⊤` if there is none. -/
@[expose] def joinUpTo (c d : ConcreteConstant) : AbstractConstant :=
  if c ≼ d then .upTo d else if d ≼ c then .upTo c else ⊤

@[expose] def join (lhs rhs : AbstractConstant) : AbstractConstant :=
  match lhs, rhs with
  | .bottom, y => y
  | x, .bottom => x
  | .top, _ => ⊤
  | _, .top => ⊤
  | .exact c, .exact d => if c = d then .exact c else joinUpTo c d
  | .exact c, .upTo d => joinUpTo c d
  | .upTo c, .exact d => joinUpTo c d
  | .upTo c, .upTo d => joinUpTo c d

instance : Join AbstractConstant where
  join := join

@[simp]
theorem mem_γ_top (v : RuntimeValue) : v ∈ γ (.top : AbstractConstant) := trivial

theorem not_mem_γ_bot (v : RuntimeValue) : v ∉ γ (.bottom : AbstractConstant) := id

theorem mem_γ_exact {c : ConcreteConstant} {v : RuntimeValue} :
    v ∈ γ (.exact c) ↔ v = .int c.bitwidth c.value := Iff.rfl

theorem mem_γ_upTo {c : ConcreteConstant} {v : RuntimeValue} :
    v ∈ γ (.upTo c) ↔ v = .int c.bitwidth c.value ∨ v = .int c.bitwidth .poison := Iff.rfl

/-- `upTo c` allows exactly the values `exact d` allows, for `d ≼ c`. -/
theorem mem_γ_upTo_of_below {c d : ConcreteConstant} (h : d ≼ c) :
    RuntimeValue.int d.bitwidth d.value ∈ γ (.upTo c) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem γ_monotone (a b : AbstractConstant) : a ≤ b → γ a ⊆ γ b := by
  intro hab v hv
  cases a <;> cases b <;> simp only [LE.le, le] at hab
  all_goals first | trivial | exact hab.elim | exact hv.elim | skip
  case exact.exact c d => subst hab; exact hv
  case exact.upTo c d =>
    rw [mem_γ_exact.mp hv]
    exact mem_γ_upTo_of_below hab
  case upTo.upTo c d =>
    rcases hv with rfl | rfl
    · exact mem_γ_upTo_of_below hab
    · rcases hab with rfl | rfl <;> exact Or.inr rfl

@[simp, grind .]
theorem le_refl (a : AbstractConstant) : a ≤ a := by
  cases a <;> first | trivial | rfl | exact below_refl _

@[grind →]
theorem le_trans (a b c : AbstractConstant) : a ≤ b → b ≤ c → a ≤ c := by
  intro h h'
  cases a <;> cases b <;> cases c <;> simp only [le_def, le] at h h' ⊢ <;>
    first
      | trivial
      | exact h.elim
      | exact h'.elim
      | (subst h; exact h')
      | (subst h'; exact h)
      | exact below_trans h h'

@[grind →]
theorem le_antisymm (a b : AbstractConstant) : a ≤ b → b ≤ a → a = b := by
  intro h h'
  cases a <;> cases b <;> simp only [le_def, le] at h h' ⊢ <;>
    first
      | rfl
      | exact h.elim
      | exact h'.elim
      | (subst h; rfl)
      | rw [below_antisymm h h']

theorem le_joinUpTo_left (c d : ConcreteConstant) : upTo c ≤ joinUpTo c d := by
  unfold joinUpTo
  split
  · next h => exact h
  · split
    · exact below_refl c
    · trivial

theorem le_joinUpTo_right (c d : ConcreteConstant) : upTo d ≤ joinUpTo c d := by
  unfold joinUpTo
  split
  · exact below_refl d
  · split
    · next h => exact h
    · trivial

theorem exact_le_upTo (c : ConcreteConstant) : exact c ≤ upTo c := below_refl c

theorem exact_le_joinUpTo_left (c d : ConcreteConstant) : exact c ≤ joinUpTo c d :=
  le_trans _ _ _ (exact_le_upTo c) (le_joinUpTo_left c d)

theorem exact_le_joinUpTo_right (c d : ConcreteConstant) : exact d ≤ joinUpTo c d :=
  le_trans _ _ _ (exact_le_upTo d) (le_joinUpTo_right c d)

/-- `joinUpTo c d` is below every `upTo e` above both. -/
theorem joinUpTo_le {c d e : ConcreteConstant} (hc : c ≼ e) (hd : d ≼ e) :
    joinUpTo c d ≤ upTo e := by
  unfold joinUpTo
  split
  · exact hd
  · split
    · exact hc
    · rcases below_total_of_below hc hd with h | h <;> contradiction

theorem join_exact_exact (c d : ConcreteConstant) :
    join (.exact c) (.exact d) = if c = d then .exact c else joinUpTo c d := rfl

@[simp, grind .]
theorem le_join_left (a b : AbstractConstant) : a ≤ a ⊔ b := by
  show a ≤ join a b
  cases a <;> cases b
  all_goals first
    | exact bot_le _
    | exact le_top _
    | exact le_refl _
    | exact exact_le_joinUpTo_left _ _
    | exact le_joinUpTo_left _ _
    | (rw [join_exact_exact]
       split
       · exact le_refl _
       · exact exact_le_joinUpTo_left _ _)

@[simp, grind .]
theorem le_join_right (a b : AbstractConstant) : b ≤ a ⊔ b := by
  show b ≤ join a b
  cases a <;> cases b
  all_goals first
    | exact bot_le _
    | exact le_top _
    | exact le_refl _
    | exact exact_le_joinUpTo_right _ _
    | exact le_joinUpTo_right _ _
    | (rw [join_exact_exact]
       split
       · next h => subst h; exact le_refl _
       · exact exact_le_joinUpTo_right _ _)

theorem join_le (a b c : AbstractConstant) : a ≤ c → b ≤ c → a ⊔ b ≤ c := by
  intro ha hb
  show join a b ≤ c
  cases c with
  | top => exact le_top _
  | bottom =>
    cases a <;> cases b <;> simp only [le_def, le] at ha hb <;>
      first | exact bot_le _ | exact ha.elim | exact hb.elim
  | exact e =>
    cases a <;> cases b <;> simp only [le_def, le] at ha hb <;>
      first
        | exact ha.elim
        | exact hb.elim
        | exact bot_le _
        | (subst hb; exact le_refl _)
        | (subst ha; exact le_refl _)
        | (subst ha; subst hb; rw [join_exact_exact]
           split
           · exact le_refl _
           · next h => exact absurd rfl h)
  | upTo e =>
    cases a <;> cases b <;> simp only [le_def, le] at ha hb <;>
      first
        | exact ha.elim
        | exact hb.elim
        | exact bot_le _
        | exact hb
        | exact ha
        | exact joinUpTo_le ha hb
        | (rw [join_exact_exact]
           split
           · exact ha
           · exact joinUpTo_le ha hb)

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

end AbstractConstant

end Veir
