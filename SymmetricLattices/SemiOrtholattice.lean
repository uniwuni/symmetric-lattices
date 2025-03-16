import Mathlib.Order.ModularLattice
import Mathlib.Tactic.Monotonicity.Basic

variable {α : Type*}
/-- Def 2.1 -/
class SemiOrtholattice (α : Type*) extends Lattice α, OrderBot α where
  perp : α → α → Prop
  perp_refl_iff_eq_bot {a : α} : perp a a ↔ a = ⊥
  perp_symm {a b : α} : perp a b → perp b a
  perp_of_le_of_perp {a b c : α} : perp a b → c ≤ a → perp c b
  perp_sup_of_sup_perp {a b c : α} : perp a b → perp (a ⊔ b) c → perp a (b ⊔ c)

export SemiOrtholattice (perp)

section
variable [SemiOrtholattice α] {a b c : α}
@[simp] theorem perp_refl_iff_eq_bot {a : α} : perp a a ↔ a = ⊥ := SemiOrtholattice.perp_refl_iff_eq_bot
instance : IsSymm α perp where
  symm _ _ := SemiOrtholattice.perp_symm
theorem perp_of_le_of_perp {a b c : α} : perp a b → c ≤ a → perp c b := SemiOrtholattice.perp_of_le_of_perp
theorem perp_of_le_of_perp' {a b c : α} : perp a b → c ≤ b → perp a c :=
  fun h h' => symm $ perp_of_le_of_perp (symm h) h'
theorem perp_inf_of_perp_left {a b c : α} : perp a b → perp (a ⊓ c) b :=
  fun h => perp_of_le_of_perp h inf_le_left
theorem perp_inf_of_perp_left' {a b c : α} : perp a b → perp (c ⊓ a) b :=
  fun h => perp_of_le_of_perp h inf_le_right
theorem perp_inf_of_perp_right {a b c : α} : perp a b → perp a (b ⊓ c) :=
  fun h => perp_of_le_of_perp' h inf_le_left
theorem perp_inf_of_perp_right' {a b c : α} : perp a b → perp a (c ⊓ b) :=
  fun h => perp_of_le_of_perp' h inf_le_right
/-- Remark below Def 2.1 -/
@[simp] theorem inf_eq_zero_of_perp (h : perp a b) : a ⊓ b = ⊥ := by
  rw[← perp_refl_iff_eq_bot]
  apply perp_inf_of_perp_left
  apply perp_inf_of_perp_right' h




end
