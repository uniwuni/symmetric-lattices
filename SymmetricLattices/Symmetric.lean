import SymmetricLattices.Basic
import Mathlib.Order.Sublattice

class IsSymmetricLattice (α : Type*) [Lattice α] : Prop where
  isModular_symm {a b : α} : Lattice.IsModular a b → Lattice.IsModular b a

class IsDualSymmetricLattice (α : Type*) [Lattice α] : Prop where
  isDualModular_symm {a b : α} : Lattice.IsDualModular a b → Lattice.IsDualModular b a

class IsWeaklyModularLattice (α : Type*) [Lattice α] [OrderBot α] : Prop where
   pair_isModular_of_inf_ne_bot {a b : α} (h : a ⊓ b ≠ ⊥) : Lattice.IsModular a b

class IsBotSymmetricLattice (α : Type*) [Lattice α] [OrderBot α] : Prop where
  isModular_symm_of_inf_eq_bot {a b : α} : Lattice.IsModular a b → a ⊓ b = ⊥ → Lattice.IsModular b a


variable {α : Type*}
instance [Lattice α] [IsModularLattice α] [OrderBot α]: IsWeaklyModularLattice α where
  pair_isModular_of_inf_ne_bot _ := pair_modular _ _

instance [Lattice α] [OrderBot α] [IsSymmetricLattice α] : IsBotSymmetricLattice α where
  isModular_symm_of_inf_eq_bot h _ := IsSymmetricLattice.isModular_symm h

instance [Lattice α] [OrderBot α] [IsBotSymmetricLattice α] {a : α} : IsBotSymmetricLattice (Set.Iic a) where
  isModular_symm_of_inf_eq_bot {a'} {b} h h' := by
    rcases a' with ⟨a',ha⟩
    rcases b with ⟨b,hb⟩
    have : a' ⊓ b = ⊥ := by
      change (⟨a', ha⟩ : Set.Iic a).val ⊓ (⟨b,hb⟩ : Set.Iic a).val = ⊥
      rw_mod_cast[h']
      simp
    rw[Lattice.IsModular.Iic_iff] at h |-
    exact IsBotSymmetricLattice.isModular_symm_of_inf_eq_bot h this

theorem isSymmetricLattice_iff_dual_isDualSymmetricLattice (α : Type*) [Lattice α] :
    IsSymmetricLattice α ↔ IsDualSymmetricLattice (α ᵒᵈ) := by
  constructor
  · intro ⟨p⟩
    constructor
    apply OrderDual.rec
    intro a
    apply OrderDual.rec
    intro b
    rw[Lattice.toDual_isDualModular_iff_modular, Lattice.toDual_isDualModular_iff_modular]
    apply p
  · intro ⟨p⟩
    constructor
    intro a b
    specialize p (a := OrderDual.toDual a) (b := OrderDual.toDual b)
    rw[Lattice.toDual_isDualModular_iff_modular, Lattice.toDual_isDualModular_iff_modular] at p
    apply p

theorem isDualSymmetricLattice_iff_dual_isSymmetricLattice (α : Type*) [Lattice α] :
    IsDualSymmetricLattice α ↔ IsSymmetricLattice (α ᵒᵈ) := by
  constructor
  · intro ⟨p⟩
    constructor
    apply OrderDual.rec
    intro a
    apply OrderDual.rec
    intro b
    rw[Lattice.toDual_isModular_iff_dualModular, Lattice.toDual_isModular_iff_dualModular]
    apply p
  · intro ⟨p⟩
    constructor
    intro a b
    specialize p (a := OrderDual.toDual a) (b := OrderDual.toDual b)
    rw[Lattice.toDual_isModular_iff_dualModular, Lattice.toDual_isModular_iff_dualModular] at p
    apply p


attribute [symm] IsSymmetricLattice.isModular_symm IsDualSymmetricLattice.isDualModular_symm

section
variable {α : Type*} [Lattice α]
theorem Lattice.isSymmetric_of_modular_to_dualModular
    (h : ∀ a b : α, IsModular a b → IsDualModular b a) : IsSymmetricLattice α where
  isModular_symm {a} {b} h' := by
    have ha : a ∈ Set.Icc (a ⊓ b) (a ⊔ b) := by simp
    have hb : b ∈ Set.Icc (a ⊓ b) (a ⊔ b) := by simp
    apply (IsModular.Icc_iff (inf_le_sup (a := a) (b := b)) (a := ⟨b,hb⟩) (b := ⟨a,ha⟩)).mp
    intro ⟨c,hc1,hc2⟩ le
    rw[Subtype.mk_le_mk]
    simp at le |-
    have : IsModular c b := h'.of_Icc_Icc hc1 le (by simp) (by simp)
    convert h _ _ this a le using 1
    · rw[inf_comm, sup_comm]
    · rw[inf_comm, sup_comm]

theorem Lattice.isDualSymmetric_of_dualModular_to_modular
    (h : ∀ a b : α, IsDualModular a b → IsModular b a) : IsDualSymmetricLattice α where
  isDualModular_symm {a} {b} h' := by
    have ha : a ∈ Set.Icc (a ⊓ b) (a ⊔ b) := by simp
    have hb : b ∈ Set.Icc (a ⊓ b) (a ⊔ b) := by simp
    apply (IsDualModular.Icc_iff (inf_le_sup (a := a) (b := b)) (a := ⟨b,hb⟩) (b := ⟨a,ha⟩)).mp
    intro ⟨c,hc1,hc2⟩ le
    rw[Subtype.mk_le_mk]
    simp at le |-
    have : IsDualModular c b := h'.of_Icc_Icc hc2 le (by simp) (by simp)
    convert h _ _ this a le using 1
    · rw[inf_comm, sup_comm]
    · rw[inf_comm, sup_comm]

instance Sublattice.isModularLattice [IsModularLattice α] {L : Sublattice α} : IsModularLattice L where
  sup_inf_le_assoc_of_le {c} a b le := by
    rcases a
    rcases b
    rcases c
    simp only [mk_sup_mk, mk_inf_mk, Subtype.mk_le_mk]
    exact IsModularLattice.sup_inf_le_assoc_of_le _ le

instance Set.Icc.isSymmetricLattice [IsSymmetricLattice α] {a b : α} (h : a ≤ b) : IsSymmetricLattice (Set.Icc a b) where
  isModular_symm {c} {d} mod := by
    rw[Lattice.IsModular.Icc_iff h] at mod |-
    exact IsSymmetricLattice.isModular_symm mod

instance Set.Icc.isDualSymmetricLattice [IsDualSymmetricLattice α] {a b : α} (h : a ≤ b) : IsDualSymmetricLattice (Set.Icc a b) where
  isDualModular_symm {c} {d} mod := by
    rw[Lattice.IsDualModular.Icc_iff h] at mod |-
    exact IsDualSymmetricLattice.isDualModular_symm mod

theorem IsWeaklyModularLattice.Ici_modular [OrderBot α] [IsWeaklyModularLattice α] (a : α) (ha : ⊥ < a):
    IsModularLattice (Set.Ici a) where
  sup_inf_le_assoc_of_le {x b} c le := by
    rcases x with ⟨x,hx⟩
    rcases b with ⟨b,hb⟩
    rcases c with ⟨c,hc⟩
    rw[Subtype.mk_le_mk]
    simp at le |-
    apply pair_isModular_of_inf_ne_bot ?goal
    · exact le
    · have : a ≤ b ⊓ c := le_inf hb hc
      intro eq
      rw[eq] at this
      apply (not_le_of_lt ha this).elim

theorem isWeaklyModularLattice.of_all_Ici_modular [OrderBot α]
    (h : ∀ a : α, ⊥ < a → IsModularLattice (Set.Ici a)) : IsWeaklyModularLattice α where
  pair_isModular_of_inf_ne_bot {a} {b} ne := by
    have : ⊥ < a ⊓ b := by rwa[bot_lt_iff_ne_bot]
    have ha : a ∈ Set.Ici (a ⊓ b) := inf_le_left
    have hb : b ∈ Set.Ici (a ⊓ b) := inf_le_right
    specialize h _ this
    rw[← Lattice.IsModular.Ici_iff (a := ⟨a,ha⟩) (b := ⟨b,hb⟩)]
    apply pair_modular

theorem isSymmetric_of_botSymmetric_of_weaklyModular
    [OrderBot α] [IsWeaklyModularLattice α] [IsBotSymmetricLattice α] : IsSymmetricLattice α where
  isModular_symm {a} {b} h := by
    by_cases h' : a ⊓ b = ⊥
    · apply IsBotSymmetricLattice.isModular_symm_of_inf_eq_bot h h'
    · have : b ⊓ a ≠ ⊥ := by rwa[inf_comm]
      apply IsWeaklyModularLattice.pair_isModular_of_inf_ne_bot this

theorem Lattice.isBotSymmetric_of_modular_to_dualModular [OrderBot α]
    (h : ∀ a b : α, IsModular a b → a ⊓ b = ⊥ → IsDualModular b a) : IsBotSymmetricLattice α where
  isModular_symm_of_inf_eq_bot {a} {b} h' ne := by
    have ha : a ∈ Set.Iic (a ⊔ b) := by simp
    have hb : b ∈ Set.Iic (a ⊔ b) := by simp
    apply (IsModular.Iic_iff (a := ⟨b,hb⟩) (b := ⟨a,ha⟩)).mp
    intro ⟨c,hc1⟩ le
    rw[Subtype.mk_le_mk]
    simp at le |-
    have : a ⊓ b ≤ c := by rw[ne]; simp
    have mod : IsModular c b := h'.of_Icc_Icc this le (by simp) (by simp)
    have : c ⊓ b = ⊥ := by rw[← le_bot_iff, ← ne]; gcongr
    convert h _ _ mod this a le using 1
    · rw[inf_comm, sup_comm]
    · rw[inf_comm, sup_comm]
