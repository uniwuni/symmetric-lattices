import SymmetricLattices.Basic
import Mathlib.Order.Sublattice

/-- Def 1.7 -/
class IsSymmetricLattice (α : Type*) [Lattice α] : Prop where
  isModular_symm {a b : α} : Lattice.IsModular a b → Lattice.IsModular b a

/-- Def 1.7 -/
class IsDualSymmetricLattice (α : Type*) [Lattice α] : Prop where
  isDualModular_symm {a b : α} : Lattice.IsDualModular a b → Lattice.IsDualModular b a
/-- Def 1.10 -/
class IsWeaklyModularLattice (α : Type*) [Lattice α] [OrderBot α] : Prop where
   pair_isModular_of_inf_ne_bot {a b : α} (h : a ⊓ b ≠ ⊥) : Lattice.IsModular a b
/-- Def 1.11 -/
class IsBotSymmetricLattice (α : Type*) [Lattice α] [OrderBot α] : Prop where
  isModular_symm_of_inf_eq_bot {a b : α} : Lattice.IsModular a b → a ⊓ b = ⊥ → Lattice.IsModular b a


variable {α : Type*}
instance [Lattice α] [IsModularLattice α] [OrderBot α]: IsWeaklyModularLattice α where
  pair_isModular_of_inf_ne_bot _ := pair_modular _ _
/-- "It is evident" below 1.11 -/
instance [Lattice α] [OrderBot α] [IsSymmetricLattice α] : IsBotSymmetricLattice α where
  isModular_symm_of_inf_eq_bot h _ := IsSymmetricLattice.isModular_symm h

/-- Remark 1.12 -/
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
variable {α β : Type*} [Lattice α] [Lattice β]
/-- Theorem 1.9 -/
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

/-- Theorem 1.9 -/
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
/-- Remark 1.8 -/
instance Sublattice.isModularLattice [IsModularLattice α] {L : Sublattice α} : IsModularLattice L where
  sup_inf_le_assoc_of_le {c} a b le := by
    rcases a
    rcases b
    rcases c
    simp only [mk_sup_mk, mk_inf_mk, Subtype.mk_le_mk]
    exact IsModularLattice.sup_inf_le_assoc_of_le _ le
/-- Remark 1.8 -/
instance Set.Icc.isSymmetricLattice [IsSymmetricLattice α] {a b : α} (h : a ≤ b) : IsSymmetricLattice (Set.Icc a b) where
  isModular_symm {c} {d} mod := by
    rw[Lattice.IsModular.Icc_iff h] at mod |-
    exact IsSymmetricLattice.isModular_symm mod
/-- Remark 1.8 -/
instance Set.Icc.isDualSymmetricLattice [IsDualSymmetricLattice α] {a b : α} (h : a ≤ b) : IsDualSymmetricLattice (Set.Icc a b) where
  isDualModular_symm {c} {d} mod := by
    rw[Lattice.IsDualModular.Icc_iff h] at mod |-
    exact IsDualSymmetricLattice.isDualModular_symm mod
/-- "It follows" below 1.10 -/
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
/-- "It follows" below 1.10 -/
theorem isWeaklyModularLattice.of_all_Ici_modular [OrderBot α]
    (h : ∀ a : α, ⊥ < a → IsModularLattice (Set.Ici a)) : IsWeaklyModularLattice α where
  pair_isModular_of_inf_ne_bot {a} {b} ne := by
    have : ⊥ < a ⊓ b := by rwa[bot_lt_iff_ne_bot]
    have ha : a ∈ Set.Ici (a ⊓ b) := inf_le_left
    have hb : b ∈ Set.Ici (a ⊓ b) := inf_le_right
    specialize h _ this
    rw[← Lattice.IsModular.Ici_iff (a := ⟨a,ha⟩) (b := ⟨b,hb⟩)]
    apply pair_modular
/-- "It is evident" below 1.11 -/
theorem isSymmetric_of_botSymmetric_of_weaklyModular
    [OrderBot α] [IsWeaklyModularLattice α] [IsBotSymmetricLattice α] : IsSymmetricLattice α where
  isModular_symm {a} {b} h := by
    by_cases h' : a ⊓ b = ⊥
    · apply IsBotSymmetricLattice.isModular_symm_of_inf_eq_bot h h'
    · have : b ⊓ a ≠ ⊥ := by rwa[inf_comm]
      apply IsWeaklyModularLattice.pair_isModular_of_inf_ne_bot this
/-- Remark 1.12 -/
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
/-- Theorem 1.14 -/
theorem IsBotSymmetricLattice.isSymmetric_of_complemented [BoundedOrder α] [IsBotSymmetricLattice α]
    (h : ∀ a : α, ∃ b, IsCompl a b ∧ Lattice.IsModular a b ∧ Lattice.IsDualModular b a) : IsSymmetricLattice α where
  isModular_symm {a b} mod := by
    obtain ⟨c, compl, mod', dmod⟩ := h (a ⊓ b)
    let iso := Lattice.infIccOrderIsoIccSup mod' dmod
    --rw[compl.inf_eq_bot, compl.sup_eq_top] at iso
    have a_in : a ∈ Set.Icc (a ⊓ b) (a ⊓ b ⊔ c) := by
      rw[compl.sup_eq_top]
      simp only [Set.Icc_top, Set.mem_Ici, inf_le_left]
    have b_in : b ∈ Set.Icc (a ⊓ b) (a ⊓ b ⊔ c) := by
      rw[compl.sup_eq_top]
      simp only [Set.Icc_top, Set.mem_Ici, inf_le_right]
    have eqa : (iso ⟨a ⊓ c, ⟨by simp[compl.inf_eq_bot], by simp⟩⟩) = ⟨a,a_in⟩ := by
      rw[Subtype.mk_eq_mk, Lattice.infIccOrderIsoIccSup_apply]
      simp only
      rw[← dmod.eq]
      · rw[inf_eq_left, sup_comm, compl.sup_eq_top]
        simp only [le_top]
      · simp only [ge_iff_le, inf_le_left]
    have eqb : ↑ (iso ⟨b ⊓ c, ⟨by simp[compl.inf_eq_bot], by simp⟩⟩) = ⟨b,b_in⟩ := by
      rw[Subtype.mk_eq_mk, Lattice.infIccOrderIsoIccSup_apply]
      simp only
      rw[← dmod.eq]
      · rw[inf_eq_left, sup_comm, compl.sup_eq_top]
        simp only [le_top]
      · simp only [ge_iff_le, inf_le_right]
    have mod2 : Lattice.IsModular (α := Set.Icc (a ⊓ b) (a ⊓ b ⊔ c)) ⟨a,a_in⟩ ⟨b,b_in⟩ := by
      rw[Lattice.IsModular.Icc_iff le_sup_left]
      exact mod
    have mod3 : Lattice.IsModular (α := Set.Icc (a ⊓ b ⊓ c) c)
        ⟨a ⊓ c, ⟨by simp[compl.inf_eq_bot], by simp⟩⟩
        ⟨b ⊓ c, ⟨by simp[compl.inf_eq_bot], by simp⟩⟩ := by
      rwa[← eqa, ← eqb, OrderIso.isModular_iff] at mod2
    have mod3' := (Lattice.IsModular.Icc_iff inf_le_right).mp mod3
    simp only at mod3'
    have mod3'_symm := IsBotSymmetricLattice.isModular_symm_of_inf_eq_bot mod3'
      (by rw[← inf_right_comm, ← inf_assoc, compl.inf_eq_bot, bot_inf_eq])
    have mod3_symm : Lattice.IsModular (α := Set.Icc (a ⊓ b ⊓ c) c)
        ⟨b ⊓ c, ⟨by simp[compl.inf_eq_bot], by simp⟩⟩
        ⟨a ⊓ c, ⟨by simp[compl.inf_eq_bot], by simp⟩⟩ := by
      rwa[Lattice.IsModular.Icc_iff inf_le_right]
    have mod2_symm : Lattice.IsModular (α := Set.Icc (a ⊓ b) (a ⊓ b ⊔ c)) ⟨b,b_in⟩ ⟨a,a_in⟩ := by
      rwa[← eqa, ← eqb, OrderIso.isModular_iff]
    rw[Lattice.IsModular.Icc_iff le_sup_left] at mod2_symm
    exact mod2_symm

variable {ι : Type*} {α' : ι → Type*} [(i : ι) → Lattice (α' i)]
instance [∀ i, IsSymmetricLattice (α' i)] : IsSymmetricLattice ((i : _) → α' i) where
  isModular_symm {a} {b} := by
    rw[Lattice.IsModular.pi_iff, Lattice.IsModular.pi_iff]
    apply forall_imp
    intro i
    apply IsSymmetricLattice.isModular_symm
/-- Lemma 1.17 -/
theorem IsSymmetricLattice.pi_iff [ne : ∀ i, Nonempty (α' i)] : IsSymmetricLattice ((i : _) → α' i) ↔ ∀ i, IsSymmetricLattice (α' i) := by
  constructor
  · intro h i
    constructor
    classical
    intro a b
    let fa : (i : ι) → α' i := Function.update (fun i => ((ne i).some : α' i)) i a
    let fb : (i : ι) → α' i := Function.update fa i b
    intro mod
    have t : Lattice.IsModular fa fb := by
      rw[Lattice.IsModular.pi_iff]
      intro j
      by_cases h' : j = i
      · rcases h'
        simp[fa, fb, mod]
      · simp only [ne_eq, h', not_false_eq_true, Function.update_of_ne, fa, fb]
        rfl
    have t := IsSymmetricLattice.isModular_symm t
    rw[Lattice.IsModular.pi_iff] at t
    specialize t i
    simpa[fa, fb] using t
  · intro h
    infer_instance

instance [∀ i, OrderBot (α' i)] [∀ i, IsBotSymmetricLattice (α' i)] : IsBotSymmetricLattice ((i : _) → α' i) where
  isModular_symm_of_inf_eq_bot {a} {b} := by
    rw[Lattice.IsModular.pi_iff, Lattice.IsModular.pi_iff]
    intro mod eq i
    apply IsBotSymmetricLattice.isModular_symm_of_inf_eq_bot (mod i) (congrFun eq i)
/-- Lemma 1.17 -/
theorem IsBotSymmetricLattice.pi_iff [∀ i, OrderBot (α' i)] : IsBotSymmetricLattice ((i : _) → α' i) ↔ ∀ i, IsBotSymmetricLattice (α' i) := by
  constructor
  · intro h i
    constructor
    classical
    intro a b
    let fa : (i : ι) → α' i := Function.update (fun i => ⊥) i a
    let fb : (i : ι) → α' i := Function.update fa i b
    intro mod h'
    have t : Lattice.IsModular fa fb := by
      rw[Lattice.IsModular.pi_iff]
      intro j
      by_cases h' : j = i
      · rcases h'
        simp[fa, fb, mod]
      · simp only [ne_eq, h', not_false_eq_true, Function.update_of_ne, fa, fb]
        rfl
    have t := IsBotSymmetricLattice.isModular_symm_of_inf_eq_bot t
    rw[Lattice.IsModular.pi_iff] at t
    have : fa ⊓ fb = ⊥ := by
      ext j
      by_cases h'' : j = i
      · rcases h''
        simp[fa,fb, h']
      · simp[h'', fa, fb]
    convert t this i
    · simp[fb]
    · simp[fa]
  · intro h
    infer_instance
/-- Lemma 1.18 -/
theorem IsWeaklyModularLattice.of_prod_left [OrderBot α] [OrderBot β] [Nontrivial α] [Nontrivial β]
    (h : IsWeaklyModularLattice (α × β)) : IsModularLattice α := by
  apply isModularLattice_of_all_isModular
  by_contra! h'
  obtain ⟨a,b,h'⟩ := h'
  have ⟨b',ne⟩ := exists_ne (⊥ : β)
  have : (a,b') ⊓ (b, b') ≠ ⊥ := by
    intro h
    rw[Prod.ext_iff] at h
    simp only [Prod.mk_inf_mk, le_refl, inf_of_le_left, Prod.fst_bot, Prod.snd_bot] at h
    exact ne h.2
  have : Lattice.IsModular (a,b') (b, b') := IsWeaklyModularLattice.pair_isModular_of_inf_ne_bot this
  rw[Lattice.IsModular.pair_iff] at this
  exact h' this.1

/-- Lemma 1.18 -/
theorem IsWeaklyModularLattice.of_prod_right [OrderBot α] [OrderBot β] [Nontrivial α] [Nontrivial β]
    (h : IsWeaklyModularLattice (α × β)) : IsModularLattice β := by
  apply isModularLattice_of_all_isModular
  by_contra! h'
  obtain ⟨a,b,h'⟩ := h'
  have ⟨a',ne⟩ := exists_ne (⊥ : α)
  have : (a',a) ⊓ (a', b) ≠ ⊥ := by
    intro h
    rw[Prod.ext_iff] at h
    simp only [Prod.mk_inf_mk, le_refl, inf_of_le_left, Prod.fst_bot, Prod.snd_bot] at h
    exact ne h.1
  have : Lattice.IsModular (a',a) (a', b) := IsWeaklyModularLattice.pair_isModular_of_inf_ne_bot this
  rw[Lattice.IsModular.pair_iff] at this
  exact h' this.2
