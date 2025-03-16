import Mathlib.Order.ModularLattice
import Mathlib.Tactic.Monotonicity.Basic

section
variable {α : Type*} [Lattice α] {a b : α}
@[simp, norm_cast] theorem Set.Icc.inf_eq (c d : Set.Icc a b) : ↑(c ⊓ d) = (c : α) ⊓ (d : α) := by rfl
@[simp, norm_cast] theorem Set.Icc.sup_eq (c d : Set.Icc a b) : ↑(c ⊔ d) = (c : α) ⊔ (d : α) := by rfl

@[simp, norm_cast]
lemma Set.Ici.coe_sup {x y : Ici a} :
    (↑(x ⊔ y) : α) = (x : α) ⊔ (y : α) := rfl
@[simp, norm_cast]
lemma Set.Ici.coe_inf {x y : Ici a} :
    (↑(x ⊓ y) : α) = (x : α) ⊓ (y : α) := rfl

end


namespace Lattice
variable {α : Type*} [Lattice α] {a b c d : α}
/-- Def 1.1a -/
def IsModular (a b : α) : Prop := ∀ c ≤ b, (c ⊔ a) ⊓ b ≤ c ⊔ (a ⊓ b)
/-- Def 1.1b -/
def IsDualModular (a b : α) : Prop := ∀ c ≥ b, c ⊓ (a ⊔ b) ≤ (c ⊓ a) ⊔ b


def IsModular.eq (h : IsModular a b) : ∀ c ≤ b, (c ⊔ a) ⊓ b = c ⊔ (a ⊓ b) := by
  intro c h'
  apply le_antisymm (h c h')
  apply le_inf (sup_le_sup_left inf_le_left _)
  apply sup_le h' inf_le_right

def isModular_of_eq (h : ∀ c ≤ b, (c ⊔ a) ⊓ b = c ⊔ (a ⊓ b)) : IsModular a b :=
  fun c h' => le_of_eq (h c h')

def IsDualModular.eq (h : IsDualModular a b) : ∀ c ≥ b, c ⊓ (a ⊔ b) = (c ⊓ a) ⊔ b := by
  intro c h'
  apply le_antisymm (h c h')
  apply le_inf (sup_le inf_le_left h') (sup_le_sup_right inf_le_right _)

def isDualModular_of_eq (h : ∀ c ≥ b, c ⊓ (a ⊔ b) = (c ⊓ a) ⊔ b) : IsDualModular a b :=
  fun c h' => le_of_eq (h c h')
/-- Note below Def 1.1 -/
theorem toDual_isModular_iff_dualModular : IsModular (OrderDual.toDual a) (OrderDual.toDual b) ↔ IsDualModular a b := by
  unfold IsModular IsDualModular
  rw[OrderDual.forall]
  apply forall_congr'
  intro c
  simp only [OrderDual.toDual_le_toDual, ge_iff_le]
  rfl

theorem toDual_isDualModular_iff_modular : IsDualModular (OrderDual.toDual a) (OrderDual.toDual b) ↔ IsModular a b := by
  unfold IsModular IsDualModular
  rw[OrderDual.forall]
  apply forall_congr'
  intro c
  simp only [OrderDual.toDual_le_toDual, ge_iff_le]
  rfl

/-- "Evidently," below Def 1.1 -/
theorem isModular_of_le (h : a ≤ b) : IsModular a b := by
  intro c h'
  simp[*]
/-- "Evidently," below Def 1.1 -/
theorem isModular_of_ge (h : b ≤ a) : IsModular a b := by
  intro c h'
  simp[*]
/-- "Evidently," below Def 1.1 -/
theorem isDualModular_of_le (h : a ≤ b) : IsDualModular a b := by
  intro c h'
  simp[*]
/-- "Evidently," below Def 1.1 -/
theorem isDualModular_of_ge (h : b ≤ a) : IsDualModular a b := by
  intro c h'
  simp[*]

@[refl] protected theorem IsModular.refl (a : α) : IsModular a a := isModular_of_le le_rfl
@[refl] protected theorem IsDualModular.refl (a : α) : IsDualModular a a := isDualModular_of_le le_rfl

instance : IsRefl α IsModular := ⟨IsModular.refl⟩
instance : IsRefl α IsDualModular := ⟨IsDualModular.refl⟩
/-- Lemma 1.2 -/
theorem isModular_all_iff_isDualModular_all : (∀ b, IsModular a b) ↔ (∀ b, IsDualModular a b) := by
  unfold IsModular IsDualModular
  rw[forall_swap]
  apply forall_congr'
  intro b
  apply forall_congr'
  intro c
  rw[inf_comm (b ⊔ a) c, sup_comm b a, sup_comm b _, inf_comm a c]
/-- Lemma 1.3 -/
@[simps]
def infIccOrderIsoIccSup (h : IsModular a b) (h' : IsDualModular b a) : Set.Icc (a ⊓ b) b ≃o Set.Icc a (a ⊔ b) where
  toFun x := ⟨x ⊔ a, le_sup_right, sup_comm (α := α) _ _ ▸ sup_le_sup_left x.2.2 _⟩
  invFun x := ⟨b ⊓ x, inf_comm a b ▸ inf_le_inf_left _ x.2.1, inf_le_left⟩
  left_inv x := by
    rcases x with ⟨x,hx1,hx2⟩
    simp
    rw[inf_comm, h.eq x hx2, sup_of_le_left hx1]
  right_inv x := by
    rcases x with ⟨x,hx1,hx2⟩
    simp
    rw[inf_comm, ← h'.eq x hx1, sup_comm, inf_of_le_left hx2]
  map_rel_iff' {x y} := by
    rcases x with ⟨x,hx1,hx2⟩
    rcases y with ⟨y,hy1,hy2⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, and_true]
    constructor
    · intro le
      have : (x ⊔ a) ⊓ b ≤ (y ⊔ a) ⊓ b := inf_le_inf_right _ le
      rw[h.eq _ hx2, h.eq _ hy2] at this
      simpa[*] using this
    · exact fun h => sup_le_sup_right h _

@[simp] theorem infIccOrderIsoIccSup_apply {h : IsModular a b} {h' : IsDualModular b a} {c : Set.Icc (a ⊓ b) b} :
    infIccOrderIsoIccSup h h' c = ↑ c ⊔ a := by
  simp[infIccOrderIsoIccSup]

/-- Lemma 1.4 -/
@[simp] lemma IsModular.Icc_iff (h : c ≤ d) {a b : Set.Icc c d} : IsModular a b ↔ IsModular (a : α) (b : α) := by
  constructor
  · intro h' x le
    have prop : x ⊔ c ∈ Set.Icc c d := ⟨le_sup_right, sup_le (le.trans b.property.2) h⟩
    replace h' := h'.eq ⟨_,prop⟩
    rcases b with ⟨b,hb⟩
    rcases a with ⟨a,ha⟩
    simp at h'
    specialize h' le hb.1
    rw[Subtype.mk_eq_mk] at h'
    simp only [Set.Icc.inf_eq, Set.Icc.sup_eq] at h' |-
    rw[sup_assoc, sup_of_le_right ha.1] at h'
    rw[h', sup_assoc]
    simp[ha.1, hb.1]
  · intro h' ⟨x,hx⟩ le
    rcases b with ⟨b,hb⟩
    rcases a with ⟨a,ha⟩
    rw[Subtype.mk_le_mk]
    simp only [Set.Icc.inf_eq, Set.Icc.sup_eq]
    apply h' _ le
/-- Lemma 1.4 variation -/
@[simp] lemma IsModular.Ici_iff {a b : Set.Ici c} : IsModular a b ↔ IsModular (a : α) (b : α) := by
  constructor
  · intro h' x le
    have prop : x ⊔ c ∈ Set.Ici c := le_sup_right
    replace h' := h'.eq ⟨_,prop⟩
    rcases b with ⟨b,hb⟩
    rcases a with ⟨a,ha⟩
    simp at h'
    specialize h' le hb
    rw[Subtype.mk_eq_mk] at h'
    simp at h' |-
    rw[sup_assoc, sup_of_le_right ha] at h'
    rw[h', sup_assoc]
    gcongr
    simp only [le_inf_iff, sup_le_iff, inf_le_left, and_true, inf_le_right]
    exact ⟨ha,hb⟩
  · intro h' ⟨x,hx⟩ le
    rcases b with ⟨b,hb⟩
    rcases a with ⟨a,ha⟩
    rw[Subtype.mk_le_mk]
    simp only [Set.Ici.coe_inf, Set.Ici.coe_sup]
    apply h' _ le
/-- Lemma 1.4 variation -/
@[simp] lemma IsModular.Iic_iff {a b : Set.Iic c} : IsModular a b ↔ IsModular (a : α) (b : α) := by
  constructor
  · intro h' x le
    have prop : x ∈ Set.Iic c := le.trans b.prop
    replace h' := h'.eq ⟨_,prop⟩
    rcases b with ⟨b,hb⟩
    rcases a with ⟨a,ha⟩
    simp at h'
    specialize h' le
    rw[Subtype.mk_eq_mk] at h'
    simp at h' |-
    exact le_of_eq h'
  · intro h' ⟨x,hx⟩ le
    rcases b with ⟨b,hb⟩
    rcases a with ⟨a,ha⟩
    rw[Subtype.mk_le_mk]
    simp only [Set.Iic.coe_inf, Set.Iic.coe_sup]
    apply h' _ le

/-- Lemma 1.4 variation -/
@[simp] lemma IsDualModular.Icc_iff (h : c ≤ d) {a b : Set.Icc c d} : IsDualModular a b ↔ IsDualModular (a : α) (b : α) := by
  constructor
  · intro h' x le
    have prop : x ⊓ d ∈ Set.Icc c d := ⟨le_inf (b.property.1.trans le) h, inf_le_right⟩
    replace h' := h'.eq ⟨_,prop⟩
    rcases b with ⟨b,hb⟩
    rcases a with ⟨a,ha⟩
    simp at h'
    specialize h' le hb.2
    rw[Subtype.mk_eq_mk] at h'
    simp only [Set.Icc.inf_eq, Set.Icc.sup_eq] at h' |-
    rw[inf_assoc, inf_of_le_right (sup_le ha.2 hb.2)] at h'
    rw[h', inf_assoc]
    simp[ha.2, hb.2]
  · intro h' ⟨x,hx⟩ le
    rcases b with ⟨b,hb⟩
    rcases a with ⟨a,ha⟩
    rw[Subtype.mk_le_mk]
    simp only [Set.Icc.inf_eq, Set.Icc.sup_eq]
    apply h' _ le
/-- Lemma 1.5.1 -/
lemma IsModular.of_isModular_Icc (h : IsModular a b) (h' : IsModular (a ⊓ b) c)
    (ge : a ⊓ c ≤ d) (le : d ≤ a) : IsModular d (b ⊓ c) := by
  rename' d => a₁
  intro d hd
  obtain ⟨hd1,hd2⟩ := le_inf_iff.mp hd
  trans (d ⊔ a) ⊓ (b ⊓ c)
  · gcongr
  · rw[← inf_assoc, h.eq _ hd1, h'.eq _ hd2]
    have : a ⊓ b ⊓ c ≤ a₁ ⊓ b ⊓ c := by
      simp only [le_inf_iff, inf_le_right, and_true]
      constructor
      · rw[inf_right_comm]
        apply inf_le_of_left_le ge
      · apply inf_le_of_left_le inf_le_right
    gcongr d ⊔ ?_
    rwa[← inf_assoc]
/-- Lemma 1.5.2 -/
lemma IsModular.of_Icc_Icc (h : IsModular a b)
    (ge_c : a ⊓ b ≤ c) (le_c : c ≤ a) (ge_d : a ⊓ b ≤ d) (le_d : d ≤ b) :
    IsModular c d := by
  have : IsModular (a ⊓ b) d := isModular_of_le ge_d
  have := h.of_isModular_Icc this (d := c)
  rw[inf_of_le_right (a := b) le_d] at this
  apply this
  · trans a ⊓ b
    · gcongr
    · assumption
  · assumption

/-- Lemma 1.5.3 -/
lemma IsModular.of_inf_bot [OrderBot α] (h : IsModular a b) (ort : a ⊓ b = ⊥) (h' : c ≤ a) (h'' : d ≤ b) : IsModular c d := by
  have := of_Icc_Icc h (c := c) (d := d)
  simpa only [ort, bot_le, forall_const, h', h''] using this

/-- Lemma 1.5.1 dual -/
lemma IsDualModular.of_isDualModular_Icc : (h : IsDualModular a b) → (h' : IsDualModular (a ⊔ b) c) →
    (ge : d ≤ a ⊔ c) → (le : a ≤ d) → IsDualModular d (b ⊔ c) := by
  rw[← toDual_isModular_iff_dualModular, ← toDual_isModular_iff_dualModular, ← toDual_isModular_iff_dualModular]
  simp only [toDual_sup]
  intro h h' ge le
  apply h.of_isModular_Icc h' ge le
/-- Lemma 1.5.2 dual -/
lemma IsDualModular.of_Icc_Icc : (h : IsDualModular a b) →
    (ge_c : c ≤ a ⊔ b) → (le_c : a ≤ c) → (ge_d : d ≤ a ⊔ b) → (le_d : b ≤ d) →
    IsDualModular c d := by
  rw[← toDual_isModular_iff_dualModular, ← toDual_isModular_iff_dualModular]
  intro h h' ge le
  apply h.of_Icc_Icc h' ge le
/-- Lemma 1.5.3 dual -/
lemma IsDualModular.of_sup_top [OrderTop α] (h : IsDualModular a b)
    (ort : a ⊔ b = ⊤) (h' : a ≤ c) (h'' : b ≤ d) : IsDualModular c d := by
  have := of_Icc_Icc h (c := c) (d := d)
  simpa only [ort, le_top, forall_const, h', h''] using this
/-- Lemma 1.6a -/
lemma IsModular.of_isModular_sup_of_le (h : IsModular a b) (h' : IsModular c (a ⊔ b))
    (h'' : c ⊓ (a ⊔ b) ≤ a) : IsModular (c ⊔ a) b := by
  intro d le
  convert_to ((a ⊔ d) ⊔ c) ⊓ (a ⊔ b) ⊓ b ≤ d ⊔ (c ⊔ a) ⊓ b
  · rw[inf_assoc, inf_comm (a ⊔ b) b, sup_comm a b, inf_sup_self]
    congr 1
    rw[← sup_right_comm, sup_comm, sup_comm a c]
  · rw[h'.eq _ (sup_le_sup_left le _)]
    convert_to (a ⊔ d) ⊓ b ≤ d ⊔ (c ⊔ a) ⊓ b using 2
    · rw[sup_eq_left]
      apply h''.trans
      apply le_sup_left
    · rw[sup_comm, h.eq _ le]
      gcongr
      simp
/-- Lemma 1.6a dual -/
lemma IsDualModular.of_isDualModular_inf_of_le : (h : IsDualModular a b) →
    (h' : IsDualModular c (a ⊓ b)) →
    (h'' : a ≤ c ⊔ (a ⊓ b)) → IsDualModular (c ⊓ a) b := by
  rw[← toDual_isModular_iff_dualModular, ← toDual_isModular_iff_dualModular, ← toDual_isModular_iff_dualModular]
  simp only [toDual_inf]
  apply IsModular.of_isModular_sup_of_le
/-- Lemma 1.6b -/
lemma IsModular.inf_sup_eq_inf (h' : IsModular c (a ⊔ b))
    (h'' : c ⊓ (a ⊔ b) ≤ a) : (c ⊔ a) ⊓ b = a ⊓ b := by
  convert_to (a ⊔ c) ⊓ (a ⊔ b) ⊓ b = _
  · rw[inf_assoc, inf_comm (a ⊔ b) b, sup_comm a b, inf_sup_self, sup_comm]
  · rw[h'.eq a le_sup_left, sup_of_le_left h'']
/-- Lemma 1.6b dual -/
lemma IsDualModular.sup_inf_eq_sup : (h' : IsDualModular c (a ⊓ b)) →
    (h'' : a ≤ c ⊔ (a ⊓ b)) → (c ⊓ a) ⊔ b = a ⊔ b := by
  rw[← toDual_isModular_iff_dualModular]
  simp only [toDual_inf]
  apply IsModular.inf_sup_eq_inf

end Lattice

section
variable {α : Type*} [Lattice α] {a b c d : α}
/-- more or less Def 1.7 -/
theorem pair_modular [IsModularLattice α] (a b : α) : Lattice.IsModular a b :=
  fun _ le => IsModularLattice.sup_inf_le_assoc_of_le a le

/-- more or less Def 1.7, "By"... -/
theorem pair_dualModular [IsModularLattice α] : Lattice.IsDualModular a b :=
  (Lattice.isModular_all_iff_isDualModular_all (a := a)).mp (fun b => pair_modular a b) b
/-- more or less Def 1.7 -/
def isModularLattice_of_all_isModular (h : ∀ a b : α, Lattice.IsModular a b) : IsModularLattice α where
  sup_inf_le_assoc_of_le _ _ := h _ _ _


theorem OrderIso.isModular_iff {β : Type*} [Lattice β] (f : α ≃o β) {a a' : α} : Lattice.IsModular (f a) (f a') ↔ Lattice.IsModular a a' := by
  unfold Lattice.IsModular
  constructor
  · intro h c le
    specialize h (f c) (by gcongr)
    rwa[← f.map_inf, ← f.map_sup, ← f.map_inf, ← f.map_sup, f.le_iff_le] at h
  · intro h c le
    obtain ⟨c', rfl⟩ := f.surjective c
    rw[← f.map_inf, ← f.map_sup, ← f.map_inf, ← f.map_sup, f.le_iff_le]
    apply h
    rwa[← f.le_iff_le]

namespace Lattice
variable {β : Type*} [Lattice β] {ι : Type*} {α' : ι → Type*} [(i : ι) → Lattice (α' i)]
-- TODO small prods and a couple other equivalences like for typeclasses
/-- Lemma 1.16 -/
lemma IsModular.pi_iff {a b : (i : ι) → α' i} : IsModular a b ↔ ∀ i, IsModular (a i) (b i) := by
  unfold IsModular
  constructor
  · intro h i c le
    classical
    specialize h (Function.update b i c)
    have : (Function.update b i c) ≤ b := by
      intro j
      by_cases h : i = j
      · rcases h; simp[le]
      · have : j ≠ i := Ne.symm h
        simp[this]
    specialize h this i
    simpa using h
  · intro h c le i
    simp only [Pi.inf_apply, Pi.sup_apply]
    apply h _ _ (le i)
/-- Lemma 1.16 -/
lemma IsModular.pair_iff {a a' : α} {b b' : β} : IsModular (a,b) (a',b') ↔ IsModular a a' ∧ IsModular b b' := by
  unfold IsModular
  rw[Prod.forall]
  constructor
  · intro h
    constructor
    · intro c le
      specialize h c b' ⟨le, le_rfl⟩
      exact h.1
    · intro c le
      specialize h a' c ⟨le_rfl, le⟩
      exact h.2
  · intro ⟨h1,h2⟩ a1 b2 ⟨le1,le2⟩
    exact ⟨h1 _ le1, h2 _ le2⟩
/-- Lemma 1.16 -/
lemma IsDualModular.pair_iff {a a' : α} {b b' : β} : IsDualModular (a,b) (a',b') ↔ IsDualModular a a' ∧ IsDualModular b b' := by
  unfold IsDualModular
  rw[Prod.forall]
  constructor
  · intro h
    constructor
    · intro c le
      specialize h c b' ⟨le, le_rfl⟩
      exact h.1
    · intro c le
      specialize h a' c ⟨le_rfl, le⟩
      exact h.2
  · intro ⟨h1,h2⟩ a1 b2 ⟨le1,le2⟩
    exact ⟨h1 _ le1, h2 _ le2⟩

instance [IsModularLattice α] [IsModularLattice β] : IsModularLattice (α × β) := by
  apply isModularLattice_of_all_isModular
  intro ⟨a,b⟩ ⟨a',b'⟩
  rw[IsModular.pair_iff]
  exact ⟨pair_modular _ _, pair_modular _ _⟩

theorem IsModularLattice.prod_iff [hα : Nonempty α] [hβ : Nonempty β] : IsModularLattice (α × β) ↔ IsModularLattice α ∧ IsModularLattice β := by
  constructor
  · intro h
    constructor
    · apply isModularLattice_of_all_isModular
      intro a a'
      have := pair_modular (a, hβ.some) (a', hβ.some)
      rw[IsModular.pair_iff] at this
      exact this.1
    · apply isModularLattice_of_all_isModular
      intro b b'
      have := pair_modular (hα.some, b) (hα.some, b')
      rw[IsModular.pair_iff] at this
      exact this.2
  · intro ⟨h1,h2⟩
    infer_instance

lemma IsDualModular.pi_iff {a b : (i : ι) → α' i} : IsDualModular a b ↔ ∀ i, IsDualModular (a i) (b i) := by
  unfold IsDualModular
  constructor
  · intro h i c le
    classical
    specialize h (Function.update b i c)
    have : b ≤ (Function.update b i c) := by
      intro j
      by_cases h : i = j
      · rcases h; simp[le]
      · have : j ≠ i := Ne.symm h
        simp[this]
    specialize h this i
    simpa using h
  · intro h c le i
    simp only [Pi.inf_apply, Pi.sup_apply]
    apply h _ _ (le i)

instance IsModularLattice.pi [(i : ι) → IsModularLattice (α' i)] : IsModularLattice ((i : ι) → α' i) := by
   apply isModularLattice_of_all_isModular
   intro a b
   rw[IsModular.pi_iff]
   intro i
   apply pair_modular

end Lattice
end
