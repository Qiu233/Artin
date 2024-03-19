import Mathlib
import Artin.Partition
import Artin.Group.Basic

namespace Group

namespace Coset
variable {G : Type u}
variable [Group G] [Group G'] {H : Subgroup G}

@[simp]
theorem mem_cmul_left {a : G} : a ∈ a * H := by
  simp [cmul_left]
  exact H.one_mem'

@[simp]
theorem one_cmul {H : Subgroup G} : (1 : G) * H = H := by
  simp [cmul_left, Set.ext_iff]

@[reducible, simp]
abbrev left_cosets (H : Subgroup G) := {a * H | a : G}

theorem left_cosets_eq_of_inter {x y : Set G} {u : G} :
    x ∈ left_cosets H → y ∈ left_cosets H → u ∈ x → u ∈ y → x = y := by
  have {x y u} : x ∈ left_cosets H → y ∈ left_cosets H → u ∈ x → u ∈ y → x ⊆ y := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hux huy
    simp [← ha, ← hb] at *
    intro t ⟨ta, ht⟩
    rw [← ht.2]
    obtain ⟨ua, hua⟩ := hux
    obtain ⟨ub, hub⟩ := huy
    simp [cmul_left]
    use (b⁻¹ * a * ta)
    apply And.intro
    . apply H.mul_mem' ?_ ht.1
      have ha : a = u * ua⁻¹ := by
        apply mul_right_cancel (b := ua)
        simp [hua.2]
      have hb : b = u * ub⁻¹ := by
        apply mul_right_cancel (b := ub)
        simp [hub.2]
      simp [ha, hb, mul_assoc]
      apply H.mul_mem' hub.1 (H.inv_mem' hua.1)
    . simp [mul_assoc]
  intro hx hy hux huy
  apply Set.eq_of_subset_of_subset (this hx hy hux huy) (this hy hx huy hux)

private theorem left_cosets_all_nonempty : ∀ cs ∈ left_cosets H, Set.Nonempty cs := by
  intro s ⟨a, ha⟩
  simp [Set.Nonempty]
  use a
  simp [← ha, cmul_left]
  exact H.one_mem'

def indexer_left : left_cosets H → Set G := (·.1)

noncomputable def left_cosets_partition {H : Subgroup G} : IndexedPartition (indexer_left (H := H)) where
  eq_of_mem {x i j} hx hy := by
    simp [indexer_left] at hx hy i j
    rw [Subtype.ext_iff]
    apply left_cosets_eq_of_inter (H := H) i.2 j.2 hx hy
  some i := by
    have t := Classical.choice (α := i.1) ?_
    exact t.1
    rw [Set.nonempty_coe_sort]
    apply left_cosets_all_nonempty (H := H) i.1 i.2
  some_mem i := by simp [indexer_left]
  index a := ⟨a * H, by simp⟩
  mem_index a := by simp [indexer_left]

open Cardinal

theorem card_of_left_coset (s : Set G) : s ∈ (left_cosets H) → #H = #s := by
  intro ⟨v, hv⟩
  rw [Cardinal.eq]
  let t : H → s := λ x => ⟨v * x, by simp [← hv, cmul_left]⟩
  have inj : Function.Injective t := by simp [Function.Injective]
  have surj : Function.Surjective t := by
    intro y
    use ⟨v⁻¹ * y, ?_⟩
    . simp
    . have := y.2
      simp [← hv, cmul_left] at this
      obtain ⟨h, hh⟩ := this
      simp [← hh.2, hh.1]
  exact Nonempty.intro (Equiv.ofBijective t ⟨inj, surj⟩)

lemma aux_1 {x : (indexer_left (H := H) i)} {y : (indexer_left (H := H) j)} : x.1 = y.1 → HEq x y := by
  intro h
  have := x.2
  rw [h] at this
  have ieqj := left_cosets_partition.eq_of_mem y.2 this |>.symm
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp at h this
  apply HEq.trans (b := ({ val := y, property := this } : { x // x ∈ indexer_left i }))
  . simp [h]
  . congr
    . ext t; revert t
      rw [← Set.ext_iff]
      rw [ieqj]
    . simp [ieqj]

theorem card_decomp_dep (H : Subgroup G) : #((i : left_cosets H) × (indexer_left i)) = #G := by
  rw [Cardinal.eq]
  let t : (i : ↑(left_cosets H)) × ↑(indexer_left i) → G := λ h => h.2.1
  have inj : Function.Injective t := by
    rw [Function.Injective]
    intro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp at h
    have := hy.2
    rw [← h] at this
    have := left_cosets_partition.eq_of_mem hx.2 this
    simp [Sigma.ext_iff, this]
    exact aux_1 h
  have surj : Function.Surjective t := by
    intro y
    let a : ((i : ↑(left_cosets H)) × (↑(indexer_left i))) :=
      Sigma.mk
        ((left_cosets_partition (H := H)).index y)
        ⟨y, by simp [indexer_left, left_cosets_partition]⟩
    use a
  exact Nonempty.intro (Equiv.ofBijective t ⟨inj, surj⟩)

theorem card_decomp_eq_dep (H : Subgroup G) : #(left_cosets H) * #H = #((i : left_cosets H) × (indexer_left i)) := by
  rw [Cardinal.mk_sigma]
  conv =>
    rhs
    rhs
    intro i
    rw [← card_of_left_coset (H := H) _ (by exact i.2)]
  rw [Cardinal.sum_const]
  simp

theorem card_decomp (H : Subgroup G) : #(left_cosets H) * #H = #G := by
  rw [card_decomp_eq_dep]
  exact card_decomp_dep H

end Coset

end Group
