import Mathlib
import Artin.Partition
import Artin.Group.Basic

namespace Coset

variable [Group G] [Group G']

theorem left_coset_order {H : Subgroup G} (o : Fin n ≃ H) :
  ∀ a : G, Fin n ≃ (a * H) := by
  intro a
  apply Equiv.trans (β := H) o
  let t : H → a * H := λ x => ⟨a * x, by simp⟩
  let t' : a * H → H := λ y => ⟨a⁻¹ * y, ?_⟩
  . apply Equiv.mk t t'
    . unfold Function.LeftInverse; simp
    . unfold Function.RightInverse Function.LeftInverse; simp
  . have ⟨h, hh⟩ := y.2
    rw [← hh.2, ← mul_assoc, mul_left_inv, one_mul]
    exact hh.1

private lemma left_coset_eq_of_inter' {H : Subgroup G} {a b : G} :
    (∃ t, t ∈ a * H ∧ t ∈ b * H) → a * H = b * H := by
  intro h
  ext x
  unfold HMul.hMul Group.instHMulSubgroupSet at *
  simp
  constructor
  . intro ⟨t, ht⟩
    use (b⁻¹ * a * t)
    constructor
    . apply H.mul_mem' ?_ ht.1
      obtain ⟨u, ⟨hua, hub⟩⟩ := h
      simp at hua hub
      obtain ⟨ta, hta⟩ := hua
      obtain ⟨tb, htb⟩ := hub
      rw [(?_ : a = u * ta⁻¹)]
      rw [(?_ : b = u * tb⁻¹)]
      simp
      rw [mul_assoc]
      rw [← mul_assoc u⁻¹]
      simp
      apply H.mul_mem' htb.1
      simp
      exact hta.1
      . apply mul_right_cancel (b := tb)
        simp
        exact htb.2
      . apply mul_right_cancel (b := ta)
        simp
        exact hta.2
    . rw [← mul_assoc]
      rw [← mul_assoc]
      simp
      exact ht.2
  . intro ⟨t, ht⟩
    use (a⁻¹ * b * t)
    constructor
    . apply H.mul_mem' ?_ ht.1
      obtain ⟨u, ⟨hua, hub⟩⟩ := h
      simp at hua hub
      obtain ⟨ta, hta⟩ := hua
      obtain ⟨tb, htb⟩ := hub
      rw [(?_ : a = u * ta⁻¹)]
      rw [(?_ : b = u * tb⁻¹)]
      simp
      rw [mul_assoc]
      rw [← mul_assoc u⁻¹]
      simp
      apply H.mul_mem' hta.1
      simp
      exact htb.1
      . apply mul_right_cancel (b := tb)
        simp
        exact htb.2
      . apply mul_right_cancel (b := ta)
        simp
        exact hta.2
    . rw [← mul_assoc]
      rw [← mul_assoc]
      simp
      exact ht.2

def left_cosets (H : Subgroup G) : Partition G := ⟨{a * H | a : G}, p1, p2⟩ where
  p1 a ha b hb h := by
    intro h'
    apply h
    obtain ⟨ta, hta⟩ := ha
    obtain ⟨tb, htb⟩ := hb
    rw [← hta, ← htb]
    rw [← hta, ← htb] at h'
    apply left_coset_eq_of_inter' h'
  p2 := by
    ext x
    simp
    use x
    use 1
    simp
    apply H.one_mem'

theorem left_coset_eq_of_inter {H : Subgroup G} {x y : (left_cosets H : Set (Set G))} :
    (∃ t, t ∈ x.1 ∧ t ∈ y.1) → x = y := by
  intro h
  have ha := x.2
  have hb := y.2
  unfold left_cosets at ha hb
  simp at ha hb
  have ⟨ta, hta⟩ := ha
  have ⟨tb, htb⟩ := hb
  rw [Subtype.ext_iff]
  rw [← hta, ← htb] at h
  rw [← hta, ← htb]
  apply left_coset_eq_of_inter' h

theorem left_cosets_elem_order {H : Subgroup G} (o : Fin n ≃ H) (c : Set G) (h : c ∈ (left_cosets H : Set (Set G))) :
  Fin n ≃ c := by
  unfold left_cosets at h; simp at h
  let ha := h.choose_spec
  rw [← ha]
  apply left_coset_order o

theorem left_coset_mul_by_self {H : Subgroup G} :
  A ∈ (left_cosets H : Set (Set G)) → ∀ a ∈ A, a * H = A := by
  unfold left_cosets
  intro h a ha
  simp at h
  obtain ⟨t, ht⟩ := h
  rw [← ht]
  simp
  rw [← ht] at ha
  simp at ha
  obtain ⟨h, hh⟩ := ha
  rw [← hh.2]
  ext x
  constructor
  . intro ⟨h', hh'⟩
    simp
    use h * h'
    constructor
    . apply H.mul_mem' hh.1 hh'.1
    . simp [← mul_assoc, hh'.2]
  . intro ⟨h', hh'⟩
    use h⁻¹ * h'
    constructor
    . apply H.mul_mem' (H.inv_mem' hh.1) hh'.1
    . rw [← mul_assoc]
      simp
      exact hh'.2

theorem left_cosets_equipotent {H : Subgroup G} (x y : (left_cosets H : Set (Set G))) : Nonempty (x ≃ y) := by
  have hx := x.2
  have hy := y.2
  unfold left_cosets at hx hy
  simp at hx hy
  have ⟨a, ha⟩ := hx
  have ⟨b, hb⟩ := hy
  let t : x.1 → y.1 := λ t => ⟨b * a⁻¹ * t.1, by
    have := t.2
    conv at this => arg 2; rw [← ha]
    simp at this
    obtain ⟨h, hh⟩ := this
    rw [← hh.2]
    rw [mul_assoc]
    rw [← mul_assoc a⁻¹]
    simp
    conv => arg 2; rw [← hb]
    simp
    exact hh.1
    ⟩
  have inj : Function.Injective t := by
    simp
    intro u v
    simp
    exact Subtype.ext_iff.mpr
  have surj : Function.Surjective t := by
    simp
    intro v
    simp
    use (a * b⁻¹ * v)
    have := v.2
    conv at this => arg 2; rw [← hb]
    simp at this
    obtain ⟨h, hh⟩ := this
    have : a * b⁻¹ * v.1 ∈ x.1 := by
      rw [← hh.2]
      rw [mul_assoc]
      rw [← mul_assoc b⁻¹]
      simp
      rw [← ha]
      simp
      exact hh.1
    use this
    rw [Subtype.ext_iff]
    simp
    rw [mul_assoc]
    rw [← mul_assoc a⁻¹]
    rw [← mul_assoc a⁻¹]
    simp
  exact Nonempty.intro (Equiv.ofBijective t ⟨inj, surj⟩)

private lemma subgroup_divides_aux {H : Subgroup G} :
    Fin n ≃ H → Fin m ≃ (left_cosets H : Set (Set G)) → Fin (m * n) ≃ G := by
  intro h2 h3
  have := left_coset_order (H := H) h2
  have : ∀ x ∈ (left_cosets H : Set (Set G)), Fin n ≃ x := by
    intro x hx
    unfold left_cosets at hx
    simp at hx
    let a := hx.choose
    have ha := hx.choose_spec
    have := this a
    simp at this
    rw [← ha]
    exact this
  exact Partition.join_finite_uniform (p := left_cosets H) h3 this

private lemma Fin.eq_of_equiv : (Fin m ≃ Fin n) → m = n := by
  intro h
  have fm : m = Nat.card (Fin m) := by simp
  have fn : n = Nat.card (Fin n) := by simp
  rw [fm, fn]
  apply Nat.card_congr h

theorem subgroup_divides {H : Subgroup G} :
    Fin k ≃ G → Fin n ≃ H → Fin m ≃ (left_cosets H : Set (Set G)) → k = m * n := by
  intro h1 h2 h3
  have := subgroup_divides_aux h2 h3
  have := Equiv.trans this h1.symm
  apply Fin.eq_of_equiv
  exact this.symm

end Coset
