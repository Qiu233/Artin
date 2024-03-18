import Mathlib
import Artin.Partition
import Artin.Group.Basic

instance cmul_left [Group G] : HMul G (Subgroup G) (Set G) where
  hMul a H := {a * h | h ∈ H}
instance cmul_right [Group G] : HMul (Subgroup G) G (Set G) where
  hMul H a := {h * a | h ∈ H}

namespace Coset

variable [Group G] [Group G'] {H : Subgroup G}

@[simp]
theorem mem_left_coset {H : Subgroup G} {x : G} : x ∈ x * H := by
  simp [cmul_left]
  exact H.one_mem'

@[simp]
theorem mem_right_coset {H : Subgroup G} {x : G} : x ∈ H * x := by
  simp [cmul_right]
  exact H.one_mem'

@[simp]
theorem one_cmul {H : Subgroup G} : (1 : G) * H = H := by
  simp [cmul_left, Set.ext_iff]

@[simp]
theorem cmul_one {H : Subgroup G} : H * (1 : G) = H := by
  simp [cmul_right, Set.ext_iff]

theorem left_coset_order' {H : Subgroup G} (o : Fin n ≃ H) :
  ∀ a : G, Fin n ≃ (a * H) := by
  intro a
  apply Equiv.trans (β := H) o
  let t : H → a * H := λ x => ⟨a * x, by simp [cmul_left]⟩
  let t' : a * H → H := λ y => ⟨a⁻¹ * y, ?_⟩
  . apply Equiv.mk t t'
    . unfold Function.LeftInverse; simp
    . unfold Function.RightInverse Function.LeftInverse; simp
  . have ⟨h, hh⟩ := y.2
    rw [← hh.2, ← mul_assoc, mul_left_inv, one_mul]
    exact hh.1

theorem right_coset_order' {H : Subgroup G} (o : Fin n ≃ H) :
  ∀ a : G, Fin n ≃ (H * a) := by
  intro a
  apply Equiv.trans (β := H) o
  let t : H → H * a := λ x => ⟨x * a, by simp [cmul_right]⟩
  let t' : H * a → H := λ y => ⟨y * a⁻¹, ?_⟩
  . apply Equiv.mk t t'
    . unfold Function.LeftInverse; simp
    . unfold Function.RightInverse Function.LeftInverse; simp
  . have ⟨h, hh⟩ := y.2
    rw [← hh.2, mul_assoc, mul_right_inv, mul_one]
    exact hh.1

private lemma left_coset_eq_of_inter' {H : Subgroup G} {a b : G} :
    (∃ t, t ∈ a * H ∧ t ∈ b * H) → a * H = b * H := by
  have {a b : G} : (∃ t, t ∈ a * H ∧ t ∈ b * H) → a * H ⊆ b * H := by
    intro ⟨t, ht⟩
    simp [cmul_left] at ht
    intro x ⟨c, hc⟩
    simp [← hc.2]
    use (b⁻¹ * a * c)
    apply And.intro ?_
    . simp [mul_assoc]
    . apply mul_mem ?_ hc.1
      obtain ⟨⟨ta, hta⟩, ⟨tb, htb⟩⟩:= ht
      have ha : a = t * ta⁻¹ := by
        apply mul_right_cancel (b := ta)
        simp [hta.2]
      have hb : b = t * tb⁻¹ := by
        apply mul_right_cancel (b := tb)
        simp [htb.2]
      simp [ha, hb, ← mul_assoc]
      apply mul_mem htb.1 (inv_mem hta.1)
  intro h
  have fa := this h
  conv at h =>
    congr; intro t
    rw [And.comm]
  have fb := this h
  apply Set.eq_of_subset_of_subset fa fb

private lemma right_coset_eq_of_inter' {H : Subgroup G} {a b : G} :
    (∃ t, t ∈ H * a ∧ t ∈ H * b) → H * a = H * b := by
  have {a b : G} : (∃ t, t ∈ H * a ∧ t ∈ H * b) → H * a ⊆ H * b := by
    intro ⟨t, ht⟩
    simp [cmul_right] at ht
    intro x ⟨c, hc⟩
    simp [← hc.2]
    use (c * a * b⁻¹)
    apply And.intro ?_
    . simp
    . rw [mul_assoc]
      apply mul_mem hc.1
      obtain ⟨⟨ta, hta⟩, ⟨tb, htb⟩⟩:= ht
      have ha : a = ta⁻¹ * t := by
        apply mul_left_cancel (a := ta)
        simp [hta.2]
      have hb : b = tb⁻¹ * t := by
        apply mul_left_cancel (a := tb)
        simp [htb.2]
      simp [ha, hb, ← mul_assoc]
      apply mul_mem (inv_mem hta.1) htb.1
  intro h
  have fa := this h
  conv at h =>
    congr; intro t
    rw [And.comm]
  have fb := this h
  apply Set.eq_of_subset_of_subset fa fb

def left_cosets (H : Subgroup G) : Partition G := ⟨{a * H | a : G}, p1, p2⟩ where
  p1 a ha b hb h h' := by
    apply h
    obtain ⟨ta, hta⟩ := ha
    obtain ⟨tb, htb⟩ := hb
    rw [← hta, ← htb] at h'
    rw [← hta, ← htb]
    apply left_coset_eq_of_inter' h'
  p2 := by
    ext x
    simp
    use x, 1
    simp
    apply H.one_mem'

def right_cosets (H : Subgroup G) : Partition G := ⟨{H * a | a : G}, p1, p2⟩ where
  p1 a ha b hb h h' := by
    apply h
    obtain ⟨ta, hta⟩ := ha
    obtain ⟨tb, htb⟩ := hb
    rw [← hta, ← htb]
    rw [← hta, ← htb] at h'
    apply right_coset_eq_of_inter' h'
  p2 := by
    ext x
    simp
    use x, 1
    simp
    apply H.one_mem'

theorem subgroup_mem_left_cosets {H : Subgroup G} : H.carrier ∈ (left_cosets H) := by
  use 1
  simp [left_cosets, Set.ext_iff]

theorem left_coset_eq_of_inter {H : Subgroup G} {x y : Set G}
  (ha : x ∈ (left_cosets H)) (hb : y ∈ (left_cosets H)) :
    (∃ t, t ∈ x ∧ t ∈ y) → x = y := by
  intro h
  simp [left_cosets] at ha hb
  have ⟨ta, hta⟩ := ha
  have ⟨tb, htb⟩ := hb
  rw [← hta, ← htb] at h
  rw [← hta, ← htb]
  apply left_coset_eq_of_inter' h

theorem right_coset_eq_of_inter {H : Subgroup G} {x y : Set G}
  (ha : x ∈ (right_cosets H)) (hb : y ∈ (right_cosets H)) :
    (∃ t, t ∈ x ∧ t ∈ y) → x = y := by
  intro h
  simp [right_cosets] at ha hb
  have ⟨ta, hta⟩ := ha
  have ⟨tb, htb⟩ := hb
  rw [← hta, ← htb] at h
  rw [← hta, ← htb]
  apply right_coset_eq_of_inter' h

theorem left_cosets_elem_order {H : Subgroup G} (o : Fin n ≃ H) (c : Set G) (h : c ∈ (left_cosets H)) :
  Fin n ≃ c := by
  simp [left_cosets] at h
  rw [← h.choose_spec]
  apply left_coset_order' o

theorem right_cosets_elem_order {H : Subgroup G} (o : Fin n ≃ H) (c : Set G) (h : c ∈ (right_cosets H)) :
  Fin n ≃ c := by
  simp [right_cosets] at h
  rw [← h.choose_spec]
  apply right_coset_order' o

theorem cmul_left_by_member {H : Subgroup G} :
  A ∈ (left_cosets H) → ∀ a ∈ A, a * H = A := by
  intro h a ha
  have : a * H ∈ (left_cosets H) := by
    simp [left_cosets]
  apply left_coset_eq_of_inter this h
  use a
  exact And.intro (mem_left_coset) ha

theorem cmul_right_by_member {H : Subgroup G} :
  A ∈ (right_cosets H) → ∀ a ∈ A, H * a = A := by
  intro h a ha
  have : H * a ∈ (right_cosets H) := by
    simp [right_cosets]
  apply right_coset_eq_of_inter this h
  use a
  exact And.intro (mem_right_coset) ha

theorem left_coset_iff_genby {H : Subgroup G} {S : Set G} :
    S ∈ (left_cosets H).1 ↔ ∃ a ∈ S, a * H = S := by
  apply Iff.intro
  . intro ⟨a, ha⟩
    use a
    apply And.intro ?_ ha
    simp [cmul_left, Set.ext_iff] at ha
    apply (ha a).mp
    use 1
    apply And.intro (H.one_mem') (mul_one a)
  . intro ⟨a, ha⟩
    use a
    exact ha.2

theorem right_coset_iff_genby {H : Subgroup G} {S : Set G} :
    S ∈ (right_cosets H) ↔ ∃ a ∈ S, H * a = S := by
  apply Iff.intro
  . intro ⟨a, ha⟩
    use a
    apply And.intro ?_ ha
    simp [cmul_right, Set.ext_iff] at ha
    apply (ha a).mp
    use 1
    apply And.intro (H.one_mem') (one_mul a)
  . intro ⟨a, ha⟩
    use a
    exact ha.2

open Cardinal in
/--Lemma 2.8.7-/
theorem left_cosets_equipotent {H : Subgroup G} {x y : Set G} :
    (x ∈ (left_cosets H)) → (y ∈ (left_cosets H)) → #x = #y := by
  intro hx hy
  simp [left_coset_iff_genby] at hx hy
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  simp [Cardinal.eq, ← ha.2, ← hb.2]
  let t : a * H → b * H := λ t => ⟨b * (a⁻¹ * t), by
    have ⟨h, h'⟩ := t.2
    simp [← h'.2, cmul_left, h'.1]
    ⟩
  have inj : Function.Injective t := by simp [Function.Injective]
  have surj : Function.Surjective t := by
    simp [Function.Surjective]
    intro y ⟨h, hy⟩
    use (a * b⁻¹ * y)
    apply And.intro <;> simp [mul_assoc, cmul_left, ← hy.2, hy.1]
  exact Nonempty.intro $ Equiv.ofBijective t ⟨inj, surj⟩

private lemma subgroup_divides_G_left_aux {H : Subgroup G} :
    Fin n ≃ H → Fin m ≃ (left_cosets H).partitions → Fin (m * n) ≃ G := by
  intro h2 h3
  have := left_coset_order' (H := H) h2
  have : ∀ x ∈ (left_cosets H), Fin n ≃ x := by
    intro x hx
    simp [left_cosets] at hx
    rw [← hx.choose_spec]
    apply this
  exact Partition.join_finite_uniform (p := left_cosets H) h3 this

private lemma Fin.eq_of_equiv : (Fin m ≃ Fin n) → m = n := by
  intro h
  have fm : m = Nat.card (Fin m) := by simp
  have fn : n = Nat.card (Fin n) := by simp
  rw [fm, fn]
  apply Nat.card_congr h

/--Theorem 2.8.9-/
theorem subgroup_divides_G_left {H : Subgroup G} :
    Fin k ≃ G → Fin n ≃ H → Fin m ≃ (left_cosets H).partitions → k = m * n := by
  intro h1 h2 h3
  have := subgroup_divides_G_left_aux h2 h3
  have := Equiv.trans this h1.symm
  apply Fin.eq_of_equiv
  exact this.symm

end Coset
