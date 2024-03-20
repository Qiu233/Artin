import Mathlib
import Artin.Group.Homo
import Artin.Group.Iso
import Artin.Group.Coset

namespace Group

variable [Group G] [Group G']
variable {H K : Subgroup G}

def f (H K : Subgroup G) (a : Subgroup.prod H K) : G := a.1.1 * a.1.2

/--Proposition 2.11.4 (a)-/
theorem f_injective_iff_inter_trivial : Function.Injective (f H K) ↔ H.carrier ∩ K.carrier = {1} := by
  unfold f
  apply Iff.intro
  . intro h
    ext x
    simp
    unfold Function.Injective at h
    apply Iff.intro
    . intro hx
      apply not_not.mp
      intro hn
      let a₁ : Subgroup.prod H K := ⟨⟨x, 1⟩, by
        simp [Subgroup.prod, Submonoid.prod]
        apply And.intro hx.1 K.one_mem
        ⟩
      let a₂ : Subgroup.prod H K := ⟨⟨1, x⟩, by
        simp [Subgroup.prod, Submonoid.prod]
        apply And.intro H.one_mem hx.2
        ⟩
      have := h (a₁ := a₁) (a₂ := a₂)
      simp at this
      apply absurd this.1 hn
    . intro h
      rw [h]
      apply And.intro H.one_mem K.one_mem
  . intro h
    intro x y
    simp
    intro h'
    rw [Subtype.ext_iff, Prod.ext_iff]
    have collected : y.1.1⁻¹ * x.1.1 = y.1.2 * x.1.2⁻¹ := by
      apply mul_right_cancel (b := x.1.2)
      simp
      apply mul_left_cancel (a := y.1.1)
      rw [← mul_assoc]
      rw [← mul_assoc]
      simp [h']
    have l1 : y.1.1⁻¹ * x.1.1 ∈ H.carrier := by
      apply H.mul_mem
      . apply H.inv_mem
        simp [Subgroup.mem_prod.mp y.2]
      . simp [Subgroup.mem_prod.mp x.2]
    have l2 : y.1.2 * x.1.2⁻¹ ∈ K.carrier := by
      apply K.mul_mem
      . simp [Subgroup.mem_prod.mp y.2]
      . apply K.inv_mem
        simp [Subgroup.mem_prod.mp x.2]
    rw [collected] at l1
    have K_id : y.1.2 * x.1.2⁻¹ = 1 := by
      rw [Set.ext_iff] at h
      have h := h (y.1.2 * x.1.2⁻¹) |>.mp
      simp at h
      exact h l1 l2
    have : y.1.2 = x.1.2 := by
      apply mul_right_cancel (b := x.1.2⁻¹)
      simp
      exact K_id
    simp [this]
    rw [K_id] at collected
    apply mul_left_cancel (a := y.1.1⁻¹)
    simp [collected]

/--Proposition 2.11.4 (b)-/
theorem f_homo_iff_HK_comm : Homomorphism (f H K) ↔ ∀ h ∈ H, ∀ k ∈ K, h * k = k * h := by
  apply Iff.intro
  . intro ⟨homo⟩ h hh k hk
    unfold f at homo
    let x : Subgroup.prod H K := ⟨(1, k), by simp [Subgroup.prod, Submonoid.prod, hk, H.one_mem]⟩
    let y : Subgroup.prod H K := ⟨(h, 1), by simp [Subgroup.prod, Submonoid.prod, hh, K.one_mem]⟩
    have := homo x y
    simp at this
    exact this
  . intro comm
    apply Homomorphism.mk
    intro x y
    simp [f]
    rw [mul_assoc]
    rw [← mul_assoc y.1.1]
    rw [← mul_assoc]
    have := comm y.1.1 ?_ x.1.2 ?_
    rw [this]
    repeat rw [← mul_assoc]
    . simp [Subgroup.mem_prod.mp y.2]
    . simp [Subgroup.mem_prod.mp x.2]

/--Proposition 2.11.4 (c)-/
def HK_subgroup_of_normal_H (H K : Subgroup G) {normal : Subgroup.Normal H} : Subgroup G where
  carrier := {h * k | (h ∈ H) (k ∈ K)}
  mul_mem' {x y} hx hy := by
    obtain ⟨normal⟩ := normal
    simp at *
    obtain ⟨hx, hhx, kx, hkx, hx'⟩ := hx
    obtain ⟨hy, hhy, ky, hky, hy'⟩ := hy
    rw [← hx', ← hy']
    have : ∃ hy' ∈ H, kx⁻¹ * hy' * kx = hy := by
      use kx * hy * kx⁻¹
      apply And.intro ?_
      . simp [mul_assoc]
      . apply normal hy hhy
    obtain ⟨hz, hhz⟩ := this
    rw [← hhz.2]
    repeat rw [mul_assoc]
    rw [← mul_assoc kx]
    simp
    rw [← mul_assoc hx]
    use hx * hz
    apply And.intro
    . apply H.mul_mem hhx hhz.1
    . use kx * ky
      apply And.intro
      . apply K.mul_mem hkx hky
      . simp
  one_mem' := by
    simp
    use 1
    simp [H.one_mem, K.one_mem]
  inv_mem' {x} hx := by
    simp at *
    obtain ⟨h, hh, k, hk, h'⟩ := hx
    rw [← h']
    simp
    have : ∃ h' ∈ H, k * h' * k⁻¹ = h := by
      use k⁻¹ * h * k
      apply And.intro
      . have := normal.1 h hh k⁻¹
        simp at this
        exact this
      . simp [mul_assoc]
    obtain ⟨z, hz⟩ := this
    rw [← hz.2]
    simp
    use z⁻¹
    simp [H.inv_mem, hz.1, hk]

lemma f_iso_iff_mp_normal_H : Isomorphism (f H K) → Subgroup.Normal H := by
  intro iso
  have linear := iso.linear
  have bij := iso.bijective
  apply Subgroup.Normal.mk
  intro h hh g
  have := bij.2 g
  simp [f, Subgroup.prod, Submonoid.prod] at this
  obtain ⟨h', k', h''⟩ := this
  rw [← h''.2]
  simp
  rw [mul_assoc]
  rw [mul_assoc]
  rw [← mul_assoc h]
  rw [← mul_assoc k']
  rw [← mul_assoc k']
  apply H.mul_mem h''.1.1
  apply H.mul_mem ?_ (H.inv_mem h''.1.1)
  let x : Subgroup.prod H K := ⟨(1, k'), by simp [Subgroup.prod, Submonoid.prod, h''.1.2, H.one_mem]⟩
  let y : Subgroup.prod H K := ⟨(h, k'⁻¹), by simp [Subgroup.prod, Submonoid.prod, h''.1.2, hh]⟩
  have := linear x y
  simp [f, ← mul_assoc] at this
  simp [← this, hh]

lemma f_iso_iff_mp_normal_K : Isomorphism (f H K) → Subgroup.Normal K := by
  intro iso
  have linear := iso.linear
  have bij := iso.bijective
  apply Subgroup.Normal.mk
  intro k hk g
  have := bij.2 g⁻¹
  simp [f, Subgroup.prod, Submonoid.prod] at this
  obtain ⟨h', k', k''⟩ := this
  have g_eq : g = (h' * k')⁻¹ := inv_eq_iff_eq_inv.mp k''.2.symm
  simp [g_eq]
  rw [mul_assoc]
  rw [mul_assoc]
  rw [← mul_assoc k]
  rw [← mul_assoc h'⁻¹]
  rw [← mul_assoc h'⁻¹]
  apply K.mul_mem (K.inv_mem k''.1.2)
  apply K.mul_mem ?_ k''.1.2
  let x : Subgroup.prod H K := ⟨(h'⁻¹, k), by simp [Subgroup.prod, Submonoid.prod, k''.1.1, hk]⟩
  let y : Subgroup.prod H K := ⟨(h', 1), by simp [Subgroup.prod, Submonoid.prod, k''.1.1, K.one_mem]⟩
  have := linear x y
  simp [f, ← mul_assoc] at this
  simp [← this, hk]

lemma f_iso_iff_mp : Isomorphism (f H K) →
    (H.carrier ∩ K.carrier = {1} ∧
    {h * k | (h ∈ H) (k ∈ K)} = Set.univ ∧
    Subgroup.Normal H ∧ Subgroup.Normal K) := by
  intro iso
  have bij := iso.bijective
  refine ⟨?inter, ?univ, ?normal_H, ?normalK⟩
  . exact f_injective_iff_inter_trivial.mp bij.1
  . ext x
    simp
    have := bij.2 x
    simp [f, Subgroup.prod, Submonoid.prod] at this
    obtain ⟨h, k, h'⟩ := this
    use h
    simp [h'.1.1]
    use k
    simp [h'.1.2, h'.2]
  . exact f_iso_iff_mp_normal_H iso
  . exact f_iso_iff_mp_normal_K iso

/-
Note: G's two subgroups H and K's elements h and k commute: `h * k = k * h`,
when both H and K are normal and there is an injective map `f : H × K → G`.
This is also enough to prove that `f` is a homomorphism.
-/
lemma HK_comm_of_inj_of_normal (inj : Function.Injective (f H K)) :
    Subgroup.Normal H →
    Subgroup.Normal K →
    ∀ h ∈ H, ∀ k ∈ K, h * k = k * h := by
  intro normal_H normal_K
  intro h hh k hk
  have hk_prod : h * K ∩ (H * k) = {h * k} := by
    ext x
    simp [cmul_left, cmul_right]
    apply Iff.intro
    . intro ⟨⟨k1, hk1⟩, ⟨h1, hh1⟩⟩
      let u : Subgroup.prod H K := ⟨(h, k1), by simp [Subgroup.prod,Submonoid.prod,hh,hk1]⟩
      let v : Subgroup.prod H K := ⟨(h1, k), by simp [Subgroup.prod,Submonoid.prod,hk,hh1]⟩
      have := inj (a₁ := u) (a₂ := v)
      simp [f, hk1.2, hh1.2] at this
      rw [this.1, hh1.2]
    . intro hypo
      simp [hypo, hk, hh]
  have kh_prod : k * H ∩ (K * h) = {k * h} := by
    ext x
    simp [cmul_left, cmul_right]
    apply Iff.intro
    . intro ⟨⟨h1, hh1⟩, ⟨k1, hk1⟩⟩
      let u : Subgroup.prod H K := ⟨(h⁻¹, k1⁻¹), by simp [Subgroup.prod,Submonoid.prod,hh,hk1]⟩
      let v : Subgroup.prod H K := ⟨(h1⁻¹, k⁻¹), by simp [Subgroup.prod,Submonoid.prod,hk,hh1]⟩
      have := inj (a₁ := u) (a₂ := v)
      simp [f] at this
      rw [← mul_inv_rev, ← mul_inv_rev, hk1.2, hh1.2] at this
      simp at this
      rw [this.1, hh1.2]
    . intro hypo
      simp [hypo, hk, hh]
  rw [← Coset.left_coset_eq_right_coset_of_normal normal_H k] at hk_prod
  rw [← Coset.left_coset_eq_right_coset_of_normal normal_K h] at kh_prod
  rw [Set.inter_comm] at kh_prod
  have hk_eq_kh := Eq.trans hk_prod.symm kh_prod
  simp at hk_eq_kh
  exact hk_eq_kh

lemma f_iso_iff_mpr :
    H.carrier ∩ K.carrier = {1} →
    {h * k | (h ∈ H) (k ∈ K)} = Set.univ →
    Subgroup.Normal H →
    Subgroup.Normal K →
    Isomorphism (f H K) := by
  intro inter univ normal_H normal_K
  have inj : Function.Injective (f H K) := f_injective_iff_inter_trivial.mpr inter
  have surj : Function.Surjective (f H K) := by
    intro g
    rw [Set.ext_iff] at univ
    have := univ g |>.mpr
    simp at this
    obtain ⟨h, hh, k, hk, h'⟩ := this
    let x : Subgroup.prod H K := ⟨(h, k), by simp [Subgroup.prod, Submonoid.prod, hh, hk]⟩
    use x
    simp [f, h']
  have homo : Homomorphism (f H K) := by
    rw [f_homo_iff_HK_comm]
    exact HK_comm_of_inj_of_normal inj normal_H normal_K
  apply Isomorphism.mk ⟨inj, surj⟩

/--Proposition 2.11.4 (d)-/
theorem f_iso_iff : Isomorphism (f H K) ↔
    (H.carrier ∩ K.carrier = {1} ∧
    {h * k | (h ∈ H) (k ∈ K)} = Set.univ ∧
    Subgroup.Normal H ∧ Subgroup.Normal K) :=
  ⟨f_iso_iff_mp, fun ⟨h1, h2, h3, h4⟩ => f_iso_iff_mpr h1 h2 h3 h4⟩

end Group
