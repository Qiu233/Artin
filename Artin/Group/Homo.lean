import Mathlib
import Artin.Group.Basic

namespace Group

class Homomorphism {G G' : Type*} [Group G] [Group G'] (ϕ : G → G') :=
  linear : ∀ x y : G, ϕ (x * y) = ϕ x * ϕ y

namespace Homomorphism

variable [g1 : Group G] [g2 : Group G']
variable {ϕ : G → G'} [homo : Homomorphism ϕ]

@[simp] theorem linear_simp {a b : G} : ϕ (a * b) = ϕ a * ϕ b := by
  rw [homo.1]

@[simp] theorem homo_one : ϕ 1 = 1 := by
  have : (1 : G) = 1 * 1 := by simp
  have : ϕ 1 * ϕ 1 = ϕ 1 * 1 := by
    rw [← homo.1 1 1]
    simp
  apply mul_left_cancel this

@[simp] theorem homo_inv (homo: Homomorphism ϕ) : ϕ (a⁻¹) = (ϕ a)⁻¹ := by
  have : ϕ (a * a⁻¹) =  ϕ a * ϕ a⁻¹ := by
    rw [homo.1]
  apply mul_left_cancel (a := ϕ a)
  rw [← this]
  simp

def ker (ϕ : G → G') [Homomorphism ϕ] : Subgroup G where
  carrier := {x | ϕ x = 1}
  mul_mem' {a b} ha hb := by
    simp
    rw [ha, hb]
    simp
  one_mem' := by simp
  inv_mem' {x} := by simp

theorem ker_iff {x : G} : x ∈ ker ϕ ↔ ϕ x = 1 := by unfold ker; simp

theorem one_mem_ker : 1 ∈ ker ϕ := by
  apply ker_iff.mpr
  simp

example {a b : G} : ϕ a = ϕ b → a⁻¹ * b ∈ ker ϕ := by
  intro h
  unfold ker
  simp
  rw [← h]
  simp

theorem ϕeq_iff_mem_coset_ker {a b : G} : ϕ a = ϕ b ↔ b ∈ a * ker ϕ := by
  constructor
  . intro h
    unfold ker
    simp
    use (a⁻¹ * b)
    simp [h]
  . intro h
    unfold ker at h
    simp at h
    have ⟨t, ht⟩ := h
    rw [← ht.2]
    simp
    exact ht.1

example {a b : G} : ϕ a = ϕ b → a * ker ϕ = b * ker ϕ := by
  intro h
  ext x
  unfold ker
  simp
  constructor
  . intro ⟨t, ht⟩
    use (b⁻¹ * a * t)
    simp [homo.linear, homo.linear, h, ht]
    simp [mul_assoc, mul_assoc, ht]
  . intro ⟨t, ht⟩
    use (a⁻¹ * b * t)
    simp [homo.linear, homo.linear, h, ht]
    simp [mul_assoc, mul_assoc, ht]

example : Function.Injective ϕ ↔ (ker ϕ).carrier = {1} := by
  unfold ker; simp
  constructor
  . intro h
    ext x; simp
    refine Iff.intro ?_ (by intro h; rw [h]; simp)
    intro h'
    apply h (a₁ := x) (a₂ := 1)
    simp [h']
  . intro h
    intro x y h'
    have := ϕeq_iff_mem_coset_ker.mp h'
    unfold ker at this; simp at this
    have ⟨t, ht⟩ := this
    rw [← ht.2]
    simp
    rw [Set.ext_iff] at h
    simp at h
    apply (h t).mp ht.1


theorem ker_normal : Subgroup.Normal (ker ϕ) := by
  constructor
  intro n hn g
  rw [ker_iff]
  simp
  rw [← ker_iff]
  exact hn

end Homomorphism

end Group
