import Mathlib


namespace Group

variable [Group G]

theorem eq_iff_inv_eq {a b : G} : a = b ↔ a⁻¹ = b⁻¹ := by
  constructor
  . intro h
    rw [h]
  . intro h
    apply mul_right_cancel (b := a⁻¹)
    simp
    rw [h]
    simp

def center : Subgroup G where
  carrier := {z | ∀ x : G, z * x = x * z}
  mul_mem' {a b} ha hb x := by
    simp at *
    rw [mul_assoc]
    rw [hb]
    rw [← mul_assoc]
    rw [ha]
    rw [← mul_assoc]
  one_mem' := by simp
  inv_mem' {x} := by
    simp
    intro h y
    obtain h := h y⁻¹
    apply eq_iff_inv_eq.mpr
    simp
    symm
    exact h

end Group
