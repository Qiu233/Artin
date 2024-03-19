import Mathlib


namespace Group

variable [Group G]

@[reducible]
instance cmul_left [Group G] : HMul G (Subgroup G) (Set G) where
  hMul a H := {a * h | h ∈ H}
@[reducible]
instance cmul_right [Group G] : HMul (Subgroup G) G (Set G) where
  hMul H a := {h * a | h ∈ H}

@[reducible]
instance smul_left [Group G] : HMul G (Set G) (Set G) where
  hMul a H := {a * h | h ∈ H}
@[reducible]
instance smul_right [Group G] : HMul (Set G) G (Set G) where
  hMul H a := {h * a | h ∈ H}

theorem eq_iff_inv_eq {a b : G} : a = b ↔ a⁻¹ = b⁻¹ := by
  constructor
  . intro h
    rw [h]
  . intro h
    apply mul_right_cancel (b := a⁻¹)
    simp
    rw [h]
    simp

def center (G : Type u) [Group G] : Subgroup G where
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
