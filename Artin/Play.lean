import Mathlib
-- #check UInt64.

#check Nat.shiftRight_eq_div_pow
-- #check UInt32.shiftRight_eq_div_pow

#check Nat.div_lt_iff_lt_mul
#check Nat.mul_lt_mul_of_pos_left
#check Nat.zero_lt_of_ne_zero
#check Nat.ne_zero_iff_zero_lt
#check Nat.div

theorem Nat.shiftRight_lt_self {x t : ℕ} : t > 0 → (x >>> t > 0) → (x >>> t) < x := by
  rw [Nat.shiftRight_eq_div_pow]
  simp
  intro ht h
  have one_eq_pow_zero : 1 = 2 ^ 0 := by decide
  have one_lt_pow_t : 1 < 2 ^ t := by
    rw [one_eq_pow_zero]
    simp
    apply Nat.ne_zero_iff_zero_lt.mpr ht
  have : x * 1 < x * 2 ^ t := by
    apply Nat.mul_lt_mul_of_pos_left one_lt_pow_t
    simp
    if c : x = 0
      then rw [c] at h; simp at h
      else apply Nat.zero_lt_of_ne_zero c
  rw [Nat.div_lt_iff_lt_mul]
  . simp at this
    exact this
  . apply Nat.lt_trans (m := 1) (by decide) one_lt_pow_t

-- theorem UInt32.shiftRight_lt_self {x t : UInt32} :
--     t > 0 → (x >>> t > 0) → (x >>> t) < x := by
--   intro ht h
--   -- unfold HShiftRight.hShiftRight
--   simp [HShiftRight.hShiftRight]
--   simp [ShiftRight.shiftRight]
--   simp [shiftRight]
--   unfold LT.lt instLTUInt32; simp
--   have : x.val.val >>> (modn t 32).val.val < x.val.val := by
--     simp
--     apply Nat.shiftRight_lt_self
--     .
--   sorry
#check Array.append
#check Array
#check ByteArray
-- #check List.tra


#check List.take
#check List.findIdx (λ t => t >>> 7 > 0)

def X := {x : ℕ | x ≤ 5}
-- def X := {x : ℕ | x ≤ 5}

-- #check {x + y | x ∈ X, y ∈ X}

#check FirstOrder.Language
#check FirstOrder.Field.FieldAxiom
#check FirstOrder.Language
