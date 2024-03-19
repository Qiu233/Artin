import Mathlib
import Artin.Group.Examples.SubZ

open Classical

namespace Group.Examples

variable {G : Type*} [is_group : Group G]

def cyclic (x : G) : Subgroup G where
  carrier := {x ^ n | n : ℤ}
  mul_mem' {a b} ha hb := by
    simp at *
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    use m + n
    simp [← hm, ← hn, zpow_add]
  one_mem' := by
    use 0
    simp
  inv_mem' {a} ha := by
    simp at *
    obtain ⟨n, hn⟩ := ha
    use -n
    simp [hn]

syntax "(<" term ">)" : term

macro_rules
| `(term| (< $a:term >)) => `(cyclic ($a))

variable {x : G}

def S (x : G) : AddSubgroup ℤ where
  carrier := {k | x ^ k = 1}
  add_mem' {a b} ha hb := by
    simp at *
    simp [zpow_add, ha, hb]
  zero_mem' := by
    simp
  neg_mem' {a} ha := by
    simp at *
    exact ha

lemma aux_cyc_1 (z : ℤ) : 0 ≤ z → ∃ n : ℕ, n = z := by
  intro h
  have := Int.natAbs_of_nonneg h
  use (Int.natAbs z)

lemma aux_cyc_2 {r : ℤ} : 0 ≤ r → x ^ Int.natAbs r = x ^ r := by
  intro h'
  cases r with
  | ofNat r => simp
  | negSucc r =>
    exfalso
    have := Int.negSucc_lt_zero r
    linarith

lemma aux_cyc_3 {n : ℤ} : x ^ (n % gen (S x)) = x ^ n := by
  have : n % gen (S x) = n - gen (S x) * (n / gen (S x)) := by
    linarith only [Int.ediv_add_emod n (gen (S x))]
  have pow_gen_S : x ^ (gen (S x)) = 1 := by
    have : gen (S x) ∈ S x := gen_mem (S x)
    conv at this => rhs; simp [S]
    simp at this
    exact this
  rw [this]
  simp [zpow_sub, zpow_mul, pow_gen_S]

/--Proposition 2.4.2 (c)-/
theorem cyclic_card : 0 < gen (S (x := x)) → Nat.card (<x>) = gen (S (x := x)) := by
  intro h
  obtain ⟨m, hm⟩ := aux_cyc_1 (gen (S x)) (le_of_lt h)
  have m_pos : 0 < m := by linarith only [hm, h]
  have m_ne_zero' : (m : Int) ≠ 0 := by linarith only [m_pos]
  have abs_m : |(m : Int)| = m := by simp
  rw [← hm]
  congr
  let t : Fin m → (<x>) := λ i => ⟨x ^ i.1, by simp [cyclic]; exists i.1; simp⟩
  refine Nat.card_eq_of_equiv_fin (Equiv.symm $ Equiv.ofBijective t ⟨?inj, ?surj⟩)
  . simp [Function.Injective]
    intro ⟨y1, hy1⟩ ⟨y2, hy2⟩
    simp
    intro he
    have gen_S_least := gen_least_pos h
    simp [IsLeast, lowerBounds] at gen_S_least
    have {a b : ℕ} : a < b → b < m → x ^ a = x ^ b → False := by
      intro hab hbm hn
      let y := b - a
      have y_lt_m : (y : ℤ) < m := by
        simp
        apply Nat.sub_lt_left_of_lt_add (le_of_lt hab)
        exact Nat.lt_add_left _ hbm
      have y_pos : 0 < (y : ℤ) := by
        simp [hab]
      have : ↑y ∈ S x := by
        simp [S, pow_sub _ (le_of_lt hab), hn]
      have := gen_S_least.2 this y_pos
      rw [← hm] at this
      apply lt_irrefl _ (lt_of_lt_of_le y_lt_m this)
    rcases lt_trichotomy y1 y2 with h' | h' | h'
    . exfalso
      exact this h' hy2 he
    . exact h'
    . exfalso
      exact this h' hy1 he.symm
  . intro ⟨y, ⟨n, hn⟩⟩
    simp [← hn]
    let n' := n % m
    have n'_nonneg : 0 ≤ n' := Int.emod_nonneg n m_ne_zero'
    use ⟨Int.natAbs n', by
      rw [← Int.ofNat_lt]
      rw [Int.natAbs_of_nonneg (n'_nonneg)]
      simp
      conv => rhs; rw [← abs_m]
      apply Int.emod_lt n m_ne_zero'
      ⟩
    simp [aux_cyc_2 n'_nonneg]
    rw [hm, aux_cyc_3]


end Group.Examples
