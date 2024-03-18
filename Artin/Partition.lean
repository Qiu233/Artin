import Mathlib

/-
The `Partition α` is a `partitions : Set (Set α)` such that:
* `⋃₀ partitions = Set.univ`,
* every distinct pair `A B ∈ partitions` are disjoint.

A `Partition α` is called **uniform** if all of its `S ∈ partitions` have the same cardinal.
Existence of `Fin n ≃ α ` equivalently means `Nat.card α = n`, for any finite type `α`.

The last theorem in this file, `join_finite_uniform`, states that a type `α` is of cardinal `m * n`,
  if there are exactly `m` uniform partitions of `α`, each of cardinal `n`.

This looks trivial at first, but eventually cost me more than one day to complete the proof,
  as it envolves manipulation of dependent objects.
-/

def Set.Disjoint (A B : Set X) : Prop := (∃ t, t ∈ A ∧ t ∈ B) → False

structure Partition (α : Type*) where
  partitions : Set (Set α)
  disjoint : ∀ A ∈ partitions, ∀ B ∈ partitions, A ≠ B → Set.Disjoint A B
  union : ⋃₀ partitions = Set.univ

instance : Coe (Partition α) (Set (Set α)) where
  coe x := x.partitions

@[reducible, simp]
instance {α : Type*} : Membership (Set α) (Partition α) where
  mem s S := s ∈ S.partitions

namespace Partition

variable {p : Partition α}

private lemma aux_0 {a b c : Prop} : (a → c) → ((¬ a ∧ b) → c) → (a ∨ b) → c := by
  intro h1 h2 h3
  rcases h3 with h | h
  . apply h1 h
  . if h' : a
      then apply h1 h'
      else apply h2 (And.intro h' h)

private lemma aux_1 : (¬ (a ∧ b)) = (¬ a ∨ ¬ b) := by
  apply propext
  constructor
  . intro h
    simp at h
    if c : a then apply Or.inr (h c)
    else apply Or.inl c
  . simp
    intro h c
    rcases h with h | h
    . contradiction
    . exact h

private lemma aux_2 {x y : α × β} : ¬ x = y ↔ x.1 ≠ y.1 ∨ x.2 ≠ y.2 := by
  constructor
  . intro h
    rw [← aux_1]
    intro hn
    apply h
    ext <;> simp [hn]
  . intro h hn
    match x, y with
    | (a, b), (c, d) =>
      simp at h hn
      rcases h with h | h
      . apply h hn.1
      . apply h hn.2

private lemma aux_3 {C : Sort u} : Fin 0 → C := by
  intro h
  have := h.2
  trivial

private lemma aux_4 : 0 < m → x < m → y < n → x * n + y < m * n := by
  intro h1 h3 h4
  rw [Nat.lt_iff_le_pred h1] at h3
  apply Nat.lt_of_lt_of_le (m := x * n + n)
  . simp
    exact h4
  . have : m = m - 1 + 1 := by
      rw [Nat.sub_add_cancel]
      apply Nat.le_of_pred_lt
      simp
      exact h1
    rw [this, Nat.add_mul]
    simp
    apply Nat.mul_le_mul_right n h3

theorem join_finite_uniform : Fin m ≃ p.partitions → (∀ x ∈ p.partitions, Fin n ≃ x) → Fin (m * n) ≃ α := by
  intro u v
  let t : Fin m × Fin n → α := λ (x, y) =>
    let k := u x
    (v k.1 k.2) y |>.1
  have d (x y : p.partitions) : x.1 ≠ y.1 → ∀ a ∈ x.1, ∀ b ∈ y.1, a ≠ b := by
    intro h a ha b hb
    have := p.disjoint x.1 x.2 y.1 y.2 h
    unfold Set.Disjoint at this
    intro h'
    apply this
    use a
    apply And.intro ha
    rw [h']
    exact hb
  have d' (x y : p.partitions) : x.1 = y.1 → ∀ a b : Fin n, a ≠ b → ((v x.1 x.2) a).1 ≠ ((v y.1 y.2) b).1 := by
    intro h a b hab
    have h' := Subtype.ext_iff_val.mpr h
    rw [← h']
    intro hn
    rw [← Subtype.ext_iff_val] at hn
    apply hab
    apply (v x.1 x.2).bijective.injective hn
  have inj : Function.Injective t := by
    simp
    intro x y h
    simp at h
    have c1 : ↑(u x.1) ∈ p.partitions := (u x.1).2
    have c2 : ↑(u y.1) ∈ p.partitions := (u y.1).2
    have h : ((v ↑(u x.1) c1) x.2).1 = ((v ↑(u y.1) c2) y.2).1 := h
    apply not_not.mp
    intro hn
    rw [aux_2] at hn
    apply aux_0 ?_ ?_ hn
    . intro hn
      have pn : (u x.1).1 ≠ (u y.1).1 := by
        intro h'
        apply hn
        rw [← Subtype.ext_iff_val] at h'
        exact u.bijective.injective h'
      have dis := p.disjoint (u x.1) ?_ (u y.1) ?_ pn
      unfold Disjoint at dis
      have := d (u x.1) (u y.1) pn (↑((v (↑(u x.1)) c1) x.2)) ?_ (↑((v (↑(u y.1)) c2) y.2)) ?_
      contradiction
      all_goals simp
    . intro hn
      simp at hn
      have : ((v (↑(u x.1)) c1) x.2).1 ≠ ((v (↑(u y.1)) c2) y.2).1 := by
        apply d'
        . rw [hn.1]
        . apply hn.2
      contradiction
  have surj : Function.Surjective t := by
    simp
    intro y
    have univ := p.3
    rw [Set.sUnion_eq_univ_iff] at univ
    have ⟨s, hs⟩ := univ y
    let x1 := u.symm ⟨s, hs.1⟩
    let x2 := (v s hs.1).symm ⟨y, hs.2⟩
    use (x1, x2)
    simp only []
    have k : u x1 = ⟨s, hs.1⟩ := by simp
    rw [k]
    simp
  have t := Equiv.ofBijective t ⟨inj, surj⟩
  if c1 : n = 0
    then
      rw [c1]
      simp
      let t' : Fin 0 → (Fin m × Fin 0) := λ a => aux_3 a
      apply Equiv.trans (β := Fin m × Fin n) ?_ t
      rw [c1]
      exact Equiv.ofBijective t' ⟨λ x _ _ => aux_3 x, λ y => aux_3 y.2⟩
    else
      if c2 : m = 0
        then
          rw [c2]
          simp
          let t' : Fin 0 → (Fin 0 × Fin n) := λ a => aux_3 a
          apply Equiv.trans (β := Fin m × Fin n) ?_ t
          rw [c2]
          exact Equiv.ofBijective t' ⟨λ x _ _ => aux_3 x, λ y => aux_3 y.1⟩
        else
          have c1 := Nat.ne_zero_iff_zero_lt.mp c1
          have c2 := Nat.ne_zero_iff_zero_lt.mp c2
          let t' : Fin (m * n) → (Fin m × Fin n) := λ v =>
            let x := v / n
            let y := v % n
            (⟨x, by simp; apply (Nat.div_lt_iff_lt_mul c1).mpr v.2⟩,
              ⟨y, by simp; apply Nat.mod_lt; simp; exact c1⟩)
          apply Equiv.trans (β := Fin m × Fin n) ?_ t
          apply Equiv.ofBijective t' ⟨?_, ?_⟩
          . intro x y
            simp
            intro h1 h2
            rw [Fin.eq_iff_veq, ← Nat.div_add_mod x.1 n,
              h1, h2, Nat.div_add_mod y.1 n]
          . intro (x, y)
            use ⟨x.1 * n + y.1, by apply aux_4 c2 x.2 y.2⟩
            simp
            rw [Fin.eq_iff_veq]
            rw [Fin.eq_iff_veq]
            simp
            constructor
            . rw [Nat.add_div_eq_of_add_mod_lt]
              . rw [(Nat.div_eq_zero_iff (a := y.1) c1).mpr y.2]
                simp
                rw [Nat.mul_div_cancel x.1 c1]
              . simp
                apply Nat.mod_lt
                exact c1
            . rw [Nat.add_mod]
              rw [Nat.mul_mod]
              simp
              rw [Nat.mod_eq_iff_lt]
              exact y.2
              trivial

end Partition
