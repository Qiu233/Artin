import Mathlib
import Data.List
namespace List

def Ordered [LinearOrder α] (l : List α) :=
  ∀ i j : Fin l.length, i < j → l.get i ≤ l.get j

class SortAlg [LinearOrder α] (alg : List α → List α) where
  ordered : ∀ l : List α, Ordered (alg l)
  permu : ∀ l : List α, List.Perm (alg l) l

@[simp] theorem Ordered.nil [LinearOrder α] : Ordered ([] : List α) := by
  intro ⟨i, hi⟩
  contradiction

@[simp] theorem Ordered.singleton [LinearOrder α] {a : α} : Ordered [a] := by
  intro i j _
  simp

theorem Ordered.tail [LinearOrder α] {a : α} {tail : List α} : Ordered (a :: tail) → Ordered tail := by
  unfold Ordered at *
  intro h i j h'
  let i' : Fin ((a :: tail).length) :=
    ⟨i + 1, by simp; rw [Nat.succ_eq_add_one]; apply Nat.add_lt_add_iff_right.mpr; exact i.2⟩
  let j' : Fin ((a :: tail).length) :=
    ⟨j + 1, by simp; rw [Nat.succ_eq_add_one]; apply Nat.add_lt_add_iff_right.mpr; exact j.2⟩
  have t := h i' j'
    (by simp; exact h')
  have ti : List.get (a :: tail) i' = List.get tail i := by simp
  have tj : List.get (a :: tail) j' = List.get tail j := by simp
  rw [← ti, ← tj]
  exact t

theorem Ordered.cons [LinearOrder α] {a : α} {tail : List α} :
  Ordered tail → (∀ x ∈ tail, a ≤ x) → Ordered (a :: tail) := by
  intro h1 h2 i j h
  have t : j.1 ≠ 0 := by
    apply Nat.ne_zero_iff_zero_lt.mpr
    apply Nat.zero_lt_of_lt (a := i.1)
    exact h
  match i with
  | ⟨0, _⟩ =>
    have : List.get (a :: tail) ⟨0, by simp⟩ = a := by
      unfold List.get; simp
    rw [this]
    unfold List.get
    match j with
    | ⟨0, _⟩ => simp
    | ⟨Nat.succ k, _⟩ =>
      simp
      apply h2
      apply List.get_mem
  | ⟨Nat.succ k, h'⟩ =>
    match j with
    | ⟨0, _⟩ => contradiction
    | ⟨Nat.succ l, _⟩ =>
      simp; apply h1; simp
      rw [← Nat.add_lt_add_iff_right (k := 1)]
      simp at h
      exact h

theorem Ordered.cons_iff [LinearOrder α] {a : α} {tail : List α} :
  Ordered tail → ((∀ x ∈ tail, a ≤ x) ↔ Ordered (a :: tail)) := by
  intro h
  constructor
  . apply Ordered.cons h
  . intro h'
    intro x hx
    have : a = (a :: tail).get ⟨0, by simp⟩ := by simp
    rw [this]
    have : x ∈ a :: tail := by
      simp
      apply Or.inr hx
    clear hx
    revert this x
    rw [List.forall_mem_iff_forall_index]
    intro ⟨i, hi⟩
    match i with
    | 0 => simp
    | Nat.succ k =>
      apply h' ⟨0, by simp⟩
      rw [Fin.lt_def]
      simp

theorem Ordered.head [LinearOrder α] {a : α} {tail : List α} :
  Ordered (a :: tail) → ∀ x ∈ tail, a ≤ x := by
  intro h
  rw [List.forall_mem_iff_forall_index]
  intro i
  have : a = (a :: tail).get ⟨0, by simp⟩ := by simp
  rw [this]
  have : List.get tail i = List.get (a :: tail)
    ⟨i + 1, by simp; rw [Nat.succ_eq_add_one]; apply Nat.add_lt_add_iff_right.mpr i.2⟩ := by simp
  rw [this]
  apply h
  rw [Fin.lt_def]
  simp

theorem Ordered.head_iff [LinearOrder α] {a : α} {tail : List α} (h : Ordered tail) :
  Ordered (a :: tail) ↔ ∀ x ∈ tail, a ≤ x := by
  constructor
  . apply Ordered.head
  . intro h' i j h''
    have ⟨i, hi⟩ := i
    have ⟨j, hj⟩ := j
    simp at h''
    cases i with
    | zero =>
      match j with
      | 0 => simp
      | Nat.succ k => simp; apply h'; apply List.get_mem
    | succ n =>
      match j with
      | 0 => simp at h''
      | Nat.succ k =>
        simp; apply h; simp
        apply Nat.succ_lt_succ_iff.mp h''

theorem Ordered.cons_cons_of [LinearOrder α] {a b : α} {tail : List α} :
    a ≤ b → Ordered (b :: tail) → Ordered (a :: b :: tail) := by
  intro h h'
  apply Ordered.cons h'
  intro x hx
  simp at hx
  rcases hx with hx | hx
  . rw [hx]; assumption
  . apply le_trans (b := b) h
    revert hx x
    apply Ordered.head h'

theorem Ordered.cons_cons_iff [LinearOrder α] {a b : α} {tail : List α} :
    Ordered (a :: b :: tail) ↔ (a ≤ b ∧ Ordered (b :: tail)) := by
  symm
  constructor
  . intro ⟨h, h'⟩
    apply Ordered.cons_cons_of h h'
  . intro h
    constructor
    apply h ⟨0, by simp⟩ ⟨1, by simp⟩
    rw [Fin.lt_def]; simp
    apply Ordered.tail h

inductive Ordered' [LinearOrder α] : (List α) → Prop where
  | nil : Ordered' []
  | sing {a : α} : Ordered' [a]
  | cons {a b : α} {tail : List α} (h : a ≤ b) (h : Ordered' (b :: tail)) : Ordered' (a :: b :: tail)

theorem Ordered_iff_Ordered' [LinearOrder α] {l : List α} :
    Ordered l ↔ Ordered' l := by
  constructor
  . intro h
    cases l with
    | nil => exact Ordered'.nil | cons a tail =>
      cases tail with
      | nil => exact Ordered'.sing | cons b tail =>
        rw [Ordered.cons_cons_iff] at h
        apply Ordered'.cons (h.1) (Ordered_iff_Ordered'.mp h.2)
  . intro h
    cases l with
    | nil => simp | cons a tail =>
      cases tail with
      | nil => simp | cons b tail =>
        cases h with
        | cons hle ho => exact Ordered.cons_cons_of hle (Ordered_iff_Ordered'.mpr ho)

end List
