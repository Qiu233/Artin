import Mathlib
import Data.List
import Sorting.Basic

namespace List

def Bubble [LinearOrder α] (l : List α) :=
  match l with
  | [] => []
  | [a] => [a]
  | a :: b :: tail =>
    if a > b
        then b :: Bubble (a :: tail)
        else a :: Bubble (b :: tail)

def BubbleSort [LinearOrder α] (l : List α) :=
  match l with
  | [] => []
  | a :: tail => Bubble (a :: (BubbleSort tail))

-- @[simp] lemma Bubble.single [LinearOrder α] {x : α} : Bubble [x] = [x] := by
--   unfold Bubble; simp

-- @[simp] lemma Bubble.tail [LinearOrder α] {a : α} {tail : List α} : a ∈ Bubble (a :: tail) := by
--   cases tail with
--   | nil => simp
--   | cons b tail =>
--     unfold Bubble; simp
--     split
--     . simp; apply Or.inr Bubble.tail
--     . simp

-- @[simp] lemma Bubble.nonempty [LinearOrder α] {l : List α} : (Bubble l ≠ []) = (l ≠ []) := by
--   symm; ext
--   unfold Bubble
--   constructor
--   . intro h
--     match l with
--     | [] => contradiction
--     | [a] => simp
--     | a :: b :: tail => simp; split <;> simp
--   . match l with
--     | [] => simp
--     | [a] => simp
--     | a :: b :: tail => simp

-- theorem Bubble.last_max [LinearOrder α] (l : List α) (h : Bubble l ≠ []) :
--   ∀ x ∈ Bubble l, (Bubble l).getLast h ≥ x := by
--   intro x h'
--   match l with
--   | [] => contradiction
--   | [a] => simp; simp at h'; rw [h']
--   | a :: b :: tail =>
--     simp
--     unfold Bubble; simp
--     split
--     . rename b < a => h''
--       unfold Bubble at h'; rw [if_pos h''] at h'
--       rw [List.mem_cons] at h'
--       have := Bubble.last_max (a :: tail) (by simp)
--       rw [List.getLast_cons (by simp)]
--       have t := this a (by simp)
--       rcases h' with h' | h'
--       . rw [h'] at *
--         apply le_of_lt
--         apply lt_of_lt_of_le (b := a) h''
--         apply this; simp
--       . apply this
--         exact h'
--     . rename ¬b < a => h''
--       unfold Bubble at h'; rw [if_neg h''] at h'
--       rw [List.mem_cons] at h'
--       have := Bubble.last_max (b :: tail) (by simp)
--       rw [List.getLast_cons (by simp)]
--       have t := this b (by simp)
--       rcases h' with h' | h'
--       . rw [h'] at *
--         if c : a < b
--           then
--             apply le_of_lt
--             apply lt_of_lt_of_le (b := b) c
--             apply this; simp
--           else
--             simp at h'' c
--             rw [PartialOrder.le_antisymm a b h'' c]
--             apply this; simp
--       . apply this
--         exact h'

theorem Bubble.permu [LinearOrder α] (l : List α) :
    List.Perm (Bubble l) l := by
  unfold Bubble
  match l with
  | [] => simp
  | [a] => simp
  | a :: b :: tail =>
    simp; split
    . apply List.Perm.trans (l₂ := b :: a :: tail)
      . apply List.Perm.cons
        exact Bubble.permu (a :: tail)
      . apply List.Perm.swap
    . apply List.Perm.cons
      exact Bubble.permu (b :: tail)

theorem BubbleSort.permu [LinearOrder α] (l : List α) :
  List.Perm (BubbleSort l) l := by
  unfold BubbleSort
  match l with
  | [] => simp
  | a :: tail =>
    simp
    apply Perm.trans (l₂ := a :: BubbleSort tail)
    . apply Bubble.permu
    . apply Perm.cons
      apply BubbleSort.permu

lemma Perm.Forall {α : Type*}  {motive : α → Prop} {l₁ l₂ : List α} :
  (List.Perm l₁ l₂) → (∀ x ∈ l₁, motive x) → (∀ x ∈ l₂, motive x) := by
  intro hp h x hx
  apply h
  apply (List.Perm.mem_iff hp).mpr hx

theorem Bubble.ordered [LinearOrder α] {a : α} {tail : List α} :
  Ordered tail → Ordered (Bubble (a :: tail)) := by
  unfold Bubble; simp
  intro h
  cases tail with
  | nil => simp
  | cons b tail =>
    have tail_ordered := Ordered.tail h
    simp
    split <;> apply (Ordered.head_iff (Bubble.ordered tail_ordered)).mpr
    . apply List.Perm.Forall (motive := λ x ↦ b ≤ x) (Bubble.permu (a :: tail)).symm
      intro x hx
      simp at hx
      rcases hx with hx | hx
      . rw [hx]; apply le_of_lt; assumption
      . revert x
        apply Ordered.head h
    . apply List.Perm.Forall (motive := λ x ↦ a ≤ x) (Bubble.permu (b :: tail)).symm
      intro x hx
      rename ¬b < a => h'; simp at h'
      apply le_trans (b := b) h'
      simp at hx
      rcases hx with hx | hx
      . rw [hx]
      . revert x
        apply (Ordered.cons_iff tail_ordered).mpr h

theorem BubbleSort.ordered [LinearOrder α] {l : List α} :
  Ordered (BubbleSort l) := by
  unfold BubbleSort
  match l with
  | [] => simp
  | _ :: _ => exact Bubble.ordered BubbleSort.ordered

instance [LinearOrder α] : SortAlg (BubbleSort (α := α)) where
  permu := BubbleSort.permu
  ordered l := BubbleSort.ordered (l := l)

instance anti : LE ℕ where
  le x y := x ≥ y

#eval [1,2] < [2,1]
def a : (LinearOrder (List ℕ)) := inferInstance

end List
