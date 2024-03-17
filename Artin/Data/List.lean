import Std
import Mathlib.Data.List.Lemmas

structure List.IndexOf {α : Type u} (x : α) (l : List α) where
  idx : Fin l.length
  eq : l.get idx = x

private def List.index_of_mem_i {α : Type u} [DecidableEq α] {x : α} : (l : List α) → x ∈ l → (Fin (l.length))
  | [], h => by contradiction
  | a :: tail, h => if _ : x = a then ⟨0, by simp⟩ else
    have i : Fin tail.length := List.index_of_mem_i tail (by
      simp at h; rcases h <;> first | contradiction | assumption)
    ⟨i.1 + 1, Nat.add_lt_add_iff_right.mpr i.2⟩

private theorem List.index_of_mem_is {α : Type u} [DecidableEq α] {x : α} (l : List α) (h : x ∈ l) :
    (l.get (List.index_of_mem_i l h)) = x := by
  unfold List.index_of_mem_i
  match l with
  | [] => contradiction
  | a :: tail =>
    simp; split
    . apply Eq.symm; assumption
    . apply List.index_of_mem_is

def List.index_of_mem {α : Type u} [DecidableEq α] (x : α) (l : List α) (h : x ∈ l) : l.IndexOf x :=
  ⟨List.index_of_mem_i l h, List.index_of_mem_is l h⟩

theorem List.IndexOf.mem {l : List α} (h : List.IndexOf x l) : x ∈ l := by
  obtain ⟨_, h⟩ := h
  rw [← h]; apply List.get_mem

def List.indexes_of_mem {α : Type u} [DecidableEq α] (x : α) (l : List α) (h : x ∈ l) : List (l.IndexOf x) :=
  have head := List.IndexOf.mk (List.index_of_mem_i l h) (List.index_of_mem_is l h)
  let remaining := l.drop (head.1.1 + 1)
  if c : x ∈ remaining then
      -- termination proof
      let rec sizeOfList {l : List α} : sizeOf l = l.length + 1 := by
        cases l with
        | nil => simp
        | cons a tail =>
          simp; rw [Nat.add_comm]
          simp; apply sizeOfList
      have _ : sizeOf remaining < sizeOf l := by
        rw [sizeOfList, sizeOfList]; simp
        rw [Nat.sub_add_eq, Nat.sub_right_comm]
        apply Nat.lt_of_le_of_lt (m := length l - 1)
        . apply Nat.sub_le
        refine Nat.sub_lt ?_ (by decide)
        match l with
        | [] => contradiction
        | _ :: _ => simp
      -- termination proof
      head :: (List.indexes_of_mem x remaining c).map
        (fun | ⟨i, hi⟩ => ⟨⟨head.1.1 + 1 + i, by
          have := i.2; simp at this
          have := Nat.add_lt_of_lt_sub this; rw [Nat.add_comm] at this; exact this
        ⟩, by
          have : get l { val := ↑head.idx + 1 + ↑i, isLt := ?_ } = get remaining i := by
            simp only [remaining]; apply List.get_drop
          rw [this]; exact hi
          rw [Nat.add_comm]
          apply Nat.add_lt_of_lt_sub
          rw [← List.length_drop]
          exact i.2
        ⟩)
    else [head]

theorem List.forall_mem_iff_forall_index [DecidableEq α] {p : α → Prop} {l : List α} :
  (∀ x ∈ l, p x) ↔ (∀ i : Fin (l.length), p (l.get i)) := by
  constructor
  . intro h _; apply h; apply List.get_mem
  . intro h x hx
    have ⟨i, hi⟩ := List.mem_iff_get.mp hx
    rw [← hi]
    apply h i

#check [0].index_of_mem 0 (by decide) |>.mem

#eval [1,2,3,3,2,2,1,1].indexes_of_mem 3 (by decide) |>.map (λ x => x.1)

#eval ([1,2,3].index_of_mem 3 (by decide)).1
