import Mathlib
open Classical

-- noncomputable def sup {s : Set ℝ} :=

-- def Upperbound (s : Set ℝ) := {y : ℝ | ∀ x ∈ s, x ≤ y}

-- def HasMinimum (s : Set ℝ) := ∃ m ∈ s, ∀ x ∈ s, m ≤ x
-- #check Classical.not_not
-- theorem Upperbound_nonempty (s : Set ℝ) : Set.Nonempty (Upperbound s) := by
--   unfold Set.Nonempty
--   if c : s = ∅ then
--     unfold Upperbound
--     use 0
--     rw [c]
--     simp
--   else
--     -- unfold EmptyCollection.emptyCollection Set.instEmptyCollectionSet at c
--     -- simp at c
--     have h : ∃ x, x ∈ s := by
--       apply not_not.mp
--       intro h; simp at h
--       apply c
--       ext x
--       simp
--       apply h

--     -- unfold Empty
--     simp


-- #check Real.isBounded_iff_bddBelow_bddAbove
-- #check Real.iInf_of_not_bddBelow

-- theorem Supremum_exists {s : Set ℝ} : Set.Nonempty (Upperbound s) → HasMinimum (Upperbound s) := by
--   intro ⟨t, ht⟩
--   unfold HasMinimum
--   apply not_not.mp
--   intro h
--   simp at h
--   obtain h :  ∀ y ∈ Upperbound s, ∃ x ∈ Upperbound s, x < y := h




#check Sup
#check Min
