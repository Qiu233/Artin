import Mathlib

-- variable {n : Type*} [Fintype n] [DecidableEq n]

-- variable {T : Type*} [Semiring T]

-- lemma lemma_1_1_15 {A L R : Matrix n n T} :
--     L * A = 1 → A * R = 1 → R = L := by
--   intro h1 h2
--   calc
--     R = 1 * R := by simp
--     _ = (L * A) * R := by rw [h1]
--     _ = L * (A * R) := by apply Matrix.mul_assoc
--     _ = L := by rw [h2]; simp

-- theorem Equiv.invFun_of_toFun [Nonempty α] {f : α ≃ β} : f.1.invFun = f.2 := by
--   unfold Function.invFun; ext t
--   if h : ∃ x, f x = t
--     then
--       apply (f.injective ·)
--       simp [dif_pos h, Exists.choose_spec h]
--     else
--       exact absurd (f.surjective t) h

-- def Equiv.id : α ≃ α := ⟨_root_.id, _root_.id, p1, p2⟩ where
--   p1 := by intro x; simp
--   p2 := by intro x; simp

-- inductive SG : ℕ → Type where
--   | id (n : ℕ) : SG n
--   | swap {n : ℕ} (i j : Fin n) : SG n →  SG n
