import Mathlib


def enum (p : α → Prop) (f : ℕ → Option α) :=
  ∀ x, p x ↔ ∃ n, f n = some x

def enumerable (p : α → Prop) :=
  ∃ f : ℕ → Option α, enum p f

def decider (p : α → Prop) (f : α → Bool) :=
  ∀ x, p x ↔ f x = true

def decidable (p : α → Prop) :=
  ∃ f : α → Bool, decider p f

def semi_decider (p : α → Prop) (f : α → ℕ → Bool) :=
  ∀ x, p x ↔ ∃ n, f x n = true

def semi_decidable (p : α → Prop) :=
  ∃ f : α → ℕ → Bool, semi_decider p f

def EA :=
  Σ' ε : ℕ → ℕ → Option ℕ,
    ∀ p : ℕ → Prop,
      enumerable p ↔ ∃ c, enum p (ε c)


axiom ea : EA
noncomputable def ε := ea.1
noncomputable def ea_ε
  : ∀ p : ℕ → Prop, enumerable p ↔ ∃ c, enum p (ε c)
  := ea.2


def W c x := ∃ n, ε c n = some x

-- lemma ea_W (p : ℕ → Prop) : enumerable p ↔ ∃ c, ∀ x, p x ↔ W c x
