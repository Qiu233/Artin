import Mathlib

open Classical

namespace Group.Examples


instance : AddGroup ℤ where
  add_left_neg a := by simp

def genℤ (a : ℤ) : AddSubgroup ℤ where
  carrier := {k * a | k : ℤ}
  add_mem' {x y} hx hy := by
    simp at *
    have ⟨kx, hx⟩ := hx
    have ⟨ky, hy⟩ := hy
    rw [← hx, ← hy]
    use (kx + ky)
    linarith
  zero_mem' := by simp
  neg_mem' {x} hx := by
    simp at *
    have ⟨k, hk⟩ := hx
    use (-k)
    linarith

notation:80 "ℤ" "⬝" a:81 => (genℤ a)

@[simp]
theorem generated_by : a ∈ ℤ⬝a := by
  unfold genℤ
  simp
  use 1
  simp

lemma aux_1 {S : AddSubgroup ℤ} : (∃ x ∈ S, x ≠ 0) → (∃ x ∈ S, 0 < x) := by
  intro ⟨x, hx⟩
  rcases lt_trichotomy x 0 with h | h | h
  . use (-x)
    apply And.intro (S.neg_mem' hx.1)
    linarith
  . apply absurd h hx.2
  . use x
    exact ⟨hx.1, h⟩

lemma aux_3 {S : Set ℤ} : (∃ b : ℤ, ∀ s ∈ S, b ≤ s) → (∃ s, s ∈ S) → (∃ lb ∈ S, ∀ s ∈ S, lb ≤ s) := by
  intro ⟨b, hb⟩ h'
  let P := λ x => x ∈ S
  have fa : (∃ b, ∀ (z : ℤ), P z → b ≤ z) := by
    use b
  have ⟨lb, hlb⟩ := Int.exists_least_of_bdd (P := P) fa h'
  use lb

lemma aux_4 {S : AddSubgroup ℤ} : (∃ x ∈ S, x ≠ 0) → (∃ a ∈ S, 0 < a ∧ ∀ s ∈ S, 0 < s → a ≤ s) := by
  intro h
  let S' := {s ∈ S | 0 < s}
  have fa : (∃ b : ℤ, ∀ s ∈ S', b ≤ s) := by
    use 0
    intro s hs
    simp at hs
    linarith
  have fb : ∃ s, s ∈ S' := by
    have ⟨x, hx⟩ := aux_1 h
    use x
    simp
    exact hx
  have ⟨lb, hlb⟩ := aux_3 fa fb
  use lb
  apply And.intro
  . exact hlb.1.1
  . apply And.intro hlb.1.2
    intro s hs h'
    apply hlb.2
    apply And.intro hs h'

theorem AddSubgroup.ext_iff [AddGroup G] {H K : AddSubgroup G} : H = K ↔ H.carrier = K.carrier := by
  apply Iff.intro
  . intro h
    rcases H with ⟨⟨⟨a⟩⟩⟩
    rcases K with ⟨⟨⟨b⟩⟩⟩
    simp at *
    exact h
  . intro h
    apply AddSubgroup.ext
    apply Set.ext_iff.mp h

lemma aux_5 {S : AddSubgroup ℤ} {a : ℤ} {h : a ∈ S} (n : ℕ) : n * a ∈ S := by
  induction n with
  | zero => simp; exact S.zero_mem'
  | succ n ih =>
    simp
    rw [Int.add_mul]
    simp
    apply S.add_mem' ih h

lemma aux_6 {S : AddSubgroup ℤ} {a : ℤ} (n : ℤ) (h : a ∈ S) : n * a ∈ S := by
  induction n with
  | ofNat n => simp; apply aux_5 (h := h)
  | negSucc n =>
    rw [Int.negSucc_eq]
    simp
    rw [Int.add_mul]
    apply S.add_mem'
    . simp; exact h
    . simp; apply aux_5 (h := h)

lemma aux_8 {y x : ℤ} : 0 < x → ∃ a r : ℤ, 0 ≤ r ∧ r < x ∧ y = a * x + r := by
  intro h
  let a := y / x
  let r := y % x
  use a, r
  simp
  apply And.intro (Int.emod_nonneg y (by linarith only [h])) $ And.intro ?_ ?_
  . exact Int.emod_lt_of_pos y h
  . rw [add_comm]
    rw [mul_comm]
    rw [Int.emod_add_ediv]

theorem generation (S : AddSubgroup ℤ) : ∃ a ≥ 0, (S = ℤ⬝a) :=
    dite (S = ℤ ⬝ 0)
      (λ c => Exists.intro 0 (And.intro (le_refl 0) c))
      (p) where
  p c := by
    simp [genℤ, AddSubgroup.ext_iff, Set.ext_iff.not] at c
    obtain ⟨c, hc⟩ := c
    if h : c ∈ S
      then
        rw [Iff.comm, Classical.not_iff, Iff.comm] at hc
        obtain hs := hc.mp h
        have fa : ∃ x ∈ S, x ≠ 0 := by
          use c
        have ⟨x, hx⟩ := aux_4 fa
        use x
        apply And.intro
        . linarith only [hx.2.1]
        ext y
        simp [genℤ]
        apply Iff.intro
        . intro h
          have ⟨t, r, ht⟩ := aux_8 hx.2.1 (y := y) (x := x)
          have : r = y - t * x := by linarith only [ht]
          have : r ∈ S := by
            rw [this, sub_eq_add_neg]
            exact S.add_mem' h (S.neg_mem' $ aux_6 _ hx.1)
          have : r = 0 := by
            rcases lt_trichotomy r 0 with h | h | h
            . absurd h; linarith only [ht]
            . exact h
            . absurd (hx.2.2 r this h); linarith only [ht]
          use t
          linarith only [ht, this]
        . intro ⟨k, h⟩
          rw [← h]
          exact aux_6 _ hx.1
      else
        rw [Classical.not_iff] at hc
        rw [hc.mp h] at h
        exact absurd S.zero_mem' h

private lemma generation_unique_zero : (ℤ ⬝ a) = (ℤ ⬝ 0) → a = 0 := by
  intro h
  apply not_not.mp
  intro hn
  have fa : ∃ x ∈ (ℤ ⬝ a), x ≠ 0 := by
    use a
    apply And.intro ?_ hn
    simp
  have ⟨c, hc⟩ := aux_1 fa
  rw [AddSubgroup.ext_iff] at h
  rw [Set.ext_iff] at h
  simp at h
  have h := (h c).mp hc.1
  unfold genℤ at h
  simp at h
  rw [h] at hc
  apply lt_irrefl 0 hc.2

lemma aux_9 {a b : ℤ} : 0 < a → 0 < b * a → 0 < b := by
  intro h1 h2
  rcases lt_trichotomy b 0 with h | h | h
  . have := Int.mul_neg_of_neg_of_pos h h1
    have := lt_trans this h2
    exfalso
    apply lt_irrefl (b * a) this
  . rw [h] at h2
    rw [h]
    conv at h2 =>
      arg 2
      simp
    exact h2
  . exact h

lemma aux_10 (a b : ℤ) : 1 < a → a * b = 1 → False := by
  intro h1 h2
  rcases lt_trichotomy b 0 with h | h | h
  . have := Int.mul_neg_of_pos_of_neg (a := a) ?_ h
    rw [h2] at this
    have : ¬ 1 < (0 : ℤ) := by decide
    contradiction
    linarith
  . rw [h] at h2
    simp at h2
  . have : 1 * b < a * b := by
      apply Int.mul_lt_mul h1 ?_ h ?_
      . trivial
      . linarith
    simp at this
    rw [h2] at this
    rw [Int.lt_iff_add_one_le] at this
    simp at this
    have := lt_of_lt_of_le h this
    apply lt_irrefl 0 this

theorem generation_unique : 0 ≤ a → 0 ≤ b → (ℤ ⬝ a) = (ℤ ⬝ b) → a = b := by
  repeat rw [le_iff_eq_or_lt]
  rintro (ha | ha) (hb | hb) h
  . rw [← ha, ← hb]
  . rw [← ha] at *
    symm at h
    symm
    apply generation_unique_zero h
  . rw [← hb] at *
    apply generation_unique_zero h
  have h' := h
  rw [AddSubgroup.ext_iff] at h
  rw [Set.ext_iff] at h
  simp at h
  unfold genℤ at h
  simp at h
  have : ∃ k, k * b = b := by
    use 1
    simp
  have ⟨k, hk⟩ := (h b).mpr this
  if c : k = 1
    then
      rw [c] at hk
      simp at hk
      exact hk
    else
      have c' : 0 < k := by
        rcases lt_trichotomy k 0 with _ | ht | ht
        . apply aux_9 ha
          rw [hk]
          exact hb
        . rw [ht] at hk
          simp at hk
          rw [← hk] at hb
          rw [ht]
          exact hb
        . exact ht
      rw [Int.lt_iff_add_one_le] at c'
      simp at c'
      rw [le_iff_eq_or_lt] at c'
      rcases c' with c' | c'
      . rw [c'] at c
        trivial
      . have : a ∉ ℤ ⬝ a := by
          rw [h']
          unfold genℤ
          simp
          intro x hn
          rw [← hn] at hk
          rw [← mul_assoc] at hk
          conv at hk =>
            arg 2
            rw [← one_mul b]
          rw [Int.mul_eq_mul_right_iff] at hk
          apply aux_10 k x c' hk
          linarith
        have : a ∈ ℤ ⬝ a := by simp
        contradiction

noncomputable def gen (S : AddSubgroup ℤ) : ℤ := generation S |>.choose

theorem gen_spec (S : AddSubgroup ℤ) : S = ℤ ⬝ (gen S) := by
  unfold gen
  exact (generation S |>.choose_spec).2

theorem gen_nonneg (S : AddSubgroup ℤ) : 0 ≤ (gen S) := by
  unfold gen
  exact (generation S |>.choose_spec).1

theorem gen_unique (S : AddSubgroup ℤ) : 0 ≤ a → (S = ℤ ⬝ a) → a = gen S := by
  intro h h'
  haveI := gen_spec S
  haveI := Eq.trans h'.symm this
  apply generation_unique h (gen_nonneg S) this

theorem gen_cancel (a : ℤ) : 0 ≤ a → gen (ℤ ⬝ a) = a := by
  intro h
  symm
  apply gen_unique _ h (by simp)

theorem genby_neg (a : ℤ) : ℤ ⬝ (-a) = ℤ ⬝ a := by
  ext x
  simp [genℤ]
  apply Iff.intro
  all_goals
    intro ⟨k, hk⟩
    use -k
    linarith

theorem gen_cancel_neg (a : ℤ) : a ≤ 0 → gen (ℤ ⬝ a) = -a := by
  intro h
  rw [← genby_neg]
  apply gen_cancel
  linarith only [h]

theorem genby_abs {a : ℤ} : (ℤ ⬝ |a|) = (ℤ ⬝ a) := by
  if c : 0 ≤ a
    then
      have : |a| = a := by
        simp [Int.abs_eq_normalize]
        simp [normUnit]
        simp [if_pos c]
      rw [this]
    else
      have : |a| = -a := by
        simp [Int.abs_eq_normalize]
        simp [normUnit]
        simp [if_neg c]
      rw [this]
      apply genby_neg

@[simp] theorem gen_mem (S : AddSubgroup ℤ) : gen S ∈ S := by
  conv => rhs; rw [gen_spec S]
  simp

@[simp] theorem gen_mul_left_mem {S : AddSubgroup ℤ} (n : ℤ) : n * gen S ∈ S :=
  aux_6 _ (gen_mem S)

@[simp] theorem gen_mul_right_mem {S : AddSubgroup ℤ} (n : ℤ) : gen S * n ∈ S := by
  rw [mul_comm]
  exact aux_6 _ (gen_mem S)

@[simp] theorem gen_mul_left_iff {S : AddSubgroup ℤ} : ∀ {s}, (∃ n, n * gen S = s) ↔ s ∈ S := by
  intro s
  apply Iff.intro
  . intro ⟨n, hn⟩
    simp [← hn]
  . intro hs
    have := gen_spec S
    simp [genℤ] at this
    simp [AddSubgroup.ext_iff, Set.ext_iff] at this
    apply (this s).mp hs

@[simp] theorem gen_mul_right_iff {S : AddSubgroup ℤ} : ∀ {s}, (∃ n, gen S * n = s) ↔ s ∈ S := by
  conv =>
    intro s
    arg 1
    congr; intro n
    rw [mul_comm]
  exact gen_mul_left_iff

lemma aux_13 {a b t : ℤ} : 0 < a → a < b → t * b = a → False := by
  intro h1 h2 h3
  have b_pos : 0 < b := by linarith only [h1, h2]
  rcases lt_trichotomy t 1 with h | h | h
  . simp [Int.lt_iff_add_one_le] at h
    rw [le_iff_lt_or_eq] at h
    rcases h with h | h
    . have : t * b < 0 := Int.mul_neg_of_neg_of_pos h b_pos
      rw [h3] at this
      apply lt_irrefl 0 (lt_trans h1 this)
    . simp [h] at h3
      rw [← h3] at h1
      apply lt_irrefl 0 h1
  . simp [h] at h3
    rw [h3] at h2
    apply lt_irrefl a h2
  . have : 1 * b  < t * b:= by
      apply Int.mul_lt_mul h _ b_pos
      . linarith
      . trivial
    simp [h3] at this
    apply lt_irrefl b (lt_trans this h2)

theorem gen_least_pos {S : AddSubgroup ℤ} : 0 < gen S → IsLeast {s ∈ S | 0 < s} (gen S) := by
  intro h
  apply And.intro
  . simp [h]
  . rw [lowerBounds]
    simp
    intro x hx h'
    apply not_not.mp
    intro hn
    simp at hn
    have ⟨t, ht⟩ := (gen_mul_left_iff).mpr hx
    exact aux_13 h' hn ht

instance : Add (AddSubgroup ℤ) where
  add x y :=
    {
      carrier :=
        letI a := gen x
        letI b := gen y
        {r * a + s * b | (r : ℤ) (s : ℤ)}
      add_mem' := by
        intro a b ha hb
        simp at *
        obtain ⟨ra, sa, ha⟩ := ha
        obtain ⟨rb, sb, hb⟩ := hb
        use (ra + rb)
        use (sa + sb)
        rw [← ha, ← hb]
        linarith
      zero_mem' := by
        simp
        use 0
        use 0
        linarith
      neg_mem' := by
        intro c
        simp at *
        intro a b
        intro h
        use -a
        use -b
        linarith
    }

theorem add_comm' {A B : AddSubgroup ℤ} : A + B = B + A := by
  simp [HAdd.hAdd]
  simp [Add.add]
  ext x
  simp
  apply Iff.intro
  all_goals
    intro ⟨r, s, h⟩
    use s, r
    linarith

@[simp] theorem add_zero' {S : AddSubgroup ℤ} : S + ℤ ⬝ 0 = S := by
  simp [HAdd.hAdd]
  simp [Add.add]
  ext x
  simp [gen_cancel]

@[simp] theorem zero'_add {S : AddSubgroup ℤ} : ℤ ⬝ 0 + S = S := by
  rw [add_comm']
  exact add_zero'

@[simp] theorem subset_add_right' {A B : AddSubgroup ℤ} : A.carrier ⊆ (A + B).carrier := by
  simp [HAdd.hAdd]
  simp [Add.add]
  intro x hx
  simp
  have ⟨r, hr⟩ := gen_mul_left_iff.mpr hx
  use r, 0
  simp [hr]

/--gcd definition from artin-/
@[reducible]
noncomputable def gcd (a b : ℤ) := gen (ℤ ⬝ a + ℤ ⬝ b)

theorem gcd_linear_comb (ha : a ≠ 0) : ∃ r s : ℤ, gcd a b = r * a + s * b := by
  simp [gcd]
  simp [HAdd.hAdd]
  simp [Add.add]
  have : gen (genℤ a + genℤ b) ∈ genℤ a + genℤ b := by
    simp
  unfold HAdd.hAdd instHAdd at this
  simp [Add.add] at this
  obtain ⟨r, s, h⟩ := this
  rw [← h]
  rw [ne_iff_lt_or_gt] at ha
  rcases ha with ha | ha
  . use -r
    rw [gen_cancel_neg a (le_of_lt ha)]
    rcases lt_trichotomy b 0 with hb | hb | hb
    . use -s
      rw [gen_cancel_neg b (le_of_lt hb)]
      linarith
    . use 0
      rw [hb, gen_cancel 0 (by simp)]
      linarith
    . use s
      rw [gen_cancel b (le_of_lt hb)]
      linarith
  . use r
    rw [gen_cancel a (le_of_lt ha)]
    rcases lt_trichotomy b 0 with hb | hb | hb
    . use -s
      rw [gen_cancel_neg b (le_of_lt hb)]
      linarith
    . use 0
      rw [hb, gen_cancel 0 (by simp)]
      linarith
    . use s
      rw [gen_cancel b (le_of_lt hb)]

theorem gcd_comm : gcd a b = gcd b a := by simp [gcd, add_comm']

theorem gcd_nonneg : 0 ≤ gcd a b := by
  simp [gcd]
  apply gen_nonneg

theorem gcd_pos_of_ne_zero (ha : a ≠ 0) : 0 < gcd a b := by
  have := gcd_nonneg (a := a) (b := b)
  rw [lt_iff_le_and_ne]
  apply And.intro (gcd_nonneg (a := a) (b := b))
  intro hn
  have : a ∈ genℤ a + genℤ b := by
    apply Set.mem_of_mem_of_subset (s := ℤ ⬝ a)
    . simp
    . apply subset_add_right'
  have ⟨r, hr⟩ := gen_mul_left_iff.mpr this
  simp [gcd] at hn
  simp [← hn] at hr
  apply ha
  simp [hr]


/--Proposition 2.3.5 (a)-/
theorem gcd_divides_left (ha : a ≠ 0) : gcd a b ∣ a := by
  simp [gcd]
  have : gen (genℤ a + genℤ b) ∈ genℤ a + genℤ b := by
    simp
  have a_mem : a ∈ genℤ a + genℤ b := by
    apply Set.mem_of_mem_of_subset (s := ℤ ⬝ a)
    . simp
    . apply subset_add_right'
  have ⟨r, hr⟩ := gen_mul_right_iff.mpr a_mem
  simp [Dvd.dvd]
  use r
  simp [hr]

/--Proposition 2.3.5 (a)-/
theorem gcd_divides_right (ha : a ≠ 0) : gcd a b ∣ b := by
  rw [gcd_comm]
  rcases lt_trichotomy b 0 with hb | hb | hb
  . apply gcd_divides_left (ne_of_lt hb)
  . simp [hb]
  . apply gcd_divides_left (ne_of_gt hb)

end Group.Examples
