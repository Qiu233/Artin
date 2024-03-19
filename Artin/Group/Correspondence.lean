import Mathlib
import Artin.Group.Homo

namespace Group

open Homomorphism

variable [Group G] [Group 𝒢]
variable (ϕ : G → 𝒢) [homo : Homomorphism ϕ]

-- def K := ker ϕ

def inverse (ℋ : Subgroup 𝒢) : Subgroup G where
  carrier := {g : G | ϕ g ∈ ℋ}
  mul_mem' {x y} hx hy := by
    simp at *
    apply ℋ.mul_mem' hx hy
  one_mem' := by
    simp
    exact ℋ.one_mem'
  inv_mem' {x} hx := by
    simp at *
    exact hx

theorem inverse_contains_kernel : (ker ϕ).carrier ⊆ (inverse ϕ ℋ).carrier := by
  simp [ker, inverse]
  intro x hx
  rw [hx]
  apply ℋ.one_mem'

theorem inverse_normal_of_normal :
  Subgroup.Normal ℋ → Subgroup.Normal (inverse ϕ ℋ) := by
  intro ⟨h⟩
  apply Subgroup.Normal.mk
  simp [inverse]
  intro n hn g
  apply h (ϕ n) hn

theorem normal_of_surj_of_inverse_normal :
    Function.Surjective ϕ → Subgroup.Normal (inverse ϕ ℋ) → Subgroup.Normal ℋ := by
  intro surj ⟨normal_inv⟩
  apply Subgroup.Normal.mk
  simp [inverse] at normal_inv
  intro 𝓃 h𝓃 ℊ
  have ⟨n, hn⟩ := surj 𝓃
  have ⟨g, hg⟩ := surj ℊ
  rw [← hn, ← hg]
  apply normal_inv
  simp [hn, h𝓃]

def corr_map (H : {H : Subgroup G | (ker ϕ).carrier ⊆ H.carrier}) : Subgroup 𝒢 where
  carrier := {ϕ h | h ∈ H.1}
  mul_mem' {𝓍 𝓎} h𝓍 h𝓎 := by
    simp at *
    obtain ⟨x, hx⟩ := h𝓍
    obtain ⟨y, hy⟩ := h𝓎
    use x * y
    apply And.intro
    . apply H.1.mul_mem' hx.1 hy.1
    . rw [← hx.2, ← hy.2]
      apply homo.linear
  one_mem' := by
    simp
    use 1
    simp
    apply H.1.one_mem'
  inv_mem' {𝓍} h𝓍 := by
    simp at *
    obtain ⟨x, hx⟩ := h𝓍
    use x⁻¹
    apply And.intro
    . apply H.1.inv_mem' hx.1
    . simp
      rw [hx.2]

def corr_map' (ℋ : Subgroup 𝒢) : {H : Subgroup G | (ker ϕ).carrier ⊆ H.carrier} where
  val :=
  {
    carrier := {g | ϕ g ∈ ℋ}
    mul_mem' := by
      intro x y hx hy
      simp at *
      apply ℋ.mul_mem' hx hy
    one_mem' := by
      simp
      apply ℋ.one_mem'
    inv_mem' := by
      intro x hx
      simp at *
      exact hx
  }
  property := by
    simp [ker]
    intro g hg
    rw [hg]
    apply ℋ.one_mem'

theorem corr_map_left_inverse (H : {H : Subgroup G | (ker ϕ).carrier ⊆ H.carrier}) :
    (corr_map' ϕ) (corr_map ϕ H) = H := by
  simp [corr_map, corr_map']
  congr
  ext g
  simp
  apply Iff.intro
  . intro ⟨h, hh⟩
    have coset_sub : h * (ker ϕ) ⊆ H.1 := by
      simp [ker, cmul_left]
      intro x ⟨y, hy⟩
      rw [← hy.2]
      apply H.1.mul_mem'
      . apply hh.1
      . apply Set.mem_of_subset_of_mem (s₁ := ker ϕ)
        . have := H.2
          simp at this
          apply this
        . simp [ker]
          exact hy.1
    have g_mem_coset : g ∈ h * ker ϕ := by
      simp [ker, cmul_left]
      use h⁻¹ * g
      apply And.intro
      . simp [hh.2]
      . simp [← mul_assoc]
    apply Set.mem_of_subset_of_mem (s₁ := h * ker ϕ) coset_sub g_mem_coset
  . intro h
    use g

theorem corr_map_right_inverse (surj : Function.Surjective ϕ) (ℋ : Subgroup 𝒢) :
    (corr_map ϕ) (corr_map' ϕ ℋ) = ℋ := by
  simp [corr_map, corr_map']
  congr
  ext ℊ
  apply Iff.intro
  . intro ⟨g, hg⟩
    rw [← hg.2]
    exact hg.1
  . intro h
    simp at *
    obtain ⟨g, hg⟩ := surj ℊ
    use g
    simp [hg, h]


theorem correspondence (surj : Function.Surjective ϕ) :
  {H : Subgroup G | (ker ϕ).carrier ⊆ H.carrier} ≃ Subgroup 𝒢 :=
    ⟨corr_map ϕ, corr_map' ϕ, corr_map_left_inverse ϕ, corr_map_right_inverse ϕ surj⟩


end Group

#check LieIdeal.ker_incl
#check Subgroup.ker_inclusion
#check MonoidHom.ker
