import Mathlib
import Partition
import Artin.Group.Basic
import Artin.Group.Homo

namespace Group

class Isomorphism {G G' : Type*} [Group G] [Group G'] (ϕ : G → G') extends Homomorphism ϕ where
  bijective : Function.Bijective ϕ

namespace Isomorphism

variable [Group G] [Group G'] (ϕ : G → G') [iso : Isomorphism ϕ]

instance : Isomorphism (ϕ.invFun) where
  linear x y := by
    have ⟨x', hx'⟩ := iso.2.2 x
    have ⟨y', hy'⟩ := iso.2.2 y
    rw [← hx', ← hy']
    rw [← iso.1.1]
    rw [Function.leftInverse_invFun iso.2.1]
    rw [Function.leftInverse_invFun iso.2.1]
    rw [Function.leftInverse_invFun iso.2.1]
  bijective := by
    constructor
    . intro x y
      have ⟨x', hx'⟩ := iso.2.2 x
      have ⟨y', hy'⟩ := iso.2.2 y
      rw [← hx', ← hy']
      rw [Function.leftInverse_invFun iso.2.1]
      rw [Function.leftInverse_invFun iso.2.1]
      intro h
      rw [h]
    . intro x
      use ϕ x
      rw [Function.leftInverse_invFun iso.2.1]

end Isomorphism

end Group
