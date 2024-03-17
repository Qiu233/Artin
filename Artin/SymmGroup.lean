import Mathlib

theorem Equiv.comp_of_invFun [Nonempty α] [Nonempty β] (f : α ≃ β) (g : β ≃ γ) :
    f.invFun ∘ g.invFun = (g ∘ f).invFun := by
  ext t
  unfold Function.invFun
  if h : ∃ x, (g ∘ f) x = t
    then
      rw [dif_pos h]
      apply (Function.Injective.comp g.injective f.injective ·)
      rw [Exists.choose_spec h]; simp
    else
      refine absurd ?_ h
      apply Function.Surjective.comp g.surjective f.surjective

def Equiv.of_comp [Nonempty α] [Nonempty β] (f : α ≃ β) (g : β ≃ γ) : (α ≃ γ) :=
    ⟨g ∘ f, f.2 ∘ g.2, p1, p2⟩ where
  p1 := by
    rw [comp_of_invFun]
    exact Function.leftInverse_invFun $ Function.Injective.comp g.injective f.injective
  p2 := by
    rw [comp_of_invFun]
    exact Function.rightInverse_invFun $ Function.Surjective.comp g.surjective f.surjective


def Fin.swap {n : ℕ} (i j : Fin n) (t : Fin n) : Fin n :=
  if t = i then j
  else if t = j then i
  else t

theorem Fin.swap_inv {n : ℕ} {i j : Fin n} : Fin.swap i j ∘ Fin.swap i j = id := by
  ext t; simp
  unfold swap
  split
  . simp
    rw [(?_ : t = i)]
    split
    . congr
    . trivial
    assumption
  . split
    . simp; symm; congr
    . simp

def SymmGroup (n : ℕ+) := Fin n ≃ Fin n

namespace SymmGroup

def id : SymmGroup n :=
    ⟨_root_.id, _root_.id, p1, p2⟩ where
  p1 _ := by simp
  p2 _ := by simp

abbrev op :
    SymmGroup n → SymmGroup n → SymmGroup n :=
  Equiv.of_comp

abbrev inv : SymmGroup n → SymmGroup n := (·.symm)

instance : Group (SymmGroup n) where
  one := id
  mul := op
  inv := inv
  mul_assoc x y z := by unfold HMul.hMul instHMul op Equiv.of_comp; simp; trivial
  one_mul x := by unfold HMul.hMul instHMul op Equiv.of_comp; simp; congr
  mul_one x := by unfold HMul.hMul instHMul op Equiv.of_comp; simp; congr
  mul_left_inv x := by unfold HMul.hMul instHMul op Equiv.of_comp; simp; congr

instance decEq : DecidableEq (SymmGroup n) := (inferInstance : DecidableEq (Fin n ≃ Fin n))

-- def toList (x : SymmGroup n) : List (Fin n) := Fin.foldr n (λ i s => (x.1 i) :: s) []

def swap_id {n : ℕ+} (i j : Fin n) : SymmGroup n :=
  ⟨Fin.swap i j, Fin.swap i j, p1, p2⟩ where
  p1 := Function.leftInverse_iff_comp.mpr Fin.swap_inv
  p2 := Function.rightInverse_iff_comp.mpr Fin.swap_inv

def swap {n : ℕ+} (i j : Fin n) : SymmGroup n → SymmGroup n :=
  (op · (swap_id i j))

def pretty (g : SymmGroup n) : String :=
  let V := Fin.foldr n (λ i s => i :: s) []
  let E := Fin.foldr n (λ i s => (i, g.1 i) :: s) []
  compute_blocks V E
    |>.filter (·.length ≥ 2)
    |>.map (List.rotateLeft)
    |>.map (·.map (Fin.val) |>.map (·+1) |>.map toString |> String.intercalate " ")
    |>.map ("(" ++ · ++ ")")
    |> String.intercalate " " where
  compute_blocks {α : Type} [DecidableEq α]
    (V : List α) (E : List (α × α)) : List (List α) :=
  let rec block (u : α) (fuel : ℕ) : StateM (List α) (List α) := do
    if fuel = 0 then pure []
      else
        let unvis ← modifyGet (λ ns => (ns \ [u], ns \ [u]))
        let nexts := unvis.filter (λ v => (u, v) ∈ E) -- may be empty
        let ts ← sequence $ nexts.map (λ v => block v (fuel - 1))
        pure (u :: ts.join)
  V.map (λ v => ((block v V.length).run V).1)
    |>.pwFilter (¬ List.Perm · ·)

instance : ToString (SymmGroup n) where
  toString x := "`[" ++ toString n.1 ++ "|" ++ SymmGroup.pretty x ++ "]"

declare_syntax_cat symm_group_syntax
syntax "(" num* ")" : symm_group_syntax
syntax symm_group_syntax symm_group_syntax : symm_group_syntax
syntax "`[" num "|" symm_group_syntax "]" : term
syntax "`[" num "|" "]" : term
syntax "`[" num "]" : term

private def verify
  (n : Lean.TSyntax `num)
  (vs : Lean.TSyntaxArray `num)
  (verified : Lean.MacroM Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  let ex := vs.filter (λ x => x.getNat > n.getNat || x.getNat == 0)
  bif ex.size = 0
    then verified
    else Lean.Macro.throwError
      ("Some components are zero or exceed limit: " ++ ex.foldl (· ++ " " ++ toString ·.getNat) "")

macro_rules
| `(`[$n:num]) => `(SymmGroup.id (n := $n))
| `(`[$n:num | ]) => `(SymmGroup.id (n := $n))

| `(`[$_:num | ()]) => Lean.Macro.throwError "Permutation notations must have at least two components."
| `(`[$_:num | ($_:num)]) => Lean.Macro.throwError "Permutation notations must have at least two components."

| `(`[$n:num | ($l:num $r:num)]) =>
  let dec_nat (v : Lean.NumLit) := Lean.Syntax.mkNumLit <| toString <| v.getNat - 1
  verify n #[l, r]
  `(SymmGroup.swap_id (n := $n) $(dec_nat l) $(dec_nat r))
| `(`[$n:num | ($l:num $r:num $rs:num*)]) =>
  verify n (#[l, r])
  `(SymmGroup.op `[$n| ($r $rs*)] `[$n| ($l $r)])
| `(`[$n:num | $l:symm_group_syntax $r:symm_group_syntax]) =>
  `(SymmGroup.op `[$n| $l] `[$n| $r])

def c : SymmGroup 5 := SymmGroup.swap_id 0 4

def x := `[3|(1 2 3)]
def y := `[3|(1 2)]

example : x * x * x = 1 := by decide
example : y * y = 1 := by decide
example : y * x = x * x * y := by decide

example : `[3|(1 2 3)] = `[3|(2 3 1)] := by decide

#eval x * x
#eval y
#eval y * x
#eval `[5|(4 5) (1 2 3)]
#eval `[3|(2 3) (1 2)]
#eval `[3|(2 3) (1 2)]

end SymmGroup
