import Lean

open Lean Parser.Term

local instance : Monad List where
  pure x := [x]
  bind la alb := la.map alb |>.join

local instance : Alternative List where
  failure := []
  orElse la ula :=
    match la with
    | [] => ula ()
    | x => x

declare_syntax_cat list_comp_constraint
syntax ident " ← " term : list_comp_constraint
syntax term : list_comp_constraint
syntax "[" term "|" list_comp_constraint,* "]" : term

macro_rules
| `([$computation:term | $(constraint),*]) => do
  let f : TSyntax `list_comp_constraint → MacroM (TSyntax ``doSeqItem)
    | `(list_comp_constraint| $var:ident ← $body:term) => `(doSeqItem | let $var ← ($body))
    | `(list_comp_constraint| $cond:term) => `(doSeqItem| guard ($cond))
    | _ => Macro.throwUnsupported
  let ts ← constraint.getElems.mapM f
  `(do $ts* pure ($computation))

def X : List Nat := [0,1,2,3,4]
def Y := [x + y | x ← X, y ← X, y < 2]
/- Y is equivalent to Z -/
def Z := do
  let x ← X
  let y ← X
  guard (y < 2)
  pure (x + y)

#eval Y = Z
