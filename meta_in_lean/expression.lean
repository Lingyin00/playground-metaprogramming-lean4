/- Chapter 2: Expression-/

import Lean

-- def main : IO Unit := IO.println "Hello, world!"
--set_option pp.universes true in
-- #check @List.map


open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Command

elab "demoListMap" : command => do
  let u₁ := mkLevelParam `u₁
  let u₂ := mkLevelParam `u₂

  -- α : Type u₁, β : Type u₂
  let α := mkSort u₁
  let β := mkSort u₂

  -- f : α → β, xs : List α
  let f := mkConst `f
  let xs := mkConst `xs

  -- List.map.{u₁, u₂} α β f xs
  let map := mkConst ``List.map [u₁, u₂]
  let fullApp := mkAppN map #[α, β, f, xs]

  logInfo m!"Expr: {fullApp}"

set_option pp.explicit true
set_option pp.universes true
demoListMap

#eval toString (mkLevelParam `u)

/- constructor Expr.const, name, a list of universe levels-/
open Nat
def z₁ := Expr.const `zero []
#eval z₁

-- double backtick make zero qualified
def z₂ := Expr.const ``zero []
#eval z₂

/- constructor Expr.app, expression for the function, expression for the argument-/
def z := Expr.const ``Nat.zero []
def one := Expr.app (.const ``Nat.succ []) z
#eval one

def natExpr: Nat → Expr
| 0 => z
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

/- Lambda expression
  | lam : Name → Expr → Expr → BinderInfo → Expr
  -/
def constZero : Expr :=
  .lam `x (.const ``Nat []) (.const ``Nat.zero []) BinderInfo.default
#eval constZero

/-**?** 1. when should I use mkAppN?
    2. how can I give in the correct universe level parameter?
    3. what is exactly BinderInfo.default?
    -/
def nat : Expr := .const ``Nat []
def addOne : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1])
    BinderInfo.default

/-? A little bit confusing for me-/
#check levelZero
def mapAddOneNil : Expr :=
  mkAppN (.const ``List.map [levelZero, levelZero])
    #[nat, nat, addOne, .app (.const ``List.nil [levelZero]) nat]

--turn Expr into a Lean term
elab "mapAddOneNil" : term => return mapAddOneNil

#check mapAddOneNil
#reduce mapAddOneNil

/- 1 + 2 with Expr.app-/
/-Expr.app (f) (x) -/
def OnePlusTwo : Expr :=
  Expr.app (Expr.app (Expr.const `Nat.add []) (mkNatLit 1)) (mkNatLit 2)
elab "OnePlusTwo" : term => return OnePlusTwo
#eval OnePlusTwo
#reduce OnePlusTwo

/- example 3 * (1+2) -/
def example01 : Expr :=
  Expr.app ( Expr.app (Expr.const `Nat.mul []) (
    Expr.app (
      Expr.app (Expr.const `Nat.add []) (mkNatLit 1)
    ) (mkNatLit 2)
  )
  ) (mkNatLit 3)

elab "example01" : term => return example01
#reduce example01

#check Lean.mkAppN

def exercise02 : Expr :=
  Lean.mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, mkNatLit 2]
elab "exercise02" : term => return exercise02
#reduce exercise02

def exercise03 : Expr :=
  Expr.lam `x (Expr.const `Nat [])
  (Lean.mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, Expr.bvar 0])
  BinderInfo.default

def exercise04 : Expr :=
  Expr.lam `a (Expr.const `Nat []) (
    Expr.lam `b (Expr.const `Nat []) (
      Expr.lam `c (Expr.const `Nat []) (
        Lean.mkAppN (Expr.const `Nat.add [])
        #[
          (Lean.mkAppN (Expr.const `Nat.mul []) #[Expr.bvar 1, Expr.bvar 2]),
          Expr.bvar 0
        ]
      ) BinderInfo.default
    ) BinderInfo.default
  ) BinderInfo.default
elab "exercise04" : term => return exercise04
#reduce exercise04 2 3 4

def exercise05 : Expr :=
  Expr.lam `x (Expr.const `Nat []) (
    Expr.lam `y (Expr.const `Nat []) (
      Lean.mkAppN (Expr.const `Nat.add [])
      #[Expr.bvar 1, Expr.bvar 0]
    ) BinderInfo.default
  ) BinderInfo.default
elab "exercise05" : term => return exercise05
#reduce exercise05 0 1

def exercise06 : Expr :=
  Expr.lam `x (Expr.const `String []) (
    Lean.mkAppN (Expr.const `String.append [])
    #[Lean.mkStrLit "hello, ", Expr.bvar 0]
  ) BinderInfo.default
elab "exercise06" : term => return exercise06
#eval exercise06 "Lingyin"

/-? an infix representation instead of And x x?-/
def exercise07 : Expr :=
  Expr.forallE `x (Expr.sort Lean.Level.zero) (
    Lean.mkAppN (Expr.const `And [])
    #[Expr.bvar 0, Expr.bvar 0]
  ) BinderInfo.default
elab "exercise07" : term => return exercise07
#reduce exercise07
def seven : Expr :=
  Expr.forallE `x (Expr.sort Lean.Level.zero)
  (Expr.app (Expr.app (Expr.const `And []) (Expr.bvar 0)) (Expr.bvar 0))
  BinderInfo.default
elab "seven" : term => return seven
#check seven  -- ∀ (x : Prop), x ∧ x : Prop
#reduce seven -- ∀ (x : Prop), x ∧ x

def exercise08 : Expr :=
  Expr.forallE `notUsed --notUsed means that here we don't have any name for variable **??**
  (Expr.const `Nat []) (Expr.const `String [])
  BinderInfo.default
elab "exercise08" : term => return exercise08
#check exercise08
#reduce exercise08

/-**?** I don't quite understand,
  why the type of hp was assigned to Expr.bvar 0,
  but the Expr.bvar 1 doesn't work at all.
  It is clear that the hp should has type p,
  where as p has de brujin index of 1?? -/
def exercise09 : Expr :=
  Expr.lam `p (Expr.sort Lean.Level.zero) (
    Expr.lam `hp (Expr.bvar 0) (Expr.bvar 0) BinderInfo.default
  ) BinderInfo.default
elab "exercise09" : term => return exercise09
#check exercise09
#reduce exercise09

def exercise10 : Expr :=
  Expr.sort (Nat.toLevel 7) -- **?** there's not something like Lean.Level.seven?
elab "exercise10" : term => return exercise10
#check exercise10
#reduce exercise10

/-**?** the difference of check and reduce?
 dose check just print out all the information,
 but reduce normalize the term more than check?-/
