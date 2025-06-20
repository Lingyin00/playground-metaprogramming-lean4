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
