import Lean

-- def main : IO Unit := IO.println "Hello, world!"
-- set_option pp.universes true in
-- #check @List.map


open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Command

elab "demoListMap" : command => do
  let u₁ := mkLevelParam `u₁
  let u₂ := mkLevelParam `u₂

  -- Define α : Type u₁ and β : Type u₂
  let α := mkSort u₁
  let β := mkSort u₂

  -- Define f : α → β
  let fType := mkArrow α β
  let f := mkConst `f

  -- Define xs : List α
  let listα := mkApp (mkConst ``List [u₁]) α
  let xs := mkConst `xs

  -- Construct: List.map.{u₁ u₂} α β f xs
  let mapConst := mkConst ``List.map [u₁, u₂]
  let fullApp := mkAppN mapConst #[α, β, f, xs]

  -- Output the resulting expression
  logInfo m!"Expr: {fullApp}"

  demoListMap
