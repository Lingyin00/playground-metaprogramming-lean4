/- Chapter 3: MetaM-/
-- MetaM gives access to the metavariable context
-- meta context: the set of metavariables that are currently declared and the values assgined to them
-- the CoreM gives meaning to constants like Nat.zero or List.map
-- the MetaM gives meaning to both metavariables and local hypothesis

import Lean
open Lean Lean.Expr Lean.Meta

-- Meta variablesa are used overall in meta programs.
-- They can be viewed as holes in an expression or as goals.

/- Goals are internally represented by metavariables.
   Each metavariable has:
   1. a local context containing hypothesis
   2. a target type
   3. a unique name usually rendered as ?m
   -/

/- To close a goal is like giving an expression of the target type.
   Internally, closing a goal in this way corresponds to assigning the metavariable.
   assignment ?m := e
-/

/- View for metavariable: holes in an expression. Later goals could be influenced by former fillings of the holes-/

/- Tactics use metavariables to communicate the current goals,
    the goals we get are holes in the final proof terms -/
example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans
  --?m1 := @Eq.trans α (f (f a)) ?b a ?m2 ?m3
  -- ?b: intermediate element of the transitivity proof, also occurs in ?m2 and ?m3
  -- now the current goals are: ?b, ?m2, ?m3
  apply h --**??** the first apply h kills two goals?!! ?b and ?m2
  apply h

--Each metavariable is identified by an MVarId(a unique Name)
--To create a new metavariable:
/- mkFreshExprMVar (type? : Option Expr) (kind := Metavarkind.natural)
      (userName := Name.anonymous) : MetaM Expr

      argument:
        - type? : the target type of the new metavariable
        - kind
        - unserName: metavariable's user-facing name

      Lean.Expr.mvarId! to extract the MVarId
      local context inherited from the current local context
      Metavariable is usually unassigned:
        assign (mvarId : MVarId) (var : Expr) : MetaM Unit
      **? assginment of metavariable**
        -/
#check Lean.MVarId.assign

--get information about a declared metavariable
--eg. type, local context and user-facing name
#check Lean.MVarId.getDecl

-- get the current assignment of a metavariable
#check Lean.getExprMVarAssignment?

-- check wether a metavariable is assigned
#check Lean.MVarId.isAssigned

-- a more powerful function
--#check Lean.Meta.instantiateMVars --**? it doesn't work**
-- **? when we assign a metavariable, existing expressions containing this metavariable are not immediately updated?**
-- **? brings our expresions up to date with the current metavariable state**

#check Lean.Meta.mkFreshExprMVar
#check Lean.mkArrow

/- expressions are only meaningful if they are interpreted in their local context-/
def e := Expr.fvar (FVarId.mk `h)
#check Expr

-- all operations involving fvars use this ambient local context
#check Lean.getLCtx

--**?looks reasonable but not totally clear**
-- update the ambient local context to match the goal we are currently working on
#check Lean.MVarId.withContext

-- free variables are identified by an FVarId
#check Lean.FVarId.getDecl
