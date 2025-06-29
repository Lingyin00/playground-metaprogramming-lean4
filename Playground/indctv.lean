import Lean

open Lean Meta

def select: Bool → Nat → Nat → Nat
  | true, _, a => a
  | false, b, _ => b
#eval select true 1 2

/- will only return the value of c, because assumption looks up the bottommost hypothesis-/
def select01 (b : Bool) (a: Nat) (c: Nat):  Nat := by
  cases b
  · trace_state
    assumption
  · trace_state
    assumption

def select02 (b : Bool) (a: Nat) (c: Nat):  Nat := by
  cases b
  · trace_state
    exact a
  · trace_state
    exact c
#eval select01 false 1 2
#eval select01 true 7 999
#eval select02 true 4 6
#eval select02 false 4 6



def test (x : Nat) : Nat :=
  let x := x + 1 --shadowing
  x

def buildList (n : Nat) : List (IO Unit) :=
  List.range n |>.map fun i => IO.println s!"value: {i}"

def runTwice : IO Unit := do
  let xs := buildList 5
  IO.println "=== first ==="
  for act in xs do act
  IO.println "=== second ==="
  for act in xs do act
#eval runTwice

/- **TODO** : shared structure, reference counting, look up rust for similar ideas.-/
