import Mathlib.Tactic.DeriveFintype
import Mathlib.Combinatorics.SimpleGraph.Basic

inductive Place where
| room1 | room2 | room3
| door1 | door2
deriving DecidableEq, Fintype

abbrev myEdges : List (Place × (List Place) ) := [
  (.room1, [.door1]),
  (.room2, [.door1, .door2]),
  (.room3, [.door2]),
  (.door1, [.room1, .room2]),
  (.door2, [.room2, .room3])
]

def AlloyGraph_to_LeanGraph (edges : List (Place × (List Place))) (n1 : Place) (n2 : Place) : Bool := edges.any (fun (node, edges) => n1 == node && edges.contains n2)

def myAdjRelBool : Place → Place → Bool := AlloyGraph_to_LeanGraph myEdges

def myGraph : SimpleGraph Place where
  Adj u v := myAdjRelBool u v
  symm := by constructor; decide
  loopless := by constructor; decide
