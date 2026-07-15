import Mathlib.Combinatorics.SimpleGraph.Basic

inductive Place where
| Room (id : Nat)
| Door (id : Nat)
deriving DecidableEq

abbrev room1 := Place.Room 1
abbrev room2 := Place.Room 2
abbrev room3 := Place.Room 3

abbrev door1 := Place.Door 1
abbrev door2 := Place.Door 2

abbrev myPlaces : List Place := [room1, room2, room3, door1, door2]

abbrev myEdges : List (Place × (List Place) ) := [
  (room1, [door1]),
  (room2, [door1, door2]),
  (room3, [door2]),
  (door1, [room1, room2]),
  (door2, [room2, room3])
]

def AlloyGraph_to_LeanGraph (edges : List (Place × (List Place))) (n1 : Place) (n2 : Place) : Bool := edges.any (fun (node, edges) => n1 == node && edges.contains n2)

def myAdjRelBool : Place → Place → Bool := AlloyGraph_to_LeanGraph myEdges

def myGraph : SimpleGraph { p : Place // p ∈ myPlaces } where
  Adj u v := myAdjRelBool u.val v.val
  symm := by constructor; decide
  loopless := by constructor; decide
