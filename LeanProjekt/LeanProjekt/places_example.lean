import LeanProjekt.places

abbrev room1 := Place.Room 1
abbrev room2 := Place.Room 2
abbrev room3 := Place.Room 3

abbrev door1 := Place.Door 1
abbrev door2 := Place.Door 2

abbrev myPlaces : Finset Place :=
  ∅ |> insert room1
    |> insert room2
    |> insert room3
    |> insert door1
    |> insert door2

abbrev myEdges : Edge :=
  ∅ |> Finmap.insert room1 (∅ |> insert door1)
    |> Finmap.insert room2 (∅ |> insert door1 |> insert door2)
    |> Finmap.insert room3 (∅ |> insert door2)
    |> Finmap.insert door1 (∅ |> insert room1 |> insert room2)
    |> Finmap.insert door2 (∅ |> insert room2 |> insert room3)

def myAdjRelBool : Place → Place → Bool := AlloyGraph_to_LeanGraph myEdges

def myGraph : GebäudePlan myPlaces where
  Adj u v := myAdjRelBool u.val v.val
  symm := by constructor; decide
  loopless := by constructor; decide

def myBipartiteGraph : BipartitePlaceGraph myPlaces where
  Adj u v := myAdjRelBool u.val v.val
  symm := by constructor; decide
  loopless := by constructor; decide
  bipartite := by
    unfold adjIsBipartite
    decide
