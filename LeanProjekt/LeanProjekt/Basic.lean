/-
  Smart Home – Allergröbstes Modell

  Modelliert werden nur:
  - Räume
  - Nachbarschaft
  - Symmetrie
  - Keine Selbstnachbarschaft
  - alle Räume liegen in einem Gebäude
-/
import Mathlib

structure Raum where
  my_id: Nat
  nachbar_ids: Finset Nat

-- axiom keineSelbstNachbarschaft : ∀ r : Raum, ¬ (r.my_id ∈ r.nachbar_ids)

-- axiom symmetrie : ∀ r₁ r₂ : Raum, r₁.my_id ∈ r₂.nachbar_ids ∧ r₂.my_id ∈ r₁.nachbar_ids

abbrev myNode := Fin 6

def myEdges : List (myNode × (List myNode)):= [

(0, [1, 2]),

(1, [0, 2, 3]), -- 1 hat die Nachbarn 2 und 3

(2, [0, 1, 4, 5]), -- 2 hat die Nachbarn 4 und 5

(3, [1]), -- 3 hat den Nachbarn 1

(4, [2]), -- 4 hat den Nachbarn 2

(5, [2]), -- 5 hat den Nachbarn 2

]

-- myAdjRel = True gdw. n1 den Nachbarn n2 hat

-- hier wird überprüft, ob knoten nachbarn sind, also eine gemeinsame Kante haben
def AlloyGraph_to_LeanGraph {Node : Type} [BEq Node] (edges : List (Node × (List Node))) (n1 : Node) (n2 : Node) : Bool :=

edges.any (fun (node, edges) => n1 == node && edges.contains n2)

-- um decide anwenden zu können (benötige ich hier) die Bool-Version

def myAdjRelBool : myNode → myNode → Bool := AlloyGraph_to_LeanGraph myEdges

-- SimpleGraph braucht als Typ aber myNode → myNode → Prop

abbrev myAdjRelProp : myNode → myNode → Prop := fun n1 n2 => myAdjRelBool n1 n2 = true

-- SimpleGraph ist eine structure mit drei Feldern:

-- Adj: Adjazenz-Relation

-- symm: Beweis, dass Adj symmetrisch ist

-- loopless: Beweis, dass Adj nicht reflexiv ist

def myGraph : SimpleGraph myNode :=
{
  Adj := myAdjRelProp
  symm := by
    constructor
    unfold myAdjRelProp
    decide
  loopless := by
    constructor
    unfold myAdjRelProp
    decide
}

/-
def myGraph2 : SimpleGraph myNode := --SimpleGraph aus Adjazenzrelation bauen
{
Adj := myAdjRelProp
symm := by
  unfold Symmetric
  unfold myAdjRelProp
  decide
loopless := by
  constructor
  unfold myAdjRelProp
  decide
}
-/

theorem test :  ∀ n1 n2, myGraph.Adj n1 n2 → n1 ≠ n2
:= by apply SimpleGraph.Adj.ne

example : ∀ n1 n2, myGraph.Adj n1 n2 → n1 ≠ n2
:= by apply SimpleGraph.Adj.ne

example : ∀ n1 n2, myGraph.Adj n1 n2 → n1 ≠ n2 := by
  intro n1 n2 h
  exact SimpleGraph.Adj.ne h
