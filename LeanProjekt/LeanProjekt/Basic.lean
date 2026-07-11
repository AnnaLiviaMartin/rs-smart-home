import Mathlib
/-
  Smart Home – Allergröbstes Modell

  Modelliert werden nur:
  - Räume: myNode und myEdges
  - Nachbarschaft: Adj := myAdjRelProp
  - Symmetrie: symm von SimpleGraph
  - Keine Selbstnachbarschaft: loopless von SimpleGraph
  - alle Räume liegen in einem Gebäude -> Alle Räume sind Teil desselben zusammenhängenden Graphen
-/

abbrev myNode := Fin 6

def myEdges : List (myNode × (List myNode)):= [
(0, [1, 2]),
(1, [0, 2, 3]),
(2, [0, 1, 4, 5]),
(3, [1]),
(4, [2]),
(5, [2]),
]

-- hier wird überprüft, ob knoten nachbarn sind, also eine gemeinsame Kante haben
def AlloyGraph_to_LeanGraph {Node : Type} [BEq Node] (edges : List (Node × (List Node))) (n1 : Node) (n2 : Node) : Bool :=
edges.any (fun (node, edges) => n1 == node && edges.contains n2)

-- um decide anwenden zu können (benötige ich hier) die Bool-Version
def myAdjRelBool : myNode → myNode → Bool := AlloyGraph_to_LeanGraph myEdges

-- SimpleGraph braucht als Typ aber myNode → myNode → Prop
abbrev myAdjRelProp : myNode → myNode → Prop := fun n1 n2 => myAdjRelBool n1 n2 = true

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
  Alle Räume sind Teil desselben zusammenhängenden Graphen
-/
-- Welche Knoten sind direkt neben n?
def neighbors (n : myNode) : List myNode :=
  match myEdges.find? (fun x => x.1 = n) with
  | some (_, ns) => ns
  | none => []

-- suche max. fuel Schritte, ob target erreicht werden kann von todo aus (Liste der Knoten, die wir untersuchen)
def reachableAux (fuel : Nat) (target : myNode) (todo : List myNode) (visited : List myNode) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      match todo with
      | [] => false
      | x :: xs =>
          if x = target then
            true
          else if x ∈ visited then
            reachableAux fuel target xs visited
          else
            reachableAux fuel target (xs ++ neighbors x) (x :: visited)

def reachableBool (start target : myNode) : Bool :=
  reachableAux 20 target [start] []

#eval neighbors 0
#eval neighbors 2
#eval reachableAux 20 5 [0] [] -- konvertiert das in untere Zeile
#eval reachableBool 0 5

def allNodes : List myNode := [0, 1, 2, 3, 4, 5]

def allReachable : Bool :=
  allNodes.all (fun start =>
    allNodes.all (fun target =>
      reachableBool start target))

#eval allReachable
