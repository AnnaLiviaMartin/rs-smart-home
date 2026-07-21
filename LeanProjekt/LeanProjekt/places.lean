import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap
import Mathlib.Combinatorics.SimpleGraph.Basic

inductive Place where
| Room (id : Nat)
| Door (id : Nat)
deriving DecidableEq

abbrev Edge := Finmap (fun _ : Place => Finset Place)

def AlloyGraph_to_LeanGraph (edges : Edge) (n1 : Place) (n2 : Place) : Bool :=
  match edges.lookup n1 with
  | none => false
  | some places => n2 ∈ places
--   edges.any (fun (node, edges) => n1 == node && edges.contains n2)

abbrev PlaceSet (places : Finset Place) := { p : Place // p ∈ places } -- Menge an Places, aus dem die tatsächlich verwendeten ausgewählt werden können

abbrev GebäudePlan (places : Finset Place) := SimpleGraph (PlaceSet places)

structure Person where
  id : Nat

abbrev Belegung := Finmap (fun _ : Place => Finset Person)
abbrev Belegung_safe (places : Finset Place) :=
  Finmap (fun _ : (PlaceSet places) => Finset Person)

def invariant_Belegung_konsistent (places : Finset Place) (plan : GebäudePlan places) (belegung : Belegung_safe places) := False


def edgeIsBipartite (u v : Place) : Prop :=
  match u, v with
  | .Room _, .Door _ => True
  | .Door _, .Room _ => True
  | _      , _       => False

def edgeIsBipartiteBool (u v : Place) : Bool :=
  match u, v with
  | .Room _, .Door _ => true
  | .Door _, .Room _ => true
  | _      , _       => false

-- Lean mitteilen, dass es für das Prädikat edgeIsBipartite einen
-- Algorithmus gibt, der (in endlicher Zeit) entscheiden kann,
-- ob edgeIsBipartite u v eine wahre oder eine falsche Aussage ist.
instance (u v : Place) : Decidable (edgeIsBipartite u v) :=
  match h : edgeIsBipartiteBool u v with
  -- Beweislast 1: edgeIsBipartiteBool u v = true → edgeIsBipartite u v
  | true => .isTrue (
    by
      unfold edgeIsBipartite
      unfold edgeIsBipartiteBool at h
      cases u
      · cases v
        · simp at h
        · simp
      . cases v
        · simp
        · simp at h
  )
  -- Beweislast 2: edgeIsBipartiteBool u v = false → ¬edgeIsBipartite u v
  | false => .isFalse (by cases u <;> cases v <;> simp_all[edgeIsBipartite, edgeIsBipartiteBool])

def adjIsBipartite {places : Finset Place} (adj : (PlaceSet places) → (PlaceSet places) → Prop) :=
  ∀ (u v : PlaceSet places), adj u v → edgeIsBipartite u v

structure BipartitePlaceGraph (places : Finset Place) extends SimpleGraph (PlaceSet places) where
  bipartite : adjIsBipartite Adj -- das ist das "geerbte" Adj aus der Def. von SimpeGraph
