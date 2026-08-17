import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Insert

structure Person where
  name: String
deriving DecidableEq, Repr

structure Raum where
  personen: Finset Person
deriving DecidableEq

structure Tuer where
  personen: Finset Person
deriving DecidableEq

inductive Ort where
| Raum (r : Raum)
| Tuer (t : Tuer)
deriving DecidableEq

def person1 : Person := {name := "Joghurta"}

abbrev room1 : Ort := Ort.Raum { personen := {person1} }
abbrev room2 := Ort.Raum {personen := ∅}
abbrev tuer := Ort.Tuer {personen := ∅}

-- Nachbarschaftsbeziehungen durch SimpleGraph

--Finset damit Orte endlich sind
abbrev myOrts : Finset Ort :=
  ∅ |> insert room1
    |> insert room2
    |> insert tuer

abbrev Kante := Finmap (fun _ : Ort => Finset Ort)

abbrev myEdges : Kante :=
  ∅ |> Finmap.insert room1 (∅ |> insert tuer)
    |> Finmap.insert room2 (∅ |> insert tuer)
    |> Finmap.insert tuer (∅ |> insert room1 |> insert room2)

def OrteSindBenachbart (Kanten : Kante) (n1 : Ort) (n2 : Ort) : Bool := -- Gibt es von n1 aus eine Verbindung zu n2?
  match Kanten.lookup n1 with
  | none => false
  | some nachbarn => n2 ∈ nachbarn

def myAdjRelBool : Ort → Ort → Bool := OrteSindBenachbart myEdges

abbrev OrtSet (Orte : Finset Ort) := { p : Ort // p ∈ Orte }

abbrev GebaeudePlan (Orte : Finset Ort) := SimpleGraph (OrtSet Orte)

def myGraph : GebaeudePlan myOrts where
  Adj u v := myAdjRelBool u.val v.val
  symm := by constructor; decide
  loopless := by constructor; decide

-- Eigenschaften / Prädikate ---

def istInOrt_1 (p: Person) (von: Raum)  : Prop :=
  p ∈ von.personen

def istInOrt_2 (p: Person) (nach: Raum) : Prop :=
  p ∈ nach.personen

def istInTuer (p: Person) (t: Tuer) : Prop :=
  p ∈ t.personen

-- Zustandsübergänge --

def move_grob (p: Person) (von nach: Raum): Raum × Raum := --hier noch das if einbauen ob die Tür dazwischen offen ist
  let von' : Raum := {
    personen := von.personen.erase p
  }
  let nach' : Raum := {
    personen := insert p nach.personen
  }
 (von', nach')

 def move_fein_To_Tuer (p: Person) (von: Raum) (nach: Tuer): Raum × Tuer :=
  let von' : Raum := {
    personen := von.personen.erase p
  }
  let nach' : Tuer := {
    personen := insert p nach.personen
  }
  (von', nach')

  def move_fein_To_Raum (p: Person) (von: Tuer) (nach: Raum) : Tuer × Raum :=
  let von' : Tuer := {
    personen := von.personen.erase p
  }
  let nach' : Raum := {
    personen := insert p nach.personen
  }
  (von', nach')

-- Beweise ---

theorem beweise_move_grob_V1 (p : Person) (von nach: Raum) :
  istInOrt_1 p von → istInOrt_2 p (move_grob p von nach).2 := by
  intro h
  simp [istInOrt_2, move_grob]

#check Finset.mem_insert.mpr

theorem beweise_move_grob_V2 (p: Person) (von nach: Raum) :
  istInOrt_1 p von → istInOrt_2 p (move_grob p von nach).2 := by
  intro h
  apply Finset.mem_insert.mpr
  left
  rfl

theorem beweise_move_fein_To_Tuer (p: Person) (von: Raum) (nach: Tuer) :
  istInOrt_1 p von → istInTuer p (move_fein_To_Tuer p von nach).2 := by
  intro h
  apply Finset.mem_insert.mpr
  left
  rfl

theorem beweise_move_fein_To_Raum (p: Person) (von: Tuer) (nach: Raum):
  istInTuer p von → istInOrt_2 p (move_fein_To_Raum p von nach).2 := by
  intro h
  apply Finset.mem_insert.mpr
  left
  rfl

-- Beweise mit Invarianten --

def personenGesamt (von nach: Raum): Finset Person :=
  von.personen ∪ nach.personen

theorem person_geht_nicht_verloren (p : Person) (von nach : Raum):
    p ∈ von.personen → personenGesamt von nach = personenGesamt (move_grob p von nach).1 (move_grob p von nach).2 := by
  intro h
  ext x --Lean erkennt Person aus Finset, Kurzform für intro?
  by_cases hx : x = p
  · subst x
    simp [personenGesamt, move_grob, h]
  · simp [personenGesamt, move_grob, hx]

def personenGesamt_V2 (raeume : Raum × Raum) : Finset Person :=
  raeume.1.personen ∪ raeume.2.personen

theorem person_geht_nicht_verloren_V2 (p : Person) (von nach : Raum):
    p ∈ von.personen → personenGesamt_V2 (von, nach) = personenGesamt_V2 (move_grob p von nach) := by
  intro h
  ext x
  by_cases hx : x = p
  · subst x
    simp [personenGesamt_V2, move_grob, h]
  · simp [personenGesamt_V2, move_grob, hx]
