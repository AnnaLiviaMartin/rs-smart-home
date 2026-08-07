import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Insert

/-
  Objekte, übernommen logisch aus Alloy, statisch: GebäudePlan ist die feste Topologie
-/

abbrev PersonId := Nat
abbrev RaumId := Nat

inductive Raumart where
  | Zimmer (id : Nat)
  | Garten
  deriving DecidableEq, Repr

structure Raum where
  id : RaumId
  raumart : Raumart
  personen : Finset PersonId
  deriving DecidableEq

structure Tuer where
  id : Nat
  offen : Bool
  deriving DecidableEq, Repr

inductive Ort where
  | Raum (r : Raum)
  | Tuer (t : Tuer)
  deriving DecidableEq

inductive Personenart where
  | Bewohner
  | Gast
  deriving DecidableEq, Repr

structure Person where
  id : PersonId
  art : Personenart
  letzterRaum : Option RaumId
  deriving DecidableEq, Repr

/-
  Hilfsprädikate
-/
def istRaum : Ort → Prop
  | .Raum _ => True
  | .Tuer _ => False

def istTuer : Ort → Prop
  | .Raum _ => False
  | .Tuer _ => True

def istBewohner : Person → Prop
  | p => p.art = Personenart.Bewohner

def istGast : Person → Prop
  | p => p.art = Personenart.Gast

def istGarten : Ort → Prop
  | .Raum r => r.raumart = .Garten
  | .Tuer _ => False

/-
  Tür und Raum, Personen Graphen aufbauen
-/

abbrev OrtSet (Orte : Finset Ort) := { p : Ort // p ∈ Orte } -- Menge an Orten, aus dem die tatsächlich verwendeten ausgewählt werden können

abbrev Belegung_safe (Orte : Finset Ort) := Finmap (fun _ : (OrtSet Orte) => Finset Person) -- arbeitet nur mit den erlaubten Orten aus Orte

abbrev Kante := Finmap (fun _ : Ort => Finset Ort) -- Graph-Kante für Ort: [Ort, Menge an Orten]

abbrev GebaeudePlan (Orte : Finset Ort) := SimpleGraph (OrtSet Orte) -- Graph, dessen Knoten genau die Orte aus Orte sind

def OrteSindBenachbart (Kanten : Kante) (n1 : Ort) (n2 : Ort) : Bool := -- Gibt es von n1 aus eine Verbindung zu n2?
  match Kanten.lookup n1 with
  | none => false
  | some nachbarn => n2 ∈ nachbarn
--   Kanten.any (fun (node, Kantes) => n1 == node && Kantes.contains n2)

-- Ein Raum kann nicht mit anderen Räumen direkt verbunden sein
def KanteIsBipartite (u v : Ort) : Prop :=
  match u, v with
  | .Raum _, .Tuer _ => True
  | .Tuer _, .Raum _ => True
  | _      , _       => False

def KanteIsBipartiteBool (u v : Ort) : Bool :=
  match u, v with
  | .Raum _, .Tuer _ => true
  | .Tuer _, .Raum _ => true
  | _      , _       => false

-- Lean mitteilen, dass es für das Prädikat KanteIsBipartite einen
-- Algorithmus gibt, der (in endlicher Zeit) entscheiden kann,
-- ob KanteIsBipartite u v eine wahre oder eine falsche Aussage ist.
instance (u v : Ort) : Decidable (KanteIsBipartite u v) :=
  match h : KanteIsBipartiteBool u v with
  -- Beweislast 1: KanteIsBipartiteBool u v = true → KanteIsBipartite u v
  | true => .isTrue (
    by
      unfold KanteIsBipartite
      unfold KanteIsBipartiteBool at h
      cases u
      · cases v
        · simp at h
        · simp
      . cases v
        · simp
        · simp at h
  )
  -- Beweislast 2: KanteIsBipartiteBool u v = false → ¬KanteIsBipartite u v
  | false => .isFalse (by cases u <;> cases v <;> simp_all[KanteIsBipartite, KanteIsBipartiteBool])

def adjIsBipartite {Orte : Finset Ort} (adj : (OrtSet Orte) → (OrtSet Orte) → Prop) :=
  ∀ (u v : OrtSet Orte), adj u v → KanteIsBipartite u v

-- Gebäudeplan, der bipartite ist
structure BipartitePlaceGraph (orte : Finset Ort) extends SimpleGraph (OrtSet orte) where
  bipartite : adjIsBipartite Adj -- das ist das "geerbte" Adj aus der Def. von SimpeGraph

def belegtePersonen {orte : Finset Ort} (b : Belegung_safe orte) (o : OrtSet orte) : Finset Person :=
  (b.lookup o).getD ∅

def einePersonGenauEinOrt {orte : Finset Ort} {personen : Finset Person} (b : Belegung_safe orte) : Prop :=
  ∀ p ∈ personen,
    (orte.attach.filter fun o => p ∈ belegtePersonen b o).card = 1

def tuerOffenWennPerson {orte} (b : Belegung_safe orte) : Prop :=
  ∀ o : OrtSet orte,
    match o.1 with
    | .Tuer t =>
        t.offen = false →
        belegtePersonen b o = ∅
    | .Raum _ =>
        True

def gartenHatGenauEineTuer {orte : Finset Ort} (G : SimpleGraph (OrtSet orte)) : Prop :=
  ∀ g : OrtSet orte,
    istGarten g.1 →
    ∃! t : OrtSet orte,
      istTuer t.1 ∧ G.Adj g t

-- Gebäudeplan, der bipartite ist, nachbar-symmetrie gegeben, damit auch tuerVerbindetZweiRaeume, alleNachbarnSindSymmerisch inkl. Axiome
structure BipartiteOrtGraph (orte : Finset Ort) (personen : Finset Person) (belegung : Belegung_safe orte) extends SimpleGraph (OrtSet orte) where
  bipartite : adjIsBipartite Adj -- das ist das "geerbte" Adj aus der Def. von SimpeGraph
  genauEinGarten : ∃! g : Ort, istGarten g ∧ g ∈ orte
  einePersonGenauEinOrt : einePersonGenauEinOrt (personen := personen) belegung
  tuerOffenWennPersonEnthalten : tuerOffenWennPerson belegung
  --gartenHatGenauEinenNachbarn : gartenHatGenauEineTuer toSimpleGraph

/-
  Invarianten, die bereits implizit definiert sind:

  offen besitzt genau einen Bool-Wert.
  Durch offen : OrtSet orte → Bool bereits garantiert.

  letzterRaum ist entweder ein Raum oder nicht gesetzt.
  Durch letzterRaum : Person → Option Raum bereits garantiert.

  Jede Person ist Bewohner:in oder Gast.
  Durch den induktiven Datentyp Person bereits garantiert.

  Räume und Türen sind getrennte Ort-Konstruktoren.
  Durch Ort.Raum und Ort.Tuer bereits garantiert.

  Die Nachbarschaftssymmetrie und die Schleifenfreiheit sind bei SimpleGraph ebenfalls bereits Bestandteile der Struktur.

  Zwischen zwei Räumen liegt jeweils eine Tür.

  Türen verbinden jeweils zwei Räume. Räume können nicht mit anderen Räumen direkt verbunden sein.
-/

/-
  Invarianten: was trotz Veränderung gleich bleibt

  pre_   = Vorbedingung vor der Aktion
  post_  = Bedingung, die nach der Aktion gilt
-/

/-
  Beweise
-/

/-
  Beispiel
-/

-- Objekte
def room1 : Ort := .Raum {id := 1, raumart := .Zimmer 1, personen := ∅}
def room2 : Ort := .Raum {id := 2, raumart := .Zimmer 2, personen := ∅}
def room3 : Ort := .Raum {id := 3, raumart := .Garten, personen := ∅}

def door1 : Ort := .Tuer {id := 1, offen := false}
def door2 : Ort := .Tuer {id := 2, offen := true}

def person1 : Person := {id := 1, art := .Bewohner, letzterRaum := some 1} -- letzter Raum muss nicht verbunden sein logisch?
def person2 : Person := {id := 2, art := .Gast, letzterRaum := some 1}
def person3 : Person := {id := 3, art := .Gast, letzterRaum := some 2}

-- Listen
abbrev meineOrte : Finset Ort :=
  ∅ |> insert room1
    |> insert room2
    |> insert room3
    |> insert door1
    |> insert door2

abbrev meinePersonen : Finset Person :=
  ∅ |> insert person1
    |> insert person2
    |> insert person3

abbrev initBelegung : Belegung_safe meineOrte :=
  ∅ |> Finmap.insert ⟨room1, by decide⟩ (∅ |> insert person1 |> insert person2)
    |> Finmap.insert ⟨room2, by decide⟩ ∅
    |> Finmap.insert ⟨room3, by decide⟩ ∅
    |> Finmap.insert ⟨door1, by decide⟩ ∅
    |> Finmap.insert ⟨door2, by decide⟩ (∅ |> insert person3)

-- Graph
abbrev meineKanten : Kante :=
  ∅ |> Finmap.insert room1 (∅ |> insert door1)
    |> Finmap.insert room2 (∅ |> insert door1 |> insert door2)
    |> Finmap.insert room3 (∅ |> insert door2)
    |> Finmap.insert door1 (∅ |> insert room1 |> insert room2)
    |> Finmap.insert door2 (∅ |> insert room2 |> insert room3)

def myAdjRelBool : Ort → Ort → Bool := OrteSindBenachbart meineKanten

def myGraph : GebaeudePlan meineOrte where
  Adj u v := myAdjRelBool u.val v.val
  symm := by constructor; decide
  loopless := by constructor; decide

def myBipartiteGraph : BipartiteOrtGraph meineOrte meinePersonen initBelegung where
  Adj u v := myAdjRelBool u.val v.val
  symm := by constructor; decide
  loopless := by constructor; decide
  bipartite := by
    unfold adjIsBipartite
    decide
  genauEinGarten := by
    refine ⟨room3, ?_, ?_⟩
    · simp [room3, meineOrte, istGarten]
    · intro g hg
      rcases hg with ⟨hgarten, hgorte⟩
      simp [meineOrte, room1, room2, room3, door1, door2] at hgorte
      rcases hgorte with rfl | rfl | rfl | rfl | rfl
      · simp [istGarten] at hgarten
      · simp [istGarten] at hgarten
      · rfl
      · simp [istGarten] at hgarten
      · simp [istGarten] at hgarten
  einePersonGenauEinOrt := by
    unfold einePersonGenauEinOrt
    intro p hp
    simp [meinePersonen] at hp
    rcases hp with rfl | rfl | rfl
    · simp [
        room1,
        door1,
        person3
      ]
      rfl
    · simp [
        room2,
        door1,
        door2,
        person2
      ]
      rfl
    · simp [
        room3,
        door2,
        person1
      ]
      rfl
  tuerOffenWennPersonEnthalten := by
    unfold tuerOffenWennPerson
    intro o
    rcases o with ⟨o, ho⟩
    cases o with
    | Raum r => trivial
    | Tuer t =>
      simp [
        meineOrte,
        door1,
        door2,
        room1,
        room2,
        room3
      ] at ho
      rcases ho with hdoor2 | hdoor1
      · subst t
        intro hclosed
        cases hclosed
      · subst t
        intro hclosed
        simp [
          belegtePersonen,
          initBelegung,
          meineOrte,
          door1,
          door2,
          room1,
          room2,
          room3
        ]
        rfl

 /- gartenHatGenauEinenNachbarn := by
      intro g hg
      obtain ⟨gval, gprop⟩ := g
      simp [meineOrte, room1, room2, room3, door1, door2] at gprop
      rcases gprop with rfl | rfl | rfl | rfl | rfl <;>
        simp [istGarten] at hg
      -- Ab hier bleibt nur noch der Fall gval = room3 übrig
      refine ⟨⟨door2, by simp [meineOrte]⟩, ?_, ?_⟩
      · refine ⟨by simp [istTuer, door2], ?_⟩
        show myAdjRelBool room3 door2 = true
        decide
      · intro y hy
        obtain ⟨yval, yprop⟩ := y
        obtain ⟨hTuer, hAdj⟩ := hy
        simp [meineOrte, room1, room2, room3, door1, door2] at yprop
        rcases yprop with rfl | rfl | rfl | rfl | rfl <;>
          first
          | (revert hTuer; simp [istTuer]; done)
          | exact absurd (hAdj : myAdjRelBool _ _ = true) (by decide)
          | rfl
          | sorry
-/