import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

/-
  Objekte, übernommen logisch aus Alloy, statisch: GebäudePlan ist die feste Topologie
-/

inductive Person where
| Bewohner (id : Nat)
| Gast (id : Nat)
deriving DecidableEq, Repr

inductive Authentifizierung where
| auth (id : Nat)
deriving DecidableEq, Repr

inductive Raum where
| Zimmer (id : Nat)
| Garten
deriving DecidableEq, Repr

inductive Tuer where
| tuer (auth : Authentifizierung) -- jedeTuerHatEigenesAuthentifizierungsGeraet
deriving DecidableEq, Repr

inductive Ort where
| Raum (r : Raum)
| Tuer (t : Tuer)
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

def istGarten : Ort → Prop
  | .Raum r => r = .Garten
  | .Tuer _ => False

def istBewohner : Person → Prop
  | .Bewohner _ => True
  | .Gast _ => False

def istGast : Person → Prop
  | .Gast _ => True
  | .Bewohner _ => False

/-
  Tür und Raum, Personen Graphen aufbauen
-/

abbrev OrtSet (Orte : Finset Ort) := { p : Ort // p ∈ Orte } -- Menge an Orten, aus dem die tatsächlich verwendeten ausgewählt werden können

abbrev PersonSet (Personen : Finset Person) := { p : Person // p ∈ Personen }

abbrev Belegung_safe (Orte : Finset Ort) := Finmap (fun _ : (OrtSet Orte) => Finset Person) -- arbeitet nur mit den erlaubten Orten aus Orte

--abbrev Belegung (orte : Finset Ort) (personen : Finset Person) := OrtSet orte → PersonSet personen

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

def gartenHatGenauEineTuer {orte : Finset Ort} (G : SimpleGraph (OrtSet orte)) : Prop :=
  ∀ g : OrtSet orte,
    istGarten g.1 →
    ∃! t : OrtSet orte,
      istTuer t.1 ∧ G.Adj g t

-- Gebäudeplan, der bipartite ist, nachbar-symmetrie gegeben, damit auch tuerVerbindetZweiRaeume, alleNachbarnSindSymmerisch inkl. Axiome
/-
  Invarianten, die bereits implizit definiert sind:

  Jede Tür besitzt genau eine Authentifizierung.
  Durch Tuer.tuer (auth : Authentifizierung) bereits garantiert.

  offen besitzt genau einen Bool-Wert.
  Durch offen : OrtSet orte → Bool bereits garantiert.

  letzterRaum ist entweder ein Raum oder nicht gesetzt.
  Durch letzterRaum : Person → Option Raum bereits garantiert.

  Jede Person ist Bewohner:in oder Gast.
  Durch den induktiven Datentyp Person bereits garantiert.

  Räume und Türen sind getrennte Ort-Konstruktoren.
  Durch Ort.Raum und Ort.Tuer bereits garantiert.

  Die Nachbarschaftssymmetrie und die Schleifenfreiheit sind bei SimpleGraph ebenfalls bereits Bestandteile der Struktur.

  Türen verbinden jeweils zwei Räume. Räume können nicht mit anderen Räumen direkt verbunden sein.
-/
structure BipartiteOrtGraph (orte : Finset Ort) extends SimpleGraph (OrtSet orte) where
  bipartite : adjIsBipartite Adj -- das ist das "geerbte" Adj aus der Def. von SimpeGraph
  --genauEinGarten (orte : Finset Ort) := ∃! g : Ort, g = Ort.Raum Raum.Garten ∧ g ∈ orte
  --gartenExistiert (orte : Finset Ort) := Ort.Raum Raum.Garten ∈ orte
  genauEinGarten : ∃! g : Ort, istGarten g ∧ g ∈ orte
  tuerEindeutig := ∀ t1 t2 : Tuer, t1 ≠ t2 →
    (match t1,t2 with | Tuer.tuer a1, Tuer.tuer a2 => a1 ≠ a2) -- jedeTuerHatEigenesAuthentifizierungsGeraet
  gartenHatGenauEinenNachbarn : gartenHatGenauEineTuer toSimpleGraph

/-
  Objekte, die sich verändern können: Zustand ist die momentane Ausprägung
-/
def einePersonGenauEinOrt {orte : Finset Ort} {personen : Finset Person} (b : Belegung_safe orte) : Prop :=
  ∀ p : PersonSet personen, (Finset.univ.filter (fun o => p.val ∈ (b.lookup o).getD ∅)).card = 1

def belegtePersonen {orte : Finset Ort} (b : Belegung_safe orte) (o : OrtSet orte) : Finset Person :=
  (b.lookup o).getD ∅

def tuerOffenWennPerson {orte} (belegungFein : Belegung_safe orte) (offen : OrtSet orte → Bool) : Prop :=
  ∀ o : OrtSet orte,
    match o.val with
    | Ort.Tuer _ =>
        (belegungFein.lookup o).getD ∅ ≠ ∅ → offen o = true
    | Ort.Raum _ => True -- Wenn Personen in der Tür sind, ist sie offen. Wenn keine Personen drin sind, darf sie offen oder geschlossen sein.

structure Zustand (orte : Finset Ort) (personen : Finset Person) where
  belegungGrob : Belegung_safe orte
  belegungFein : Belegung_safe orte -- einePersonInGenauEinemOrt
  offen : OrtSet orte → Bool -- jede Tür hat individuell ein "offen"
  letzterRaum : Person → Option Raum -- 1 oder kein Raum
  grob_einePersonGenauEinOrt : einePersonGenauEinOrt (personen := personen) belegungGrob
  fein_einePersonGenauEinOrt : einePersonGenauEinOrt (personen := personen) belegungFein
  tuerOffenWennPersonEnthalten : tuerOffenWennPerson belegungFein offen -- Wenn Personen in der Tür sind, ist sie offen. Wenn keine Personen drin sind, darf sie offen oder geschlossen sein.

/-
  Invarianten: was trotz Veränderung gleich bleibt
  und Lemma

  pre_   = Vorbedingung vor der Aktion
  post_  = Bedingung, die nach der Aktion gilt
  frame_ = Teil des Zustands bleibt unverändert
-/

-- Belegung lesen
def personenImOrt {orte : Finset Ort} (b : Belegung_safe orte) (o : OrtSet orte) : Finset Person :=
  (b.lookup o).getD ∅

def istBelegt {orte : Finset Ort} (b : Belegung_safe orte) (p : Person) (o : OrtSet orte) : Prop :=
  p ∈ personenImOrt b o

-- Belegung verändern
def setzeBelegung {orte : Finset Ort} (b : Belegung_safe orte) (o : OrtSet orte) (personen : Finset Person) :
  Belegung_safe orte := Finmap.insert o personen b

def moveGrobBelegung {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) :
  Belegung_safe orte :=
  let personenVon := personenImOrt b von
  let personenNach := personenImOrt b nach
  let bVon := setzeBelegung b von (personenVon.erase p)
  setzeBelegung bVon nach (insert p personenNach)

-- Vorbedingung
def pre_moveGrobMitTuer {orte : Finset Ort} (G : SimpleGraph (OrtSet orte)) (offen : OrtSet orte → Bool) (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) : Prop :=
  p ∈ personenImOrt b von ∧ von ≠ nach ∧ ∃ t : OrtSet orte,
    istTuer t.1 ∧
    G.Adj von t ∧ -- von und nach verbindet t
    G.Adj nach t ∧
    offen t = true

-- Relation für einen gültigen groben Übergang
def moveGrobSchritt {orte : Finset Ort} (G : SimpleGraph (OrtSet orte)) (offen : OrtSet orte → Bool) (p : Person) (von nach : OrtSet orte) (b b' : Belegung_safe orte) : Prop :=
  pre_moveGrobMitTuer G offen p von nach b ∧ b' = moveGrobBelegung p von nach b

/-
  Beweise
-/

-- Person wurde aus dem Ausgangsort entfernt wenn hpre erfüllt ist
theorem moveGrob_person_nicht_in_von {orte : Finset Ort} (G : SimpleGraph (OrtSet orte)) (offen : OrtSet orte → Bool) (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) (hpre : pre_moveGrobMitTuer G offen p von nach b) : p ∉ personenImOrt (moveGrobBelegung p von nach b) von := by
  rcases hpre with ⟨hpVon, hVonNach⟩
  simp [moveGrobBelegung, setzeBelegung, personenImOrt, hVonNach]

-- Alle anderen Orte bleiben unverändert
theorem moveGrob_frame {orte : Finset Ort} (p : Person) (von nach o : OrtSet orte) (b : Belegung_safe orte) (hVon : o ≠ von) (hNach : o ≠ nach) : personenImOrt (moveGrobBelegung p von nach b) o = personenImOrt b o := by
  simp [moveGrobBelegung, setzeBelegung, personenImOrt, hVon, hNach]

-- Nach Bewegung enthält Ausgangsort dieselben Personen - pPerson
theorem moveGrob_belegung_von {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) (hVonNach : von ≠ nach) : personenImOrt (moveGrobBelegung p von nach b) von = (personenImOrt b von).erase p := by
  simp [moveGrobBelegung, setzeBelegung, personenImOrt, hVonNach]

-- Nach Bewegung enthält Zielort vorherige Personen + p.
theorem moveGrob_belegung_nach {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) (hVonNach : von ≠ nach) : personenImOrt (moveGrobBelegung p von nach b) nach = insert p (personenImOrt b nach) := by
  have hNachVon : nach ≠ von := Ne.symm hVonNach
  simp [moveGrobBelegung, setzeBelegung, personenImOrt]

-- Person befindet sich im Zielort wenn hpre erfüllt wurde
theorem moveGrob_person_in_nach {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (G : SimpleGraph (OrtSet orte)) (offen : OrtSet orte → Bool) (b : Belegung_safe orte) (hpre : pre_moveGrobMitTuer G offen p von nach b) : p ∈ personenImOrt (moveGrobBelegung p von nach b) nach := by
  rcases hpre with ⟨hpVon, hVonNach, t, htuer, hAdjVon, hAdjNach, hOffen⟩
  rw [moveGrob_belegung_nach p von nach b hVonNach]
  simp

-- aus hpre folgt dass es eine offene Tür gibt, die von mit nach verbindet
theorem pre_moveGrobMitTuer_enthaelt_offene_tuer {orte : Finset Ort} (G : SimpleGraph (OrtSet orte)) (offen : OrtSet orte → Bool) (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) (hpre : pre_moveGrobMitTuer G offen p von nach b) :
    ∃ t : OrtSet orte,
      istTuer t.1 ∧
      G.Adj von t ∧
      G.Adj nach t ∧
      offen t = true := by
  rcases hpre with ⟨hpVon, hVonNach, t, htuer, hVonT, hNachT, hOffen⟩
  exact ⟨t, htuer, hVonT, hNachT, hOffen⟩

-- Wenn b' aus b durch einen gültigen moveGrobSchritt entstanden ist, dann gab es eine offene Tür zwischen von und nach.
theorem moveGrobSchritt_nur_mit_offener_tuer {orte : Finset Ort} (G : SimpleGraph (OrtSet orte)) (offen : OrtSet orte → Bool) (p : Person) (von nach : OrtSet orte) (b b' : Belegung_safe orte) (hschritt : moveGrobSchritt G offen p von nach b b') :
    ∃ t : OrtSet orte,
      istTuer t.1 ∧
      G.Adj von t ∧
      G.Adj nach t ∧
      offen t = true := by
  unfold moveGrobSchritt at hschritt
  exact hschritt.1.2.2

/-
  Beispiel
-/

-- Graph
abbrev room1 := Ort.Raum (Raum.Zimmer 1)
abbrev room2 := Ort.Raum (Raum.Zimmer 2)
abbrev room3 := Ort.Raum Raum.Garten

abbrev door1 : Ort := Ort.Tuer (Tuer.tuer (Authentifizierung.auth 1))

abbrev door2 : Ort := Ort.Tuer (Tuer.tuer (Authentifizierung.auth 2))

abbrev meineOrte : Finset Ort :=
  ∅ |> insert room1
    |> insert room2
    |> insert room3
    |> insert door1
    |> insert door2

abbrev myEdges : Kante :=
  ∅ |> Finmap.insert room1 (∅ |> insert door1)
    |> Finmap.insert room2 (∅ |> insert door1 |> insert door2)
    |> Finmap.insert room3 (∅ |> insert door2)
    |> Finmap.insert door1 (∅ |> insert room1 |> insert room2)
    |> Finmap.insert door2 (∅ |> insert room2 |> insert room3)

def myAdjRelBool : Ort → Ort → Bool := OrteSindBenachbart myEdges

def myGraph : GebaeudePlan meineOrte where
  Adj u v := myAdjRelBool u.val v.val
  symm := by constructor; decide
  loopless := by constructor; decide

def myBipartiteGraph : BipartiteOrtGraph meineOrte where
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
  gartenHatGenauEinenNachbarn := by
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
        | sorry -- todo fertig machen

-- TODO: initial Zustand als Beispiel anlegen