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

abbrev TuerSet (Orte : Finset Ort) := { t : Tuer // Ort.Tuer t ∈ Orte }

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
structure BipartitePlaceGraph (orte : Finset Ort) extends GebaeudePlan orte where
  bipartite : adjIsBipartite Adj -- das ist das "geerbte" Adj aus der Def. von SimpeGraph

def gartenHatGenauEineTuer {orte : Finset Ort} (G : GebaeudePlan orte) : Prop :=
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
structure BipartiteOrtGraph (orte : Finset Ort) extends GebaeudePlan orte where
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

/-
  Hilfsmethoden
-/

-- Letzter Raum updaten
def raumVonOrt {orte : Finset Ort} (o : OrtSet orte) : Option Raum :=
  match o.1 with
  | Ort.Raum r => some r
  | Ort.Tuer _ => none

def aktualisiereLetztenRaum {orte : Finset Ort} (letzterRaum : Person → Option Raum) (p : Person) (nach : OrtSet orte) :
    Person → Option Raum := Function.update letzterRaum p (raumVonOrt nach)

-- Tür öffnen
def setzeOffen {orte : Finset Ort} (offen : OrtSet orte → Bool) (t : OrtSet orte) (wert : Bool) :
    OrtSet orte → Bool := Function.update offen t wert

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

-- Tür
def hatOffeneVerbindung {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : OrtSet orte → Bool) (von nach : OrtSet orte) : Prop :=
  ∃ t : OrtSet orte,
    istTuer t.1 ∧
    G.Adj von t ∧
    G.Adj nach t ∧
    offen t = true

/-
  Bedingungen
-/

-- Vorbedingung: Person p ist im Raum von, von ≠ nach, es gibt eine Tür die die beiden Räume verbindet
def pre_moveGrobMitTuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : OrtSet orte → Bool) (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) : Prop :=
  p ∈ personenImOrt b von ∧
  von ≠ nach ∧
  hatOffeneVerbindung G offen von nach

-- Nachbedingung
def post_moveGrob {orte : Finset Ort} (p : Person) (G : BipartiteOrtGraph orte) (von nach : OrtSet orte) (b b' : Belegung_safe orte) (offen' : OrtSet orte → Bool) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  p ∉ personenImOrt b' von ∧
  p ∈ personenImOrt b' nach ∧
  letzterRaum' = aktualisiereLetztenRaum letzterRaum p nach ∧ -- letzter ort todo
  hatOffeneVerbindung G offen' von nach -- tuer offen todo

-- Frame
def frame_moveGrob {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b b' : Belegung_safe orte) : Prop :=
  ∀ o : OrtSet orte,
    o ≠ von →
    o ≠ nach →
    personenImOrt b' o = personenImOrt b o

def frame_moveGrob_personen {orte : Finset Ort} (p : Person) (b b' : Belegung_safe orte) : Prop :=
  ∀ q : Person,
    q ≠ p →
    ∀ o : OrtSet orte,
      q ∈ personenImOrt b' o ↔
      q ∈ personenImOrt b o

def frame_moveGrob_tuer {orte : Finset Ort} (offen offen' : OrtSet orte → Bool) : Prop :=
  offen' = offen

-- Aktion
def moveGrobAktion {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) (offen : OrtSet orte → Bool) (letzterRaum : Person → Option Raum):
  Belegung_safe orte × (OrtSet orte → Bool) × (Person → Option Raum) :=
  (
    moveGrobBelegung p von nach b,
    offen,
    aktualisiereLetztenRaum letzterRaum p nach
  )

-- Relation für einen gültigen groben Übergang -> aka moveGrob
def moveGrobSchritt {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen offen' : OrtSet orte → Bool) (p : Person) (von nach : OrtSet orte) (b b' : Belegung_safe orte) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  pre_moveGrobMitTuer G offen p von nach b ∧
  let aktion := moveGrobAktion p von nach b offen letzterRaum
  b' = aktion.1 ∧
  offen' = aktion.2.1 ∧
  letzterRaum' = aktion.2.2 ∧
  post_moveGrob p G von nach b b' offen' letzterRaum letzterRaum' ∧
  frame_moveGrob p von nach b b' ∧
  frame_moveGrob_personen p b b' ∧
  frame_moveGrob_tuer offen offen'

/-
  Nutzung von Zustand (extra)
-/

-- Beweise dass das auch als Zustand mit BipartiteOrtGraph geht und nicht nur durch möglicherweise inkorrekte Listen etc.
def moveGrobSchrittZustand {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : OrtSet orte) (Z Z' : Zustand orte personen) : Prop :=
  ∃ t : OrtSet orte, -- tuer zwischen von und nach
      istTuer t.1 ∧
      G.Adj von t ∧
      G.Adj nach t ∧
      Z.offen t = true  ∧
  pre_moveGrobMitTuer G Z.offen p von nach Z.belegungGrob ∧
  Z'.belegungGrob = moveGrobBelegung p von nach Z.belegungGrob ∧
  Z'.offen = setzeOffen Z.offen t true ∧
  Z'.letzterRaum = aktualisiereLetztenRaum Z.letzterRaum p nach

/-
  Beweise
-/
-- TODO: Türset statt ortset, prüfen dass tür offen ist und letzterRaum gesetzt wird

-- Person wurde aus dem Ausgangsort entfernt wenn hpre erfüllt ist
theorem moveGrob_person_nicht_in_von {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : OrtSet orte → Bool) (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte)  :
    pre_moveGrobMitTuer G offen p von nach b → p ∉ personenImOrt (moveGrobBelegung p von nach b) von := by
  intro hpre
  rcases hpre with ⟨hpVon, hVonNach, hTür⟩
  simp [
    moveGrobBelegung,
    setzeBelegung,
    personenImOrt,
    hVonNach
  ]

-- gleicher Beweis aber nun mit Zustand und Graphen -> damit nur korrekte Inputs möglich
theorem moveGrobSchrittZustand_person_nicht_in_von {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : OrtSet orte) (Z Z' : Zustand orte personen) (hmove : moveGrobSchrittZustand G p von nach Z Z') :
    p ∉ personenImOrt Z'.belegungGrob von := by
  rcases hmove with ⟨t, htuer, hVonTuer, hNachTuer, htOffen, hpre, hGrob, hOffenPost, hLetzterRaum⟩
  rw [hGrob]
  apply moveGrob_person_nicht_in_von
    G
    Z.offen
    p
    von
    nach
    Z.belegungGrob
  exact hpre

-- Alle anderen Orte bleiben unverändert, o ist einfach ein anderer random Ort
theorem moveGrob_frame_orte_gleichbleibend {orte : Finset Ort} (p : Person) (von nach o : OrtSet orte) (b : Belegung_safe orte) :
  o ≠ von → o ≠ nach → personenImOrt (moveGrobBelegung p von nach b) o = personenImOrt b o := by
  intro hVon hNach
  simp [
    moveGrobBelegung,
    setzeBelegung,
    personenImOrt,
    hVon,
    hNach
  ]

-- Alle anderen Personen bleiben unverändert, q ist einfach eine andere random Person
theorem moveGrob_frame_personen_gleichbleibend {orte : Finset Ort} (p q: Person) (von nach : OrtSet orte) (b : Belegung_safe orte) : p ≠ q → von ≠ nach → ∀ o : OrtSet orte, q ∈ personenImOrt (moveGrobBelegung p von nach b) o ↔ q ∈ personenImOrt b o := by
  intro hpq hVonNach o
  -- Für erase p und insert p benötigt simp q ≠ p
  have hqp : q ≠ p := by exact Ne.symm hpq
  by_cases hVon : o = von
  · subst o -- o = von
    simp [
      moveGrobBelegung,
      setzeBelegung,
      personenImOrt,
      hVonNach,
      hqp
    ]
  · by_cases hNach : o = nach
    · subst o -- o = nach
      simp [
        moveGrobBelegung,
        setzeBelegung,
        personenImOrt,
        hqp
      ]
    · simp [ -- o ≠ von und o ≠ nach
        moveGrobBelegung,
        setzeBelegung,
        personenImOrt,
        hVon,
        hNach
      ]

-- Nach Bewegung enthält Ausgangsort dieselben Personen - pPerson -> TODO doppelt?
theorem moveGrob_belegung_von {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) :
    von ≠ nach → personenImOrt (moveGrobBelegung p von nach b) von = (personenImOrt b von).erase p := by
  intro hVonNach
  simp [
    moveGrobBelegung,
    setzeBelegung,
    personenImOrt,
    hVonNach
  ]

-- Nach Bewegung enthält Zielort vorherige Personen + p -> TODO doppelt?
theorem moveGrob_belegung_nach {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) :
  von ≠ nach → personenImOrt (moveGrobBelegung p von nach b) nach = insert p (personenImOrt b nach) := by
  intro hVonNach
  simp [
    moveGrobBelegung,
    setzeBelegung,
    personenImOrt
  ]

-- Person befindet sich im Zielort wenn hpre erfüllt wurde
theorem moveGrob_person_in_nach {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (G : BipartiteOrtGraph orte) (offen : OrtSet orte → Bool) (b : Belegung_safe orte) : pre_moveGrobMitTuer G offen p von nach b → p ∈ personenImOrt (moveGrobBelegung p von nach b) nach := by
  intro hpre
  rcases hpre with ⟨hpVon, hVonNach, t, htuer, hAdjVon, hAdjNach, hOffen⟩
  rw [moveGrob_belegung_nach p von nach b hVonNach]
  simp

-- aus hpre folgt dass es eine offene Tür gibt, die von mit nach verbindet -> moveGrobBelegung fehlt hier komplett?
theorem pre_moveGrobMitTuer_enthaelt_offene_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : OrtSet orte → Bool) (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) : pre_moveGrobMitTuer G offen p von nach b →
    ∃ t : OrtSet orte,
      istTuer t.1 ∧
      G.Adj von t ∧
      G.Adj nach t ∧
      offen t = true := by
  intro hpre
  rcases hpre with ⟨hpVon, hVonNach, t, htuer, hVonT, hNachT, hOffen⟩
  exact ⟨t, htuer, hVonT, hNachT, hOffen⟩

-- Wenn b' aus b durch einen gültigen moveGrobSchritt entstanden ist, dann gab es eine offene Tür zwischen von und nach. -> moveGrobBelegung fehlt hier komplett?
theorem moveGrobSchritt_nur_mit_offener_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : OrtSet orte → Bool) (p : Person) (von nach : OrtSet orte) (b b' : Belegung_safe orte) : moveGrobSchritt G offen p von nach b b' →
    ∃ t : OrtSet orte,
      istTuer t.1 ∧
      G.Adj von t ∧
      G.Adj nach t ∧
      offen t = true := by
  intro hschritt
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
        | (exfalso; revert hAdj; simp [myAdjRelBool, OrteSindBenachbart, myEdges])

-- Initialer Zustand mit drei Personen

def person1 : Person := Person.Bewohner 1
def person2 : Person := Person.Bewohner 2
def person3 : Person := Person.Gast 1

def meinePersonen : Finset Person :=
  {person1, person2, person3}

def initialBelegung : Belegung_safe meineOrte :=
  ∅
  |> Finmap.insert ⟨room1, by simp [meineOrte]⟩ ({person1} : Finset Person)
  |> Finmap.insert ⟨room2, by simp [meineOrte]⟩ ({person2} : Finset Person)
  |> Finmap.insert ⟨room3, by simp [meineOrte]⟩ ({person3} : Finset Person)

def initialOffen : OrtSet meineOrte → Bool :=
  fun _ => false

def initialLetzterRaum : Person → Option Raum :=
  fun _ => none

def initialZustand : Zustand meineOrte meinePersonen where
  belegungGrob := initialBelegung
  belegungFein := initialBelegung
  offen := initialOffen
  letzterRaum := initialLetzterRaum

  grob_einePersonGenauEinOrt := by
    rintro ⟨p, hp⟩
    simp [meinePersonen] at hp
    rcases hp with rfl | rfl | rfl
    · native_decide +revert
    · native_decide +revert
    · native_decide +revert

  fein_einePersonGenauEinOrt := by
    rintro ⟨p, hp⟩
    simp [meinePersonen] at hp
    rcases hp with rfl | rfl | rfl
    · native_decide +revert
    · native_decide +revert
    · native_decide +revert

  tuerOffenWennPersonEnthalten := by
    rintro ⟨o, ho⟩
    cases o with
    | Raum r =>
        trivial
    | Tuer t =>
        intro hBelegt
        simp [initialBelegung] at hBelegt
