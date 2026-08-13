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

abbrev RaumSet (Orte : Finset Ort) := { r : Raum // Ort.Raum r ∈ Orte }

-- Raum ist Ort
def raumAlsOrt {orte : Finset Ort} (r : RaumSet orte) : OrtSet orte :=
  ⟨Ort.Raum r.1, r.2⟩

-- Tuer ist Ort
def tuerAlsOrt {orte : Finset Ort} (t : TuerSet orte) : OrtSet orte :=
  ⟨Ort.Tuer t.1, t.2⟩

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
structure BipartiteOrtGraph (orte : Finset Ort) extends GebaeudePlan orte where -- statisch
  bipartite : adjIsBipartite Adj -- das ist das "geerbte" Adj aus der Def. von SimpeGraph
  --genauEinGarten (orte : Finset Ort) := ∃! g : Ort, g = Ort.Raum Raum.Garten ∧ g ∈ orte
  --gartenExistiert (orte : Finset Ort) := Ort.Raum Raum.Garten ∈ orte
  genauEinGarten : ∃! g : Ort, istGarten g ∧ g ∈ orte
  tuerEindeutig := ∀ t1 t2 : Tuer, t1 ≠ t2 →
    (match t1,t2 with | Tuer.tuer a1, Tuer.tuer a2 => a1 ≠ a2) -- jedeTuerHatEigenesAuthentifizierungsGeraet
  gartenHatGenauEinenNachbarn : gartenHatGenauEineTuer toSimpleGraph

-- Belegung lesen
def personenImOrt {orte : Finset Ort} (b : Belegung_safe orte) (o : OrtSet orte) : Finset Person :=
  (b.lookup o).getD ∅

def istBelegt {orte : Finset Ort} (b : Belegung_safe orte) (p : Person) (o : OrtSet orte) : Prop :=
  p ∈ personenImOrt b o

/-
  Objekte, die sich verändern können: Zustand ist die momentane Ausprägung
-/
def einePersonGenauEinOrt {orte : Finset Ort} {personen : Finset Person} (b : Belegung_safe orte) : Prop :=
  ∀ p : PersonSet personen, (Finset.univ.filter (fun o => p.val ∈ (b.lookup o).getD ∅)).card = 1

def belegtePersonen {orte : Finset Ort} (b : Belegung_safe orte) (o : OrtSet orte) : Finset Person :=
  (b.lookup o).getD ∅

def tuerOffenWennPerson {orte} (belegungFein : Belegung_safe orte) (offen : TuerSet orte → Bool) : Prop :=
  ∀ o : TuerSet orte, (belegungFein.lookup (tuerAlsOrt o)).getD ∅ ≠ ∅ → offen o = true

def verfeinerungsrelation {orte : Finset Ort} {personen : Finset Person} (grob fein : Belegung_safe orte) : Prop :=
  ∀ p : PersonSet personen,
    ∀ r : OrtSet orte,
      istRaum r →
      p.1 ∈ personenImOrt fein r →
      p.1 ∈ personenImOrt grob r

def verfeinerung_tuer_letzterRaum {orte : Finset Ort} {personen : Finset Person} (grob fein : Belegung_safe orte) (letzterRaum : Person → Option Raum) : Prop :=
  ∀ p : PersonSet personen,
    ∀ t : TuerSet orte,
      p.1 ∈ personenImOrt fein (tuerAlsOrt t) →
      ∃ r : Raum,
        letzterRaum p.1 = some r ∧
        ∃ hr : Ort.Raum r ∈ orte,
          p.1 ∈ personenImOrt grob ⟨Ort.Raum r, hr⟩ ∧ p.1 ∈ personenImOrt fein ⟨Ort.Raum r, hr⟩

structure Zustand (orte : Finset Ort) (personen : Finset Person) where --dynamische
  belegungGrob : Belegung_safe orte
  belegungFein : Belegung_safe orte
  offen : TuerSet orte → Bool -- jede Tür hat individuell ein "offen"
  letzterRaum : Person → Option Raum -- 1 oder kein Raum
  grob_einePersonGenauEinOrt : einePersonGenauEinOrt (personen := personen) belegungGrob
  fein_einePersonGenauEinOrt : einePersonGenauEinOrt (personen := personen) belegungFein
  tuerOffenWennPersonEnthalten : tuerOffenWennPerson belegungFein offen -- Wenn Personen in der Tür sind, ist sie offen. Wenn keine Personen drin sind, darf sie offen oder geschlossen sein.
  verfeinerung : verfeinerungsrelation (personen := personen) belegungGrob belegungFein -- Jede Person, die sich im feinen Modell in einem Raum befindet, muss sich dort auch im groben Modell befinden.
  tuerVerfeinerung : verfeinerung_tuer_letzterRaum (personen := personen) belegungGrob belegungFein letzterRaum -- Für jede betrachtete Person und jede Tür gilt: Wenn die Person im feinen Modell in dieser Tür steht, dann gibt es einen Raum, der als ihr letzter Raum gespeichert ist, und die Person befindet sich sowohl im groben als auch im feinen Modell in diesem Raum.

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

def aktualisiereLetztenRaum {orte : Finset Ort} (letzterRaum : Person → Option Raum) (p : Person) (nach : RaumSet orte) :
    Person → Option Raum := Function.update letzterRaum p (raumVonOrt (raumAlsOrt nach))

-- Belegung verändern
def setzeBelegung {orte : Finset Ort} (b : Belegung_safe orte) (o : OrtSet orte) (personen : Finset Person) :
  Belegung_safe orte := Finmap.insert o personen b

def verschiebePerson {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) :
  Belegung_safe orte :=
  let personenVon := personenImOrt b von
  let personenNach := personenImOrt b nach
  let bVon := setzeBelegung b von (personenVon.erase p)
  setzeBelegung bVon nach (insert p personenNach)

-- Tür
def hatOffeneVerbindung {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (von nach : RaumSet orte) : Prop :=
  ∃ t : TuerSet orte,
    istTuer (tuerAlsOrt t) ∧
    G.Adj (raumAlsOrt von) (tuerAlsOrt t) ∧
    G.Adj (raumAlsOrt nach) (tuerAlsOrt t) ∧
    offen t = true

/- ######### Initiales Modell (0. Verfeinerung) ######### -/

/-
  Bedingungen
-/

-- Vorbedingung: Person p ist im Raum von, von ≠ nach, es gibt eine Tür die die beiden Räume verbindet, von und nach sind Räume
def pre_moveGrobMitTuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) : Prop :=
  p ∈ personenImOrt b (raumAlsOrt von) ∧ 
  istRaum (raumAlsOrt von) ∧
  istRaum (raumAlsOrt nach) ∧ 
  von ≠ nach ∧ 
  hatOffeneVerbindung G offen von nach

-- Nachbedingung
def post_moveGrob {orte : Finset Ort} (p : Person) (G : BipartiteOrtGraph orte) (von nach : RaumSet orte) (b' : Belegung_safe orte) (offen' : TuerSet orte → Bool) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  p ∉ personenImOrt b' (raumAlsOrt von) ∧
  p ∈ personenImOrt b' (raumAlsOrt nach) ∧
  letzterRaum' = aktualisiereLetztenRaum letzterRaum p nach ∧
  hatOffeneVerbindung G offen' von nach

-- Frame, andere Personen bleiben gleich, tuer bleibt gleich
def frame_moveGrob_personen {orte : Finset Ort} (p : Person) (b b' : Belegung_safe orte) : Prop :=
  ∀ q : Person,
    q ≠ p →
    ∀ o : RaumSet orte,
      q ∈ personenImOrt b' (raumAlsOrt o) ↔
      q ∈ personenImOrt b (raumAlsOrt o)

def frame_moveGrob_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (von nach : RaumSet orte) (offen offen' : TuerSet orte → Bool) : Prop :=
  offen' = offen ∧ hatOffeneVerbindung G offen von nach

-- Aktion
def aktion_moveGrob {orte : Finset Ort} (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) :
  Belegung_safe orte × (TuerSet orte → Bool) × (Person → Option Raum) :=
  (
    verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b,
    offen,
    aktualisiereLetztenRaum letzterRaum p nach
  )

-- Stutter
def stutterGrob {orte : Finset Ort} {personen : Finset Person} (Z Z' : Zustand orte personen) : Prop :=
  Z'.belegungGrob = Z.belegungGrob ∧
  Z'.belegungFein = Z.belegungFein ∧
  Z'.offen = Z.offen ∧
  Z'.letzterRaum = Z.letzterRaum

-- Relation für einen gültigen groben Übergang -> aka moveGrob
def moveGrobSchritt {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen offen' : TuerSet orte → Bool) (p : Person) (von nach : RaumSet orte) (b b' : Belegung_safe orte) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  pre_moveGrobMitTuer G offen p von nach b ∧
  let aktion := aktion_moveGrob p von nach b offen letzterRaum
  b' = aktion.1 ∧
  offen' = aktion.2.1 ∧
  letzterRaum' = aktion.2.2 ∧
  post_moveGrob p G von nach b' offen' letzterRaum letzterRaum'

/-
  Nutzung von Zustand (extra)
-/

-- Beweise dass das auch als Zustand mit BipartiteOrtGraph geht und nicht nur durch möglicherweise inkorrekte Listen etc. 
def moveGrobSchrittZustand {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (Z Z' : Zustand orte personen) : Prop :=
  moveGrobSchritt G Z.offen Z'.offen p von nach Z.belegungGrob Z'.belegungGrob Z.letzterRaum Z'.letzterRaum

/-
  Beweise moveGrob
-/

-- Wenn zwei Räume nach der Umwandlung in OrtSet gleich sind, dann waren auch die ursprünglichen Räume gleich.
theorem raumAlsOrt_injektiv {orte : Finset Ort} : Function.Injective (@raumAlsOrt orte) := by
  intro r₁ r₂ h
  apply Subtype.ext
  cases r₁ with
  | mk r₁ hr₁ =>
    cases r₂ with
    | mk r₂ hr₂ =>
      cases h
      rfl

-- Person wurde aus dem Ausgangsort entfernt wenn hpre erfüllt ist
theorem moveGrob_person_nicht_in_von {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte)  :
    pre_moveGrobMitTuer G offen p von nach b → p ∉ personenImOrt (verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b) (raumAlsOrt von) := by
  intro hpre
  rcases hpre with ⟨hpVon, r1, r2, hVonNach, hTür⟩
  have hVonNachOrt : raumAlsOrt von ≠ raumAlsOrt nach := by -- beweist: raumAlsOrt von ≠ raumAlsOrt nach -> Angenommen, raumAlsOrt von = raumAlsOrt nach. Dann folgt wegen der Injektivität von raumAlsOrt: von = nach. Das widerspricht hVonNach. Also sind raumAlsOrt von und raumAlsOrt nach verschieden.
    intro hGleich
    apply hVonNach
    exact raumAlsOrt_injektiv hGleich
  simp [
    verschiebePerson,
    setzeBelegung,
    personenImOrt,
    hVonNachOrt
  ]

-- gleicher Beweis aber nun mit Zustand und Graphen -> damit nur korrekte Inputs möglich
/-theorem moveGrobSchrittZustand_person_nicht_in_von {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (Z Z' : Zustand orte personen) (hmove : moveGrobSchrittZustand G p von nach Z Z') :
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
-/

-- Alle anderen Personen bleiben unverändert, q ist einfach eine andere random Person
theorem moveGrob_frame_personen {orte : Finset Ort} (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) (hVonNach : von ≠ nach) :
    frame_moveGrob_personen p b (verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b) := by
  have hVonNachOrt : raumAlsOrt von ≠ raumAlsOrt nach := by
    intro hGleich
    apply hVonNach
    exact raumAlsOrt_injektiv hGleich
  intro q hqp o
  by_cases hVon : o = von
  · subst o
    simp [
      verschiebePerson,
      setzeBelegung,
      personenImOrt,
      hVonNachOrt,
      hqp
    ]
  · by_cases hNach : o = nach
    · subst o
      simp [
        verschiebePerson,
        setzeBelegung,
        personenImOrt,
        hqp
      ]
    · have hOVon : raumAlsOrt o ≠ raumAlsOrt von := by
        intro hGleich
        apply hVon
        exact raumAlsOrt_injektiv hGleich
      have hONach : raumAlsOrt o ≠ raumAlsOrt nach := by
        intro hGleich
        apply hNach
        exact raumAlsOrt_injektiv hGleich
      simp [
        verschiebePerson,
        setzeBelegung,
        personenImOrt,
        hOVon,
        hONach
      ]

theorem moveGrob_frame_personen_gleichbleibend {orte : Finset Ort} (p q : Person) (von nach : RaumSet orte) (G : BipartiteOrtGraph orte) (b : Belegung_safe orte) (hpq : q ≠ p) (hVonNach : von ≠ nach) :
    ∀ o : RaumSet orte,
      q ∈ personenImOrt (verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b) (raumAlsOrt o) ↔
      q ∈ personenImOrt b (raumAlsOrt o) := by
  intro o
  exact (moveGrob_frame_personen p von nach b hVonNach) q hpq o


-- Nach Bewegung enthält Ausgangsort dieselben Personen - pPerson -> TODO doppelt?
theorem moveGrob_belegung_von {orte : Finset Ort} (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) :
    von ≠ nach → personenImOrt (verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b) (raumAlsOrt von) = (personenImOrt b (raumAlsOrt von)).erase p := by
  intro hVonNach
  have hVonNachOrt : raumAlsOrt von ≠ raumAlsOrt nach := by
    intro hGleich
    apply hVonNach
    exact raumAlsOrt_injektiv hGleich
  simp [
    verschiebePerson,
    setzeBelegung,
    personenImOrt,
    hVonNachOrt
  ]

-- Nach Bewegung enthält Zielort vorherige Personen + p
theorem moveGrob_belegung_nach {orte : Finset Ort} (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) : 
  von ≠ nach → personenImOrt (verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b) (raumAlsOrt nach) = insert p (personenImOrt b (raumAlsOrt nach)) := by
  intro hVonNach
  simp [
    verschiebePerson,
    setzeBelegung,
    personenImOrt
  ]

-- Person befindet sich im Zielort nach move
theorem moveGrob_person_in_nach {orte : Finset Ort} (p : Person) (von nach : RaumSet orte) (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (b : Belegung_safe orte) : pre_moveGrobMitTuer G offen p von nach b → p ∈ personenImOrt (verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b) (raumAlsOrt nach) := by
  intro hpre
  rcases hpre with ⟨hpVon, hVonRaum, hRest⟩
  rcases hRest with ⟨hNachRaum, hVonNach, hTür⟩
  rw [moveGrob_belegung_nach p von nach b hVonNach]
  simp

-- aus hpre folgt dass es eine offene Tür gibt, die von mit nach verbindet -> verschiebePerson fehlt hier komplett?
theorem pre_moveGrobMitTuer_enthaelt_offene_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) : pre_moveGrobMitTuer G offen p von nach b →
    ∃ t : TuerSet orte,
      istTuer (tuerAlsOrt t) ∧
      G.Adj (raumAlsOrt von) (tuerAlsOrt t) ∧
      G.Adj (raumAlsOrt nach) (tuerAlsOrt t) ∧
      offen t = true := by
  intro hpre
  rcases hpre with ⟨hpVon, hVonRaum, hRest⟩
  rcases hRest with ⟨hNachRaum, hVonNach, hOffeneVerbindung⟩
  rcases hOffeneVerbindung with ⟨t, htuer, hVonT, hNachT, hOffen⟩
  exact ⟨t, htuer, hVonT, hNachT, hOffen⟩

-- Frame: Tür verändert Öffnungsstatus nicht während move
theorem moveGrob_frame_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) :
    pre_moveGrobMitTuer G offen p von nach b → frame_moveGrob_tuer G von nach offen (aktion_moveGrob p von nach b offen letzterRaum).2.1 := by
  intro hpre
  rcases hpre with ⟨hpVon, hVonRaum, hNachRaum, hVonNach, hVerbindung⟩
  unfold frame_moveGrob_tuer
  constructor
  · simp [aktion_moveGrob]
  · exact hVerbindung

-- moveGrob geht nur über Räume (einmal im pre und einmal in der aktion selbst)
theorem grobeBewegung_hat_Raumparameter {orte : Finset Ort} {G : BipartiteOrtGraph orte} {offen : TuerSet orte → Bool} {p : Person} {von nach : RaumSet orte} {b : Belegung_safe orte} (hpre : pre_moveGrobMitTuer G offen p von nach b) :
    istRaum (raumAlsOrt von) ∧ istRaum (raumAlsOrt nach) := by
  exact ⟨hpre.2.1, hpre.2.2.1⟩

theorem moveGrobSchritt_nur_zwischen_Raeumen {orte : Finset Ort} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (belegungGrob belegungGrob' : Belegung_safe orte) (offen offen' : TuerSet orte → Bool) (letzterRaum letzterRaum' : Person → Option Raum) (hschritt : moveGrobSchritt G offen offen' p von nach belegungGrob belegungGrob' letzterRaum letzterRaum') :
    istRaum (raumAlsOrt von) ∧ istRaum (raumAlsOrt nach) := by
  exact ⟨hschritt.1.2.1, hschritt.1.2.2.1⟩

-- Keine grobe Bewegung in eine Tür.

-- Die Verfeinerungsrelation bleibt erhalten.


/- ######### 1. Verfeinerung ######### -/

-- todo basic beweise wie oben machen

-- betreteTuer
def pre_betreteTuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) : Prop :=
  p ∈ personenImOrt fein (raumAlsOrt von) ∧
  istRaum (raumAlsOrt von) ∧
  istTuer (tuerAlsOrt t) ∧
  G.Adj (raumAlsOrt von) (tuerAlsOrt t) ∧
  offen t = true

def post_betreteTuer {orte : Finset Ort} (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein' : Belegung_safe orte) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  p ∉ personenImOrt fein' (raumAlsOrt von) ∧
  p ∈ personenImOrt fein' (tuerAlsOrt t) ∧
  letzterRaum' = letzterRaum

-- alle anderen personen bleiben an gleichem ort, offen verändert sich nicht, alle anderen personen letzter Raum bleibt gleich
-- frame gleich für beide Versionen
def frame_betreteTuer_verlasseTuer {orte : Finset Ort} (p : Person) (fein fein' : Belegung_safe orte) (letzterRaum letzterRaum' : Person → Option Raum) (offen offen' : TuerSet orte → Bool) : Prop :=
  (∀ q : Person, q ≠ p →
    ∀ o : OrtSet orte,
      q ∈ personenImOrt fein' o ↔
      q ∈ personenImOrt fein o) ∧
  offen' = offen ∧
  (∀ q : Person, q ≠ p → letzterRaum' q = letzterRaum q)

def frame_betreteTuer_grob {orte : Finset Ort} (grob grob' : Belegung_safe orte) : Prop :=
  grob' = grob

def aktion_betreteTuer {orte : Finset Ort} (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) : Belegung_safe orte × (TuerSet orte → Bool) :=
  (
    verschiebePerson p (raumAlsOrt von) (tuerAlsOrt t) fein,
    offen
  )

-- verlasseTuer
def pre_verlasseTuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (letzterRaum : Person → Option Raum) : Prop :=
  p ∈ personenImOrt fein (tuerAlsOrt t) ∧
  istRaum (raumAlsOrt nach) ∧
  istRaum (raumAlsOrt von) ∧
  istTuer (tuerAlsOrt t) ∧
  G.Adj (raumAlsOrt von) (tuerAlsOrt t) ∧
  G.Adj (raumAlsOrt nach) (tuerAlsOrt t) ∧
  von ≠ nach ∧
  letzterRaum p = raumVonOrt (raumAlsOrt von)

def post_verlasseTuer {orte : Finset Ort} (p : Person) (nach : RaumSet orte) (t : TuerSet orte) (fein fein' : Belegung_safe orte) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  p ∉ personenImOrt fein (tuerAlsOrt t) ∧
  p ∈ personenImOrt fein' (raumAlsOrt nach) ∧
  letzterRaum' = aktualisiereLetztenRaum letzterRaum p nach

def aktion_verlasseTuer {orte : Finset Ort} (p : Person) (t : TuerSet orte) (nach : RaumSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) : Belegung_safe orte × (TuerSet orte → Bool) × (Person → Option Raum) :=
  (
    verschiebePerson p (tuerAlsOrt t) (raumAlsOrt nach) fein,
    offen,
    aktualisiereLetztenRaum letzterRaum p nach
  )

-- move fein
def pre_fein {orte : Finset Ort} (G : BipartiteOrtGraph orte) (r1 r2 : RaumSet orte) (t : TuerSet orte) : Prop :=
  r1 ≠ r2 ∧
  istRaum (raumAlsOrt r1) ∧
  istRaum (raumAlsOrt r2) ∧
  istTuer (tuerAlsOrt t) ∧
  G.Adj (raumAlsOrt r1) (tuerAlsOrt t) ∧
  G.Adj (raumAlsOrt r2) (tuerAlsOrt t)

def betreteTuerSchritt {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : Prop :=
  pre_fein G von nach t ∧
  pre_betreteTuer G Z.offen p von t Z.belegungFein ∧
  Z'.belegungGrob = Z.belegungGrob ∧
  let aktion := aktion_betreteTuer p von t Z.belegungFein Z.offen
  Z'.belegungFein = aktion.1 ∧
  Z'.offen = aktion.2 ∧
  post_betreteTuer p von t Z.belegungFein Z.letzterRaum Z'.letzterRaum

def verlasseTuerSchritt {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : Prop :=
  pre_fein G von nach t ∧
  pre_verlasseTuer G p von nach t Z.belegungFein Z.letzterRaum ∧
  Z'.belegungGrob = Z.belegungGrob ∧
  let aktion := aktion_verlasseTuer p t nach Z.belegungFein Z.offen Z.letzterRaum
  Z'.belegungFein = aktion.1 ∧
  Z'.offen = aktion.2.1 ∧
  Z'.letzterRaum = aktion.2.2 ∧
  post_verlasseTuer p nach t Z.belegungFein Z'.belegungFein Z.letzterRaum Z'.letzterRaum

def aktion_moveFein {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 : Zustand orte personen) : Prop :=
  betreteTuerSchritt G p r1 r2 t Z0 Z1 ∧
  verlasseTuerSchritt G p r1 r2 t Z1 Z2

def aktion_moveFein_stutter {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 Z3 : Zustand orte personen) : Prop :=
  betreteTuerSchritt G p r1 r2 t Z0 Z1 ∧
  stutterGrob Z1 Z2 ∧
  verlasseTuerSchritt G p r1 r2 t Z2 Z3

def relation_verfeinerung {orte : Finset Ort} {personen : Finset Person} (fein grob : Belegung_safe orte) : Prop :=
  ∀ p : PersonSet personen, ∀ r : RaumSet orte,
    istRaum (raumAlsOrt r) →
    p.val ∈ personenImOrt fein (raumAlsOrt r) →
    p.val ∈ personenImOrt grob (raumAlsOrt r)

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