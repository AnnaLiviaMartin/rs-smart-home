import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases


/-
  TODO:

  Was insgesamt bewiesen wird: raumset/ortset checken, kommentare schreiben, aufräumen, schreibweise umändern von \and in ->, ungenutzte Methoden löschen, Feedback der KI einarbeiten

  Statische Struktur
  Räume und Türen sind disjunkt.
  Nur Raum–Tür-Kanten sind erlaubt.
  Nachbarschaft ist symmetrisch.
  Graph ist schleifenfrei.
  Genau ein Garten existiert.
  Der Garten hat genau eine Tür.
  Jede Tür verbindet genau zwei Räume.

  Belegung
  Jede betrachtete Person befindet sich im groben Modell genau einmal.
  Jede betrachtete Person befindet sich im feinen Modell genau einmal.
  Keine Person befindet sich grob in einer Tür.
  Nur bekannte Personen kommen in den Belegungen vor.
  Eine belegte feine Tür ist offen.
  Die feine Belegung verfeinert die grobe Belegung.
  Die Verfeinerungsrelation bleibt erhalten.

  Grobe Bewegung
  Person verlässt den Ausgangsraum.
  Person kommt im Zielraum an.
  Andere Personen bleiben unverändert. 
  Die Personen im von Raum bleiben unverändert bis auf p. 
  Nach Bewegung enthält Zielort vorherige Personen + p.
  Türen und Graph bleiben unverändert.
  Es gibt eine offene Tür die die zwei Räume miteinander verbindet.
  Keine grobe Bewegung in/über eine Tür.
  Der Öffnungsstatus der Tür zwischen den zwei Räumen verändert sich nicht.
  Keine grobe Bewegung in eine Tür. -> durch Typen sichergestellt

  Feine Bewegung
  Person kann eine offene Tür betreten.
  Person befindet sich danach in der Tür.
  Grobes Modell bleibt beim Betreten unverändert.
  Person kann die Tür in den Zielraum verlassen.
  Person befindet sich danach im Zielraum.
  Der grobe Schritt stimmt mit dem Ergebnis des feinen Schritts überein.
  Andere Personen bleiben unverändert.
  letzterRaum wird korrekt aktualisiert. -> erst nach verlasseTuer ist der letzteRaum neu gesetzt worden, nicht schon bei betreteTuer
  Die Verfeinerungsrelation bleibt nach Aktionen erhalten.

  Türöffnung
  Nur Bewohner:innen dürfen Türen öffnen.
  Die Person muss an die Tür angrenzen.
  Eine geschlossene Tür wird geöffnet.
  Andere Öffnungszustände bleiben unverändert.
  Belegungen bleiben unverändert.
-/

/-
  Objekte, uebernommen logisch aus Alloy, statisch: GebaeudePlan ist die feste Topologie
-/

inductive Person where
| Bewohner (id : Nat)
| Gast (id : Nat)
deriving DecidableEq, Repr

inductive Raum where
| Zimmer (id : Nat)
| Garten
deriving DecidableEq, Repr

inductive Tuer where
| tuer (id : Nat)
deriving DecidableEq, Repr

inductive Ort where
| Raum (r : Raum)
| Tuer (t : Tuer)
deriving DecidableEq, Repr

/-
  Hilfspraedikate
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

def darfTuerOeffnen (p : Person) : Prop :=
  istBewohner p

/-
  Tuer und Raum, Personen Graphen aufbauen
-/

abbrev OrtSet (Orte : Finset Ort) := { p : Ort // p ∈ Orte } -- Menge an Orten, aus dem die tatsaechlich verwendeten ausgewaehlt werden koennen

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

abbrev Kante := Finmap (fun _ : Ort => Finset Ort) -- Graph-Kante fuer Ort: [Ort, Menge an Orten]

abbrev GebaeudePlan (Orte : Finset Ort) := SimpleGraph (OrtSet Orte) -- Graph, dessen Knoten genau die Orte aus Orte sind

def OrteSindBenachbart (Kanten : Kante) (n1 : Ort) (n2 : Ort) : Bool := -- Gibt es von n1 aus eine Verbindung zu n2?
  match Kanten.lookup n1 with
  | none => false
  | some nachbarn => n2 ∈ nachbarn
--   Kanten.any (fun (node, Kantes) => n1 == node && Kantes.contains n2)

-- Ein Raum kann nicht mit anderen Raeumen direkt verbunden sein
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

-- Lean mitteilen, dass es fuer das Praedikat KanteIsBipartite einen
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

-- Gebaeudeplan, der bipartite ist
structure BipartitePlaceGraph (orte : Finset Ort) extends GebaeudePlan orte where
  bipartite : adjIsBipartite Adj -- das ist das "geerbte" Adj aus der Def. von SimpeGraph

def gartenHatGenauEineTuer {orte : Finset Ort} (G : GebaeudePlan orte) : Prop :=
  ∀ g : OrtSet orte,
    istGarten g.1 →
    ∃! t : OrtSet orte,
      istTuer t.1 ∧ G.Adj g t

-- Gebaeudeplan, der bipartite ist, nachbar-symmetrie gegeben, damit auch tuerVerbindetZweiRaeume, alleNachbarnSindSymmerisch inkl. Axiome
/-
  Invarianten, die bereits implizit definiert sind:

  Jede Tuer besitzt genau eine Authentifizierung.
  Durch Tuer.tuer (auth : Authentifizierung) bereits garantiert.

  offen besitzt genau einen Bool-Wert.
  Durch offen : OrtSet orte → Bool bereits garantiert.

  letzterRaum ist entweder ein Raum oder nicht gesetzt.
  Durch letzterRaum : Person → Option Raum bereits garantiert.

  Jede Person ist Bewohner:in oder Gast.
  Durch den induktiven Datentyp Person bereits garantiert.

  Raeume und Tueren sind getrennte Ort-Konstruktoren.
  Durch Ort.Raum und Ort.Tuer bereits garantiert.

  Die Nachbarschaftssymmetrie und die Schleifenfreiheit sind bei SimpleGraph ebenfalls bereits Bestandteile der Struktur.

  Tueren verbinden jeweils zwei Raeume. Raeume koennen nicht mit anderen Raeumen direkt verbunden sein.
-/
structure BipartiteOrtGraph (orte : Finset Ort) extends GebaeudePlan orte where -- statisch
  bipartite : adjIsBipartite Adj -- das ist das "geerbte" Adj aus der Def. von SimpeGraph
  --genauEinGarten (orte : Finset Ort) := ∃! g : Ort, g = Ort.Raum Raum.Garten ∧ g ∈ orte
  --gartenExistiert (orte : Finset Ort) := Ort.Raum Raum.Garten ∈ orte
  genauEinGarten : ∃! g : Ort, istGarten g ∧ g ∈ orte
  tuerEindeutig := ∀ t1 t2 : Tuer, t1 ≠ t2 →
    (match t1,t2 with | Tuer.tuer id1, Tuer.tuer id2 => id1 ≠ id2) -- jedeTuerHatEigenesAuthentifizierungsGeraet
  gartenHatGenauEinenNachbarn : gartenHatGenauEineTuer toSimpleGraph

-- Belegung lesen
def personenImOrt {orte : Finset Ort} (b : Belegung_safe orte) (o : OrtSet orte) : Finset Person :=
  (b.lookup o).getD ∅

def istBelegt {orte : Finset Ort} (b : Belegung_safe orte) (p : Person) (o : OrtSet orte) : Prop :=
  p ∈ personenImOrt b o

/-
  Objekte, die sich veraendern koennen: Zustand ist die momentane Auspraegung
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
          p.1 ∈ personenImOrt grob ⟨Ort.Raum r, hr⟩

def grobeTuerenSindLeer {orte : Finset Ort} (grob : Belegung_safe orte) : Prop :=
  ∀ t : TuerSet orte,
    personenImOrt grob (tuerAlsOrt t) = ∅

def nurBekanntePersonen {orte : Finset Ort} {personen : Finset Person} (b : Belegung_safe orte) : Prop :=
  ∀ o : OrtSet orte,
    ∀ p : Person,
      p ∈ personenImOrt b o →
      p ∈ personen


structure Zustand (orte : Finset Ort) (personen : Finset Person) where --dynamische
  belegungGrob : Belegung_safe orte
  belegungFein : Belegung_safe orte
  offen : TuerSet orte → Bool -- jede Tuer hat individuell ein "offen"
  letzterRaum : Person → Option Raum -- 1 oder kein Raum
  grob_einePersonGenauEinOrt : einePersonGenauEinOrt (personen := personen) belegungGrob
  fein_einePersonGenauEinOrt : einePersonGenauEinOrt (personen := personen) belegungFein
  tuerOffenWennPersonEnthalten : tuerOffenWennPerson belegungFein offen -- Wenn Personen in der Tuer sind, ist sie offen. Wenn keine Personen drin sind, darf sie offen oder geschlossen sein.
  verfeinerung : verfeinerungsrelation (personen := personen) belegungGrob belegungFein -- Jede Person, die sich im feinen Modell in einem Raum befindet, muss sich dort auch im groben Modell befinden.
  tuerVerfeinerung : verfeinerung_tuer_letzterRaum (personen := personen) belegungGrob belegungFein letzterRaum -- Fuer jede betrachtete Person und jede Tuer gilt: Wenn die Person im feinen Modell in dieser Tuer steht, dann gibt es einen Raum, der als ihr letzter Raum gespeichert ist, und die Person befindet sich im groben in diesem Raum.
  grobeTuerenSindImmerLeer : grobeTuerenSindLeer belegungGrob
  grobNurBekanntePersonen : nurBekanntePersonen (personen := personen) belegungGrob
  feinNurBekanntePersonen : nurBekanntePersonen (personen := personen) belegungFein


/-
  Invarianten: was trotz Veraenderung gleich bleibt
  und Lemma

  pre_   = Vorbedingung vor der Aktion
  post_  = Bedingung, die nach der Aktion gilt
  frame_ = Teil des Zustands bleibt unveraendert
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

-- Belegung veraendern
def setzeBelegung {orte : Finset Ort} (b : Belegung_safe orte) (o : OrtSet orte) (personen : Finset Person) :
  Belegung_safe orte := Finmap.insert o personen b

def verschiebePerson {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) :
  Belegung_safe orte :=
  let personenVon := personenImOrt b von
  let personenNach := personenImOrt b nach
  let bVon := setzeBelegung b von (personenVon.erase p)
  setzeBelegung bVon nach (insert p personenNach)

-- Tuer
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

-- Vorbedingung: Person p ist im Raum von, von ≠ nach, es gibt eine Tuer die die beiden Raeume verbindet, von und nach sind Raeume
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
def stutter {orte : Finset Ort} {personen : Finset Person} (Z Z' : Zustand orte personen) : Prop :=
  Z'.belegungGrob = Z.belegungGrob ∧
  Z'.belegungFein = Z.belegungFein ∧
  Z'.offen = Z.offen ∧
  Z'.letzterRaum = Z.letzterRaum

-- Relation fuer einen gueltigen groben uebergang -> aka moveGrob
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

-- Beweise dass das auch als Zustand mit BipartiteOrtGraph geht und nicht nur durch moeglicherweise inkorrekte Listen etc. 
def moveGrobSchrittZustand {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (Z Z' : Zustand orte personen) : Prop :=
  moveGrobSchritt G Z.offen Z'.offen p von nach Z.belegungGrob Z'.belegungGrob Z.letzterRaum Z'.letzterRaum

/-
  Beweise moveGrob
-/

-- Wenn zwei Raeume nach der Umwandlung in OrtSet gleich sind, dann waren auch die urspruenglichen Raeume gleich.
theorem raumAlsOrt_injektiv {orte : Finset Ort} : Function.Injective (@raumAlsOrt orte) := by
  intro r₁ r₂ h
  apply Subtype.ext
  cases r₁ with
  | mk r₁ hr₁ =>
    cases r₂ with
    | mk r₂ hr₂ =>
      cases h
      rfl

-- Person wurde aus dem Ausgangsort entfernt wenn hpre erfuellt ist
theorem moveGrob_person_nicht_in_von {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte)  :
    pre_moveGrobMitTuer G offen p von nach b → p ∉ personenImOrt (verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b) (raumAlsOrt von) := by
  intro hpre
  rcases hpre with ⟨hpVon, r1, r2, hVonNach, hTuer⟩
  have hVonNachOrt : raumAlsOrt von ≠ raumAlsOrt nach := by -- beweist: raumAlsOrt von ≠ raumAlsOrt nach -> Angenommen, raumAlsOrt von = raumAlsOrt nach. Dann folgt wegen der Injektivitaet von raumAlsOrt: von = nach. Das widerspricht hVonNach. Also sind raumAlsOrt von und raumAlsOrt nach verschieden.
    intro hGleich
    apply hVonNach
    exact raumAlsOrt_injektiv hGleich
  simp [
    verschiebePerson,
    setzeBelegung,
    personenImOrt,
    hVonNachOrt
  ]

-- gleicher Beweis aber nun mit Zustand und Graphen -> damit nur korrekte Inputs moeglich
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

-- Alle anderen Personen bleiben unveraendert, q ist einfach eine andere random Person
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

theorem moveGrob_frame_personen_gleichbleibend {orte : Finset Ort} (p q : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) (hpq : q ≠ p) (hVonNach : von ≠ nach) :
    ∀ o : RaumSet orte,
      q ∈ personenImOrt (verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b) (raumAlsOrt o) ↔
      q ∈ personenImOrt b (raumAlsOrt o) := by
  intro o
  exact (moveGrob_frame_personen p von nach b hVonNach) q hpq o


-- Nach Bewegung enthaelt Ausgangsort dieselben Personen - pPerson
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

-- Nach Bewegung enthaelt Zielort vorherige Personen + p
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
  rcases hRest with ⟨hNachRaum, hVonNach, hTuer⟩
  rw [moveGrob_belegung_nach p von nach b hVonNach]
  simp

-- aus hpre folgt dass es eine offene Tuer gibt, die von mit nach verbindet -> verschiebePerson fehlt hier komplett?
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

-- Frame: Tuer veraendert oeffnungsstatus nicht waehrend move
theorem moveGrob_frame_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) :
    pre_moveGrobMitTuer G offen p von nach b → frame_moveGrob_tuer G von nach offen (aktion_moveGrob p von nach b offen letzterRaum).2.1 := by
  intro hpre
  rcases hpre with ⟨hpVon, hVonRaum, hNachRaum, hVonNach, hVerbindung⟩
  unfold frame_moveGrob_tuer
  constructor
  · simp [aktion_moveGrob]
  · exact hVerbindung

-- moveGrob geht nur ueber Raeume (einmal im pre und einmal in der aktion selbst)
theorem grobeBewegung_hat_Raumparameter {orte : Finset Ort} {G : BipartiteOrtGraph orte} {offen : TuerSet orte → Bool} {p : Person} {von nach : RaumSet orte} {b : Belegung_safe orte} (hpre : pre_moveGrobMitTuer G offen p von nach b) :
    istRaum (raumAlsOrt von) ∧ istRaum (raumAlsOrt nach) := by
  exact ⟨hpre.2.1, hpre.2.2.1⟩

theorem moveGrobSchritt_nur_zwischen_Raeumen {orte : Finset Ort} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (belegungGrob belegungGrob' : Belegung_safe orte) (offen offen' : TuerSet orte → Bool) (letzterRaum letzterRaum' : Person → Option Raum) (hschritt : moveGrobSchritt G offen offen' p von nach belegungGrob belegungGrob' letzterRaum letzterRaum') :
    istRaum (raumAlsOrt von) ∧ istRaum (raumAlsOrt nach) := by
  exact ⟨hschritt.1.2.1, hschritt.1.2.2.1⟩

-- Keine grobe Bewegung in eine Tuer. todo

-- Die Verfeinerungsrelation bleibt erhalten. todo


/- ######### 1. Verfeinerung ######### -/

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

-- offen veraendert sich nicht, alle anderen personen letzter Raum bleibt gleich
-- frame gleich fuer beide Versionen
def frame_betreteTuer_verlasseTuer_letzterRaum (p : Person) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  (∀ q : Person, q ≠ p → letzterRaum' q = letzterRaum q)

def frame_betreteTuer_verlasseTuer_offen {orte : Finset Ort} (offen offen' : TuerSet orte → Bool) : Prop :=
  offen' = offen

-- alle anderen personen bleiben an gleichem ort
def frame_betreteTuer_verlasseTuer_personen {orte : Finset Ort} (p : Person) (fein fein' : Belegung_safe orte) : Prop :=
  ∀ q : Person, q ≠ p →
    ∀ o : OrtSet orte,
      q ∈ personenImOrt fein' o ↔
      q ∈ personenImOrt fein o

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
  moveGrobSchrittZustand G p von nach Z Z' ∧ -- hier muss auch das grobe Modell ausgefuehrt werden, sonst sind die Zustaende nicht konsistent
  Z'.belegungGrob = verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) Z.belegungGrob ∧
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
  stutter Z1 Z2 ∧
  verlasseTuerSchritt G p r1 r2 t Z2 Z3

-- ist eine person in einem Raum muss der Raum in fein + grob gleich sein -> das bedeutet nicht dass man nicht in fein in einer Tuer sein kann und gleichzeit in grob nicht in einem Raum!
def relation_verfeinerung {orte : Finset Ort} {personen : Finset Person} (fein grob : Belegung_safe orte) : Prop :=
  ∀ p : PersonSet personen, ∀ r : RaumSet orte,
    istRaum (raumAlsOrt r) →
    p.val ∈ personenImOrt fein (raumAlsOrt r) →
    p.val ∈ personenImOrt grob (raumAlsOrt r)

/-
  Beweise
-/

theorem verschiebePerson_person_nicht_in_von {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) (hVonNach : von ≠ nach) :
    p ∉ personenImOrt (verschiebePerson p von nach b) von := by
  simp [
    verschiebePerson,
    setzeBelegung,
    personenImOrt,
    hVonNach
  ]

theorem verschiebePerson_person_in_nach {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) :
    p ∈ personenImOrt (verschiebePerson p von nach b) nach := by
  simp [
    verschiebePerson,
    setzeBelegung,
    personenImOrt
  ]

-- ein Raum ist keine Tuer
theorem raumAlsOrt_neq_tuerAlsOrt {orte : Finset Ort} (r : RaumSet orte) (t : TuerSet orte) :
    raumAlsOrt r ≠ tuerAlsOrt t := by
  intro h
  cases h

-- eine Tuer ist kein Raum
theorem betreteTuer_von_neq_tuer {orte : Finset Ort} (von : RaumSet orte) (t : TuerSet orte) :
    raumAlsOrt von ≠ tuerAlsOrt t := by
  intro h
  cases h

-- Hilflemma: bewegte Person landet in keinem anderen Ort
theorem verschiebePerson_person_nicht_in_fremdem_ort {orte : Finset Ort} (p : Person) (von nach o : OrtSet orte) (b : Belegung_safe orte) (hVon : o ≠ von) (hNach : o ≠ nach) (hpNichtInO : p ∉ personenImOrt b o):
    p ∉ personenImOrt (verschiebePerson p von nach b) o := by
  simp [
    verschiebePerson,
    setzeBelegung,
    personenImOrt,
    hVon,
    hNach
  ]
  simpa [personenImOrt] using hpNichtInO

-- Beweise fuer betreteTuer

-- wird eine Tuer betreten ist sie offen
theorem betreteTuer_offene_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (hpre : pre_betreteTuer G offen p von t fein) :
    offen t = true := by
  exact hpre.2.2.2.2

-- nach betreten der Tuer ist die person in der tuer
theorem betreteTuer_person_in_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (hpre : pre_betreteTuer G offen p von t fein) :
    p ∈ personenImOrt (aktion_betreteTuer p von t fein offen).1 (tuerAlsOrt t) := by
  unfold aktion_betreteTuer
  apply verschiebePerson_person_in_nach

-- nach betreten der Tuer ist der Ausgangsraum ohne die Person
theorem betreteTuer_person_nicht_mehr_in_von {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (hpre : pre_betreteTuer G offen p von t fein) :
    p ∉ personenImOrt (aktion_betreteTuer p von t fein offen).1 (raumAlsOrt von) := by
  unfold aktion_betreteTuer
  apply verschiebePerson_person_nicht_in_von
  · exact betreteTuer_von_neq_tuer von t

-- wird die tuer betreten aendert sich in Grob nichts mehr
theorem betreteTuer_grob_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : betreteTuerSchritt G p von nach t Z Z') :
    frame_betreteTuer_grob Z.belegungGrob Z'.belegungGrob := by
  exact hschritt.2.2.1

-- beim betreten ist die tuer offen
theorem betreteTuer_offen_unveraendert {orte : Finset Ort} (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) :
    (aktion_betreteTuer p von t fein offen).2 = offen := by
  rfl

-- der letzteRaum aendert sich beim betreten der Tuer nicht
theorem betreteTuer_letzterRaum_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : betreteTuerSchritt G p von nach t Z Z') :
    p ∈ personenImOrt Z.belegungFein (tuerAlsOrt t) ∧ Z'.letzterRaum = Z.letzterRaum := by
  rcases hschritt with ⟨hpreFein, hpreBetrete, hGrob, haktion, hpost⟩
  exact hpost.2.2

-- alle anderen personen bleiben unveraendert beim betreten der Tuer
theorem betreteTuer_frame_personen {orte : Finset Ort} (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (hVonTuer : raumAlsOrt von ≠ tuerAlsOrt t) :
    frame_betreteTuer_verlasseTuer_personen p fein (aktion_betreteTuer p von t fein (fun _ => true)).1 := by
  intro q hqp o
  by_cases hVon : o = raumAlsOrt von
  · subst hVon
    simp [
      aktion_betreteTuer,
      verschiebePerson,
      setzeBelegung,
      personenImOrt,
      hVonTuer,
      hqp
    ]
  · by_cases hTuer : o = tuerAlsOrt t
    · subst hTuer
      simp [
        aktion_betreteTuer,
        verschiebePerson,
        setzeBelegung,
        personenImOrt,
        hqp
      ]
    · simp [
        aktion_betreteTuer,
        verschiebePerson,
        setzeBelegung,
        personenImOrt,
        hVon,
        hTuer
      ]

-- die anderen tueren bleiben offen
theorem betreteTuer_frame_offen {orte : Finset Ort} (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) :
    frame_betreteTuer_verlasseTuer_offen offen (aktion_betreteTuer p von t fein offen).2 := by
  unfold frame_betreteTuer_verlasseTuer_offen
  rfl

-- wenn betreteTuer aufgerufen ist dann bleibt die person in grob erstmal in ihrem ausgangsort
theorem person_grob_in_ausgangsraum_nach_betreteTuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z0 Z1 : Zustand orte personen) (hp : p ∈ personenImOrt Z0.belegungGrob (raumAlsOrt von)) (hbetrete : betreteTuerSchritt G p von nach t Z0 Z1) :
    p ∈ personenImOrt Z1.belegungGrob (raumAlsOrt von) := by
  rcases hbetrete with ⟨_, _, hGrob, _, _⟩
  rw [hGrob]
  exact hp

-- Beim Verschieben von p bleibt die Zugehoerigkeit einer anderen Person q an jedem Ort unveraendert
theorem verschiebePerson_frame {orte : Finset Ort} (p q : Person) (von nach o : OrtSet orte) (b : Belegung_safe orte) (hpq : q ≠ p) (hVonNach : von ≠ nach) : 
  q ∈ personenImOrt (verschiebePerson p von nach b) o ↔ q ∈ personenImOrt b o := by
  have hNachVon : nach ≠ von := by exact Ne.symm hVonNach
  by_cases hVon : o = von
  · subst o
    simp [
      verschiebePerson,
      setzeBelegung,
      personenImOrt,
      hpq,
      hVonNach
    ]
  · by_cases hNach : o = nach
    · subst o
      simp [
        verschiebePerson,
        setzeBelegung,
        personenImOrt,
        hpq
      ]
    · have hVon' : von ≠ o := by exact Ne.symm hVon
      have hNach' : nach ≠ o := by exact Ne.symm hNach
      simp [
        verschiebePerson,
        setzeBelegung,
        personenImOrt,
        hVon,
        hNach
      ]

-- Hilfslemma
theorem person_nicht_in_anderem_ort {orte : Finset Ort} {personen : Finset Person} (b : Belegung_safe orte) (hEinOrt : einePersonGenauEinOrt (personen := personen) b) (p : Person) (hpBekannt : p ∈ personen) (von o : OrtSet orte) (hpVon : p ∈ personenImOrt b von) (hNichtGleich : o ≠ von) :
    p ∉ personenImOrt b o := by
  intro hpO
  let ps : PersonSet personen := ⟨p, hpBekannt⟩
  let orteMitPerson : Finset (OrtSet orte) :=
    Finset.univ.filter (fun x : OrtSet orte => ps.val ∈ (b.lookup x).getD ∅)
  have hCard : orteMitPerson.card = 1 := by
    change (Finset.univ.filter (fun x : OrtSet orte => ps.val ∈ (b.lookup x).getD ∅)).card = 1
    exact hEinOrt ps
  have hVonIn : von ∈ orteMitPerson := by
    simpa [orteMitPerson, ps, personenImOrt] using hpVon
  have hOIn : o ∈ orteMitPerson := by
    simpa [orteMitPerson, ps, personenImOrt] using hpO
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hCard
  have hVonEq : von = x := by
    rw [hx] at hVonIn
    simpa using hVonIn
  have hOEq : o = x := by
    rw [hx] at hOIn
    simpa using hOIn
  apply hNichtGleich
  exact hOEq.trans hVonEq.symm

-- Wenn vor dem Betreten die Verfeinerungsrelation zwischen dem feinen und dem groben Modell gilt und p eine gueltige Tuer-Betreten-Aktion ausfuehrt, dann gilt die Verfeinerungsrelation auch nach dem Betreten.
theorem relation_nach_betreteTuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hrel : relation_verfeinerung (personen := personen) Z.belegungFein Z.belegungGrob) (hbetrete : betreteTuerSchritt G p von nach t Z Z') : 
  relation_verfeinerung (personen := personen) Z'.belegungFein Z'.belegungGrob := by
  intro q r hraum hq
  rcases hbetrete with ⟨hPreFein, hPreBetrete, hGrob, hBelegung, hPostBetrete⟩
  by_cases hqp : q.val = p
  · -- q ist die bewegte Person
    have hpFein : p ∈ personenImOrt Z'.belegungFein (raumAlsOrt r) := by
      simpa [hqp] using hq
    by_cases hr : r = von
    · subst r
      have hpNichtInVon : p ∉ personenImOrt Z'.belegungFein (raumAlsOrt von) := by
        rw [hBelegung]
        exact betreteTuer_person_nicht_mehr_in_von G Z.offen p von t Z.belegungFein hPreBetrete
      exact (hpNichtInVon hpFein).elim
    · -- r ist ein anderer Raum als von
      have hRaumNichtVon : raumAlsOrt r ≠ raumAlsOrt von := by
        intro h
        apply hr
        exact raumAlsOrt_injektiv h
      have hRaumNichtTuer : raumAlsOrt r ≠ tuerAlsOrt t := by
        intro h
        cases h
      have hpBekannt : p ∈ personen := by
        exact Z.feinNurBekanntePersonen (raumAlsOrt von) p hPreBetrete.1
      have hpNichtInAltemR : p ∉ personenImOrt Z.belegungFein (raumAlsOrt r) := by
        exact person_nicht_in_anderem_ort Z.belegungFein Z.fein_einePersonGenauEinOrt p hpBekannt (raumAlsOrt von) (raumAlsOrt r) hPreBetrete.1 hRaumNichtVon
      have hpNichtInR : p ∉ personenImOrt (aktion_betreteTuer p von t Z.belegungFein Z.offen).1 (raumAlsOrt r) := by
        unfold aktion_betreteTuer
        exact verschiebePerson_person_nicht_in_fremdem_ort p (raumAlsOrt von) (tuerAlsOrt t) (raumAlsOrt r) Z.belegungFein hRaumNichtVon hRaumNichtTuer hpNichtInAltemR
      have hpFeinAktion : p ∈ personenImOrt (aktion_betreteTuer p von t Z.belegungFein Z.offen).1 (raumAlsOrt r) := by
        rw [← hBelegung]
        exact hpFein
      exact (hpNichtInR hpFeinAktion).elim
  · -- q ist eine andere Person
    have hFeinFrame : q.val ∈ personenImOrt Z'.belegungFein (raumAlsOrt r) ↔ q.val ∈ personenImOrt Z.belegungFein (raumAlsOrt r) := by
      rw [hBelegung]
      exact verschiebePerson_frame p q.val (raumAlsOrt von) (tuerAlsOrt t) (raumAlsOrt r) Z.belegungFein hqp (raumAlsOrt_neq_tuerAlsOrt von t)
    have hqVorher : q.val ∈ personenImOrt Z.belegungFein (raumAlsOrt r) := by
      exact hFeinFrame.mp hq
    have hqGrobVorher : q.val ∈ personenImOrt Z.belegungGrob (raumAlsOrt r) := by
      exact hrel q r hraum hqVorher
    rw [hGrob]
    exact hqGrobVorher


-- Beweise fuer verlasseTuer

-- person ist zu beginn in einer tuer im feinen modell
theorem verlasseTuer_person_in_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte)
    (t : TuerSet orte)
    (fein : Belegung_safe orte)
    (letzterRaum : Person → Option Raum)
    (hpre : pre_verlasseTuer G p von nach t fein letzterRaum) :
    p ∈ personenImOrt fein (tuerAlsOrt t) := by
  exact hpre.1

-- person ist danach im zielraum
theorem verlasseTuer_person_in_nach {orte : Finset Ort} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) (hpre : pre_verlasseTuer G p von nach t fein letzterRaum) :
    p ∈ personenImOrt (aktion_verlasseTuer p t nach fein offen letzterRaum).1 (raumAlsOrt nach) := by
  unfold aktion_verlasseTuer
  apply verschiebePerson_person_in_nach

-- person ist nach verlassen nicht mehr in tuer
theorem verlasseTuer_person_nicht_mehr_in_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) (hpre : pre_verlasseTuer G p von nach t fein letzterRaum) :
    p ∉ personenImOrt (aktion_verlasseTuer p t nach fein offen letzterRaum).1 (tuerAlsOrt t) := by
  unfold aktion_verlasseTuer
  apply verschiebePerson_person_nicht_in_von
  · intro h
    cases h

-- letzterRaum wird beim verlassen der tuer korrekt gesetzt
theorem verlasseTuer_letzterRaum_korrekt {orte : Finset Ort} (p : Person) (nach : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) : 
    (aktion_verlasseTuer p t nach fein offen letzterRaum).2.2 = aktualisiereLetztenRaum letzterRaum p nach := by
  rfl

-- letzterRaum aller anderen Personen bleibt erhalten
theorem verlasseTuer_frame_letzterRaum {orte : Finset Ort} (p : Person) (nach : RaumSet orte) (letzterRaum letzterRaum' : Person → Option Raum) (hUpdate : letzterRaum' = aktualisiereLetztenRaum letzterRaum p nach):
    frame_betreteTuer_verlasseTuer_letzterRaum p letzterRaum letzterRaum' := by
  unfold frame_betreteTuer_verlasseTuer_letzterRaum
  intro q hqp
  rw [hUpdate]
  simp [
    aktualisiereLetztenRaum,
    hqp
  ]

-- beim verlasse ist die tuer offen
theorem verlasseTuer_offen_unveraendert {orte : Finset Ort} (p : Person) (t : TuerSet orte) (nach : RaumSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) :
    (aktion_verlasseTuer p t nach fein offen letzterRaum).2.1 = offen := by
  rfl

-- verfeinerung nach betreteTuer zu grob
theorem verfeinerung_nach_betreteTuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hrel : relation_verfeinerung (personen := personen) Z.belegungFein Z.belegungGrob) (hschritt : betreteTuerSchritt G p von nach t Z Z') :
    relation_verfeinerung (personen := personen) Z'.belegungFein Z'.belegungGrob := by
  rcases hschritt with ⟨hPreFein, hPreBetrete, hGrob, hBelegung, hPostBetrete⟩
  intro q r hraum hqfein
  by_cases hq : q.val = p
  · -- Fall 1: q ist die bewegte Person p
    have hpFein : p ∈ personenImOrt Z'.belegungFein (raumAlsOrt r) := by
      simpa [hq] using hqfein
    by_cases hr : r = von
    · -- Fall 1a: p befindet sich nachher angeblich wieder in von
      subst r
      have hpNichtInVon : p ∉ personenImOrt Z'.belegungFein (raumAlsOrt von) := by
        rw [hBelegung]
        exact betreteTuer_person_nicht_mehr_in_von G Z.offen p von t Z.belegungFein hPreBetrete
      exact (hpNichtInVon hpFein).elim
    · -- Fall 1b: p befindet sich nachher angeblich in einem anderen Raum
      have hRaumNichtVon : raumAlsOrt r ≠ raumAlsOrt von := by
        intro h
        apply hr
        exact raumAlsOrt_injektiv h
      have hRaumNichtTuer : raumAlsOrt r ≠ tuerAlsOrt t := by
        exact raumAlsOrt_neq_tuerAlsOrt r t
      -- p gehoert zu den bekannten Personen.
      have hpBekannt : p ∈ personen := by
        exact Z.feinNurBekanntePersonen (raumAlsOrt von) p hPreBetrete.1
      -- Vor dem Betreten war p in keinem anderen Raum.
      have hpNichtInAltemR : p ∉ personenImOrt Z.belegungFein (raumAlsOrt r) := by
        exact person_nicht_in_anderem_ort Z.belegungFein Z.fein_einePersonGenauEinOrt p hpBekannt (raumAlsOrt von) (raumAlsOrt r) hPreBetrete.1 hRaumNichtVon
      -- Nach dem Verschieben ist p ebenfalls nicht in r.
      have hpNichtInR : p ∉ personenImOrt (aktion_betreteTuer p von t Z.belegungFein Z.offen).1 (raumAlsOrt r) := by
        unfold aktion_betreteTuer
        exact verschiebePerson_person_nicht_in_fremdem_ort p (raumAlsOrt von) (tuerAlsOrt t) (raumAlsOrt r) Z.belegungFein hRaumNichtVon hRaumNichtTuer hpNichtInAltemR
      -- Die Belegung nach dem Schritt ist die Aktionsbelegung.
      have hpFeinAktion : p ∈ personenImOrt (aktion_betreteTuer p von t Z.belegungFein Z.offen).1 (raumAlsOrt r) := by
        rw [← hBelegung]
        exact hpFein
      -- Widerspruch: p kann nach dem Betreten nicht in r liegen.
      exact (hpNichtInR hpFeinAktion).elim
  · -- Fall 2: q ist eine andere Person als p
    have hFeinFrame : q.val ∈ personenImOrt Z'.belegungFein (raumAlsOrt r) ↔ q.val ∈ personenImOrt Z.belegungFein (raumAlsOrt r) := by
      rw [hBelegung]
      exact verschiebePerson_frame p q.val (raumAlsOrt von) (tuerAlsOrt t) (raumAlsOrt r) Z.belegungFein hq (raumAlsOrt_neq_tuerAlsOrt von t)
    -- q war bereits vor dem Betreten im Raum r.
    have hqVorher : q.val ∈ personenImOrt Z.belegungFein (raumAlsOrt r) := by
      exact hFeinFrame.mp hqfein
    -- Alte Verfeinerungsrelation anwenden.
    have hqGrobVorher : q.val ∈ personenImOrt Z.belegungGrob (raumAlsOrt r) := by
      exact hrel q r hraum hqVorher
    -- Das grobe Modell bleibt beim Betreten unveraendert.
    rw [hGrob]
    exact hqGrobVorher

-- Nach dem Verlassen der Tuer gilt die Verfeinerungsrelation weiterhin.
-- Hilfslemma
theorem verlasseTuer_person_grob_in_nach {orte : Finset Ort} (p : Person) (von nach : RaumSet orte) (grob : Belegung_safe orte) :
    p ∈ personenImOrt (verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) grob) (raumAlsOrt nach) := by
  apply verschiebePerson_person_in_nach

theorem relation_nach_verlasseTuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hrel : relation_verfeinerung (personen := personen) Z.belegungFein Z.belegungGrob) (hverlasse : verlasseTuerSchritt G p von nach t Z Z') :
    relation_verfeinerung (personen := personen) Z'.belegungFein Z'.belegungGrob := by
  /-
    Zuerst wird der Verlassensschritt zerlegt.
  -/
  rcases hverlasse with ⟨hPreFein, hPreVerlasse, hMoveGrob, hFein, hOffen, hLetzterRaum⟩
  /-
    hMoveGrob ist selbst ein moveGrobSchrittZustand.
    Daraus werden die Vorbedingung und die neue grobe Belegung extrahiert.
  -/
  unfold moveGrobSchrittZustand moveGrobSchritt at hMoveGrob
  rcases hMoveGrob with ⟨hPreGrob, hBelegungGrob, hOffenGrob, hLetzterRaumGrob, hPostGrob⟩
  /-
    Jetzt wird die Definition der Verfeinerungsrelation entfaltet.
  -/
  intro q r hraum hqfein
  by_cases hqp : q.val = p
  · ------------------------------------------------------------
    -- Fall 1: q ist die bewegte Person p
    ------------------------------------------------------------
    have hpFein : p ∈ personenImOrt Z'.belegungFein (raumAlsOrt r) := by
      simpa [hqp] using hqfein
    by_cases hr : r = nach
    · --------------------------------------------------------
      -- Fall 1a: p befindet sich im Zielraum
      --------------------------------------------------------
      subst r
      /-
        Aus hFein folgt, dass die feine Belegung nach
        dem Schritt die Verschiebung von der Tuer in nach ist.
      -/
      have hpFeinNach : p ∈ personenImOrt (verschiebePerson p (tuerAlsOrt t) (raumAlsOrt nach) Z.belegungFein) (raumAlsOrt nach) := by
        have hpFein' := hpFein
        rw [hOffen] at hpFein'
        exact hpFein'
      /-
        Aus hMoveGrob folgt, dass die grobe Belegung nach
        dem Schritt die Verschiebung von von nach nach ist.
      -/
      have hpGrobNach : p ∈ personenImOrt Z'.belegungGrob (raumAlsOrt nach) := by
        rw [hBelegungGrob]
        /-
          hPreGrob enthaelt insbesondere:
          p befindet sich grob in von,
          von und nach sind verschieden,
          und es gibt eine offene Tuerverbindung.
        -/
        apply moveGrob_person_in_nach p von nach G Z.offen Z.belegungGrob
        exact hPreGrob
      simpa [hqp] using hpGrobNach
    · --------------------------------------------------------
      -- Fall 1b: p befindet sich in einem anderen Raum
      --------------------------------------------------------
      have hRaumNichtNach : raumAlsOrt r ≠ raumAlsOrt nach := by
        intro h
        apply hr
        exact raumAlsOrt_injektiv h
      have hRaumNichtTuer : raumAlsOrt r ≠ tuerAlsOrt t := by
        intro h
        cases h
      /-
        p befindet sich vor dem Verlassen in der Tuer.
        Deshalb befindet sich p vor dem Schritt in keinem anderen Ort.
      -/
      have hpBekannt : p ∈ personen := by
        exact Z.feinNurBekanntePersonen (tuerAlsOrt t) p hPreVerlasse.1
      have hpNichtInAltemR : p ∉ personenImOrt Z.belegungFein (raumAlsOrt r) := by
        exact person_nicht_in_anderem_ort Z.belegungFein Z.fein_einePersonGenauEinOrt p hpBekannt (tuerAlsOrt t) (raumAlsOrt r) hPreVerlasse.1 hRaumNichtTuer
      /-
        Beim Verlassen wird p nur aus der Tuer entfernt
        und in nach eingefuegt. Der andere Raum r bleibt unveraendert.
      -/
      have hpNichtInR : p ∉ personenImOrt Z'.belegungFein (raumAlsOrt r) := by
        rw [hOffen]
        exact verschiebePerson_person_nicht_in_fremdem_ort p (tuerAlsOrt t) (raumAlsOrt nach) (raumAlsOrt r) Z.belegungFein hRaumNichtTuer hRaumNichtNach hpNichtInAltemR
      exact (hpNichtInR hpFein).elim
  · ------------------------------------------------------------
    -- Fall 2: q ist eine andere Person als p
    ------------------------------------------------------------
    have hFeinFrame : q.val ∈ personenImOrt Z'.belegungFein (raumAlsOrt r) ↔ q.val ∈ personenImOrt Z.belegungFein (raumAlsOrt r) := by
      rw [hOffen]
      have hTuerNichtNach : tuerAlsOrt t ≠ raumAlsOrt nach := by
        intro h
        cases h
      simpa [aktion_verlasseTuer] using (verschiebePerson_frame p q.val (tuerAlsOrt t) (raumAlsOrt nach) (raumAlsOrt r) Z.belegungFein hqp hTuerNichtNach)
    /-
      q war also schon vor dem Verlassen im Raum r.
    -/
    have hqVorher : q.val ∈ personenImOrt Z.belegungFein (raumAlsOrt r) := by
      exact hFeinFrame.mp hqfein
    /-
      Die alte Verfeinerungsrelation liefert:
      q war auch grob im Raum r.
    -/
    have hqGrobVorher : q.val ∈ personenImOrt Z.belegungGrob (raumAlsOrt r) := by
      exact hrel q r hraum hqVorher
    /-
      Im groben Modell wird ebenfalls nur p verschoben.
      Deshalb bleibt q an allen Raeumen unveraendert.
    -/
    have hGrobFrame : q.val ∈ personenImOrt Z'.belegungGrob (raumAlsOrt r) ↔ q.val ∈ personenImOrt Z.belegungGrob (raumAlsOrt r) := by
      rw [hBelegungGrob]
      have hVonNach : raumAlsOrt von ≠ raumAlsOrt nach := by
        intro h
        apply hPreVerlasse.2.2.2.2.2.2.1
        exact raumAlsOrt_injektiv h
      exact verschiebePerson_frame p q.val (raumAlsOrt von) (raumAlsOrt nach) (raumAlsOrt r) Z.belegungGrob hqp hVonNach
    exact hGrobFrame.mpr hqGrobVorher

-- grob + fein zusammen machen gleiche
theorem relation_nach_aktion_moveFein {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 : Zustand orte personen) (hrel : relation_verfeinerung (personen := personen) Z0.belegungFein Z0.belegungGrob) (hmove : aktion_moveFein G p r1 r2 t Z0 Z1 Z2) :
  relation_verfeinerung (personen := personen) Z2.belegungFein Z2.belegungGrob := by
  rcases hmove with ⟨hbetrete, hverlasse⟩
  have hrel1 : relation_verfeinerung Z1.belegungFein Z1.belegungGrob := relation_nach_betreteTuer G p r1 r2 t Z0 Z1 hrel hbetrete
  exact relation_nach_verlasseTuer G p r1 r2 t Z1 Z2 hrel1 hverlasse

-- grob + fein zusammen machen gleiche + stutter macht keinen unterschied
theorem relation_nach_stutterGrob {orte : Finset Ort} {personen : Finset Person} (Z Z' : Zustand orte personen) (hrel : relation_verfeinerung (personen := personen) Z.belegungFein Z.belegungGrob) (hstutter : stutter Z Z') : 
  relation_verfeinerung (personen := personen) Z'.belegungFein Z'.belegungGrob := by
  rcases hstutter with ⟨hGrob, hFein, hoff, hletzter⟩
  intro p r hraum hp
  rw [hFein] at hp
  rw [hGrob]
  exact hrel p r hraum hp

theorem relation_nach_aktion_moveFein_stutter {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 Z3 : Zustand orte personen) (hrel : relation_verfeinerung (personen := personen) Z0.belegungFein Z0.belegungGrob) (hmove : aktion_moveFein_stutter G p r1 r2 t Z0 Z1 Z2 Z3) :
  relation_verfeinerung (personen := personen) Z3.belegungFein Z3.belegungGrob := by
  rcases hmove with ⟨hbetrete, hstutter, hverlasse⟩
  have hrel1 : relation_verfeinerung Z1.belegungFein Z1.belegungGrob := relation_nach_betreteTuer G p r1 r2 t Z0 Z1 hrel hbetrete
  have hrel2 : relation_verfeinerung Z2.belegungFein Z2.belegungGrob := relation_nach_stutterGrob Z1 Z2 hrel1 hstutter
  exact relation_nach_verlasseTuer
    G p r1 r2 t Z2 Z3 hrel2 hverlasse

-- Person befindet sich nach verlassen im zielraum
theorem verlasseTuerSchritt_person_in_nach {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : verlasseTuerSchritt G p von nach t Z Z') :
  p ∈ personenImOrt Z'.belegungFein (raumAlsOrt nach) := by
  rcases hschritt with ⟨hPreFein, hPreVerlasse, hMoveGrob, hBelegungGrob, hBelegungFein, hOffen, hLetzterRaum, hPost⟩
  have hpAktion : p ∈ personenImOrt (aktion_verlasseTuer p t nach Z.belegungFein Z.offen Z.letzterRaum).1 (raumAlsOrt nach) := by
    exact verlasseTuer_person_in_nach G p von nach t Z.belegungFein Z.offen Z.letzterRaum hPreVerlasse
  rw [hBelegungFein]
  exact hpAktion

-- Person ist nach verlasseTuer nicht mehr in Tuer
theorem verlasseTuerSchritt_person_nicht_mehr_in_tuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : verlasseTuerSchritt G p von nach t Z Z') :
    p ∉ personenImOrt Z'.belegungFein (tuerAlsOrt t) := by
  rcases hschritt with ⟨hPreFein, hPreVerlasse, hMoveGrob, hBelegungGrob, hBelegungFein, hOffen, hLetzterRaum, hPost⟩
  have hpAktion : p ∉ personenImOrt (aktion_verlasseTuer p t nach Z.belegungFein Z.offen Z.letzterRaum).1 (tuerAlsOrt t) := by
    exact verlasseTuer_person_nicht_mehr_in_tuer G p von nach t Z.belegungFein Z.offen Z.letzterRaum hPreVerlasse
  rw [hBelegungFein]
  exact hpAktion

-- andere personen wechseln nicht
theorem verlasseTuer_frame_personen_fein {orte : Finset Ort} (p : Person) (t : TuerSet orte) (nach : RaumSet orte) (fein : Belegung_safe orte) (hTuerNach : tuerAlsOrt t ≠ raumAlsOrt nach) : 
  frame_betreteTuer_verlasseTuer_personen p fein (aktion_verlasseTuer p t nach fein (fun _ => true) (fun _ => none)).1 := by
  intro q hqp o
  unfold aktion_verlasseTuer
  exact verschiebePerson_frame p q (tuerAlsOrt t) (raumAlsOrt nach) o fein hqp hTuerNach

-- andere personen wechseln nicht
theorem verlasseTuerSchritt_frame_personen_fein {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : verlasseTuerSchritt G p von nach t Z Z') : 
  frame_betreteTuer_verlasseTuer_personen p Z.belegungFein Z'.belegungFein := by
  rcases hschritt with ⟨hPreFein, hPreVerlasse, hMoveGrob, hBelegungGrob, hBelegungFein, hOffen, hLetzterRaum, hPost⟩
  have hTuerNach :   tuerAlsOrt t ≠ raumAlsOrt nach := by 
    intro h 
    cases h
  intro q hqp o
  rw [hBelegungFein]
  simpa [aktion_verlasseTuer] using (verschiebePerson_frame p q (tuerAlsOrt t) (raumAlsOrt nach) o Z.belegungFein hqp hTuerNach)

-- tuer bleibt offen
theorem verlasseTuerSchritt_frame_offen {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : verlasseTuerSchritt G p von nach t Z Z') : 
  Z'.offen = Z.offen := by
  rcases hschritt with ⟨hPreFein, hPreVerlasse, hMoveGrob,   hBelegungGrob, hBelegungFein,   hOffen, hLetzterRaum, hPost⟩
  simpa [aktion_verlasseTuer] using hOffen

theorem verlasseTuer_frame_offen {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : verlasseTuerSchritt G p von nach t Z Z') :
    frame_betreteTuer_verlasseTuer_offen Z.offen Z'.offen := by
  unfold frame_betreteTuer_verlasseTuer_offen
  exact verlasseTuerSchritt_frame_offen G p von nach t Z Z' hschritt

-- alle anderen personen aendern ihren standort nicht
theorem verlasseTuer_frame_personen_grob {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : verlasseTuerSchritt G p von nach t Z Z') :    
  frame_moveGrob_personen p Z.belegungGrob Z'.belegungGrob := by
  rcases hschritt with ⟨hPreFein, hPreVerlasse, hMoveGrob, hBelegungGrobDirekt, hBelegungFein, hOffen, hLetzterRaum, hPost⟩
  have hVonNach : von ≠ nach := by exact hPreVerlasse.2.2.2.2.2.2.1
  have hBelegungGrob : Z'.belegungGrob = verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) Z.belegungGrob := by
    exact hBelegungGrobDirekt
  rw [hBelegungGrob]
  exact moveGrob_frame_personen p von nach Z.belegungGrob hVonNach

/- ######### 2. Verfeinerung ######### -/

-- Bedingungen
def oeffneTuer {orte : Finset Ort} (offen : TuerSet orte → Bool) (t : TuerSet orte) : TuerSet orte → Bool :=
  Function.update offen t true

def pre_oeffneTuer {orte : Finset Ort} {personen  : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z : Zustand orte personen) : Prop :=
  darfTuerOeffnen p ∧
  p ∈ personenImOrt Z.belegungFein (raumAlsOrt r) ∧
  G.Adj (raumAlsOrt r) (tuerAlsOrt t) ∧
  Z.offen t = false

def aktion_oeffneTuer {orte : Finset Ort} {personen : Finset Person} (t : TuerSet orte) (Z : Zustand orte personen) : 
  Belegung_safe orte × Belegung_safe orte × (TuerSet orte → Bool) × (Person → Option Raum) :=
  (Z.belegungGrob, Z.belegungFein, oeffneTuer Z.offen t, Z.letzterRaum)

def post_oeffneTuer {orte : Finset Ort} {personen : Finset Person} (t : TuerSet orte) (Z' : Zustand orte personen) : Prop :=
  Z'.offen t = true

def frame_oeffneTuer_grob {orte : Finset Ort} (grob grob' : Belegung_safe orte) : Prop :=
  grob' = grob

def frame_oeffneTuer_fein {orte : Finset Ort} (fein fein' : Belegung_safe orte) : Prop :=
  fein' = fein

def frame_oeffneTuer_letzterRaum (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  letzterRaum' = letzterRaum

def frame_oeffneTuer_offen {orte : Finset Ort} (t : TuerSet orte) (offen offen' : TuerSet orte → Bool) : Prop :=
  offen' t = true ∧
  ∀ m : TuerSet orte, m ≠ t → offen' m = offen m

def oeffneTuerSchritt {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : Prop :=
  pre_oeffneTuer G p r t Z ∧
  Z'.belegungGrob = Z.belegungGrob ∧
  Z'.belegungFein = Z.belegungFein ∧
  Z'.offen = oeffneTuer Z.offen t ∧
  Z'.letzterRaum = Z.letzterRaum ∧
  post_oeffneTuer t Z'

def aktion_grob_fein_oeffne_stutter {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 Z3 Z4 : Zustand orte personen) : Prop :=
  oeffneTuerSchritt G p r1 t Z0 Z1 ∧
  betreteTuerSchritt G p r1 r2 t Z1 Z2 ∧
  stutter Z2 Z3 ∧
  verlasseTuerSchritt G p r1 r2 t Z3 Z4


-- Beweise

-- bewohner koennen aktion ausfuehren
theorem oeffneTuer_nur_durch_Bewohner
    {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z : Zustand orte personen) (hpre : pre_oeffneTuer G p r t Z) :
    istBewohner p := by
  exact hpre.1
  
-- Hilslemma
theorem gast_ist_keine_bewohnerin (g : Person) (hgast : istGast g) : 
  ¬ istBewohner g := by
  cases g <;> 
  simp [istGast, istBewohner] at *

-- die zu oeffnende tuer ist neben dem raum in dem die person ist
theorem oeffneTuer_raum_grenzt_an_tuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z : Zustand orte personen) (hpre : pre_oeffneTuer G p r t Z) :
    G.Adj (raumAlsOrt r) (tuerAlsOrt t) := by
  rcases hpre with ⟨hBewohner, hpRaum, hAdj, hGeschlossen⟩
  exact hAdj

-- gaeste koennen aktion nicht ausfuehren
theorem gast_kann_keine_Tuer_oeffnen {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (g : Person) (r : RaumSet orte) (t : TuerSet orte) (Z : Zustand orte personen) (hgast : istGast g) :
    ¬ pre_oeffneTuer G g r t Z := by
  intro hpre
  have hbewohner : istBewohner g := by
    exact hpre.1
  exact gast_ist_keine_bewohnerin g hgast hbewohner

-- nach oeffen tuer ist die tuer auch offen
theorem oeffneTuer_tuer_ist_offen {orte : Finset Ort} {personen : Finset Person} (t : TuerSet orte) (Z : Zustand orte personen) :
    (oeffneTuer Z.offen t) t = true := by
  simp [oeffneTuer]

-- vor oeffnen war die tuer geschlossen
theorem oeffneTuer_vorher_geschlossen {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z : Zustand orte personen) (hpre : pre_oeffneTuer G p r t Z) :
    Z.offen t = false := by
  exact hpre.2.2.2

-- nach oeffen tuer ist die tuer auch offen
theorem oeffneTuerSchritt_tuer_ist_offen {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : oeffneTuerSchritt G p r t Z Z') :
    Z'.offen t = true := by
  rcases hschritt with ⟨hpre, hGrob, hFein, hOffen, hLetzterRaum, hpost⟩
  rw [hOffen]
  simp [oeffneTuer]

-- belegung bleibt unveraendert
theorem oeffneTuerSchritt_grob_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : oeffneTuerSchritt G p r t Z Z') :
    frame_oeffneTuer_grob Z.belegungGrob Z'.belegungGrob := by
  exact hschritt.2.1

-- belegung bleibt unveraendert
theorem oeffneTuerSchritt_fein_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : oeffneTuerSchritt G p r t Z Z') :
    frame_oeffneTuer_fein Z.belegungFein Z'.belegungFein := by
  exact hschritt.2.2.1

-- der letzteRaum aendert sich nicht beim aufschließen der tuer
theorem oeffneTuerSchritt_letzterRaum_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hschritt : oeffneTuerSchritt G p r t Z Z') :
    frame_oeffneTuer_letzterRaum Z.letzterRaum Z'.letzterRaum := by
  exact hschritt.2.2.2.2.1

-- andere tueren erhalten ihren öffnungsstatus
theorem oeffneTuer_frame_offen {orte : Finset Ort} {personen : Finset Person} (t : TuerSet orte) (Z : Zustand orte personen) :
    frame_oeffneTuer_offen t Z.offen (oeffneTuer Z.offen t) := by
  unfold frame_oeffneTuer_offen
  constructor
  · simp [oeffneTuer]
  · intro t' hne
    simp [oeffneTuer, hne]

-- andere tueren bleiben unveraendert
theorem oeffneTuerSchritt_andere_tueren_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t m : TuerSet orte) (Z Z' : Zustand orte personen) (hne : m ≠ t) (hschritt : oeffneTuerSchritt G p r t Z Z') :
    Z'.offen m = Z.offen m := by
  rcases hschritt with ⟨hpre, hGrob, hFein, hOffen, hLetzterRaum, hpost⟩
  rw [hOffen]
  have hframe : frame_oeffneTuer_offen t Z.offen (oeffneTuer Z.offen t) := oeffneTuer_frame_offen t Z
  exact hframe.2 m hne

-- verfeinerung + relation zusammen

-- Hilfslemma
theorem relation_nach_oeffneTuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) (hrel : relation_verfeinerung (personen := personen) Z.belegungFein Z.belegungGrob) (hschritt : oeffneTuerSchritt G p r t Z Z') : relation_verfeinerung (personen := personen)   Z'.belegungFein Z'.belegungGrob := by
  intro q s hsraum hq
  have hGrob : Z'.belegungGrob = Z.belegungGrob := by
    exact hschritt.2.1
  have hFein : Z'.belegungFein = Z.belegungFein := by
    exact hschritt.2.2.1
  rw [hFein] at hq
  rw [hGrob]
  exact hrel q s hsraum hq

theorem relation_nach_aktion_grob_fein_oeffne_stutter {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 Z3 Z4 : Zustand orte personen) (hrel : relation_verfeinerung (personen := personen) Z0.belegungFein Z0.belegungGrob) (haktion : aktion_grob_fein_oeffne_stutter G p r1 r2 t Z0 Z1 Z2 Z3 Z4) :
  relation_verfeinerung (personen := personen) Z4.belegungFein Z4.belegungGrob := by
  rcases haktion with ⟨hOeffne, hBetrete, hStutter, hVerlasse⟩
  -- Nach dem Öffnen bleiben grob und fein unverändert.
  have hrel1 : relation_verfeinerung (personen := personen) Z1.belegungFein Z1.belegungGrob := relation_nach_oeffneTuer G p r1 t Z0 Z1 hrel hOeffne
  -- Beim Betreten wird nur das feine Modell verändert.
  have hrel2 : relation_verfeinerung (personen := personen) Z2.belegungFein Z2.belegungGrob := relation_nach_betreteTuer G p r1 r2 t Z1 Z2 hrel1 hBetrete
  -- Der Stutter-Schritt verändert weder grob noch fein.
  have hrel3 : relation_verfeinerung (personen := personen) Z3.belegungFein Z3.belegungGrob := relation_nach_stutterGrob Z2 Z3 hrel2 hStutter
  -- Beim Verlassen werden fein und grob konsistent weiterbewegt.
  exact relation_nach_verlasseTuer G p r1 r2 t Z3 Z4 hrel3 hVerlasse

/-
  Beispiel
-/

-- Graph
abbrev room1 := Ort.Raum (Raum.Zimmer 1)
abbrev room2 := Ort.Raum (Raum.Zimmer 2)
abbrev room3 := Ort.Raum Raum.Garten

abbrev door1 : Ort := Ort.Tuer (Tuer.tuer 1)
abbrev door2 : Ort := Ort.Tuer (Tuer.tuer 2)

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
    -- Ab hier bleibt nur noch der Fall gval = room3 uebrig
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
        | sorry -- fertig machen

-- initial Zustand als Beispiel hinzufuegen