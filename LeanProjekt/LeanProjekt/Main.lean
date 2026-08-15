import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

/-!
# Gebäude, Räume und Türen

Dieses Modell beschreibt ein Gebäude mit Räumen und Türen. Personen können
sich zwischen Räumen bewegen, indem sie Türen betreten und wieder verlassen.

Das Modell verwendet zwei Ebenen:

* Das **grobe Modell** speichert, in welchem Raum sich eine Person befindet.
* Das **feine Modell** speichert zusätzlich, ob sich eine Person gerade in einer
  Tür befindet.

Eine Bewegung durch eine Tür besteht deshalb aus zwei feinen Schritten:

1. Die Person verlässt den Ausgangsraum und betritt die Tür.
2. Die Person verlässt die Tür und betritt den Zielraum.

Das grobe Modell wird erst beim Verlassen der Tür aktualisiert.

## Modellierungsidee

Die statischen Eigenschaften des Gebäudes werden durch Typen und Strukturen
beschrieben. Dadurch können nur Objekte verwendet werden, die grundsätzlich
zum Modell passen.

Die dynamischen Eigenschaften werden durch `Zustand` beschrieben. Ein Zustand
enthält unter anderem:

* die grobe Belegung,
* die feine Belegung,
* den Öffnungszustand jeder Tür,
* den letzten Raum jeder Person.

Vor- und Nachbedingungen werden als logische Aussagen formuliert. Eine Aktion
ist gültig, wenn ihre Vorbedingung gilt und die entsprechende Nachbedingung
nach dem Schritt erfüllt ist.

## Wichtige Invarianten

Das Modell berücksichtigt insbesondere folgende Eigenschaften:

* Räume und Türen sind verschiedene Ortstypen.
* Türen verbinden nur Räume mit Räumen.
* Die Nachbarschaft ist symmetrisch.
* Der Graph ist schleifenfrei.
* Genau ein Garten existiert.
* Der Garten besitzt genau eine Tür.
* Jede Person befindet sich im jeweiligen Modell höchstens beziehungsweise
  genau an einem Ort.
* Grobe Türen sind immer leer.
* Personen in einer feinen Tür befinden sich im groben Modell in ihrem letzten
  Raum.
* Nur bekannte Personen kommen in Belegungen vor.
* Eine Tür mit einer Person ist geöffnet.
* Die feine Belegung verfeinert die grobe Belegung.
* Die Verfeinerungsrelation bleibt nach gültigen Aktionen erhalten.

## Benennung von Bedingungen

Für die Definitionen werden folgende Präfixe verwendet:

* `pre_` bezeichnet eine Vorbedingung.
* `post_` bezeichnet eine Nachbedingung.
* `frame_` bezeichnet Eigenschaften, die unverändert bleiben.
* `aktion_` bezeichnet die eigentliche Zustandsänderung.
* `...Schritt` bezeichnet eine vollständige Übergangsrelation.
-/

/-!
## 1. Domänenobjekte

Die folgenden induktiven Typen bilden die grundlegenden Objekte des Gebäudes.
-/

/-- Eine Person ist entweder Bewohner:in oder Gast. -/
inductive Person where
  | Bewohner (id : Nat)
  | Gast (id : Nat)
deriving DecidableEq, Repr

/-- Ein Raum ist entweder ein nummeriertes Zimmer oder der Garten. -/
inductive Raum where
  | Zimmer (id : Nat)
  | Garten
deriving DecidableEq, Repr

/-- Eine Tür wird durch eine natürliche Nummer identifiziert. -/
inductive Tuer where
  | tuer (id : Nat)
deriving DecidableEq, Repr

/--
Ein Ort ist entweder ein Raum oder eine Tür.

Diese Unterscheidung ist wichtig, weil Personen im feinen Modell sowohl in
Räumen als auch in Türen stehen können, während das grobe Modell nur Räume
verwendet.
-/
inductive Ort where
  | Raum (r : Raum)
  | Tuer (t : Tuer)
deriving DecidableEq, Repr

/-!
## 2. Klassifikationsprädikate

Diese Funktionen klassifizieren Orte und Personen. Sie werden später in
Vorbedingungen und Invarianten verwendet.
-/

/-- Gibt an, ob ein Ort ein Raum ist. -/
def istRaum : Ort → Prop
  | .Raum _ => True
  | .Tuer _ => False

/-- Gibt an, ob ein Ort eine Tür ist. -/
def istTuer : Ort → Prop
  | .Raum _ => False
  | .Tuer _ => True

/-- Gibt an, ob ein Ort der Garten ist. -/
def istGarten : Ort → Prop
  | .Raum r => r = .Garten
  | .Tuer _ => False

/-- Gibt an, ob eine Person Bewohner:in ist. -/
def istBewohner : Person → Prop
  | .Bewohner _ => True
  | .Gast _ => False

/-- Gibt an, ob eine Person Gast ist. -/
def istGast : Person → Prop
  | .Gast _ => True
  | .Bewohner _ => False

/-- Nur Bewohner:innen dürfen Türen öffnen. -/
def darfTuerOeffnen (p : Person) : Prop :=
  istBewohner p

/-!
## 3. Endliche Mengen und Teiltypen

Das Gebäude enthält eine endliche Menge erlaubter Orte. Die Typen `OrtSet`,
`RaumSet` und `TuerSet` enthalten zusätzlich den Beweis, dass das jeweilige
Objekt tatsächlich in dieser Ortsmenge vorkommt.

Dadurch können ungültige Räume oder Türen nicht versehentlich verwendet werden.
-/

/-- Ein Ort, der in der Ortsmenge enthalten ist. -/
abbrev OrtSet (Orte : Finset Ort) := { p : Ort // p ∈ Orte }

/-- Eine Tür, deren Ort in der Ortsmenge enthalten ist. -/
abbrev TuerSet (Orte : Finset Ort) := { t : Tuer // Ort.Tuer t ∈ Orte }

/-- Ein Raum, dessen Ort in der Ortsmenge enthalten ist. -/
abbrev RaumSet (Orte : Finset Ort) := { r : Raum // Ort.Raum r ∈ Orte }

/-- Eine Person, die in der Personenmenge enthalten ist. -/
abbrev PersonSet (Personen : Finset Person) := { p : Person // p ∈ Personen }

/-- Ein Raum als Ort. -/
def raumAlsOrt {orte : Finset Ort} (r : RaumSet orte) : OrtSet orte :=
  ⟨Ort.Raum r.1, r.2⟩
/-- Eine Tür als Ort. -/
def tuerAlsOrt {orte : Finset Ort} (t : TuerSet orte) : OrtSet orte :=
  ⟨Ort.Tuer t.1, t.2⟩

/-!
## 4. Graph und Gebäudeplan

Der Gebäudeplan beschreibt die statische Topologie des Gebäudes: die
erlaubten Orte und die Nachbarschaftsbeziehung zwischen diesen Orten.

Die eigentliche Graphstruktur wird durch `SimpleGraph` bereitgestellt. Dadurch
sind Symmetrie der Nachbarschaft und Schleifenfreiheit bereits Bestandteil
der Struktur. `Kante` wird zusätzlich für das konkrete Beispielgebäude
(Abschnitt 12) benötigt, um aus einer einfachen Nachbarschaftsliste einen
`SimpleGraph` zu konstruieren.
-/

/--
Eine Kante ordnet jedem Ort eine Menge benachbarter Orte zu.

Diese Definition wird für das Beispielgebäude verwendet. Für die beweisbaren
Graph-Eigenschaften wird anschließend `SimpleGraph` genutzt.
-/
abbrev Kante := Finmap (fun _ : Ort => Finset Ort)

/-- Ein Gebäudeplan ist ein einfacher Graph über den erlaubten Orten. -/
abbrev GebaeudePlan (Orte : Finset Ort) := SimpleGraph (OrtSet Orte)

/-- Prüft anhand der Kantenliste `Kanten`, ob von `n1` aus eine direkte Verbindung zu `n2` besteht. -/
def OrteSindBenachbart (Kanten : Kante) (n1 : Ort) (n2 : Ort) : Bool := -- Gibt es von n1 aus eine Verbindung zu n2?
  match Kanten.lookup n1 with
  | none => false
  | some nachbarn => n2 ∈ nachbarn
--   Kanten.any (fun (node, Kantes) => n1 == node && Kantes.contains n2)

/-- Eine Kante ist bipartit, wenn sie einen Raum mit einer Tür verbindet (in beliebiger Richtung). Räume dürfen nicht direkt mit anderen Räumen verbunden sein. -/
def KanteIsBipartite (u v : Ort) : Prop :=
  match u, v with
  | .Raum _, .Tuer _ => True
  | .Tuer _, .Raum _ => True
  | _      , _       => False

/-- Entscheidbare (boolesche) Version von `KanteIsBipartite`. -/
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

/-- Eine Nachbarschaftsrelation ist bipartit, wenn jede ihrer Kanten bipartit ist. -/
def adjIsBipartite {Orte : Finset Ort} (adj : (OrtSet Orte) → (OrtSet Orte) → Prop) :=
  ∀ (u v : OrtSet Orte), adj u v → KanteIsBipartite u v

/-!
## 5. Belegungen

Eine Belegung beschreibt, welche Personen sich an welchen Orten aufhalten.
Die folgenden Prädikate beschreiben Eigenschaften einzelner Belegungen sowie
den Zusammenhang zwischen der groben und der feinen Belegung. Sie werden im
`Zustand` (Abschnitt 7) als Invarianten verwendet.
-/

/--
Eine sichere Belegung ordnet jedem erlaubten Ort eine endliche Menge von
Personen zu.
-/
abbrev Belegung_safe (Orte : Finset Ort) := Finmap (fun _ : (OrtSet Orte) => Finset Person) -- arbeitet nur mit den erlaubten Orten aus Orte

/-- Liest die Menge der Personen, die sich laut Belegung `b` am Ort `o` befinden. -/
def personenImOrt {orte : Finset Ort} (b : Belegung_safe orte) (o : OrtSet orte) : Finset Person :=
  (b.lookup o).getD ∅

/-- Jede Person aus `personen` befindet sich in der Belegung `b` an genau einem Ort. -/
def einePersonGenauEinOrt {orte : Finset Ort} {personen : Finset Person} (b : Belegung_safe orte) : Prop :=
  ∀ p : PersonSet personen, (Finset.univ.filter (fun o => p.val ∈ (b.lookup o).getD ∅)).card = 1

/-- Jede Tür, in der sich (im feinen Modell) eine Person befindet, ist geöffnet. -/
def tuerOffenWennPerson {orte} (belegungFein : Belegung_safe orte) (offen : TuerSet orte → Bool) : Prop :=
  ∀ o : TuerSet orte, (belegungFein.lookup (tuerAlsOrt o)).getD ∅ ≠ ∅ → offen o = true

/-- Verfeinerungsrelation: Befindet sich eine Person im feinen Modell in einem Raum, so befindet sie sich auch im groben Modell in diesem Raum. (Das schließt nicht aus, dass sie im feinen Modell zugleich in einer Tür steht.) -/
def relation_verfeinerung {orte : Finset Ort} {personen : Finset Person} (fein grob : Belegung_safe orte) : Prop :=
  ∀ p : PersonSet personen, ∀ r : RaumSet orte,
    istRaum (raumAlsOrt r) →
    p.val ∈ personenImOrt fein (raumAlsOrt r) →
    p.val ∈ personenImOrt grob (raumAlsOrt r)

/-- Steht eine Person im feinen Modell in einer Tür, so ist ihr letzter Raum bekannt, und im groben Modell befindet sie sich dort. -/
def verfeinerung_tuer_letzterRaum {orte : Finset Ort} {personen : Finset Person} (grob fein : Belegung_safe orte) (letzterRaum : Person → Option Raum) : Prop :=
  ∀ p : PersonSet personen,
    ∀ t : TuerSet orte,
      p.1 ∈ personenImOrt fein (tuerAlsOrt t) →
      ∃ r : Raum,
        letzterRaum p.1 = some r ∧
        ∃ hr : Ort.Raum r ∈ orte,
          p.1 ∈ personenImOrt grob ⟨Ort.Raum r, hr⟩

/-- Im groben Modell sind Türen stets leer; Personen stehen dort nur in Räumen. -/
def grobeTuerenSindLeer {orte : Finset Ort} (grob : Belegung_safe orte) : Prop :=
  ∀ t : TuerSet orte,
    personenImOrt grob (tuerAlsOrt t) = ∅

/-- In der Belegung `b` kommen nur Personen aus `personen` vor. -/
def nurBekanntePersonen {orte : Finset Ort} {personen : Finset Person} (b : Belegung_safe orte) : Prop :=
  ∀ o : OrtSet orte,
    ∀ p : Person,
      p ∈ personenImOrt b o →
      p ∈ personen

/-!
## 6. Statische Eigenschaften des Gebäudeplans

`BipartiteOrtGraph` bündelt alle statischen Eigenschaften, die ein gültiger
Gebäudeplan erfüllen muss: Die Nachbarschaft ist bipartit (Türen verbinden
ausschließlich Räume, nie Räume mit Räumen oder Türen mit Türen), es gibt
genau einen Garten, und dieser Garten besitzt genau eine Tür.
-/

/-- Der Garten besitzt unter der Nachbarschaftsrelation `G` genau eine angrenzende Tür. -/
def gartenHatGenauEineTuer {orte : Finset Ort} (G : GebaeudePlan orte) : Prop :=
  ∀ g : OrtSet orte,
    istGarten g.1 →
    ∃! t : OrtSet orte,
      istTuer t.1 ∧ G.Adj g t

/-
  Gebaeudeplan, der bipartite ist, nachbar-symmetrie gegeben, damit auch tuerVerbindetZweiRaeume, alleNachbarnSindSymmerisch inkl. Axiome

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
    (match t1,t2 with | Tuer.tuer id1, Tuer.tuer id2 => id1 ≠ id2) -- jede Tuer gibt es nur einmal
  gartenHatGenauEinenNachbarn : gartenHatGenauEineTuer toSimpleGraph

/-!
## 7. Dynamische Zustände und Invarianten

Während der Gebäudeplan statisch ist, beschreibt ein `Zustand` die momentane,
veränderliche Ausprägung des Gebäudemodells: die grobe und die feine
Belegung, den Öffnungszustand jeder Tür sowie den letzten Raum jeder Person.

Die Felder am Ende der Struktur sind Invarianten. Sie stellen sicher, dass
jeder gültige Zustand die gewünschten Eigenschaften erfüllt.
-/

structure Zustand (orte : Finset Ort) (personen : Finset Person) where
  /-- Belegung des groben Modells. -/
  belegungGrob : Belegung_safe orte
  /-- Belegung des feinen Modells. -/
  belegungFein : Belegung_safe orte
  /-- Öffnungszustand jeder Tür. -/
  offen : TuerSet orte → Bool
  /--
  Der letzte Raum einer Person.

  Dieser Wert wird erst aktualisiert, wenn eine Person die Tür wieder verlässt.
  Beim Betreten einer Tür bleibt der letzte Raum unverändert.
  -/
  letzterRaum : Person → Option Raum -- 1 oder kein Raum
  /-- Jede betrachtete Person befindet sich grob genau an einem Ort. -/
  grob_einePersonGenauEinOrt : einePersonGenauEinOrt (personen := personen) belegungGrob
  /-- Jede betrachtete Person befindet sich fein genau an einem Ort. -/
  fein_einePersonGenauEinOrt : einePersonGenauEinOrt (personen := personen) belegungFein
  /-- Eine belegte Tür ist geöffnet. -/
  tuerOffenWennPersonEnthalten : tuerOffenWennPerson belegungFein offen
  /--
  Die feine Belegung verfeinert die grobe Belegung.

  Befindet sich eine Person im feinen Modell in einem Raum, dann befindet sie
  sich dort auch im groben Modell.
  -/
  verfeinerung : relation_verfeinerung (personen := personen) belegungGrob belegungFein
  /--
  Fuer jede betrachtete Person und jede Tuer gilt: Wenn die Person im feinen Modell in dieser Tuer steht, dann gibt es einen Raum, der als ihr letzter Raum gespeichert ist, und die Person befindet sich im groben in diesem Raum.
  -/
  tuerVerfeinerung : verfeinerung_tuer_letzterRaum (personen := personen) belegungGrob belegungFein letzterRaum
  /-- Türen sind im groben Modell immer leer. -/
  grobeTuerenSindImmerLeer : grobeTuerenSindLeer belegungGrob
  /-- Im groben Modell kommen nur bekannte Personen vor. -/
  grobNurBekanntePersonen : nurBekanntePersonen (personen := personen) belegungGrob
  /-- Im feinen Modell kommen nur bekannte Personen vor. -/
  feinNurBekanntePersonen : nurBekanntePersonen (personen := personen) belegungFein

/-!
## 8. Allgemeine Hilfsfunktionen

Diese Hilfsfunktionen werden von mehreren Aktionen (grobe Bewegung, feine
Bewegung und Türöffnung) gemeinsam verwendet.
-/

/-- Extrahiert den Raum aus einem Ort, sofern es sich um einen Raum handelt (sonst `none`). -/
def raumVonOrt {orte : Finset Ort} (o : OrtSet orte) : Option Raum :=
  match o.1 with
  | Ort.Raum r => some r
  | Ort.Tuer _ => none

/-- Setzt `letzterRaum p` auf den Zielraum `nach`; für alle anderen Personen bleibt der Wert unverändert. -/
def aktualisiereLetztenRaum {orte : Finset Ort} (letzterRaum : Person → Option Raum) (p : Person) (nach : RaumSet orte) :
    Person → Option Raum := Function.update letzterRaum p (raumVonOrt (raumAlsOrt nach))

/-- Überschreibt die Personenmenge am Ort `o` in der Belegung `b`. -/
def setzeBelegung {orte : Finset Ort} (b : Belegung_safe orte) (o : OrtSet orte) (personen : Finset Person) :
  Belegung_safe orte := Finmap.insert o personen b

/-- Verschiebt Person `p` von Ort `von` nach Ort `nach` innerhalb der Belegung `b`. -/
def verschiebePerson {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) :
  Belegung_safe orte :=
  let personenVon := personenImOrt b von
  let personenNach := personenImOrt b nach
  let bVon := setzeBelegung b von (personenVon.erase p)
  setzeBelegung bVon nach (insert p personenNach)

/-- Es gibt eine geöffnete Tür, die die Räume `von` und `nach` direkt verbindet. -/
def hatOffeneVerbindung {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (von nach : RaumSet orte) : Prop :=
  ∃ t : TuerSet orte,
    istTuer (tuerAlsOrt t) ∧
    G.Adj (raumAlsOrt von) (tuerAlsOrt t) ∧
    G.Adj (raumAlsOrt nach) (tuerAlsOrt t) ∧
    offen t = true

-- Stutter
def stutter {orte : Finset Ort} {personen : Finset Person} (Z Z' : Zustand orte personen) : Prop :=
  Z'.belegungGrob = Z.belegungGrob ∧
  Z'.belegungFein = Z.belegungFein ∧
  Z'.offen = Z.offen ∧
  Z'.letzterRaum = Z.letzterRaum

/-!
## 9. Grobe Bewegung

Ab hier beginnt das initiale Modell (die nullte Verfeinerung) der Aktionen.
Ein grober Bewegungsschritt verschiebt eine Person direkt von einem Raum in
einen benachbarten Raum, sofern eine offene Tür beide verbindet. Das feine
Modell (Abschnitt 10) verfeinert diesen Schritt in zwei Teilschritte über
die Tür.
-/

/-!
### 9.1 Vor- und Nachbedingungen
-/

/-- Vorbedingung für einen groben Schritt: `p` steht in `von`, `von` und `nach` sind verschiedene Räume, und es gibt eine offene Tür dazwischen. -/
def pre_moveGrobMitTuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) : Prop :=
  p ∈ personenImOrt b (raumAlsOrt von) ∧
  istRaum (raumAlsOrt von) ∧
  istRaum (raumAlsOrt nach) ∧
  von ≠ nach ∧
  hatOffeneVerbindung G offen von nach

/-- Nachbedingung für einen groben Schritt: `p` ist nun in `nach`, nicht mehr in `von`, und `letzterRaum` wurde aktualisiert. -/
def post_moveGrob {orte : Finset Ort} (p : Person) (G : BipartiteOrtGraph orte) (von nach : RaumSet orte) (b' : Belegung_safe orte) (offen' : TuerSet orte → Bool) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  p ∉ personenImOrt b' (raumAlsOrt von) ∧
  p ∈ personenImOrt b' (raumAlsOrt nach) ∧
  letzterRaum' = aktualisiereLetztenRaum letzterRaum p nach ∧
  hatOffeneVerbindung G offen' von nach

/-!
### 9.2 Frame-Bedingungen und Aktionen
-/

/-- Alle Personen außer `p` bleiben in jedem Raum unverändert. -/
def frame_moveGrob_personen {orte : Finset Ort} (p : Person) (b b' : Belegung_safe orte) : Prop :=
  ∀ q : Person,
    q ≠ p →
    ∀ o : RaumSet orte,
      q ∈ personenImOrt b' (raumAlsOrt o) ↔
      q ∈ personenImOrt b (raumAlsOrt o)

/-- Der Öffnungszustand der Türen ändert sich nicht, und `von`/`nach` bleiben weiterhin durch eine offene Tür verbunden. -/
def frame_moveGrob_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (von nach : RaumSet orte) (offen offen' : TuerSet orte → Bool) : Prop :=
  offen' = offen ∧ hatOffeneVerbindung G offen von nach

/-- Führt den groben Schritt aus: verschiebt `p` von `von` nach `nach` und aktualisiert `letzterRaum`. -/
def aktion_moveGrob {orte : Finset Ort} (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) :
  Belegung_safe orte × (TuerSet orte → Bool) × (Person → Option Raum) :=
  (
    verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b,
    offen,
    aktualisiereLetztenRaum letzterRaum p nach
  )

/-!
### 9.3 Übergangsrelation
-/

/-- Übergangsrelation für einen gültigen groben Schritt (direkt über Belegungen, Türen und `letzterRaum` formuliert). -/
def moveGrobSchritt {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen offen' : TuerSet orte → Bool) (p : Person) (von nach : RaumSet orte) (b b' : Belegung_safe orte) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  pre_moveGrobMitTuer G offen p von nach b ∧
  let aktion := aktion_moveGrob p von nach b offen letzterRaum
  b' = aktion.1 ∧
  offen' = aktion.2.1 ∧
  letzterRaum' = aktion.2.2 ∧
  post_moveGrob p G von nach b' offen' letzterRaum letzterRaum'

/-- Variante von `moveGrobSchritt`, formuliert direkt über zwei Zustände `Z` und `Z'` statt über einzelne Felder. -/
def moveGrobSchrittZustand {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (Z Z' : Zustand orte personen) : Prop :=
  moveGrobSchritt G Z.offen Z'.offen p von nach Z.belegungGrob Z'.belegungGrob Z.letzterRaum Z'.letzterRaum

/-!
### 9.4 Beweise zur groben Bewegung
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

-- gleicher Beweis aber nun mit Zustand und Graphen
theorem moveGrobSchrittZustand_person_nicht_in_von {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (Z Z' : Zustand orte personen) : moveGrobSchrittZustand G p von nach Z Z' → p ∉ personenImOrt Z'.belegungGrob (raumAlsOrt von) := by
  intro hmove
  unfold moveGrobSchrittZustand moveGrobSchritt at hmove
  dsimp [aktion_moveGrob] at hmove
  rcases hmove with ⟨hpre, hbelegungGrob, hoffenen, hletzterRaum, hpost⟩
  rw [hbelegungGrob]
  exact moveGrob_person_nicht_in_von G Z.offen p von nach Z.belegungGrob hpre

-- Alle anderen Personen bleiben unveraendert, q ist einfach eine andere random Person
theorem moveGrob_frame_personen {orte : Finset Ort} (p : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) : von ≠ nach → frame_moveGrob_personen p b (verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b) := by
  intro hVonNach
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

theorem moveGrob_frame_personen_gleichbleibend {orte : Finset Ort} (p q : Person) (von nach : RaumSet orte) (b : Belegung_safe orte) : q ≠ p → von ≠ nach → ∀ o : RaumSet orte,
      q ∈ personenImOrt (verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) b) (raumAlsOrt o) ↔
      q ∈ personenImOrt b (raumAlsOrt o) := by
  intro hpq hVonNach o
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
theorem grobeBewegung_hat_Raumparameter {orte : Finset Ort} {G : BipartiteOrtGraph orte} {offen : TuerSet orte → Bool} {p : Person} {von nach : RaumSet orte} {b : Belegung_safe orte} : pre_moveGrobMitTuer G offen p von nach b → istRaum (raumAlsOrt von) ∧ istRaum (raumAlsOrt nach) := by
  intro hpre
  exact ⟨hpre.2.1, hpre.2.2.1⟩

theorem moveGrobSchritt_nur_zwischen_Raeumen {orte : Finset Ort} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (belegungGrob belegungGrob' : Belegung_safe orte) (offen offen' : TuerSet orte → Bool) (letzterRaum letzterRaum' : Person → Option Raum) : moveGrobSchritt G offen offen' p von nach belegungGrob belegungGrob' letzterRaum letzterRaum' → istRaum (raumAlsOrt von) ∧ istRaum (raumAlsOrt nach) := by
  intro hschritt
  exact ⟨hschritt.1.2.1, hschritt.1.2.2.1⟩

/-!
## 10. Feine Bewegung

Eine Bewegung durch eine Tür besteht aus zwei feinen Schritten: Die Person
verlässt zunächst den Ausgangsraum und betritt die Tür (Abschnitt 10.1); im
zweiten Schritt verlässt sie die Tür und betritt den Zielraum (Abschnitt
10.2). Das grobe Modell wird erst beim Verlassen der Tür aktualisiert.
-/

/-!
### 10.1 Eine Tür betreten

Beim Betreten einer Tür wird nur die feine Belegung verändert:

* Die Person wird aus dem Ausgangsraum entfernt.
* Die Person wird in die Tür eingefügt.
* Das grobe Modell bleibt unverändert.
* Der Öffnungszustand bleibt unverändert.
* Der letzte Raum der Person bleibt unverändert.
-/

/-- Vorbedingung zum Betreten einer Tür: `p` steht im angrenzenden Raum `von`, und die Tür `t` ist offen. -/
def pre_betreteTuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (offen : TuerSet orte → Bool) (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) : Prop :=
  p ∈ personenImOrt fein (raumAlsOrt von) ∧
  istRaum (raumAlsOrt von) ∧
  istTuer (tuerAlsOrt t) ∧
  G.Adj (raumAlsOrt von) (tuerAlsOrt t) ∧
  offen t = true

/-- Nachbedingung zum Betreten einer Tür: `p` ist nun in `t`, nicht mehr in `von`; `letzterRaum` bleibt unverändert. -/
def post_betreteTuer {orte : Finset Ort} (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein' : Belegung_safe orte) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  p ∉ personenImOrt fein' (raumAlsOrt von) ∧
  p ∈ personenImOrt fein' (tuerAlsOrt t) ∧
  letzterRaum' = letzterRaum

/-- Rahmenbedingung: `letzterRaum` aller anderen Personen bleibt unverändert. Gilt sowohl für das Betreten als auch für das Verlassen einer Tür. -/
def frame_betreteTuer_verlasseTuer_letzterRaum (p : Person) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  (∀ q : Person, q ≠ p → letzterRaum' q = letzterRaum q)

/-- Rahmenbedingung: Der Öffnungszustand aller Türen bleibt unverändert. Gilt sowohl für das Betreten als auch für das Verlassen einer Tür. -/
def frame_betreteTuer_verlasseTuer_offen {orte : Finset Ort} (offen offen' : TuerSet orte → Bool) : Prop :=
  offen' = offen

/-- Rahmenbedingung: Alle Personen außer `p` bleiben im feinen Modell an ihrem Ort. Gilt sowohl für das Betreten als auch für das Verlassen einer Tür. -/
def frame_betreteTuer_verlasseTuer_personen {orte : Finset Ort} (p : Person) (fein fein' : Belegung_safe orte) : Prop :=
  ∀ q : Person, q ≠ p →
    ∀ o : OrtSet orte,
      q ∈ personenImOrt fein' o ↔
      q ∈ personenImOrt fein o

/-- Rahmenbedingung: Das grobe Modell bleibt beim Betreten einer Tür unverändert. -/
def frame_betreteTuer_grob {orte : Finset Ort} (grob grob' : Belegung_safe orte) : Prop :=
  grob' = grob

/-- Führt das Betreten der Tür aus: verschiebt `p` von `von` in die Tür `t`; der Öffnungszustand bleibt unverändert. -/
def aktion_betreteTuer {orte : Finset Ort} (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) : Belegung_safe orte × (TuerSet orte → Bool) :=
  (
    verschiebePerson p (raumAlsOrt von) (tuerAlsOrt t) fein,
    offen
  )

/-!
### 10.2 Eine Tür verlassen

Beim Verlassen einer Tür wird die Person:

* aus der Tür entfernt,
* in den Zielraum eingefügt,
* im feinen Modell in den Zielraum verschoben,
* im groben Modell ebenfalls in den Zielraum verschoben.

Erst bei diesem Schritt wird `letzterRaum` aktualisiert.
-/

/-- Vorbedingung zum Verlassen einer Tür: `p` steht in der Tür `t`, die `von` mit `nach` verbindet, und `von` ist als letzter Raum von `p` vermerkt. -/
def pre_verlasseTuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (letzterRaum : Person → Option Raum) : Prop :=
  p ∈ personenImOrt fein (tuerAlsOrt t) ∧
  istRaum (raumAlsOrt nach) ∧
  istRaum (raumAlsOrt von) ∧
  istTuer (tuerAlsOrt t) ∧
  G.Adj (raumAlsOrt von) (tuerAlsOrt t) ∧
  G.Adj (raumAlsOrt nach) (tuerAlsOrt t) ∧
  von ≠ nach ∧
  letzterRaum p = raumVonOrt (raumAlsOrt von)

/-- Nachbedingung zum Verlassen einer Tür: `p` ist nun in `nach`, nicht mehr in `t`; `letzterRaum` wird auf `nach` aktualisiert. -/
def post_verlasseTuer {orte : Finset Ort} (p : Person) (nach : RaumSet orte) (t : TuerSet orte) (fein fein' : Belegung_safe orte) (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  p ∉ personenImOrt fein (tuerAlsOrt t) ∧
  p ∈ personenImOrt fein' (raumAlsOrt nach) ∧
  letzterRaum' = aktualisiereLetztenRaum letzterRaum p nach

/-- Führt das Verlassen der Tür aus: verschiebt `p` von der Tür `t` nach `nach` und aktualisiert `letzterRaum`. -/
def aktion_verlasseTuer {orte : Finset Ort} (p : Person) (t : TuerSet orte) (nach : RaumSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) : Belegung_safe orte × (TuerSet orte → Bool) × (Person → Option Raum) :=
  (
    verschiebePerson p (tuerAlsOrt t) (raumAlsOrt nach) fein,
    offen,
    aktualisiereLetztenRaum letzterRaum p nach
  )

/-!
### 10.3 Zusammengesetzte feine Bewegung
-/

/-- Gemeinsame Vorbedingung an Räume und Tür für einen feinen Bewegungsschritt: `r1` und `r2` sind verschiedene, durch `t` verbundene Räume. -/
def pre_fein {orte : Finset Ort} (G : BipartiteOrtGraph orte) (r1 r2 : RaumSet orte) (t : TuerSet orte) : Prop :=
  r1 ≠ r2 ∧
  istRaum (raumAlsOrt r1) ∧
  istRaum (raumAlsOrt r2) ∧
  istTuer (tuerAlsOrt t) ∧
  G.Adj (raumAlsOrt r1) (tuerAlsOrt t) ∧
  G.Adj (raumAlsOrt r2) (tuerAlsOrt t)

/-- Übergangsrelation für das Betreten einer Tür, formuliert über zwei Zustände `Z` und `Z'`. -/
def betreteTuerSchritt {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : Prop :=
  pre_fein G von nach t ∧
  pre_betreteTuer G Z.offen p von t Z.belegungFein ∧
  Z'.belegungGrob = Z.belegungGrob ∧
  let aktion := aktion_betreteTuer p von t Z.belegungFein Z.offen
  Z'.belegungFein = aktion.1 ∧
  Z'.offen = aktion.2 ∧
  post_betreteTuer p von t Z.belegungFein Z.letzterRaum Z'.letzterRaum

/-- Übergangsrelation für das Verlassen einer Tür, formuliert über zwei Zustände `Z` und `Z'`. Aktualisiert dabei auch konsistent das grobe Modell. -/
def verlasseTuerSchritt {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : Prop :=
  pre_fein G von nach t ∧
  pre_verlasseTuer G p von nach t Z.belegungFein Z.letzterRaum ∧
  moveGrobSchrittZustand G p von nach Z Z' ∧ -- hier muss auch das grobe Modell ausgefuehrt werden, sonst sind die Zustaende nicht konsistent
  -- Z'.belegungGrob = verschiebePerson p (raumAlsOrt von) (raumAlsOrt nach) Z.belegungGrob ∧
  let aktion := aktion_verlasseTuer p t nach Z.belegungFein Z.offen Z.letzterRaum
  Z'.belegungFein = aktion.1 ∧
  Z'.offen = aktion.2.1 ∧
  Z'.letzterRaum = aktion.2.2 ∧
  post_verlasseTuer p nach t Z.belegungFein Z'.belegungFein Z.letzterRaum Z'.letzterRaum

/-- Eine vollständige feine Bewegung von `r1` nach `r2`: Tür betreten (`Z0 → Z1`), dann Tür verlassen (`Z1 → Z2`). -/
def aktion_moveFein {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 : Zustand orte personen) : Prop :=
  betreteTuerSchritt G p r1 r2 t Z0 Z1 ∧
  verlasseTuerSchritt G p r1 r2 t Z1 Z2

/-- Wie `aktion_moveFein`, jedoch mit einem zusätzlichen Stutter-Schritt zwischen Betreten und Verlassen der Tür. -/
def aktion_moveFein_stutter {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 Z3 : Zustand orte personen) : Prop :=
  betreteTuerSchritt G p r1 r2 t Z0 Z1 ∧
  stutter Z1 Z2 ∧
  verlasseTuerSchritt G p r1 r2 t Z2 Z3

/-!
### 10.4 Beweise zur feinen Bewegung
-/

-- hier wird OrtSet verwendet, später wird dieses bei Nutzung spezifiziert, Hilfslemma
theorem verschiebePerson_person_nicht_in_von {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) : von ≠ nach → p ∉ personenImOrt (verschiebePerson p von nach b) von := by
  intro hVonNach
  simp [
    verschiebePerson,
    setzeBelegung,
    personenImOrt,
    hVonNach
  ]

-- hier wird OrtSet verwendet, später wird dieses bei Nutzung spezifiziert, Hilfslemma
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
theorem verschiebePerson_person_nicht_in_fremdem_ort {orte : Finset Ort} (p : Person) (von nach o : OrtSet orte) (b : Belegung_safe orte) : o ≠ von → o ≠ nach → p ∉ personenImOrt b o → p ∉ personenImOrt (verschiebePerson p von nach b) o := by
  intro hVon hNach hpNichtInO
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
theorem betreteTuer_aktion_offen {orte : Finset Ort} (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) :
  (aktion_betreteTuer p von t fein offen).2 = offen := by
  rfl

-- Hilfslemma für betreteTuer_person_in_tuer
set_option maxHeartbeats 800000 in
theorem verschiebePerson_person_in_nach_ort {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) :
    p ∈ personenImOrt (verschiebePerson p von nach b) nach := by
  unfold personenImOrt verschiebePerson setzeBelegung
  simp

-- nach betreten der Tuer ist die person in der tuer
theorem betreteTuer_person_in_tuer {orte : Finset Ort} (offen : TuerSet orte → Bool) (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) :
  p ∈ personenImOrt (aktion_betreteTuer p von t fein offen).1 (tuerAlsOrt t) := by
  simpa [aktion_betreteTuer] using
  verschiebePerson_person_in_nach_ort
    p
    (raumAlsOrt von)
    (tuerAlsOrt t)
    fein

-- Hilfslemma für betreteTuer_person_nicht_mehr_in_von
theorem verschiebePerson_person_nicht_in_von_ort {orte : Finset Ort} (p : Person) (von nach : OrtSet orte) (b : Belegung_safe orte) : von ≠ nach → p ∉ personenImOrt (verschiebePerson p von nach b) von := by
  intro hVonNach
  have hNachVon : nach ≠ von := Ne.symm hVonNach
  unfold personenImOrt verschiebePerson setzeBelegung
  simp [hVonNach]

-- nach betreten der Tuer ist der Ausgangsraum ohne die Person
theorem betreteTuer_person_nicht_mehr_in_von {orte : Finset Ort} (offen : TuerSet orte → Bool) (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) :
    p ∉ personenImOrt (aktion_betreteTuer p von t fein offen).1 (raumAlsOrt von) := by
  have hVonTuer : raumAlsOrt von ≠ tuerAlsOrt t := by
    intro h
    cases h
  simpa [aktion_betreteTuer] using verschiebePerson_person_nicht_in_von_ort p (raumAlsOrt von) (tuerAlsOrt t) fein hVonTuer

-- wird die tuer betreten aendert sich in Grob nichts mehr
theorem betreteTuer_grob_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : betreteTuerSchritt G p von nach t Z Z' → frame_betreteTuer_grob Z.belegungGrob Z'.belegungGrob := by
  intro hschritt
  exact hschritt.2.2.1

-- beim betreten ist die tuer offen
theorem betreteTuer_offen_unveraendert {orte : Finset Ort} (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) :
    (aktion_betreteTuer p von t fein offen).2 = offen := by
  rfl

-- der letzteRaum aendert sich beim betreten der Tuer nicht
theorem betreteTuer_letzterRaum_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : betreteTuerSchritt G p von nach t Z Z' → p ∈ personenImOrt Z.belegungFein (tuerAlsOrt t) ∧ Z'.letzterRaum = Z.letzterRaum := by
  intro hschritt
  rcases hschritt with ⟨hpreFein, hpreBetrete, hGrob, haktion, hpost⟩
  exact hpost.2.2

-- alle anderen personen bleiben unveraendert beim betreten der Tuer
theorem betreteTuer_frame_personen {orte : Finset Ort} (p : Person) (von : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) : raumAlsOrt von ≠ tuerAlsOrt t → frame_betreteTuer_verlasseTuer_personen p fein (aktion_betreteTuer p von t fein (fun _ => true)).1 := by
  intro hVonTuer q hqp o
  by_cases hVon : o = raumAlsOrt von
  · subst o
    simp [
      aktion_betreteTuer,
      verschiebePerson,
      setzeBelegung,
      personenImOrt,
      hVonTuer,
      hqp
    ]
  · by_cases hTuer : o = tuerAlsOrt t
    · subst o
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
theorem person_grob_in_ausgangsraum_nach_betreteTuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z0 Z1 : Zustand orte personen) : p ∈ personenImOrt Z0.belegungGrob (raumAlsOrt von) → betreteTuerSchritt G p von nach t Z0 Z1 → p ∈ personenImOrt Z1.belegungGrob (raumAlsOrt von) := by
  intro hp hbetrete
  rcases hbetrete with ⟨_, _, hGrob, _, _⟩
  rw [hGrob]
  exact hp

-- Beim Verschieben von p bleibt die Zugehoerigkeit einer anderen Person q an jedem Ort unveraendert
theorem verschiebePerson_frame {orte : Finset Ort} (p q : Person) (von nach o : OrtSet orte) (b : Belegung_safe orte) : q ≠ p → von ≠ nach → (q ∈ personenImOrt (verschiebePerson p von nach b) o ↔ q ∈ personenImOrt b o) := by
  intro hqp hVonNach
  have hNachVon : nach ≠ von := by exact Ne.symm hVonNach
  by_cases hVon : o = von
  · subst o
    simp [
      verschiebePerson,
      setzeBelegung,
      personenImOrt,
      hqp,
      hVonNach
    ]
  · by_cases hNach : o = nach
    · subst o
      simp [
        verschiebePerson,
        setzeBelegung,
        personenImOrt,
        hqp
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
theorem person_nicht_in_anderem_ort {orte : Finset Ort} {personen : Finset Person} (b : Belegung_safe orte) (p : Person) (von o : OrtSet orte) : p ∈ personen → p ∈ personenImOrt b von → einePersonGenauEinOrt (personen := personen) b → o ≠ von → p ∉ personenImOrt b o := by
  intro hpBekannt hpVon hEinOrt hNichtGleich hpO
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
theorem relation_nach_betreteTuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : relation_verfeinerung (personen := personen) Z.belegungFein Z.belegungGrob → betreteTuerSchritt G p von nach t Z Z' → relation_verfeinerung (personen := personen) Z'.belegungFein Z'.belegungGrob := by
  intro hrel hbetrete q r hraum hq
  rcases hbetrete with ⟨hPreFein, hPreBetrete, hGrob, hBelegung, hPostBetrete⟩
  by_cases hqp : q.val = p
  · -- q ist die bewegte Person
    have hpFein : p ∈ personenImOrt Z'.belegungFein (raumAlsOrt r) := by
      simpa [hqp] using hq
    by_cases hr : r = von
    · subst r
      have hpNichtInVon : p ∉ personenImOrt Z'.belegungFein (raumAlsOrt von) := by
        rw [hBelegung]
        exact betreteTuer_person_nicht_mehr_in_von Z.offen p von t Z.belegungFein
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
        exact person_nicht_in_anderem_ort (b := Z.belegungFein) (p := p) (von := raumAlsOrt von) (o := raumAlsOrt r) hpBekannt hPreBetrete.1 Z.fein_einePersonGenauEinOrt hRaumNichtVon
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
theorem verlasseTuer_person_in_tuer {orte : Finset Ort} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (letzterRaum : Person → Option Raum) : pre_verlasseTuer G p von nach t fein letzterRaum → p ∈ personenImOrt fein (tuerAlsOrt t) := by
  intro hpre
  exact hpre.1

-- person ist danach im zielraum
theorem verlasseTuer_person_in_nach {orte : Finset Ort} (p : Person) (nach : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) :
    p ∈ personenImOrt (aktion_verlasseTuer p t nach fein offen letzterRaum).1 (raumAlsOrt nach) := by
  unfold aktion_verlasseTuer
  apply verschiebePerson_person_in_nach

-- person ist nach verlassen nicht mehr in tuer
theorem verlasseTuer_person_nicht_mehr_in_tuer {orte : Finset Ort} (p : Person) (nach : RaumSet orte) (t : TuerSet orte) (fein : Belegung_safe orte) (offen : TuerSet orte → Bool) (letzterRaum : Person → Option Raum) :
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
theorem verlasseTuer_frame_letzterRaum {orte : Finset Ort} (p : Person) (nach : RaumSet orte) (letzterRaum letzterRaum' : Person → Option Raum) : letzterRaum' = aktualisiereLetztenRaum letzterRaum p nach → frame_betreteTuer_verlasseTuer_letzterRaum p letzterRaum letzterRaum' := by
  intro hUpdate
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
theorem verfeinerung_nach_betreteTuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : relation_verfeinerung (personen := personen) Z.belegungFein Z.belegungGrob → betreteTuerSchritt G p von nach t Z Z' → relation_verfeinerung (personen := personen) Z'.belegungFein Z'.belegungGrob := by
  intro hrel hschritt
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
        exact betreteTuer_person_nicht_mehr_in_von Z.offen p von t Z.belegungFein
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
        exact person_nicht_in_anderem_ort (b := Z.belegungFein) (p := p) (von := raumAlsOrt von) (o := raumAlsOrt r) hpBekannt hPreBetrete.1 Z.fein_einePersonGenauEinOrt hRaumNichtVon
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

theorem relation_nach_verlasseTuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : relation_verfeinerung (personen := personen) Z.belegungFein Z.belegungGrob → verlasseTuerSchritt G p von nach t Z Z' → relation_verfeinerung (personen := personen) Z'.belegungFein Z'.belegungGrob := by
  intro hrel hverlasse
  /-
    Zuerst wird der Verlassensschritt zerlegt.
    Nach dem Entfalten von aktion_verlasseTuer enthält
    hBelegungFein direkt die Gleichung für die feine Belegung.
  -/
  unfold verlasseTuerSchritt at hverlasse
  dsimp [aktion_verlasseTuer] at hverlasse
  rcases hverlasse with ⟨hPreFein,  hPreVerlasse,  hMoveGrob,  hBelegungFein,  hOffenFein,  hLetzterRaumFein,  hPostVerlasse⟩
  /-
    Jetzt wird der grobe Teilschritt zerlegt.

    Nach dem Entfalten von aktion_moveGrob enthält
    hBelegungGrob direkt die Verschiebung im groben Modell.
  -/
  unfold moveGrobSchrittZustand moveGrobSchritt at hMoveGrob
  dsimp [aktion_moveGrob] at hMoveGrob
  rcases hMoveGrob with ⟨hPreGrob,  hBelegungGrob,  hOffenGrob,  hLetzterRaumGrob,  hPostGrob⟩
  /-
    Ziel der Verfeinerungsrelation:
    Jede Person, die nachher in einem Raum im feinen Modell ist,
    befindet sich auch im groben Modell in diesem Raum.
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
      -- Fall 1a: p befindet sich nachher im Zielraum
      --------------------------------------------------------
      subst r
      have hpGrobNach : p ∈ personenImOrt Z'.belegungGrob (raumAlsOrt nach) := by
        rw [hBelegungGrob]
        apply moveGrob_person_in_nach p von nach G Z.offen Z.belegungGrob
        exact hPreGrob
      simpa [hqp] using hpGrobNach
    · --------------------------------------------------------
      -- Fall 1b: p befindet sich angeblich in einem anderen Raum
      --------------------------------------------------------
      have hRaumNichtNach : raumAlsOrt r ≠ raumAlsOrt nach := by
        intro h
        apply hr
        exact raumAlsOrt_injektiv h
      have hRaumNichtTuer : raumAlsOrt r ≠ tuerAlsOrt t := by
        intro h
        cases h
      /-
        Die Person p ist bekannt, weil sie vor dem Verlassen
        in der Tür enthalten ist.
      -/
      have hpBekannt : p ∈ personen := by
        exact Z.feinNurBekanntePersonen (tuerAlsOrt t) p hPreVerlasse.1
      /-
        Vor dem Verlassen befindet sich p in keinem anderen Ort.
      -/
      have hpNichtInAltemR : p ∉ personenImOrt Z.belegungFein (raumAlsOrt r) := by
        exact person_nicht_in_anderem_ort Z.belegungFein p (tuerAlsOrt t) (raumAlsOrt r) hpBekannt hPreVerlasse.1 Z.fein_einePersonGenauEinOrt hRaumNichtTuer
      /-
        Beim Verlassen wird p nur von der Tür nach nach verschoben.
        Daher kann p im anderen Raum r nicht auftauchen.
      -/
      have hpNichtInR : p ∉ personenImOrt Z'.belegungFein (raumAlsOrt r) := by
        rw [hBelegungFein]
        simpa [aktion_verlasseTuer] using verschiebePerson_person_nicht_in_fremdem_ort p (tuerAlsOrt t) (raumAlsOrt nach) (raumAlsOrt r) Z.belegungFein hRaumNichtTuer hRaumNichtNach hpNichtInAltemR
      exact (hpNichtInR hpFein).elim
  · ------------------------------------------------------------
    -- Fall 2: q ist eine andere Person als p
    ------------------------------------------------------------
    have hTuerNichtNach : tuerAlsOrt t ≠ raumAlsOrt nach := by
      intro h
      cases h
    /-
      Andere Personen bleiben im feinen Modell unverändert.
      Die feine Belegung wird mit hBelegungFein ersetzt.
    -/
    have hFeinFrame : q.val ∈ personenImOrt Z'.belegungFein (raumAlsOrt r) ↔ q.val ∈ personenImOrt Z.belegungFein (raumAlsOrt r) := by
      rw [hBelegungFein]
      simpa [aktion_verlasseTuer] using (verschiebePerson_frame p q.val (tuerAlsOrt t) (raumAlsOrt nach) (raumAlsOrt r) Z.belegungFein hqp hTuerNichtNach)
    /-
      Also war q bereits vor dem Schritt im Raum r.
    -/
    have hqVorher : q.val ∈ personenImOrt Z.belegungFein (raumAlsOrt r) := by
      exact hFeinFrame.mp hqfein
    /-
      Anwendung der ursprünglichen Verfeinerungsrelation.
    -/
    have hqGrobVorher : q.val ∈ personenImOrt Z.belegungGrob (raumAlsOrt r) := by
      exact hrel q r hraum hqVorher
    /-
      Auch im groben Modell wird nur p verschoben.
      Daher bleibt q im Raum r.
    -/
    have hVonNach : raumAlsOrt von ≠ raumAlsOrt nach := by
      intro h
      apply hPreVerlasse.2.2.2.2.2.2.1
      exact raumAlsOrt_injektiv h
    have hGrobFrame : q.val ∈ personenImOrt Z'.belegungGrob (raumAlsOrt r) ↔ q.val ∈ personenImOrt Z.belegungGrob (raumAlsOrt r) := by
      rw [hBelegungGrob]
      exact verschiebePerson_frame p q.val (raumAlsOrt von) (raumAlsOrt nach) (raumAlsOrt r) Z.belegungGrob hqp hVonNach
    exact hGrobFrame.mpr hqGrobVorher

-- grob + fein zusammen machen gleiche
theorem relation_nach_aktion_moveFein {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 : Zustand orte personen) : relation_verfeinerung (personen := personen) Z0.belegungFein Z0.belegungGrob → aktion_moveFein G p r1 r2 t Z0 Z1 Z2 → relation_verfeinerung (personen := personen) Z2.belegungFein Z2.belegungGrob := by
  intro hrel hmove
  rcases hmove with ⟨hbetrete, hverlasse⟩
  have hrel1 : relation_verfeinerung Z1.belegungFein Z1.belegungGrob := relation_nach_betreteTuer G p r1 r2 t Z0 Z1 hrel hbetrete
  exact relation_nach_verlasseTuer G p r1 r2 t Z1 Z2 hrel1 hverlasse

-- grob + fein zusammen machen gleiche + stutter macht keinen unterschied
theorem relation_nach_stutterGrob {orte : Finset Ort} {personen : Finset Person} (Z Z' : Zustand orte personen) : relation_verfeinerung (personen := personen) Z.belegungFein Z.belegungGrob → stutter Z Z' → relation_verfeinerung (personen := personen) Z'.belegungFein Z'.belegungGrob := by
  intro hrel hstutter
  rcases hstutter with ⟨hGrob, hFein, hoff, hletzter⟩
  intro p r hraum hp
  rw [hFein] at hp
  rw [hGrob]
  exact hrel p r hraum hp

theorem relation_nach_aktion_moveFein_stutter {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 Z3 : Zustand orte personen) : relation_verfeinerung (personen := personen) Z0.belegungFein Z0.belegungGrob → aktion_moveFein_stutter G p r1 r2 t Z0 Z1 Z2 Z3 → relation_verfeinerung (personen := personen) Z3.belegungFein Z3.belegungGrob := by
  intro hrel hmove
  rcases hmove with ⟨hbetrete, hstutter, hverlasse⟩
  have hrel1 : relation_verfeinerung Z1.belegungFein Z1.belegungGrob := relation_nach_betreteTuer G p r1 r2 t Z0 Z1 hrel hbetrete
  have hrel2 : relation_verfeinerung Z2.belegungFein Z2.belegungGrob := relation_nach_stutterGrob Z1 Z2 hrel1 hstutter
  exact relation_nach_verlasseTuer
    G p r1 r2 t Z2 Z3 hrel2 hverlasse

-- Person befindet sich nach verlassen im zielraum
theorem verlasseTuerSchritt_person_in_nach {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : verlasseTuerSchritt G p von nach t Z Z' → p ∈ personenImOrt Z'.belegungFein (raumAlsOrt nach) := by
  intro hschritt
  unfold verlasseTuerSchritt at hschritt
  dsimp [aktion_verlasseTuer] at hschritt
  rcases hschritt with ⟨hPreFein, hPreVerlasse, hMoveGrob, hBelegungFein, hOffen, hLetzterRaum, hPost⟩
  rw [hBelegungFein]
  exact verschiebePerson_person_in_nach_ort p (tuerAlsOrt t) (raumAlsOrt nach) Z.belegungFein

-- Person ist nach verlasseTuer nicht mehr in Tuer
theorem verlasseTuerSchritt_person_nicht_mehr_in_tuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : verlasseTuerSchritt G p von nach t Z Z' → p ∉ personenImOrt Z'.belegungFein (tuerAlsOrt t) := by
  intro hschritt
  unfold verlasseTuerSchritt at hschritt
  dsimp [aktion_verlasseTuer] at hschritt
  rcases hschritt with ⟨hPreFein, hPreVerlasse, hMoveGrob, hBelegungFein, hOffen, hLetzterRaum, hPost⟩
  have hTuerNach : tuerAlsOrt t ≠ raumAlsOrt nach := by
    intro h
    cases h
  rw [hBelegungFein]
  exact verschiebePerson_person_nicht_in_von_ort p (tuerAlsOrt t) (raumAlsOrt nach) Z.belegungFein hTuerNach

-- andere personen wechseln nicht
theorem verlasseTuer_frame_personen_fein {orte : Finset Ort} (p : Person) (t : TuerSet orte) (nach : RaumSet orte) (fein : Belegung_safe orte) : tuerAlsOrt t ≠ raumAlsOrt nach → frame_betreteTuer_verlasseTuer_personen p fein (aktion_verlasseTuer p t nach fein (fun _ => true) (fun _ => none)).1 := by
  intro hTuerNach q hqp o
  unfold aktion_verlasseTuer
  exact verschiebePerson_frame p q (tuerAlsOrt t) (raumAlsOrt nach) o fein hqp hTuerNach

-- andere personen wechseln nicht
theorem verlasseTuerSchritt_frame_personen_fein {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : verlasseTuerSchritt G p von nach t Z Z' → frame_betreteTuer_verlasseTuer_personen p Z.belegungFein Z'.belegungFein := by
  intro hschritt
  unfold verlasseTuerSchritt at hschritt
  dsimp [aktion_verlasseTuer] at hschritt
  rcases hschritt with ⟨hPreFein,  hPreVerlasse, hMoveGrob, hBelegungFein, hOffenFein, hLetzterRaumFein, hPostVerlasse⟩
  have hTuerNach : tuerAlsOrt t ≠ raumAlsOrt nach := by
    intro h
    cases h
  intro q hqp o
  rw [hBelegungFein]
  exact verschiebePerson_frame p q (tuerAlsOrt t) (raumAlsOrt nach) o Z.belegungFein hqp hTuerNach

-- tuer bleibt offen
theorem verlasseTuerSchritt_frame_offen {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : verlasseTuerSchritt G p von nach t Z Z' → Z'.offen = Z.offen := by
  intro hschritt
  unfold verlasseTuerSchritt at hschritt
  dsimp [aktion_verlasseTuer] at hschritt
  rcases hschritt with ⟨hPreFein, hPreVerlasse, hMoveGrob, hBelegungFein, hOffen, hLetzterRaum, hPostVerlasse⟩
  simpa using hOffen

theorem verlasseTuer_frame_offen {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : verlasseTuerSchritt G p von nach t Z Z' → frame_betreteTuer_verlasseTuer_offen Z.offen Z'.offen := by
  intro hschritt
  unfold frame_betreteTuer_verlasseTuer_offen
  exact verlasseTuerSchritt_frame_offen G p von nach t Z Z' hschritt

-- alle anderen personen aendern ihren standort nicht
theorem verlasseTuer_frame_personen_grob {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (von nach : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : verlasseTuerSchritt G p von nach t Z Z' → frame_moveGrob_personen p Z.belegungGrob Z'.belegungGrob := by
  intro hschritt
  unfold verlasseTuerSchritt at hschritt
  dsimp [aktion_verlasseTuer] at hschritt
  rcases hschritt with ⟨hPreFein, hPreVerlasse, hMoveGrob, hBelegungFein, hOffenFein, hLetzterRaumFein, hPostVerlasse⟩
  unfold moveGrobSchrittZustand moveGrobSchritt at hMoveGrob
  dsimp [aktion_moveGrob] at hMoveGrob
  rcases hMoveGrob with ⟨hPreGrob, hBelegungGrob, hOffenGrob, hLetzterRaumGrob, hPostGrob⟩
  have hVonNach : von ≠ nach := by
    exact hPreVerlasse.2.2.2.2.2.2.1
  rw [hBelegungGrob]
  exact moveGrob_frame_personen p von nach Z.belegungGrob hVonNach

/-!
## 11. Türöffnung

Eine Tür darf nur von einer Bewohnerin oder einem Bewohner geöffnet werden.

Zusätzlich muss gelten:

* Die Person befindet sich in einem angrenzenden Raum.
* Die Tür ist geschlossen.

Beim Öffnen werden nur die Belegungen nicht verändert. Lediglich der
Öffnungszustand der ausgewählten Tür wird auf `true` gesetzt.
-/

/-!
### 11.1 Vor- und Nachbedingungen
-/

/-- Setzt den Öffnungszustand der Tür `t` auf `true`; alle anderen Türen bleiben unverändert. -/
def oeffneTuer {orte : Finset Ort} (offen : TuerSet orte → Bool) (t : TuerSet orte) : TuerSet orte → Bool :=
  Function.update offen t true

/-- Vorbedingung zum Öffnen einer Tür: `p` ist Bewohner:in, steht im angrenzenden Raum `r`, und die Tür `t` ist geschlossen. -/
def pre_oeffneTuer {orte : Finset Ort} {personen  : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z : Zustand orte personen) : Prop :=
  darfTuerOeffnen p ∧
  p ∈ personenImOrt Z.belegungFein (raumAlsOrt r) ∧
  G.Adj (raumAlsOrt r) (tuerAlsOrt t) ∧
  Z.offen t = false

/-- Führt das Öffnen der Tür `t` aus; Belegungen und `letzterRaum` bleiben unverändert. -/
def aktion_oeffneTuer {orte : Finset Ort} {personen : Finset Person} (t : TuerSet orte) (Z : Zustand orte personen) :
  Belegung_safe orte × Belegung_safe orte × (TuerSet orte → Bool) × (Person → Option Raum) :=
  (Z.belegungGrob, Z.belegungFein, oeffneTuer Z.offen t, Z.letzterRaum)

/-- Nachbedingung zum Öffnen einer Tür: Die Tür `t` ist danach geöffnet. -/
def post_oeffneTuer {orte : Finset Ort} {personen : Finset Person} (t : TuerSet orte) (Z' : Zustand orte personen) : Prop :=
  Z'.offen t = true

/-!
### 11.2 Frame-Bedingungen
-/

/-- Rahmenbedingung: Das grobe Modell bleibt beim Öffnen einer Tür unverändert. -/
def frame_oeffneTuer_grob {orte : Finset Ort} (grob grob' : Belegung_safe orte) : Prop :=
  grob' = grob

/-- Rahmenbedingung: Das feine Modell bleibt beim Öffnen einer Tür unverändert. -/
def frame_oeffneTuer_fein {orte : Finset Ort} (fein fein' : Belegung_safe orte) : Prop :=
  fein' = fein

/-- Rahmenbedingung: `letzterRaum` bleibt beim Öffnen einer Tür unverändert. -/
def frame_oeffneTuer_letzterRaum (letzterRaum letzterRaum' : Person → Option Raum) : Prop :=
  letzterRaum' = letzterRaum

/-- Rahmenbedingung: Die geöffnete Tür `t` bleibt offen, alle anderen Türen behalten ihren Öffnungszustand. -/
def frame_oeffneTuer_offen {orte : Finset Ort} (t : TuerSet orte) (offen offen' : TuerSet orte → Bool) : Prop :=
  offen' t = true ∧
  ∀ m : TuerSet orte, m ≠ t → offen' m = offen m

/-- Übergangsrelation für das Öffnen einer Tür, formuliert über zwei Zustände `Z` und `Z'`. -/
def oeffneTuerSchritt {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : Prop :=
  pre_oeffneTuer G p r t Z ∧
  Z'.belegungGrob = Z.belegungGrob ∧
  Z'.belegungFein = Z.belegungFein ∧
  Z'.offen = oeffneTuer Z.offen t ∧
  Z'.letzterRaum = Z.letzterRaum ∧
  post_oeffneTuer t Z'

/-- Zusammengesetzte Aktion: Tür öffnen, danach eine vollständige feine Bewegung (mit Stutter-Schritt) durch diese Tür. -/
def aktion_grob_fein_oeffne_stutter {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 Z3 Z4 : Zustand orte personen) : Prop :=
  oeffneTuerSchritt G p r1 t Z0 Z1 ∧
  betreteTuerSchritt G p r1 r2 t Z1 Z2 ∧
  stutter Z2 Z3 ∧
  verlasseTuerSchritt G p r1 r2 t Z3 Z4

/-!
### 11.3 Beweise zur Türöffnung
-/

-- bewohner koennen aktion ausfuehren
theorem oeffneTuer_nur_durch_Bewohner {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z : Zustand orte personen) : pre_oeffneTuer G p r t Z → istBewohner p := by
  intro hpre
  exact hpre.1

-- Hilslemma
theorem gast_ist_keine_bewohnerin (g : Person) : istGast g → ¬ istBewohner g := by
  cases g <;>
  simp [istGast, istBewohner] at *

-- die zu oeffnende tuer ist neben dem raum in dem die person ist
theorem oeffneTuer_raum_grenzt_an_tuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z : Zustand orte personen) : pre_oeffneTuer G p r t Z → G.Adj (raumAlsOrt r) (tuerAlsOrt t) := by
  intro hpre
  rcases hpre with ⟨hBewohner, hpRaum, hAdj, hGeschlossen⟩
  exact hAdj

-- gaeste koennen aktion nicht ausfuehren
theorem gast_kann_keine_Tuer_oeffnen {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (g : Person) (r : RaumSet orte) (t : TuerSet orte) (Z : Zustand orte personen) : istGast g → ¬ pre_oeffneTuer G g r t Z := by
  intro hgast hpre
  have hbewohner : istBewohner g := by
    exact hpre.1
  exact gast_ist_keine_bewohnerin g hgast hbewohner

-- nach oeffen tuer ist die tuer auch offen
theorem oeffneTuer_tuer_ist_offen {orte : Finset Ort} {personen : Finset Person} (t : TuerSet orte) (Z : Zustand orte personen) :
    (oeffneTuer Z.offen t) t = true := by
  simp [oeffneTuer]

-- vor oeffnen war die tuer geschlossen
theorem oeffneTuer_vorher_geschlossen {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z : Zustand orte personen) : pre_oeffneTuer G p r t Z → Z.offen t = false := by
  intro hpre
  exact hpre.2.2.2

-- nach oeffen tuer ist die tuer auch offen
theorem oeffneTuerSchritt_tuer_ist_offen {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : oeffneTuerSchritt G p r t Z Z' → Z'.offen t = true := by
  intro hschritt
  rcases hschritt with ⟨hpre, hGrob, hFein, hOffen, hLetzterRaum, hpost⟩
  rw [hOffen]
  simp [oeffneTuer]

-- belegung bleibt unveraendert
theorem oeffneTuerSchritt_grob_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : oeffneTuerSchritt G p r t Z Z' → frame_oeffneTuer_grob Z.belegungGrob Z'.belegungGrob := by
  intro hschritt
  exact hschritt.2.1

-- belegung bleibt unveraendert
theorem oeffneTuerSchritt_fein_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : oeffneTuerSchritt G p r t Z Z' → frame_oeffneTuer_fein Z.belegungFein Z'.belegungFein := by
  intro hschritt
  exact hschritt.2.2.1

-- der letzteRaum aendert sich nicht beim aufschließen der tuer
theorem oeffneTuerSchritt_letzterRaum_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : oeffneTuerSchritt G p r t Z Z' → frame_oeffneTuer_letzterRaum Z.letzterRaum Z'.letzterRaum := by
  intro hschritt
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
theorem oeffneTuerSchritt_andere_tueren_unveraendert {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t m : TuerSet orte) (Z Z' : Zustand orte personen) : m ≠ t → oeffneTuerSchritt G p r t Z Z' → Z'.offen m = Z.offen m := by
  intro hne hschritt
  rcases hschritt with ⟨hpre, hGrob, hFein, hOffen, hLetzterRaum, hpost⟩
  rw [hOffen]
  have hframe : frame_oeffneTuer_offen t Z.offen (oeffneTuer Z.offen t) := oeffneTuer_frame_offen t Z
  exact hframe.2 m hne

-- verfeinerung + relation zusammen

-- Hilfslemma
theorem relation_nach_oeffneTuer {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r : RaumSet orte) (t : TuerSet orte) (Z Z' : Zustand orte personen) : relation_verfeinerung (personen := personen) Z.belegungFein Z.belegungGrob → oeffneTuerSchritt G p r t Z Z' → relation_verfeinerung (personen := personen)   Z'.belegungFein Z'.belegungGrob := by
  intro hrel hschritt q s hsraum hq
  have hGrob : Z'.belegungGrob = Z.belegungGrob := by
    exact hschritt.2.1
  have hFein : Z'.belegungFein = Z.belegungFein := by
    exact hschritt.2.2.1
  rw [hFein] at hq
  rw [hGrob]
  exact hrel q s hsraum hq

theorem relation_nach_aktion_grob_fein_oeffne_stutter {orte : Finset Ort} {personen : Finset Person} (G : BipartiteOrtGraph orte) (p : Person) (r1 r2 : RaumSet orte) (t : TuerSet orte) (Z0 Z1 Z2 Z3 Z4 : Zustand orte personen) : relation_verfeinerung (personen := personen) Z0.belegungFein Z0.belegungGrob → aktion_grob_fein_oeffne_stutter G p r1 r2 t Z0 Z1 Z2 Z3 Z4 → relation_verfeinerung (personen := personen) Z4.belegungFein Z4.belegungGrob := by
  intro hrel haktion
  rcases haktion with ⟨hOeffne, hBetrete, hStutter, hVerlasse⟩
  -- Nach dem Öffnen bleiben grob und fein unverändert.
  have hrel1 : relation_verfeinerung (personen := personen) Z1.belegungFein Z1.belegungGrob := relation_nach_oeffneTuer G p r1 t Z0 Z1 hrel hOeffne
  -- Beim Betreten wird nur das feine Modell verändert.
  have hrel2 : relation_verfeinerung (personen := personen) Z2.belegungFein Z2.belegungGrob := relation_nach_betreteTuer G p r1 r2 t Z1 Z2 hrel1 hBetrete
  -- Der Stutter-Schritt verändert weder grob noch fein.
  have hrel3 : relation_verfeinerung (personen := personen) Z3.belegungFein Z3.belegungGrob := relation_nach_stutterGrob Z2 Z3 hrel2 hStutter
  -- Beim Verlassen werden fein und grob konsistent weiterbewegt.
  exact relation_nach_verlasseTuer G p r1 r2 t Z3 Z4 hrel3 hVerlasse

/-!
## 12. Beispielgebäude

Das Beispielgebäude besteht aus:

* drei Räumen:
  * Zimmer 1,
  * Zimmer 2,
  * Garten;
* zwei Türen:
  * Tür 1 verbindet Zimmer 1 und Zimmer 2,
  * Tür 2 verbindet Zimmer 2 und den Garten.

Die Ortsmenge enthält genau diese fünf Orte.
-/

abbrev room1 := Ort.Raum (Raum.Zimmer 1)
abbrev room2 := Ort.Raum (Raum.Zimmer 2)
abbrev room3 := Ort.Raum Raum.Garten

abbrev door1 : Ort := Ort.Tuer (Tuer.tuer 1)
abbrev door2 : Ort := Ort.Tuer (Tuer.tuer 2)

/-- Alle Orte des Beispielgebäudes. -/
abbrev meineOrte : Finset Ort :=
  ∅ |> insert room1
    |> insert room2
    |> insert room3
    |> insert door1
    |> insert door2

/-- Die Nachbarschaftslisten des Beispielgebäudes. -/
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

/-!
## 13. Offene Beweise und TODOs

* In `myBipartiteGraph.gartenHatGenauEinenNachbarn` ist der letzte Fall (die
  Eindeutigkeit der an den Garten angrenzenden Tür) noch nicht bewiesen
  (`sorry`).
* Es fehlt noch ein konkretes Beispiel für einen initialen `Zustand` des
  Beispielgebäudes (z. B. alle Personen im Garten, alle Türen geschlossen).
-/

/-
  Was insgesamt bewiesen wird:

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

  Uns wurde beigebracht dass wir mit Axiomen/Invarianten und -> arbeiten. Wir mussten dass für Lean etwas anpassen, da wir mit komplexen Objekten nicht einfach so wie in vorherigen Beispielen Axiome/Invarianten einfach so definieren konnten. Wir sind deshabl so vorgegangen:
  - Struktur beweisen (Zustand, Graph) sodass man nur korrekte Sachen erstellen kann
  - die Aktionen beweisen die man mit der Strukur vorgehen kann: defs für die Zustandsbeschreibung (Das ist eine Beschreibung eines Zustands, in dem mehrere Bedingungen gleichzeitig gelten. daher nutzen wir hier auch ∧)
  - Beweise über → führen
-/
