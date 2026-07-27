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

-- Gebäudeplan, der bipartite ist, nachbar-symmetrie gegeben, damit auch tuerVerbindetZweiRaeume, alleNachbarnSindSymmerisch inkl. Axiome
structure BipartiteOrtGraph (orte : Finset Ort) extends SimpleGraph (OrtSet orte) where
  bipartite : adjIsBipartite Adj -- das ist das "geerbte" Adj aus der Def. von SimpeGraph
  --genauEinGarten (orte : Finset Ort) := ∃! g : Ort, g = Ort.Raum Raum.Garten ∧ g ∈ orte
  --gartenExistiert (orte : Finset Ort) := Ort.Raum Raum.Garten ∈ orte
  genauEinGarten : Ort.Raum Raum.Garten ∈ orte
  tuerEindeutig := ∀ t1 t2 : Tuer, t1 ≠ t2 →
    (match t1,t2 with | Tuer.tuer a1, Tuer.tuer a2 => a1 ≠ a2) -- jedeTuerHatEigenesAuthentifizierungsGeraet

/-
  Objekte, die sich verändern können: Zustand ist die momentane Ausprägung
-/
def einePersonGenauEinOrt {orte : Finset Ort} {personen : Finset Person} (b : Belegung_safe orte) : Prop :=
  ∀ p : PersonSet personen, (Finset.univ.filter (fun o => p.val ∈ (b.lookup o).getD ∅)).card = 1

structure Zustand (orte : Finset Ort) (personen : Finset Person) where
  belegungGrob : Belegung_safe orte
  belegungFein : Belegung_safe orte -- einePersonInGenauEinemOrt
  offen : OrtSet orte → Bool -- jede Tür hat individuell ein "offen"
  letzterRaum : Person → Option Raum -- 1 oder kein Raum
  grob_gueltig : einePersonGenauEinOrt (personen := personen) belegungGrob
  fein_gueltig : einePersonGenauEinOrt (personen := personen) belegungFein
  tuerImmerOffenWennPersonEnthalten :
    ∀ o : OrtSet orte,
      match o.val with
      | Ort.Tuer _ =>
          (belegungFein.lookup o).getD ∅ ≠ ∅ →
          offen o = true
      | Ort.Raum _ => True -- Wenn Personen in der Tür sind, ist sie offen. Wenn keine Personen drin sind, darf sie offen oder geschlossen sein.

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

/-
  Invarianten: was trotz Veränderung gleich bleibt

  pre_   = Vorbedingung vor der Aktion
  post_  = Bedingung, die nach der Aktion gilt
  frame_ = Teil des Zustands bleibt unverändert
  inv_   = Eigenschaft, die in jedem gültigen Zustand gilt -> liegen teils auch in den Graphen-Strukturen direkt als Eigenschaft drin
-/
-- inv_genauEinGarten
-- inv_einePersonGenauEinOrtGrob
-- inv_einePersonGenauEinOrtFein
-- inv_tuerImmerOffenWennPersonEnthalten
-- inv_personNurDurchOffeneTuer
-- inv_personNieInTuerGrob
-- inv_feinImpliziertGrob
-- inv_ortHatMindestensEinenNachbarn
-- inv_gartenHatGenauEinenNachbarn
-- inv_grobBelegungEnthaeltNurBekanntePersonen
-- inv_feinBelegungEnthaeltNurBekanntePersonen

-- post_init_allePersonenImGarten
-- post_init_letzterRaumIstGarten
-- post_init_alleTuerenGeschlossen

-- pre_moveGrob_tuerIstOffen
-- pre_moveGrob_raeumeSindBenachbart
-- pre_moveGrob_personImQuellraumGrob
-- pre_moveGrob_quellraumIstRaum
-- pre_moveGrob_zielraumIstRaum
-- pre_moveGrob_quellraumUngleichZielraum
-- pre_moveGrob_tuerVerbindetQuellraumUndZielraum
-- post_moveGrob_personImZielraum
-- post_moveGrob_personAusQuellraumEntfernt
-- post_moveGrob_grobBelegungAktualisiert
-- post_moveGrob_keineTeleportationGrob
-- post_moveGrob_personNieInTuerGrob
-- post_moveGrob_einePersonGenauEinOrtGrob
-- post_moveGrob_einePersonGenauEinOrtFein
-- post_moveGrob_personNichtInTuerGrob
-- frame_moveGrob_alleAnderenGrobBelegungenUnveraendert
-- frame_moveGrob_feinBelegungUnveraendert
-- frame_moveGrob_offenUnveraendert
-- frame_moveGrob_letzterRaumUnveraendert

-- pre_betreteTuer_personImQuellraum
-- pre_betreteTuer_tuerIstNachbar
-- pre_betreteTuer_tuerIstOffen
-- pre_betreteTuer_quellortIstRaum
-- pre_betreteTuer_tuerIstTuer
-- post_betreteTuer_personInTuer
-- post_betreteTuer_personAusRaumEntfernt
-- post_betreteTuer_letzterRaumAktualisiert
-- post_betreteTuer_keineTeleportationFein
-- frame_betreteTuer_alleAnderenFeinenBelegungenUnveraendert

-- pre_verlasseTuer_personInTuer
-- pre_verlasseTuer_tuerIstTuer
-- pre_verlasseTuer_zielraumIstRaum
-- pre_verlasseTuer_tuerVerbindetZielraum
-- pre_verlasseTuer_zielraumIstNachbar
-- pre_verlasseTuer_zielraumUngleichLetzterRaum
-- post_verlasseTuer_personImZielraum
-- post_verlasseTuer_personAusTuerEntfernt
-- post_verlasseTuer_keineTeleportationFein
-- frame_verlasseTuer_grobBelegungVeraendert
-- frame_verlasseTuer_alleAnderenFeinenBelegungenUnveraendert

-- pre_move2_raeumeSindDurchTuerVerbunden
-- pre_move2_betreteOderVerlasseTuer
-- post_move2_verlasseTuerGrobBewegt
-- post_move2_keineTeleportationFein
-- post_move2_keineTeleportationGrob
-- post_move2_feinImpliziertGrob
-- post_move2_betreteTuerFeinAktualisiert
-- post_move2_verlasseTuerFeinAktualisiert
-- post_move2_letzterRaumKorrektBehandelt
-- frame_move2_grobBelegungVeraendert
-- frame_move2_offenUnveraendert
-- frame_move2_betreteTuerGrobUnveraendert

-- pre_anmelden_authentifizierungGueltig
-- pre_anmelden_authentifizierungsGeraetGehoertZurTuer
-- pre_anmelden_personImRaum
-- pre_anmelden_personIstBewohner
-- pre_anmelden_tuerIstNachbar
-- post_anmelden_tuerGeoeffnet
-- post_anmelden_authentifizierungGespeichert
-- frame_anmelden_belegungGrobUnveraendert
-- frame_anmelden_belegungFeinUnveraendert
-- frame_anmelden_letzterRaumUnveraendert
-- frame_anmelden_andereTuerenUnveraendert

-- pre_anmeldungFehlgeschlagen_personImRaum
-- pre_anmeldungFehlgeschlagen_tuerIstNachbar
-- frame_anmeldungFehlgeschlagen_tuerUnveraendert
-- frame_anmeldungFehlgeschlagen_belegungGrobUnveraendert
-- frame_anmeldungFehlgeschlagen_belegungFeinUnveraendert
-- frame_anmeldungFehlgeschlagen_offenUnveraendert
-- frame_anmeldungFehlgeschlagen_letzterRaumUnveraendert
-- frame_anmeldungFehlgeschlagen_authentifizierungUnveraendert

-- pre_tuerFaelltZu_tuerIstOffen
-- pre_tuerFaelltZu_tuerIstLeer
-- post_tuerFaelltZu_tuerGeschlossen
-- frame_tuerFaelltZu_andereTuerenUnveraendert
-- frame_tuerFaelltZu_belegungUnveraendert
-- frame_tuerFaelltZu_letzterRaumUnveraendert
-- frame_tuerFaelltZu_authentifizierungUnveraendert

-- pre_move3_anmelden
-- pre_move3_anmeldungFehlgeschlagen
-- pre_move3_move2
-- pre_move3_tuerFaelltZu
-- post_move3_anmelden_tuerGeoeffnet
-- frame_move3_anmelden_belegungGrobUnveraendert
-- frame_move3_anmelden_belegungFeinUnveraendert
-- frame_move3_anmelden_letzterRaumUnveraendert
-- frame_move3_anmeldungFehlgeschlagen_tuerUnveraendert
-- frame_move3_anmeldungFehlgeschlagen_belegungGrobUnveraendert
-- frame_move3_anmeldungFehlgeschlagen_belegungFeinUnveraendert
-- frame_move3_anmeldungFehlgeschlagen_letzterRaumUnveraendert
-- frame_move3_anmeldungFehlgeschlagen_authentifizierungUnveraendert
-- post_move3_tuerFaelltZu_tuerGeschlossen
-- frame_move3_tuerFaelltZu_andereTuerenUnveraendert
-- frame_move3_tuerFaelltZu_belegungGrobUnveraendert
-- frame_move3_tuerFaelltZu_belegungFeinUnveraendert
-- frame_move3_tuerFaelltZu_letzterRaumUnveraendert
-- post_move3_einePersonGenauEinOrtGrob
-- post_move3_einePersonGenauEinOrtFein
-- post_move3_tuerImmerOffenWennPersonEnthalten
-- post_move3_personNurDurchOffeneTuer
-- post_move3_personNieInTuerGrob
-- post_move3_feinImpliziertGrob
-- post_move3_keineTeleportationGrob
-- post_move3_keineTeleportationFein

/-
  Beweise
-/

-- beweisen: personKannNurDurchOffeneTürGehen

/-
  Beispiel
-/

-- Graph
abbrev room1 := Ort.Raum (Raum.Zimmer 1)
abbrev room2 := Ort.Raum (Raum.Zimmer 2)
abbrev room3 := Ort.Raum Raum.Garten

abbrev door1 : Ort := Ort.Tuer (Tuer.tuer (Authentifizierung.auth 1))

abbrev door2 : Ort := Ort.Tuer (Tuer.tuer (Authentifizierung.auth 2))

abbrev myOrts : Finset Ort :=
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

def myGraph : GebaeudePlan myOrts where
  Adj u v := myAdjRelBool u.val v.val
  symm := by constructor; decide
  loopless := by constructor; decide

def myBipartiteGraph : BipartiteOrtGraph myOrts where
  Adj u v := myAdjRelBool u.val v.val
  symm := by constructor; decide
  loopless := by constructor; decide
  bipartite := by
    unfold adjIsBipartite
    decide
  genauEinGarten := by simp [myOrts]

-- Person
abbrev person1 := Person.Bewohner 1
abbrev person2 := Person.Gast 1
abbrev person3 := Person.Gast 2

abbrev myPersonen : Finset Person :=
  ∅ |> insert person1
  |> insert person2
  |> insert person3

abbrev initBelegung : Belegung_safe myOrts :=
  ∅ |> Finmap.insert ⟨room1, by decide⟩
      (∅ |> insert person1
        |> insert person2)
    |> Finmap.insert ⟨room2, by decide⟩ ∅
    |> Finmap.insert ⟨room3, by decide⟩ ∅
    |> Finmap.insert ⟨door1, by decide⟩ ∅
    |> Finmap.insert ⟨door2, by decide⟩ (∅ |> insert person3)

instance {s : Finset Ort} : Fintype (OrtSet s) :=
  Fintype.ofFinset s (by
    intro x
    simp)

instance {s : Finset Ort} : DecidableEq (OrtSet s) :=
  Subtype.instDecidableEq

def initZustand : Zustand myOrts myPersonen where
  belegungGrob := initBelegung
  belegungFein := initBelegung
  offen := fun o =>
    match o.val with
    | Ort.Tuer (Tuer.tuer (Authentifizierung.auth 1)) => false
    | Ort.Tuer (Tuer.tuer (Authentifizierung.auth 2)) => true
    | _ => false
  letzterRaum := fun _ => Raum.Garten
  grob_gueltig := by
    unfold einePersonGenauEinOrt
    decide
  fein_gueltig := by
    unfold einePersonGenauEinOrt
    decide
  tuerImmerOffenWennPersonEnthalten := by
    rintro ⟨v, hv⟩
    cases v with
    | Raum r => trivial
    | Tuer t =>
      intro hpersonen
      have ht :
          t = Tuer.tuer (Authentifizierung.auth 1) ∨
          t = Tuer.tuer (Authentifizierung.auth 2) := by
        simpa [myOrts, door1, door2, room1, room2, room3, or_comm] using hv
      rcases ht with hdoor1 | hdoor2
      · subst t
        simp [initBelegung] at hpersonen
      · subst t
        simp [initBelegung]