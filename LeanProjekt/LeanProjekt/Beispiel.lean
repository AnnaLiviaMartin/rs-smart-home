import LeanProjekt.Main

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

abbrev meineRaeume : Finset Ort :=
  ∅ |> insert room1
    |> insert room2
    |> insert room3

abbrev meineTueren : Finset Ort :=
  ∅ |> insert door1
    |> insert door2

/-- Die Nachbarschaftslisten des Beispielgebäudes. -/
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
        | (exfalso; revert hAdj; simp [myAdjRelBool, OrteSindBenachbart, meineKanten])

-- Initialer Zustand als Beispiel für meineOrte
def person1 : Person := Person.Bewohner 1
def person2 : Person := Person.Gast 2
def person3 : Person := Person.Gast 3

def meinePersonen : Finset Person := {person1, person2, person3}

def initialBelegung : Belegung_safe meineOrte :=
  ∅ |> Finmap.insert ⟨room1, by simp [meineOrte]⟩ ({person1, person2} : Finset Person)
    |> Finmap.insert ⟨room2, by simp [meineOrte]⟩ ({person3} : Finset Person)

def initialOffen : TuerSet meineOrte → Bool
  | ⟨Tuer.tuer 1, _⟩ => false
  | ⟨Tuer.tuer 2, _⟩ => false

-- Hilfslemma
lemma initialBelegung_personen (o : OrtSet meineOrte) :
    personenImOrt initialBelegung o ⊆ meinePersonen := by
  classical
  fin_cases o <;>
    simp [
      personenImOrt,
      initialBelegung,
      meinePersonen,
      meineOrte,
      room1,
      room2,
      room3,
      door1,
      door2
    ] <;>
    native_decide

def initialZustand : Zustand meineOrte meinePersonen where
  belegungGrob := initialBelegung
  belegungFein := initialBelegung
  offen := initialOffen

  grob_einePersonGenauEinOrt := by
    rintro ⟨p, hp⟩
    simp [meinePersonen] at hp
    rcases hp with rfl | rfl | rfl <;>
      native_decide +revert

  fein_einePersonGenauEinOrt := by
    rintro ⟨p, hp⟩
    simp [meinePersonen] at hp
    rcases hp with rfl | rfl | rfl <;>
      native_decide +revert

  tuerOffenWennPersonEnthalten := by
    intro t hBelegt
    let r1 : OrtSet meineOrte :=  ⟨room1, by simp [meineOrte]⟩
    let r2 : OrtSet meineOrte :=  ⟨room2, by simp [meineOrte]⟩
    have ht1 : tuerAlsOrt t ≠ r1 := by
      intro h
      have hVal : (tuerAlsOrt t).val = r1.val := congrArg Subtype.val h
      simp [tuerAlsOrt, r1, room1] at hVal
    have ht2 : tuerAlsOrt t ≠ r2 := by
      intro h
      have hVal : (tuerAlsOrt t).val = r2.val := congrArg Subtype.val h
      simp [tuerAlsOrt, r2, room2] at hVal
    have hLeer :
        personenImOrt initialBelegung (tuerAlsOrt t) = ∅ := by
      simp [
        personenImOrt,
        initialBelegung,
        r1,
        r2,
        ht1,
        ht2
      ]
    exfalso
    apply hBelegt
    exact hLeer

  verfeinerung := by
    intro p r _ hpFein
    exact hpFein

  grobeTuerenSindImmerLeer := by
    intro t
    simp [
      personenImOrt,
      initialBelegung,
      tuerAlsOrt
    ]

  grobNurBekanntePersonen := by
    intro o p hp
    have hTeilmenge :
        personenImOrt initialBelegung o ⊆ meinePersonen := initialBelegung_personen o
    exact hTeilmenge hp

  feinNurBekanntePersonen := by
    intro o p hp
    have hTeilmenge :
        personenImOrt initialBelegung o ⊆ meinePersonen := initialBelegung_personen o
    exact hTeilmenge hp
