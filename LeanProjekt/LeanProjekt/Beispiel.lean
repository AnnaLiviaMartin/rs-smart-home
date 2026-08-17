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
        | (exfalso; revert hAdj; simp [myAdjRelBool, OrteSindBenachbart, myEdges])

-- Initialer Zustand als Beispiel für meineOrte/-!

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

def initialOffen : TuerSet meineOrte → Bool :=
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
    rcases hp with rfl | rfl | rfl <;>
      native_decide +revert

  fein_einePersonGenauEinOrt := by
    rintro ⟨p, hp⟩
    simp [meinePersonen] at hp
    rcases hp with rfl | rfl | rfl <;>
      native_decide +revert

  tuerOffenWennPersonEnthalten := by
    intro t hBelegt
    simp [initialBelegung] at hBelegt

  verfeinerung := by
    intro p r _ hpFein
    exact hpFein

  tuerVerfeinerung := by
    intro p t hpInTuer
    simp [initialBelegung] at hpInTuer

  grobeTuerenSindImmerLeer := by
    intro t
    simp [initialBelegung]

  grobNurBekanntePersonen := by
    intro o p hp
    simp [initialBelegung, meinePersonen] at hp ⊢
    exact hp

  feinNurBekanntePersonen := by
    intro o p hp
    simp [initialBelegung, meinePersonen] at hp ⊢
    exact hp
