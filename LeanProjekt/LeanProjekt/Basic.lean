/-
  Smart Home – Allergröbstes Modell

  Modelliert werden nur:
  - Räume
  - Nachbarschaft
  - Symmetrie
  - Keine Selbstnachbarschaft
  - alle Räume liegen in einem Gebäude
-/
import Mathlib

structure Raum where
  my_id: Nat
  nachbar_ids: Finset Nat

axiom keineSelbstNachbarschaft : ∀ r : Raum, ¬ (r.my_id ∈ r.nachbar_ids)

axiom symmetrie : ∀ r₁ r₂ : Raum, r₁.my_id ∈ r₂.nachbar_ids ∧ r₂.my_id ∈ r₁.nachbar_ids
