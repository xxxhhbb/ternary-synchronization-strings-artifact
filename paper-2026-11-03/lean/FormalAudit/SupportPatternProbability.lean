import Mathlib
import FormalAudit.VariableIndependence

namespace TernarySyncAudit

open Finset

/-- Allowed assignments on an event's declared support, evaluated using an
arbitrary fixed assignment outside that support. -/
noncomputable def supportPatterns
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (event : Finset (V → A)) (support : Finset V) :
    Finset (InsideCoordinate support → A) := by
  classical
  let outsideDefault : OutsideCoordinate support → A := fun _ =>
    Classical.choice inferInstance
  exact Finset.univ.filter fun inside =>
    assembleCoordinates support inside outsideDefault ∈ event

theorem assemble_mem_iff_supportPatterns
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (event : Finset (V → A)) (support : Finset V)
    (eventDepends : DependsOn event support)
    (inside : InsideCoordinate support → A)
    (outside : OutsideCoordinate support → A) :
    assembleCoordinates support inside outside ∈ event ↔
      inside ∈ supportPatterns event support := by
  classical
  let outsideDefault : OutsideCoordinate support → A := fun _ =>
    Classical.choice inferInstance
  have invariant := eventDepends
    (assembleCoordinates support inside outside)
    (assembleCoordinates support inside outsideDefault) (by
      intro coordinate coordinateIn
      simp [assembleCoordinates, coordinateIn])
  simpa [supportPatterns, outsideDefault] using invariant

/-- Under the coordinate-splitting equivalence, a support event is exactly
its set of allowed support patterns times the unrestricted complement. -/
theorem support_event_preimage_eq_product
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (event : Finset (V → A)) (support : Finset V)
    (eventDepends : DependsOn event support) :
    Finset.univ.filter (fun pair =>
      coordinateSplitEquiv (A := A) support pair ∈ event) =
      supportPatterns event support ×ˢ
        (Finset.univ : Finset (OutsideCoordinate support → A)) := by
  classical
  ext pair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product]
  change assembleCoordinates support pair.1 pair.2 ∈ event ↔
    pair.1 ∈ supportPatterns event support ∧ True
  rw [and_true]
  exact assemble_mem_iff_supportPatterns event support eventDepends pair.1 pair.2

/-- Uniform event mass is exactly the uniform mass of its allowed patterns on
the declared support. -/
theorem uniformFinsetMass_eq_supportPatterns
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (event : Finset (V → A)) (support : Finset V)
    (eventDepends : DependsOn event support) :
    uniformFinsetMass event = uniformFinsetMass (supportPatterns event support) := by
  classical
  let split := coordinateSplitEquiv (A := A) support
  have preimageMass := uniformFinsetMass_preimage_equiv split event
  rw [support_event_preimage_eq_product event support eventDepends] at preimageMass
  unfold uniformFinsetMass at preimageMass ⊢
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fun] at preimageMass ⊢
  have insidePositive :
      (0 : ℝ) < Fintype.card A ^ Fintype.card (InsideCoordinate support) := by
    exact_mod_cast pow_pos Fintype.card_pos _
  have totalPositive :
      (0 : ℝ) < Fintype.card A ^ Fintype.card V := by
    exact_mod_cast pow_pos Fintype.card_pos _
  have outsidePositive :
      (0 : ℝ) < Fintype.card A ^ Fintype.card (OutsideCoordinate support) := by
    exact_mod_cast pow_pos Fintype.card_pos _
  have outsideNe :
      (Fintype.card A : ℝ) ^ Fintype.card (OutsideCoordinate support) ≠ 0 :=
    ne_of_gt outsidePositive
  have insideNe :
      (Fintype.card A : ℝ) ^ Fintype.card (InsideCoordinate support) ≠ 0 :=
    ne_of_gt insidePositive
  have totalNe :
      (Fintype.card A : ℝ) ^ Fintype.card V ≠ 0 :=
    ne_of_gt totalPositive
  push_cast at preimageMass ⊢
  field_simp [outsideNe] at preimageMass
  field_simp [insideNe, totalNe]
  simpa [mul_comm] using preimageMass.symm

end TernarySyncAudit
