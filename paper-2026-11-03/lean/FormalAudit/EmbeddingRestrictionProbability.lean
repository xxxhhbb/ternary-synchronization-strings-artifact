import Mathlib
import FormalAudit.VariableIndependence

namespace TernarySyncAudit

open Finset

/-- Uniform mass is unchanged after adjoining a completely unrestricted
finite coordinate factor. -/
theorem uniformFinsetMass_product_univ
    {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Nonempty I] [Nonempty O]
    (allowed : Finset I) :
    uniformFinsetMass
        (allowed ×ˢ (Finset.univ : Finset O)) =
      uniformFinsetMass allowed := by
  unfold uniformFinsetMass
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_prod]
  have iPositive : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have oPositive : (0 : ℝ) < Fintype.card O := by
    exact_mod_cast Fintype.card_pos
  push_cast
  field_simp

/-- Equivalence from the domain of an embedding to its set-theoretic range. -/
noncomputable def embeddingRangeEquiv
    {D C : Type*} (embedding : D ↪ C) :
    D ≃ Set.range embedding :=
  Equiv.ofInjective embedding embedding.injective

@[simp] theorem embeddingRangeEquiv_apply
    {D C : Type*} (embedding : D ↪ C) (coordinate : D) :
    (embeddingRangeEquiv embedding coordinate).1 = embedding coordinate := by
  rfl

@[simp] theorem embeddingRangeEquiv_symm_apply
    {D C : Type*} (embedding : D ↪ C) (coordinate : D) :
    (embeddingRangeEquiv embedding).symm
        ⟨embedding coordinate, Set.mem_range_self coordinate⟩ = coordinate := by
  exact Equiv.ofInjective_symm_apply embedding.injective coordinate

/-- Split a global assignment into its values on an embedded coordinate set
and its values off the range. -/
noncomputable def embeddingSplitEquiv
    {D C A : Type*} (embedding : D ↪ C) :
    ((D → A) × ({coordinate : C // coordinate ∉ Set.range embedding} → A)) ≃
      (C → A) := by
  classical
  exact
    { toFun := fun pair coordinate =>
        if inside : coordinate ∈ Set.range embedding then
          pair.1 ((embeddingRangeEquiv embedding).symm ⟨coordinate, inside⟩)
        else
          pair.2 ⟨coordinate, inside⟩
      invFun := fun assignment =>
        (fun coordinate => assignment (embedding coordinate),
          fun coordinate => assignment coordinate.1)
      left_inv := by
        intro pair
        apply Prod.ext
        · funext coordinate
          simp [embeddingRangeEquiv]
        · funext coordinate
          simp [coordinate.2]
      right_inv := by
        intro assignment
        funext coordinate
        by_cases inside : coordinate ∈ Set.range embedding
        · rcases inside with ⟨source, rfl⟩
          simp [embeddingRangeEquiv]
        · simp [inside] }

@[simp] theorem embeddingSplitEquiv_apply_embedded
    {D C A : Type*} (embedding : D ↪ C)
    (pair : (D → A) ×
      ({coordinate : C // coordinate ∉ Set.range embedding} → A))
    (coordinate : D) :
    embeddingSplitEquiv embedding pair (embedding coordinate) =
      pair.1 coordinate := by
  simp [embeddingSplitEquiv, embeddingRangeEquiv]

/-- Global assignments whose restriction along an embedding lies in a given
finite local pattern family. -/
noncomputable def restrictionPatternEvent
    {D C A : Type*} [Fintype D] [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A]
    (embedding : D ↪ C) (allowed : Finset (D → A)) :
    Finset (C → A) :=
  Finset.univ.filter fun assignment =>
    (fun coordinate => assignment (embedding coordinate)) ∈ allowed

/-- Restricting a uniform finite product assignment along any embedding is
again uniform.  Hence the preimage of a local pattern family has exactly the
same mass as that family. -/
theorem uniformFinsetMass_restrictionPatternEvent
    {D C A : Type*} [Fintype D] [DecidableEq D]
    [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (embedding : D ↪ C) (allowed : Finset (D → A)) :
    uniformFinsetMass (restrictionPatternEvent embedding allowed) =
      uniformFinsetMass allowed := by
  classical
  let split := embeddingSplitEquiv (A := A) embedding
  have preimageMass := uniformFinsetMass_preimage_equiv split
    (restrictionPatternEvent embedding allowed)
  have preimageEquality :
      Finset.univ.filter (fun pair =>
        split pair ∈ restrictionPatternEvent embedding allowed) =
        allowed ×ˢ (Finset.univ : Finset
          ({coordinate : C // coordinate ∉ Set.range embedding} → A)) := by
    ext pair
    simp [restrictionPatternEvent, split,
      embeddingSplitEquiv_apply_embedded]
  rw [preimageEquality,
    uniformFinsetMass_product_univ] at preimageMass
  exact preimageMass.symm

end TernarySyncAudit
