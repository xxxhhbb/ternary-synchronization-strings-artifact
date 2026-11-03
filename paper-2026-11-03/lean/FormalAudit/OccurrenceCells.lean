import Mathlib
import FormalAudit.MoserTardosProcess

namespace TernarySyncAudit

/-- The random-table cell read by one coordinate of one chronological log
occurrence.  Its row index is exactly the number of earlier resamplings whose
supports contain that coordinate. -/
def occurrenceCell
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (initial : V → ℕ) (log : List E) :
    (Σ index : Fin log.length,
      {coordinate : V // coordinate ∈ support (log.get index)}) → V × ℕ :=
  fun occurrence =>
    (occurrence.2.1,
      initial occurrence.2.1 +
        supportOccurrenceCount support occurrence.2.1
          (log.take occurrence.1.1))

/-- At an occurrence touching a coordinate, extending the prefix through
that occurrence increases its support-occurrence count by exactly one. -/
theorem supportOccurrenceCount_take_succ
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (log : List E)
    (index : Fin log.length) (coordinate : V)
    (inside : coordinate ∈ support (log.get index)) :
    supportOccurrenceCount support coordinate
        (log.take (index.1 + 1)) =
      supportOccurrenceCount support coordinate (log.take index.1) + 1 := by
  have takeEquality : log.take (index.1 + 1) =
      (log.take index.1).concat (log.get index) := by
    rw [List.get_eq_getElem]
    exact (List.take_concat_get (l := log) (i := index.1) index.2).symm
  have insideElem : coordinate ∈ support log[index.1] := by
    simpa [List.get_eq_getElem] using inside
  unfold supportOccurrenceCount
  rw [takeEquality, List.concat_eq_append, List.filter_append]
  simp [insideElem]

/-- Once the occurrence at `left` has consumed a coordinate, every strictly
later prefix has a strictly larger row index for that coordinate. -/
theorem supportOccurrenceCount_take_strict
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (log : List E)
    (left right : Fin log.length) (coordinate : V)
    (order : left.1 < right.1)
    (inside : coordinate ∈ support (log.get left)) :
    supportOccurrenceCount support coordinate (log.take left.1) <
      supportOccurrenceCount support coordinate (log.take right.1) := by
  have throughLeft := supportOccurrenceCount_take_succ
    support log left coordinate inside
  have prefixRelation : List.IsPrefix (log.take (left.1 + 1))
      (log.take right.1) := by
    rw [List.take_isPrefix_take]
    exact Or.inl (by omega)
  have filteredPrefix := prefixRelation.filter
    (fun event => decide (coordinate ∈ support event))
  have lengthBound := filteredPrefix.length_le
  change supportOccurrenceCount support coordinate
      (log.take (left.1 + 1)) ≤
    supportOccurrenceCount support coordinate (log.take right.1) at lengthBound
  omega

/-- Distinct log occurrences and supported coordinates always read distinct
resampling-table cells.  This is the independence fact behind the fixed-log
and fixed-witness probability product. -/
theorem occurrenceCell_injective
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (initial : V → ℕ) (log : List E) :
    Function.Injective (occurrenceCell support initial log) := by
  intro left right cellEquality
  have coordinateEquality : left.2.1 = right.2.1 :=
    congrArg Prod.fst cellEquality
  have rowEquality :
      initial left.2.1 +
          supportOccurrenceCount support left.2.1 (log.take left.1.1) =
        initial right.2.1 +
          supportOccurrenceCount support right.2.1 (log.take right.1.1) :=
    congrArg Prod.snd cellEquality
  have indexValueEquality : left.1.1 = right.1.1 := by
    by_contra different
    rcases lt_or_gt_of_ne different with order | order
    · have strict := supportOccurrenceCount_take_strict
        support log left.1 right.1 left.2.1 order left.2.2
      have sameRow :
          initial left.2.1 + supportOccurrenceCount support left.2.1
              (log.take left.1.1) =
            initial left.2.1 + supportOccurrenceCount support left.2.1
              (log.take right.1.1) := by
        simpa only [← coordinateEquality] using rowEquality
      omega
    · have strict := supportOccurrenceCount_take_strict
        support log right.1 left.1 right.2.1 order right.2.2
      have sameRow :
          initial right.2.1 + supportOccurrenceCount support right.2.1
              (log.take left.1.1) =
            initial right.2.1 + supportOccurrenceCount support right.2.1
              (log.take right.1.1) := by
        simpa only [coordinateEquality] using rowEquality
      omega
  have indexEquality : left.1 = right.1 := Fin.ext indexValueEquality
  cases left with
  | mk leftIndex leftCoordinate =>
      cases right with
      | mk rightIndex rightCoordinate =>
          dsimp at indexEquality coordinateEquality ⊢
          subst rightIndex
          have coordinateSubtypeEquality : leftCoordinate = rightCoordinate :=
            Subtype.ext coordinateEquality
          subst rightCoordinate
          rfl

/-- The occurrence-cell map packaged as an embedding for finite counting. -/
def occurrenceCellEmbedding
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (initial : V → ℕ) (log : List E) :
    (Σ index : Fin log.length,
      {coordinate : V // coordinate ∈ support (log.get index)}) ↪ V × ℕ where
  toFun := occurrenceCell support initial log
  inj' := occurrenceCell_injective support initial log

end TernarySyncAudit
