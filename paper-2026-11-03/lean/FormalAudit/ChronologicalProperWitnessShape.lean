import Mathlib
import FormalAudit.CompatibleEntrySort
import FormalAudit.ProperWitnessShapeEntryLog

namespace TernarySyncAudit

/-- Canonical chronological entry log of a proper witness shape, obtained by
sorting every node by decreasing witness depth.  Equal-depth branches may be
ordered arbitrarily because proper witness branches at equal depth have
pairwise distinct labels and the actual retained-log argument only swaps
support-disjoint entries. -/
noncomputable def chronologicalProperWitnessShapeEntryLog
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (height : ℕ) (root : E)
    (shape : ProperWitnessShape neighbors height root) :
    List (WitnessScanEntry E) :=
  (properWitnessShapeEntryLog neighbors height root shape 0).insertionSort
    witnessDepthBefore

/-- Label projection of the canonical chronological entry log. -/
noncomputable def chronologicalProperWitnessShapeLog
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (height : ℕ) (root : E)
    (shape : ProperWitnessShape neighbors height root) : List E :=
  (chronologicalProperWitnessShapeEntryLog neighbors height root shape).map
    WitnessScanEntry.label

/-- Chronological sorting only permutes the ordinary deterministic shape log. -/
theorem chronologicalProperWitnessShapeLog_perm
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (height : ℕ) (root : E)
    (shape : ProperWitnessShape neighbors height root) :
    List.Perm (chronologicalProperWitnessShapeLog neighbors height root shape)
      (properWitnessShapeLog neighbors height root shape) := by
  classical
  have entryPerm := List.perm_insertionSort witnessDepthBefore
    (properWitnessShapeEntryLog neighbors height root shape 0)
  have labelPerm := entryPerm.map WitnessScanEntry.label
  simpa [chronologicalProperWitnessShapeLog,
    chronologicalProperWitnessShapeEntryLog,
    properWitnessShapeEntryLog_map_label] using labelPerm

/-- Sorting the shape into chronological order preserves its exact recursive
product mass. -/
theorem chronologicalProperWitnessShapeLog_mass
    {E : Type*} [Fintype E] [DecidableEq E]
    (eventMass : E → ℝ) (neighbors : E → Finset E)
    (height : ℕ) (root : E)
    (shape : ProperWitnessShape neighbors height root) :
    ((chronologicalProperWitnessShapeLog neighbors height root shape).map
        eventMass).prod =
      properWitnessShapeMass eventMass neighbors height root shape := by
  calc
    ((chronologicalProperWitnessShapeLog neighbors height root shape).map
        eventMass).prod =
      ((properWitnessShapeLog neighbors height root shape).map
        eventMass).prod :=
      ((chronologicalProperWitnessShapeLog_perm
        neighbors height root shape).map eventMass).prod_eq
    _ = properWitnessShapeMass eventMass neighbors height root shape :=
      properWitnessShapeLog_mass eventMass neighbors height root shape

/-- Fin-indexed fixed-log mass for the chronological shape log. -/
theorem chronologicalProperWitnessShapeLog_fin_mass
    {E : Type*} [Fintype E] [DecidableEq E]
    (eventMass : E → ℝ) (neighbors : E → Finset E)
    (height : ℕ) (root : E)
    (shape : ProperWitnessShape neighbors height root) :
    (∏ index : Fin
        (chronologicalProperWitnessShapeLog neighbors height root shape).length,
      eventMass
        ((chronologicalProperWitnessShapeLog neighbors height root shape).get
          index)) =
      properWitnessShapeMass eventMass neighbors height root shape := by
  rw [fin_product_get_eq_list_product]
  exact chronologicalProperWitnessShapeLog_mass
    eventMass neighbors height root shape

end TernarySyncAudit
