import Mathlib
import FormalAudit.ParentedWitnessScan

namespace TernarySyncAudit

/-- One deepest-witness scan step appends at most one retained entry. -/
theorem deepestWitnessStep_length_le_succ
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (entries : List (WitnessScanEntry E)) :
    (deepestWitnessStep neighbors newLabel entries).length ≤
      entries.length + 1 := by
  unfold deepestWitnessStep
  split <;> simp

/-- Folding the deepest-witness update over a continuation retains no more
entries than the initial entries plus the number of processed labels. -/
theorem foldl_deepestWitnessStep_length_le
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (labels : List E)
    (entries : List (WitnessScanEntry E)) :
    (labels.foldl (fun current label =>
      deepestWitnessStep neighbors label current) entries).length ≤
        entries.length + labels.length := by
  induction labels generalizing entries with
  | nil => simp
  | cons label rest inductionHypothesis =>
      simp only [List.foldl_cons, List.length_cons]
      have stepBound := deepestWitnessStep_length_le_succ
        neighbors label entries
      have foldBound := inductionHypothesis
        (deepestWitnessStep neighbors label entries)
      omega

/-- A complete nonempty reverse scan retains no more entries than the input
log contains. -/
theorem deepestWitnessScanReversed_length_le
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root : E) (older : List E) :
    (deepestWitnessScanReversed neighbors (root :: older)).length ≤
      (root :: older).length := by
  unfold deepestWitnessScanReversed
  simpa [Nat.add_comm] using foldl_deepestWitnessStep_length_le
    neighbors older [⟨root, 0⟩]

/-- The labelled-entry projection of the parented scan obeys the same input
length bound. -/
theorem parentedEntries_deepestParentedWitnessScanReversed_length_le
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root : E) (older : List E) :
    (parentedEntries
      (deepestParentedWitnessScanReversed neighbors (root :: older))).length ≤
        (root :: older).length := by
  rw [parentedEntries_deepestParentedWitnessScanReversed]
  exact deepestWitnessScanReversed_length_le neighbors root older

end TernarySyncAudit
