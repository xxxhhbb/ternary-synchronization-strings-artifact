import Mathlib
import FormalAudit.DeepestWitnessScan
import FormalAudit.ParentedWitnessScan

namespace TernarySyncAudit

/-- Chronological retained entries are ordered by strictly decreasing depth
whenever their supports intersect. -/
def SupportsFollowDepth
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V)
    (entries : List (WitnessScanEntry E)) : Prop :=
  entries.Pairwise fun earlier later =>
    ¬Disjoint (support earlier.label) (support later.label) →
      later.depth < earlier.depth

/-- One deepest insertion preserves the chronological depth order. -/
theorem deepestWitnessStep_supportsFollowDepth
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (support : E → Finset V) (neighbors : E → Finset E)
    (overlapDependent : ∀ left right,
      ¬Disjoint (support left) (support right) →
        left ∈ closedNeighbors neighbors right)
    (newLabel : E) (entries : List (WitnessScanEntry E))
    (ordered : SupportsFollowDepth support entries) :
    SupportsFollowDepth support
      (deepestWitnessStep neighbors newLabel entries) := by
  unfold deepestWitnessStep
  split
  · exact ordered
  · next maximum maximumEq =>
      rw [SupportsFollowDepth, List.pairwise_cons]
      constructor
      · intro oldEntry oldMember overlaps
        have dependent := overlapDependent newLabel oldEntry.label overlaps
        exact deepestWitnessStep_depth_gt
          neighbors newLabel entries maximum maximumEq
            oldEntry oldMember dependent
      · exact ordered

/-- An arbitrary reverse-scan fold preserves the order invariant. -/
theorem foldl_deepestWitnessStep_supportsFollowDepth
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (support : E → Finset V) (neighbors : E → Finset E)
    (overlapDependent : ∀ left right,
      ¬Disjoint (support left) (support right) →
        left ∈ closedNeighbors neighbors right)
    (labels : List E) (entries : List (WitnessScanEntry E))
    (ordered : SupportsFollowDepth support entries) :
    SupportsFollowDepth support
      (labels.foldl (fun current label =>
        deepestWitnessStep neighbors label current) entries) := by
  induction labels generalizing entries with
  | nil => exact ordered
  | cons label rest inductionHypothesis =>
      simp only [List.foldl_cons]
      exact inductionHypothesis _
        (deepestWitnessStep_supportsFollowDepth
          support neighbors overlapDependent label entries ordered)

/-- Every nonempty deepest scan has the chronological depth-order property. -/
theorem deepestWitnessScanReversed_supportsFollowDepth
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (support : E → Finset V) (neighbors : E → Finset E)
    (overlapDependent : ∀ left right,
      ¬Disjoint (support left) (support right) →
        left ∈ closedNeighbors neighbors right)
    (root : E) (older : List E) :
    SupportsFollowDepth support
      (deepestWitnessScanReversed neighbors (root :: older)) := by
  simp only [deepestWitnessScanReversed]
  exact foldl_deepestWitnessStep_supportsFollowDepth
    support neighbors overlapDependent older [⟨root, 0⟩] (by
      simp [SupportsFollowDepth])

/-- Parented scans inherit the same chronological depth order after parent
pointers are forgotten. -/
theorem deepestParentedWitnessScanReversed_supportsFollowDepth
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (support : E → Finset V) (neighbors : E → Finset E)
    (overlapDependent : ∀ left right,
      ¬Disjoint (support left) (support right) →
        left ∈ closedNeighbors neighbors right)
    (root : E) (older : List E) :
    SupportsFollowDepth support
      (parentedEntries
        (deepestParentedWitnessScanReversed neighbors (root :: older))) := by
  rw [parentedEntries_deepestParentedWitnessScanReversed]
  exact deepestWitnessScanReversed_supportsFollowDepth
    support neighbors overlapDependent root older

end TernarySyncAudit
