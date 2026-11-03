import Mathlib
import FormalAudit.ParentedWitnessScan

namespace TernarySyncAudit

/-- If all retained nodes have depth below `bound`, one further scan step has
all depths below `bound+1`. -/
theorem deepestWitnessStep_depth_bound
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (entries : List (WitnessScanEntry E)) (bound : ℕ)
    (oldBound : ∀ entry ∈ entries, entry.depth < bound) :
    ∀ entry ∈ deepestWitnessStep neighbors newLabel entries,
      entry.depth < bound + 1 := by
  intro entry entryMember
  unfold deepestWitnessStep at entryMember
  split at entryMember
  · exact (oldBound entry entryMember).trans (by omega)
  · next maximum maximumEq =>
      rcases List.mem_cons.mp entryMember with entryEq | oldMember
      · subst entry
        obtain ⟨parent, parentMember, dependent, parentDepth⟩ :=
          deepestWitnessStep_parent_exists
            neighbors newLabel entries maximum maximumEq
        have parentBound := oldBound parent parentMember
        change maximum + 1 < bound + 1
        omega
      · exact (oldBound entry oldMember).trans (by omega)

/-- Folding `labels` through the deepest scan raises the uniform depth bound
by at most the number of processed labels. -/
theorem foldl_deepestWitnessStep_depth_bound
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (labels : List E)
    (entries : List (WitnessScanEntry E)) (bound : ℕ)
    (initialBound : ∀ entry ∈ entries, entry.depth < bound) :
    ∀ entry ∈ labels.foldl (fun current label =>
        deepestWitnessStep neighbors label current) entries,
      entry.depth < bound + labels.length := by
  induction labels generalizing entries bound with
  | nil =>
      intro entry entryMember
      simpa using initialBound entry entryMember
  | cons label rest inductionHypothesis =>
      simp only [List.foldl_cons, List.length_cons]
      have afterStep := deepestWitnessStep_depth_bound
        neighbors label entries bound initialBound
      have tailBound := inductionHypothesis
        (deepestWitnessStep neighbors label entries) (bound + 1) afterStep
      intro entry entryMember
      have boundResult := tailBound entry entryMember
      omega

/-- Every node in a nonempty reversed scan has depth strictly smaller than
the length of the scanned prefix. -/
theorem deepestWitnessScanReversed_depth_lt_length
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root : E) (older : List E)
    (entry : WitnessScanEntry E)
    (entryMember : entry ∈
      deepestWitnessScanReversed neighbors (root :: older)) :
    entry.depth < (root :: older).length := by
  simp only [deepestWitnessScanReversed] at entryMember
  have bound := foldl_deepestWitnessStep_depth_bound
    neighbors older [⟨root, 0⟩] 1 (by
      intro candidate candidateMember
      simp only [List.mem_singleton] at candidateMember
      subst candidate
      exact Nat.zero_lt_succ 0)
  have result := bound entry entryMember
  change entry.depth < older.length + 1
  omega

/-- The same depth bound for the parented scan follows by forgetting parent
pointers. -/
theorem deepestParentedWitnessScanReversed_depth_lt_length
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root : E) (older : List E)
    (node : ParentedWitnessNode E)
    (nodeMember : node ∈
      deepestParentedWitnessScanReversed neighbors (root :: older)) :
    node.entry.depth < (root :: older).length := by
  apply deepestWitnessScanReversed_depth_lt_length
    neighbors root older node.entry
  rw [← parentedEntries_deepestParentedWitnessScanReversed]
  change node.entry ∈
    (deepestParentedWitnessScanReversed neighbors
      (root :: older)).map ParentedWitnessNode.entry
  exact List.mem_map_of_mem nodeMember

end TernarySyncAudit
