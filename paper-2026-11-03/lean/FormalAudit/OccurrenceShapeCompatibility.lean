import Mathlib
import FormalAudit.ChronologicalProperWitnessShapeEvent
import FormalAudit.DeepestWitnessLength
import FormalAudit.ParentedWitnessEntryNodup
import FormalAudit.MTLogCompatibility

namespace TernarySyncAudit

/-- Compatibility is inherited by every chronological prefix. -/
theorem logCompatible_take
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (eventSet : E → Set (V → A))
    (table : V → ℕ → A) (initial : V → ℕ) :
    ∀ (log : List E) (length : ℕ),
      logCompatible support eventSet table initial log →
        logCompatible support eventSet table initial (log.take length) := by
  intro log
  induction log generalizing initial with
  | nil => simp
  | cons head tail inductionHypothesis =>
      intro length compatible
      cases length with
      | zero => simp
      | succ length =>
          simp only [List.take_succ_cons]
          rw [logCompatible_cons] at compatible ⊢
          exact ⟨compatible.1,
            inductionHypothesis
              (incrementSupport (support head) initial) length compatible.2⟩

/-- Sorting two permutations by the canonical witness-entry order produces
literally the same list. -/
theorem insertionSort_witnessDepthBefore_eq_of_perm
    {E : Type*} [Fintype E] [DecidableEq E]
    {left right : List (WitnessScanEntry E)} (permutation : left.Perm right) :
    left.insertionSort witnessDepthBefore =
      right.insertionSort witnessDepthBefore := by
  classical
  have sortedPermutation :
      List.Perm (left.insertionSort witnessDepthBefore)
        (right.insertionSort witnessDepthBefore) :=
    (List.perm_insertionSort witnessDepthBefore left).trans
      (permutation.trans
        (List.perm_insertionSort witnessDepthBefore right).symm)
  exact sortedPermutation.eq_of_pairwise'
    (List.pairwise_insertionSort witnessDepthBefore left)
    (List.pairwise_insertionSort witnessDepthBefore right)

/-- The canonical chronological entry log of an occurrence shape is exactly
the canonical sort of the entries retained by its deepest parented scan. -/
theorem chronologicalOccurrenceShapeEntryLog_eq
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (event : E) (log : List E)
    (occurrence : EventOccurrence event log) :
    chronologicalProperWitnessShapeEntryLog neighbors (log.length + 1) event
        (occurrenceWitnessShape neighbors event log occurrence) =
      (parentedEntries
        (occurrenceWitnessNodes neighbors event log occurrence)).insertionSort
          witnessDepthBefore := by
  classical
  let nodes := occurrenceWitnessNodes neighbors event log occurrence
  let rooted := deepestParentedWitnessScanReversed_rooted neighbors event
    (log.take occurrence.1.1).reverse
  let proper := rooted.proper
  let shapeEntries := properWitnessShapeEntryLog neighbors (log.length + 1)
    event (occurrenceWitnessShape neighbors event log occurrence) 0
  let actualEntries := parentedEntries nodes
  have rootMember : (⟨event, 0⟩ : WitnessScanEntry E) ∈ actualEntries := by
    unfold actualEntries nodes occurrenceWitnessNodes parentedEntries
    apply List.mem_map.mpr
    exact ⟨⟨⟨event, 0⟩, none⟩, rooted.root_mem, rfl⟩
  have exactShapeLog : shapeEntries =
      parentedWitnessEntryLog proper log.length ⟨event, 0⟩ := by
    simpa [shapeEntries, occurrenceWitnessShape, rooted, proper] using
      (properWitnessShapeEntryLog_parentedWitnessShape
        proper log.length ⟨event, 0⟩)
  have shapeNodup : shapeEntries.Nodup := by
    rw [exactShapeLog]
    exact parentedWitnessEntryLog_nodup proper log.length
      ⟨event, 0⟩ rootMember
  have actualNodup : actualEntries.Nodup := by
    unfold actualEntries nodes occurrenceWitnessNodes
    rw [parentedEntries_deepestParentedWitnessScanReversed]
    exact deepestWitnessScanReversed_nodup neighbors _
  have entrySetEq : shapeEntries.toFinset = actualEntries.toFinset := by
    simpa [shapeEntries, actualEntries, nodes] using
      occurrenceWitnessShape_entrySet neighbors event log occurrence
  have permutation : shapeEntries.Perm actualEntries :=
    List.perm_of_nodup_nodup_toFinset_eq shapeNodup actualNodup entrySetEq
  unfold chronologicalProperWitnessShapeEntryLog
  exact insertionSort_witnessDepthBefore_eq_of_perm permutation

/-- Every occurrence shape contains no more nodes than the log prefix that
ends at that occurrence. -/
theorem chronologicalOccurrenceShapeLog_length_le
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (event : E) (log : List E)
    (occurrence : EventOccurrence event log) :
    (chronologicalProperWitnessShapeLog neighbors (log.length + 1) event
      (occurrenceWitnessShape neighbors event log occurrence)).length ≤
        log.length := by
  have scanBound :=
    parentedEntries_deepestParentedWitnessScanReversed_length_le
      neighbors event (log.take occurrence.1.1).reverse
  have prefixBound :
      (event :: (log.take occurrence.1.1).reverse).length ≤ log.length := by
    simp only [List.length_cons, List.length_reverse, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt occurrence.1.isLt)]
    omega
  rw [chronologicalProperWitnessShapeLog,
    List.length_map, chronologicalOccurrenceShapeEntryLog_eq,
    List.length_insertionSort]
  exact le_trans scanBound prefixBound

/-- If a chronological MT log is compatible with a finite resampling table,
then the table lies in the canonical compatibility event attached to every
individual event occurrence. -/
theorem occurrence_table_mem_chronologicalShapeEvent
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate,
      DependsOn (event candidate) (support candidate))
    (neighbors : E → Finset E)
    (overlapDependent : ∀ left right,
      ¬Disjoint (support left) (support right) →
        left ∈ closedNeighbors neighbors right)
    (rows : ℕ) (default : A) (table : (V × Fin rows) → A)
    (log : List E)
    (logLength : log.length ≤ rows)
    (compatible : logCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      (extendBoundedTable rows default table) (fun _ => 0) log)
    (root : E) (occurrence : EventOccurrence root log) :
    table ∈ chronologicalProperWitnessShapeCompatibilityEvent support event
      neighbors rows (log.length + 1) root
        (occurrenceWitnessShape neighbors root log occurrence) := by
  classical
  let older := (log.take occurrence.1.1).reverse
  let actualEntries := parentedEntries
    (occurrenceWitnessNodes neighbors root log occurrence)
  have prefixEq : log.take (occurrence.1.1 + 1) =
      log.take occurrence.1.1 ++ [root] := by
    calc
      log.take (occurrence.1.1 + 1) =
          log.take occurrence.1.1 ++ [log.get occurrence.1] := by simp
      _ = log.take occurrence.1.1 ++ [root] := by rw [occurrence.2]
  have prefixCompatible := logCompatible_take support
    (fun candidate => (event candidate : Set (V → A)))
    (extendBoundedTable rows default table) (fun _ => 0)
      log (occurrence.1.1 + 1) compatible
  rw [prefixEq] at prefixCompatible
  have retainedCompatible : witnessEntryLogCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      (extendBoundedTable rows default table) (fun _ => 0)
      actualEntries := by
    let embedding := deepestWitnessScanReversed_supportCountEmbedding
      support neighbors overlapDependent root older
    have olderCompatible : logCompatible support
        (fun candidate => (event candidate : Set (V → A)))
        (extendBoundedTable rows default table) (fun _ => 0)
        (older.reverse ++ [root]) := by
      simpa [older] using prefixCompatible
    have inherited := embedding.compatible support event eventDepends
      (extendBoundedTable rows default table) (fun _ => 0)
      (older.reverse ++ [root])
      (witnessEntryLabels
        (deepestWitnessScanReversed neighbors (root :: older)))
      olderCompatible
    unfold witnessEntryLogCompatible actualEntries occurrenceWitnessNodes
    simpa [older, parentedEntries_deepestParentedWitnessScanReversed] using
      inherited
  have retainedOrder : SupportsFollowDepth support actualEntries := by
    unfold actualEntries occurrenceWitnessNodes
    exact deepestParentedWitnessScanReversed_supportsFollowDepth
      support neighbors overlapDependent root
        (log.take occurrence.1.1).reverse
  have sortedCompatible := insertionSort_witnessEntryLogCompatible
    support event eventDepends (extendBoundedTable rows default table)
      (fun _ => 0) actualEntries retainedOrder retainedCompatible
  have chronologicalCompatible : logCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      (extendBoundedTable rows default table) (fun _ => 0)
      (chronologicalProperWitnessShapeLog neighbors (log.length + 1) root
        (occurrenceWitnessShape neighbors root log occurrence)) := by
    unfold chronologicalProperWitnessShapeLog witnessEntryLogCompatible at *
    rw [chronologicalOccurrenceShapeEntryLog_eq]
    exact sortedCompatible
  have shapeLength := chronologicalOccurrenceShapeLog_length_le
    neighbors root log occurrence
  have lengthBound :
      (chronologicalProperWitnessShapeLog neighbors (log.length + 1) root
        (occurrenceWitnessShape neighbors root log occurrence)).length ≤ rows :=
    le_trans shapeLength logLength
  rw [chronologicalProperWitnessShapeCompatibilityEvent]
  simp only [lengthBound, dite_true]
  exact bounded_logCompatible_mem support event eventDepends
    (chronologicalProperWitnessShapeLog neighbors (log.length + 1) root
      (occurrenceWitnessShape neighbors root log occurrence))
    rows lengthBound default table chronologicalCompatible

end TernarySyncAudit
