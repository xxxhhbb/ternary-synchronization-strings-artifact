import Mathlib
import FormalAudit.OccurrenceShapeCompatibility

namespace TernarySyncAudit

/-- A common-height proper witness shape for one occurrence.  This is the
version needed for finite double counting, where every outcome must map into
the same certificate type. -/
noncomputable def occurrenceWitnessShapeAt
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (height : ℕ)
    (event : E) (log : List E) (occurrence : EventOccurrence event log) :
    ProperWitnessShape neighbors (height + 1) event :=
  let proper := deepestParentedWitnessScanReversed_proper neighbors event
    (log.take occurrence.1.1).reverse
  parentedWitnessShape proper height ⟨event, 0⟩

/-- When the common height covers the log, the fixed-height shape recovers
the full retained entry set. -/
theorem occurrenceWitnessShapeAt_entrySet
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (height : ℕ)
    (event : E) (log : List E) (occurrence : EventOccurrence event log)
    (heightCovers : log.length ≤ height) :
    (properWitnessShapeEntryLog neighbors (height + 1) event
        (occurrenceWitnessShapeAt neighbors height event log occurrence)
        0).toFinset =
      (parentedEntries
        (occurrenceWitnessNodes neighbors event log occurrence)).toFinset := by
  classical
  let nodes := occurrenceWitnessNodes neighbors event log occurrence
  let rooted := deepestParentedWitnessScanReversed_rooted neighbors event
    (log.take occurrence.1.1).reverse
  let proper := rooted.proper
  have depthBound : ∀ node ∈ nodes, node.entry.depth < height := by
    intro node nodeMember
    have prefixBound :=
      deepestParentedWitnessScanReversed_depth_lt_length
        neighbors event (log.take occurrence.1.1).reverse node nodeMember
    have prefixLength :
        (event :: (log.take occurrence.1.1).reverse).length ≤ log.length := by
      simp
    omega
  calc
    (properWitnessShapeEntryLog neighbors (height + 1) event
        (occurrenceWitnessShapeAt neighbors height event log occurrence)
        0).toFinset =
      (parentedWitnessEntryLog proper height ⟨event, 0⟩).toFinset := by
        simpa [occurrenceWitnessShapeAt, rooted, proper] using
          congrArg List.toFinset
            (properWitnessShapeEntryLog_parentedWitnessShape
              proper height ⟨event, 0⟩)
    _ = (parentedEntries
        (occurrenceWitnessNodes neighbors event log occurrence)).toFinset := by
      have properEq : proper = rooted.proper := Subsingleton.elim _ _
      rw [properEq]
      simpa [nodes, occurrenceWitnessNodes] using
        parentedWitnessEntryLog_toFinset_eq rooted height depthBound

/-- Distinct occurrences remain distinct when encoded at any common height
covering the whole log. -/
theorem occurrenceWitnessShapeAt_injective
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (height : ℕ)
    (event : E) (log : List E) (heightCovers : log.length ≤ height) :
    Function.Injective
      (occurrenceWitnessShapeAt neighbors height event log) := by
  intro left right shapeEq
  have entrySetEq :
      (parentedEntries
        (occurrenceWitnessNodes neighbors event log left)).toFinset =
      (parentedEntries
        (occurrenceWitnessNodes neighbors event log right)).toFinset := by
    rw [← occurrenceWitnessShapeAt_entrySet neighbors height event log left
        heightCovers,
      ← occurrenceWitnessShapeAt_entrySet neighbors height event log right
        heightCovers,
      shapeEq]
  have leftNodup : (parentedEntries
      (occurrenceWitnessNodes neighbors event log left)).Nodup := by
    rw [occurrenceWitnessNodes,
      parentedEntries_deepestParentedWitnessScanReversed]
    exact deepestWitnessScanReversed_nodup neighbors _
  have rightNodup : (parentedEntries
      (occurrenceWitnessNodes neighbors event log right)).Nodup := by
    rw [occurrenceWitnessNodes,
      parentedEntries_deepestParentedWitnessScanReversed]
    exact deepestWitnessScanReversed_nodup neighbors _
  have countEq : witnessScanLabelCount event
        (parentedEntries
          (occurrenceWitnessNodes neighbors event log left)) =
      witnessScanLabelCount event
        (parentedEntries
          (occurrenceWitnessNodes neighbors event log right)) := by
    rw [witnessScanLabelCount_eq_toFinset_filter_card event _ leftNodup,
      witnessScanLabelCount_eq_toFinset_filter_card event _ rightNodup,
      entrySetEq]
  rw [occurrenceWitnessNodes_root_count,
    occurrenceWitnessNodes_root_count] at countEq
  apply Subtype.ext
  apply Fin.ext
  by_contra indexNe
  rcases lt_or_gt_of_ne indexNe with positionLt | positionLt
  · have := eventOccurrenceRank_strictMono
      event log left right positionLt
    omega
  · have := eventOccurrenceRank_strictMono
      event log right left positionLt
    omega

/-- Fixed-height canonical entry log equals the canonical sort of the actual
retained scan entries. -/
theorem chronologicalOccurrenceShapeAtEntryLog_eq
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (height : ℕ)
    (event : E) (log : List E) (occurrence : EventOccurrence event log)
    (heightCovers : log.length ≤ height) :
    chronologicalProperWitnessShapeEntryLog neighbors (height + 1) event
        (occurrenceWitnessShapeAt neighbors height event log occurrence) =
      (parentedEntries
        (occurrenceWitnessNodes neighbors event log occurrence)).insertionSort
          witnessDepthBefore := by
  classical
  let nodes := occurrenceWitnessNodes neighbors event log occurrence
  let rooted := deepestParentedWitnessScanReversed_rooted neighbors event
    (log.take occurrence.1.1).reverse
  let proper := rooted.proper
  let shapeEntries := properWitnessShapeEntryLog neighbors (height + 1)
    event (occurrenceWitnessShapeAt neighbors height event log occurrence) 0
  let actualEntries := parentedEntries nodes
  have rootMember : (⟨event, 0⟩ : WitnessScanEntry E) ∈ actualEntries := by
    unfold actualEntries nodes occurrenceWitnessNodes parentedEntries
    apply List.mem_map.mpr
    exact ⟨⟨⟨event, 0⟩, none⟩, rooted.root_mem, rfl⟩
  have exactShapeLog : shapeEntries =
      parentedWitnessEntryLog proper height ⟨event, 0⟩ := by
    simpa [shapeEntries, occurrenceWitnessShapeAt, rooted, proper] using
      properWitnessShapeEntryLog_parentedWitnessShape
        proper height ⟨event, 0⟩
  have shapeNodup : shapeEntries.Nodup := by
    rw [exactShapeLog]
    exact parentedWitnessEntryLog_nodup proper height
      ⟨event, 0⟩ rootMember
  have actualNodup : actualEntries.Nodup := by
    unfold actualEntries nodes occurrenceWitnessNodes
    rw [parentedEntries_deepestParentedWitnessScanReversed]
    exact deepestWitnessScanReversed_nodup neighbors _
  have entrySetEq : shapeEntries.toFinset = actualEntries.toFinset := by
    simpa [shapeEntries, actualEntries, nodes] using
      occurrenceWitnessShapeAt_entrySet neighbors height event log occurrence
        heightCovers
  have permutation : shapeEntries.Perm actualEntries :=
    List.perm_of_nodup_nodup_toFinset_eq shapeNodup actualNodup entrySetEq
  unfold chronologicalProperWitnessShapeEntryLog
  exact insertionSort_witnessDepthBefore_eq_of_perm permutation

/-- The fixed-height chronological occurrence log still has at most the full
run-log length. -/
theorem chronologicalOccurrenceShapeAtLog_length_le
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (height : ℕ)
    (event : E) (log : List E) (occurrence : EventOccurrence event log)
    (heightCovers : log.length ≤ height) :
    (chronologicalProperWitnessShapeLog neighbors (height + 1) event
      (occurrenceWitnessShapeAt neighbors height event log occurrence)).length ≤
        log.length := by
  have scanBound :=
    parentedEntries_deepestParentedWitnessScanReversed_length_le
      neighbors event (log.take occurrence.1.1).reverse
  have prefixBound :
      (event :: (log.take occurrence.1.1).reverse).length ≤ log.length := by
    simp only [List.length_cons, List.length_reverse, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt occurrence.1.isLt)]
    omega
  rw [chronologicalProperWitnessShapeLog, List.length_map,
    chronologicalOccurrenceShapeAtEntryLog_eq neighbors height event log
      occurrence heightCovers,
    List.length_insertionSort]
  exact le_trans scanBound prefixBound

/-- Fixed-height counterpart of occurrence compatibility, suitable for a
single certificate family shared by all finite-table outcomes. -/
theorem occurrence_table_mem_chronologicalShapeEventAt
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
    (rows height : ℕ) (default : A) (table : (V × Fin rows) → A)
    (log : List E) (heightCovers : log.length ≤ height)
    (logLength : log.length ≤ rows)
    (compatible : logCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      (extendBoundedTable rows default table) (fun _ => 0) log)
    (root : E) (occurrence : EventOccurrence root log) :
    table ∈ chronologicalProperWitnessShapeCompatibilityEvent support event
      neighbors rows (height + 1) root
        (occurrenceWitnessShapeAt neighbors height root log occurrence) := by
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
      (chronologicalProperWitnessShapeLog neighbors (height + 1) root
        (occurrenceWitnessShapeAt neighbors height root log occurrence)) := by
    unfold chronologicalProperWitnessShapeLog witnessEntryLogCompatible at *
    rw [chronologicalOccurrenceShapeAtEntryLog_eq neighbors height root log
      occurrence heightCovers]
    exact sortedCompatible
  have shapeLength := chronologicalOccurrenceShapeAtLog_length_le
    neighbors height root log occurrence heightCovers
  have lengthBound :
      (chronologicalProperWitnessShapeLog neighbors (height + 1) root
        (occurrenceWitnessShapeAt neighbors height root log occurrence)).length ≤
          rows := le_trans shapeLength logLength
  rw [chronologicalProperWitnessShapeCompatibilityEvent]
  simp only [lengthBound, dite_true]
  exact bounded_logCompatible_mem support event eventDepends
    (chronologicalProperWitnessShapeLog neighbors (height + 1) root
      (occurrenceWitnessShapeAt neighbors height root log occurrence))
    rows lengthBound default table chronologicalCompatible

end TernarySyncAudit
