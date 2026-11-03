import Mathlib
import FormalAudit.ParentedWitnessCompleteness
import FormalAudit.ProperWitnessShapeLog
import FormalAudit.DeepestWitnessDepthBound
import FormalAudit.OccurrenceWitnessCertificates

namespace TernarySyncAudit

/-- The deterministic proper-shape linearization with canonical tree depths
retained in every entry. -/
noncomputable def properWitnessShapeEntryLog
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) :
    ∀ height event,
      ProperWitnessShape neighbors height event →
      ℕ → List (WitnessScanEntry E)
  | 0, _, shape, _ => nomatch shape
  | height + 1, event, children, baseDepth =>
      (Finset.univ.toList.map (fun child =>
        match children child with
        | none => []
        | some subtree => properWitnessShapeEntryLog
            neighbors height child.1 subtree (baseDepth + 1))).flatten ++
        [⟨event, baseDepth⟩]

/-- Forgetting depths in the entry linearization gives the ordinary
proper-shape label log. -/
theorem properWitnessShapeEntryLog_map_label
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) :
    ∀ height event (shape : ProperWitnessShape neighbors height event)
      (baseDepth : ℕ),
      (properWitnessShapeEntryLog neighbors height event shape baseDepth).map
          WitnessScanEntry.label =
        properWitnessShapeLog neighbors height event shape := by
  intro height
  induction height with
  | zero =>
      intro event shape baseDepth
      exact PEmpty.elim shape
  | succ height inductionHypothesis =>
      intro event children baseDepth
      classical
      simp only [properWitnessShapeEntryLog, properWitnessShapeLog,
        List.map_append, List.map_singleton, List.map_flatten,
        List.map_map]
      congr 2
      apply List.map_congr_left
      intro child
      cases childEq : children child with
      | none => simp [childEq]
      | some subtree =>
          simp [childEq,
            inductionHypothesis child.1 subtree (baseDepth + 1)]

/-- Relabelling the dependent root index does not change the entry
linearization after transporting the shape along the same equality. -/
theorem properWitnessShapeEntryLog_cast_root
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (height : ℕ)
    {left right : E} (labelEq : left = right)
    (shape : ProperWitnessShape neighbors height left) (baseDepth : ℕ) :
    properWitnessShapeEntryLog neighbors height right
        (labelEq ▸ shape) baseDepth =
      properWitnessShapeEntryLog neighbors height left shape baseDepth := by
  subst right
  rfl

/-- For a valid parented structure, the entry linearization of its encoded
proper shape is exactly the direct parented-entry linearization. -/
theorem properWitnessShapeEntryLog_parentedWitnessShape
    {E : Type*} [Fintype E] [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ height (rootEntry : WitnessScanEntry E),
      properWitnessShapeEntryLog neighbors (height + 1) rootEntry.label
          (parentedWitnessShape proper height rootEntry) rootEntry.depth =
        parentedWitnessEntryLog proper height rootEntry := by
  intro height
  induction height with
  | zero =>
      intro rootEntry
      simp [properWitnessShapeEntryLog, parentedWitnessShape,
        parentedWitnessEntryLog]
  | succ height inductionHypothesis =>
      intro rootEntry
      classical
      rw [parentedWitnessShape, properWitnessShapeEntryLog,
        parentedWitnessEntryLog]
      congr 2
      apply List.map_congr_left
      intro childLabel
      cases selectedEq : directParentedChild?
          proper rootEntry childLabel.1 with
      | none => simp
      | some child =>
          intro childLabelMember
          have childDepth := proper.parent_depth child.1 child.2.1
            rootEntry child.2.2.1
          simp only
          calc
            properWitnessShapeEntryLog neighbors (height + 1) childLabel.1
                (child.2.2.2 ▸
                  parentedWitnessShape proper height child.1.entry)
                (rootEntry.depth + 1) =
              properWitnessShapeEntryLog neighbors (height + 1)
                child.1.entry.label
                (parentedWitnessShape proper height child.1.entry)
                (rootEntry.depth + 1) :=
              properWitnessShapeEntryLog_cast_root neighbors (height + 1)
                child.2.2.2
                (parentedWitnessShape proper height child.1.entry)
                (rootEntry.depth + 1)
            _ = properWitnessShapeEntryLog neighbors (height + 1)
                child.1.entry.label
                (parentedWitnessShape proper height child.1.entry)
                child.1.entry.depth := by rw [childDepth]
            _ = parentedWitnessEntryLog proper height child.1.entry :=
              inductionHypothesis child.1.entry

/-- At any height covering every recorded depth, the deterministic component
entry set is exactly the set of entries in the rooted parented scan. -/
theorem parentedWitnessEntryLog_toFinset_eq
    {E : Type*} [Fintype E] [DecidableEq E]
    {neighbors : E → Finset E} {root : E}
    {nodes : List (ParentedWitnessNode E)}
    (rooted : RootedParentedWitnessNodes neighbors root nodes)
    (height : ℕ)
    (depthBound : ∀ node ∈ nodes, node.entry.depth < height) :
    (parentedWitnessEntryLog rooted.proper height ⟨root, 0⟩).toFinset =
      (parentedEntries nodes).toFinset := by
  classical
  ext entry
  constructor
  · intro entryMember
    rw [List.mem_toFinset] at entryMember ⊢
    exact mem_parentedWitnessEntryLog_mem_nodes rooted.proper height
      ⟨root, 0⟩ (by
        change ⟨root, 0⟩ ∈ nodes.map ParentedWitnessNode.entry
        exact List.mem_map_of_mem rooted.root_mem) entry entryMember
  · intro entryMember
    rw [List.mem_toFinset] at entryMember ⊢
    change entry ∈ nodes.map ParentedWitnessNode.entry at entryMember
    obtain ⟨node, nodeMember, entryEq⟩ := List.mem_map.mp entryMember
    subst entry
    have path := rooted_node_component_contains rooted
      node.entry.depth node nodeMember rfl
    have lifted := ParentedComponentContains.mono rooted.proper
      (Nat.le_of_lt (depthBound node nodeMember)) path
    exact componentContains_mem_parentedWitnessEntryLog
      rooted.proper height ⟨root, 0⟩ node.entry lifted

/-- For a duplicate-free entry list, label multiplicity is the cardinality of
the corresponding label fiber in its entry set. -/
theorem witnessScanLabelCount_eq_toFinset_filter_card
    {E : Type*} [DecidableEq E] (target : E)
    (entries : List (WitnessScanEntry E)) (entriesNodup : entries.Nodup) :
    witnessScanLabelCount target entries =
      (entries.toFinset.filter fun entry => entry.label = target).card := by
  unfold witnessScanLabelCount
  rw [← List.toFinset_card_of_nodup
    (List.Nodup.filter (fun entry => decide (entry.label = target))
      entriesNodup)]
  congr 1
  ext entry
  simp

/-- Fixed-height proper witness shape generated by one occurrence.  The
ambient log length is used as a common truncation height for every occurrence
of the same event. -/
noncomputable def occurrenceWitnessShape
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (event : E) (log : List E)
    (occurrence : EventOccurrence event log) :
    ProperWitnessShape neighbors (log.length + 1) event :=
  let proper := deepestParentedWitnessScanReversed_proper neighbors event
    (log.take occurrence.1.1).reverse
  parentedWitnessShape proper log.length ⟨event, 0⟩

/-- The occurrence shape recovers exactly the retained labelled-depth entry
set of its parented certificate. -/
theorem occurrenceWitnessShape_entrySet
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (event : E) (log : List E)
    (occurrence : EventOccurrence event log) :
    (properWitnessShapeEntryLog neighbors (log.length + 1) event
        (occurrenceWitnessShape neighbors event log occurrence) 0).toFinset =
      (parentedEntries
        (occurrenceWitnessNodes neighbors event log occurrence)).toFinset := by
  classical
  let nodes := occurrenceWitnessNodes neighbors event log occurrence
  let rooted := deepestParentedWitnessScanReversed_rooted neighbors event
    (log.take occurrence.1.1).reverse
  let proper := rooted.proper
  have depthBound : ∀ node ∈ nodes, node.entry.depth < log.length := by
    intro node nodeMember
    have prefixBound :=
      deepestParentedWitnessScanReversed_depth_lt_length
        neighbors event (log.take occurrence.1.1).reverse node nodeMember
    have prefixLength :
        (event :: (log.take occurrence.1.1).reverse).length ≤ log.length := by
      simp
    omega
  calc
    (properWitnessShapeEntryLog neighbors (log.length + 1) event
        (occurrenceWitnessShape neighbors event log occurrence) 0).toFinset =
      (parentedWitnessEntryLog proper log.length ⟨event, 0⟩).toFinset := by
        simpa [occurrenceWitnessShape, rooted, proper] using
          congrArg List.toFinset
            (properWitnessShapeEntryLog_parentedWitnessShape
              proper log.length ⟨event, 0⟩)
    _ = (parentedEntries
        (occurrenceWitnessNodes neighbors event log occurrence)).toFinset := by
      have properEq : proper = rooted.proper := Subsingleton.elim _ _
      rw [properEq]
      simpa [nodes, occurrenceWitnessNodes] using
        (parentedWitnessEntryLog_toFinset_eq
          rooted log.length depthBound)

/-- Distinct occurrences yield distinct fixed-height proper witness shapes. -/
theorem occurrenceWitnessShape_injective
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (event : E) (log : List E) :
    Function.Injective (occurrenceWitnessShape neighbors event log) := by
  intro left right shapeEq
  have entrySetEq :
      (parentedEntries
        (occurrenceWitnessNodes neighbors event log left)).toFinset =
      (parentedEntries
        (occurrenceWitnessNodes neighbors event log right)).toFinset := by
    rw [← occurrenceWitnessShape_entrySet,
      ← occurrenceWitnessShape_entrySet, shapeEq]
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
    rw [witnessScanLabelCount_eq_toFinset_filter_card
        event _ leftNodup,
      witnessScanLabelCount_eq_toFinset_filter_card
        event _ rightNodup,
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

end TernarySyncAudit
