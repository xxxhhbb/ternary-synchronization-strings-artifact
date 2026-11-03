import Mathlib
import FormalAudit.ParentedWitnessScan

namespace TernarySyncAudit

/-- Local correctness conditions for a list produced by the parented deepest
scan.  They are exactly the facts needed to regard every root component as a
proper witness tree. -/
structure ProperParentedWitnessNodes
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E)
    (nodes : List (ParentedWitnessNode E)) : Prop where
  entries_nodup : (parentedEntries nodes).Nodup
  parent_mem : ∀ node ∈ nodes, ∀ parentEntry,
    node.parent = some parentEntry → parentEntry ∈ parentedEntries nodes
  parent_neighbor : ∀ node ∈ nodes, ∀ parentEntry,
    node.parent = some parentEntry →
      node.entry.label ∈ closedNeighbors neighbors parentEntry.label
  parent_depth : ∀ node ∈ nodes, ∀ parentEntry,
    node.parent = some parentEntry →
      node.entry.depth = parentEntry.depth + 1
  children_label_injective : ∀ left ∈ nodes, ∀ right ∈ nodes,
    ∀ parentEntry,
      left.parent = some parentEntry →
      right.parent = some parentEntry →
      left.entry.label = right.entry.label →
      left.entry = right.entry

/-- A singleton root with no parent is a valid parented witness forest. -/
theorem properParentedWitnessNodes_singleton
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root : E) :
    ProperParentedWitnessNodes neighbors [⟨⟨root, 0⟩, none⟩] := by
  constructor
  · simp [parentedEntries]
  · intro node nodeMember parentEntry parentEq
    simp at nodeMember
    subst node
    simp at parentEq
  · intro node nodeMember parentEntry parentEq
    simp at nodeMember
    subst node
    simp at parentEq
  · intro node nodeMember parentEntry parentEq
    simp at nodeMember
    subst node
    simp at parentEq
  · intro left leftMember right rightMember parentEntry leftParent
      rightParent sameLabel
    simp at leftMember rightMember
    subst left
    subst right
    rfl

/-- One deepest insertion preserves all parent validity and proper-sibling
conditions. -/
theorem deepestParentedWitnessStep_preserves_proper
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (nodes : List (ParentedWitnessNode E))
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ProperParentedWitnessNodes neighbors
      (deepestParentedWitnessStep neighbors newLabel nodes) := by
  classical
  unfold deepestParentedWitnessStep
  split
  · exact proper
  · next maximum maximumEq =>
      let parentNode := deepestParentNode
        neighbors newLabel nodes maximum maximumEq
      let newNode : ParentedWitnessNode E :=
        ⟨⟨newLabel, maximum + 1⟩, some parentNode.entry⟩
      have parentNodeMember : parentNode ∈ nodes :=
        deepestParentNode_mem neighbors newLabel nodes maximum maximumEq
      have parentNodeDependent :
          newLabel ∈ closedNeighbors neighbors parentNode.entry.label :=
        deepestParentNode_dependent
          neighbors newLabel nodes maximum maximumEq
      have parentNodeDepth : parentNode.entry.depth = maximum :=
        deepestParentNode_depth neighbors newLabel nodes maximum maximumEq
      have oldEntryDepthLt (oldNode : ParentedWitnessNode E)
          (oldMember : oldNode ∈ nodes)
          (sameLabel : newLabel = oldNode.entry.label) :
          oldNode.entry.depth < maximum + 1 := by
        apply deepestWitnessStep_depth_gt neighbors newLabel
          (parentedEntries nodes) maximum maximumEq oldNode.entry
        · change oldNode.entry ∈
              nodes.map ParentedWitnessNode.entry
          exact List.mem_map_of_mem oldMember
        · rw [← sameLabel]
          exact Finset.mem_insert_self _ _
      change ProperParentedWitnessNodes neighbors (newNode :: nodes)
      constructor
      · have preserved := deepestWitnessStep_preserves_nodup
            neighbors newLabel (parentedEntries nodes) proper.entries_nodup
        change (⟨newLabel, maximum + 1⟩ ::
          parentedEntries nodes).Nodup
        simpa [deepestWitnessStep, maximumEq] using preserved
      · intro node nodeMember parentEntry parentEq
        rcases List.mem_cons.mp nodeMember with nodeEq | oldMember
        · subst node
          have entryEq : parentNode.entry = parentEntry := by
            exact Option.some.inj parentEq
          subst parentEntry
          change parentNode.entry ∈
            (newNode :: nodes).map ParentedWitnessNode.entry
          exact List.mem_map_of_mem
            (List.mem_cons_of_mem newNode parentNodeMember)
        · exact List.mem_cons_of_mem _
            (proper.parent_mem node oldMember parentEntry parentEq)
      · intro node nodeMember parentEntry parentEq
        rcases List.mem_cons.mp nodeMember with nodeEq | oldMember
        · subst node
          have entryEq : parentNode.entry = parentEntry := by
            exact Option.some.inj parentEq
          subst parentEntry
          exact parentNodeDependent
        · exact proper.parent_neighbor node oldMember parentEntry parentEq
      · intro node nodeMember parentEntry parentEq
        rcases List.mem_cons.mp nodeMember with nodeEq | oldMember
        · subst node
          have entryEq : parentNode.entry = parentEntry := by
            exact Option.some.inj parentEq
          subst parentEntry
          simp [newNode, parentNodeDepth]
        · exact proper.parent_depth node oldMember parentEntry parentEq
      · intro left leftMember right rightMember parentEntry leftParent
          rightParent sameLabel
        rcases List.mem_cons.mp leftMember with leftEq | leftOld
        · subst left
          rcases List.mem_cons.mp rightMember with rightEq | rightOld
          · subst right
            rfl
          · have parentEq : parentNode.entry = parentEntry :=
              Option.some.inj leftParent
            have rightDepth := proper.parent_depth
              right rightOld parentEntry rightParent
            have strict := oldEntryDepthLt right rightOld sameLabel
            have parentDepth : parentEntry.depth = maximum := by
              rw [← parentEq]
              exact parentNodeDepth
            exfalso
            simp [newNode] at sameLabel ⊢
            omega
        · rcases List.mem_cons.mp rightMember with rightEq | rightOld
          · subst right
            have parentEq : parentNode.entry = parentEntry :=
              Option.some.inj rightParent
            have leftDepth := proper.parent_depth
              left leftOld parentEntry leftParent
            have strict := oldEntryDepthLt left leftOld sameLabel.symm
            have parentDepth : parentEntry.depth = maximum := by
              rw [← parentEq]
              exact parentNodeDepth
            exfalso
            simp [newNode] at sameLabel ⊢
            omega
          · exact proper.children_label_injective left leftOld right
              rightOld parentEntry leftParent rightParent sameLabel

/-- Every reverse scan produces a certified proper parented witness forest. -/
theorem deepestParentedWitnessScanReversed_proper
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root : E) (older : List E) :
    ProperParentedWitnessNodes neighbors
      (deepestParentedWitnessScanReversed neighbors (root :: older)) := by
  simp only [deepestParentedWitnessScanReversed]
  induction older generalizing root with
  | nil => exact properParentedWitnessNodes_singleton neighbors root
  | cons label rest inductionHypothesis =>
      simp only [List.foldl_cons]
      have initialProper := properParentedWitnessNodes_singleton neighbors root
      have afterFirst := deepestParentedWitnessStep_preserves_proper
        neighbors label [⟨⟨root, 0⟩, none⟩] initialProper
      have foldPreserves : ∀ (remaining : List E)
          (current : List (ParentedWitnessNode E)),
          ProperParentedWitnessNodes neighbors current →
          ProperParentedWitnessNodes neighbors
            (remaining.foldl (fun nodes nextLabel =>
              deepestParentedWitnessStep neighbors nextLabel nodes) current) := by
        intro remaining
        induction remaining with
        | nil => intro current currentProper; exact currentProper
        | cons nextLabel tail tailHypothesis =>
            intro current currentProper
            simp only [List.foldl_cons]
            exact tailHypothesis _
              (deepestParentedWitnessStep_preserves_proper
                neighbors nextLabel current currentProper)
      exact foldPreserves rest _ afterFirst

/-- A proper parented forest with one distinguished depth-zero root and no
other parentless node.  This is the stronger invariant satisfied by an actual
scan started from one terminal occurrence. -/
structure RootedParentedWitnessNodes
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root : E)
    (nodes : List (ParentedWitnessNode E)) : Prop where
  proper : ProperParentedWitnessNodes neighbors nodes
  root_mem : ⟨⟨root, 0⟩, none⟩ ∈ nodes
  parent_none_eq_root : ∀ node ∈ nodes,
    node.parent = none → node = ⟨⟨root, 0⟩, none⟩

theorem rootedParentedWitnessNodes_singleton
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root : E) :
    RootedParentedWitnessNodes neighbors root
      [⟨⟨root, 0⟩, none⟩] := by
  refine ⟨properParentedWitnessNodes_singleton neighbors root, by simp, ?_⟩
  intro node nodeMember parentNone
  simpa using nodeMember

theorem deepestParentedWitnessStep_preserves_rooted
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root newLabel : E)
    (nodes : List (ParentedWitnessNode E))
    (rooted : RootedParentedWitnessNodes neighbors root nodes) :
    RootedParentedWitnessNodes neighbors root
      (deepestParentedWitnessStep neighbors newLabel nodes) := by
  classical
  refine ⟨deepestParentedWitnessStep_preserves_proper
    neighbors newLabel nodes rooted.proper, ?_, ?_⟩
  · unfold deepestParentedWitnessStep
    split
    · exact rooted.root_mem
    · exact List.mem_cons_of_mem _ rooted.root_mem
  · intro node nodeMember parentNone
    unfold deepestParentedWitnessStep at nodeMember
    split at nodeMember
    · exact rooted.parent_none_eq_root node nodeMember parentNone
    · rcases List.mem_cons.mp nodeMember with nodeEq | oldMember
      · subst node
        simp at parentNone
      · exact rooted.parent_none_eq_root node oldMember parentNone

/-- An arbitrary continuation fold preserves the distinguished-root
invariant. -/
theorem foldl_deepestParentedWitnessStep_preserves_rooted
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root : E) (labels : List E)
    (nodes : List (ParentedWitnessNode E))
    (rooted : RootedParentedWitnessNodes neighbors root nodes) :
    RootedParentedWitnessNodes neighbors root
      (labels.foldl (fun current label =>
        deepestParentedWitnessStep neighbors label current) nodes) := by
  induction labels generalizing nodes with
  | nil => exact rooted
  | cons label rest inductionHypothesis =>
      simp only [List.foldl_cons]
      exact inductionHypothesis _
        (deepestParentedWitnessStep_preserves_rooted
          neighbors root label nodes rooted)

/-- Every nonempty reverse scan is a single rooted proper witness tree, not
merely an unstructured forest. -/
theorem deepestParentedWitnessScanReversed_rooted
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root : E) (older : List E) :
    RootedParentedWitnessNodes neighbors root
      (deepestParentedWitnessScanReversed neighbors (root :: older)) := by
  simp only [deepestParentedWitnessScanReversed]
  exact foldl_deepestParentedWitnessStep_preserves_rooted
    neighbors root older [⟨⟨root, 0⟩, none⟩]
      (rootedParentedWitnessNodes_singleton neighbors root)

end TernarySyncAudit
