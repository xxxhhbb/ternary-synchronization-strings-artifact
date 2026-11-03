import Mathlib
import FormalAudit.ParentedWitnessShape

namespace TernarySyncAudit

/-- A target entry lies in the parent component below `rootEntry` within a
given number of parent edges. -/
def ParentedComponentContains
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ℕ → WitnessScanEntry E → WitnessScanEntry E → Prop
  | 0, rootEntry, targetEntry => targetEntry = rootEntry
  | height + 1, rootEntry, targetEntry =>
      targetEntry = rootEntry ∨
        ∃ childNode ∈ nodes,
          childNode.parent = some rootEntry ∧
          ParentedComponentContains proper height
            childNode.entry targetEntry

/-- A direct child extends every path ending at its parent by one level. -/
theorem ParentedComponentContains.extend_child
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ height rootEntry parentEntry,
      ParentedComponentContains proper height rootEntry parentEntry →
      ∀ childNode ∈ nodes,
        childNode.parent = some parentEntry →
        ParentedComponentContains proper (height + 1)
          rootEntry childNode.entry := by
  intro height
  induction height with
  | zero =>
      intro rootEntry parentEntry path childNode childMember parentEq
      have parentIsRoot : parentEntry = rootEntry := path
      subst parentEntry
      right
      exact ⟨childNode, childMember, parentEq, rfl⟩
  | succ height inductionHypothesis =>
      intro rootEntry parentEntry path childNode childMember parentEq
      rcases path with parentIsRoot | ⟨firstChild, firstMember,
        firstParent, subpath⟩
      · subst parentEntry
        right
        exact ⟨childNode, childMember, parentEq,
          Or.inl rfl⟩
      · right
        exact ⟨firstChild, firstMember, firstParent,
          inductionHypothesis firstChild.entry parentEntry subpath
            childNode childMember parentEq⟩

/-- One extra allowed level preserves component containment. -/
theorem ParentedComponentContains.succ
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ {height : ℕ} {rootEntry targetEntry : WitnessScanEntry E},
      ParentedComponentContains proper height rootEntry targetEntry →
      ParentedComponentContains proper (height + 1) rootEntry targetEntry := by
  intro height
  induction height with
  | zero =>
      intro rootEntry targetEntry path
      exact Or.inl path
  | succ height inductionHypothesis =>
      intro rootEntry targetEntry path
      rcases path with targetIsRoot |
        ⟨childNode, childMember, parentEq, subpath⟩
      · exact Or.inl targetIsRoot
      · exact Or.inr ⟨childNode, childMember, parentEq,
          inductionHypothesis subpath⟩

/-- Component containment is monotone in the allowed height. -/
theorem ParentedComponentContains.mono
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ {small large : ℕ} {rootEntry targetEntry : WitnessScanEntry E},
      small ≤ large →
      ParentedComponentContains proper small rootEntry targetEntry →
      ParentedComponentContains proper large rootEntry targetEntry := by
  intro small large rootEntry targetEntry heightLe path
  induction large, heightLe using Nat.le_induction with
  | base => exact path
  | succ large heightLe inductionHypothesis =>
      exact ParentedComponentContains.succ proper inductionHypothesis

/-- In a rooted parented scan, every node lies in the root component at a
height equal to its recorded depth. -/
theorem rooted_node_component_contains
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E} {root : E}
    {nodes : List (ParentedWitnessNode E)}
    (rooted : RootedParentedWitnessNodes neighbors root nodes) :
    ∀ depth (node : ParentedWitnessNode E),
      node ∈ nodes → node.entry.depth = depth →
      ParentedComponentContains rooted.proper depth
        ⟨root, 0⟩ node.entry := by
  intro depth
  induction depth with
  | zero =>
      intro node nodeMember nodeDepth
      cases parentEq : node.parent with
      | none =>
          have nodeIsRoot := rooted.parent_none_eq_root
            node nodeMember parentEq
          subst node
          rfl
      | some parentEntry =>
          have depthEq := rooted.proper.parent_depth
            node nodeMember parentEntry parentEq
          omega
  | succ depth inductionHypothesis =>
      intro node nodeMember nodeDepth
      cases parentEq : node.parent with
      | none =>
          have nodeIsRoot := rooted.parent_none_eq_root
            node nodeMember parentEq
          subst node
          simp at nodeDepth
      | some parentEntry =>
          have parentEntryMember := rooted.proper.parent_mem
            node nodeMember parentEntry parentEq
          change parentEntry ∈ nodes.map ParentedWitnessNode.entry at parentEntryMember
          obtain ⟨parentNode, parentMember, parentEntryEq⟩ :=
            List.mem_map.mp parentEntryMember
          have depthEq := rooted.proper.parent_depth
            node nodeMember parentEntry parentEq
          have parentDepth : parentNode.entry.depth = depth := by
            rw [parentEntryEq]
            omega
          have parentPath := inductionHypothesis
            parentNode parentMember parentDepth
          apply ParentedComponentContains.extend_child rooted.proper
            depth ⟨root, 0⟩ parentNode.entry parentPath node nodeMember
          simpa [parentEntryEq] using parentEq

/-- Deterministic labelled-depth linearization of the globally selected child
components.  It mirrors `parentedWitnessShape` but retains node depths. -/
noncomputable def parentedWitnessEntryLog
    {E : Type*} [Fintype E] [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ℕ → WitnessScanEntry E → List (WitnessScanEntry E)
  | 0, rootEntry => [rootEntry]
  | height + 1, rootEntry =>
      (Finset.univ.toList.map (fun childLabel :
          {candidate : E //
            candidate ∈ closedNeighbors neighbors rootEntry.label} =>
        match directParentedChild? proper rootEntry childLabel.1 with
        | none => []
        | some child =>
            parentedWitnessEntryLog proper height child.1.entry)).flatten ++
        [rootEntry]

/-- Every bounded component path appears in the deterministic entry
linearization at the same height. -/
theorem componentContains_mem_parentedWitnessEntryLog
    {E : Type*} [Fintype E] [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ height rootEntry targetEntry,
      ParentedComponentContains proper height rootEntry targetEntry →
      targetEntry ∈ parentedWitnessEntryLog proper height rootEntry := by
  intro height
  induction height with
  | zero =>
      intro rootEntry targetEntry path
      change targetEntry = rootEntry at path
      simp [parentedWitnessEntryLog, path]
  | succ height inductionHypothesis =>
      intro rootEntry targetEntry path
      rcases path with targetIsRoot |
        ⟨childNode, childMember, parentEq, subpath⟩
      · subst targetEntry
        simp [parentedWitnessEntryLog]
      · have neighbor := proper.parent_neighbor
            childNode childMember rootEntry parentEq
        let childLabel : {candidate : E //
            candidate ∈ closedNeighbors neighbors rootEntry.label} :=
          ⟨childNode.entry.label, neighbor⟩
        let child : DirectParentedChild proper rootEntry childLabel.1 :=
          ⟨childNode, childMember, parentEq, rfl⟩
        have subtreeMember := inductionHypothesis
          childNode.entry targetEntry subpath
        apply List.mem_append_left
        rw [List.mem_flatten]
        refine ⟨parentedWitnessEntryLog proper height childNode.entry, ?_,
          subtreeMember⟩
        rw [List.mem_map]
        refine ⟨childLabel, by simp, ?_⟩
        rw [directParentedChild?_eq_some
          proper rootEntry childLabel.1 child]

/-- Every entry emitted by the deterministic component linearization is an
entry of an actual node in the global parented list. -/
theorem mem_parentedWitnessEntryLog_mem_nodes
    {E : Type*} [Fintype E] [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ height rootEntry,
      rootEntry ∈ parentedEntries nodes →
      ∀ targetEntry,
        targetEntry ∈ parentedWitnessEntryLog proper height rootEntry →
        targetEntry ∈ parentedEntries nodes := by
  intro height
  induction height with
  | zero =>
      intro rootEntry rootMember targetEntry targetMember
      simp only [parentedWitnessEntryLog, List.mem_singleton] at targetMember
      rwa [targetMember]
  | succ height inductionHypothesis =>
      intro rootEntry rootMember targetEntry targetMember
      rw [parentedWitnessEntryLog, List.mem_append] at targetMember
      rcases targetMember with inChildren | atRoot
      · rw [List.mem_flatten] at inChildren
        obtain ⟨subtreeLog, subtreeLogMember, targetInSubtree⟩ := inChildren
        rw [List.mem_map] at subtreeLogMember
        obtain ⟨childLabel, childLabelMember, subtreeLogEq⟩ :=
          subtreeLogMember
        cases selectedEq : directParentedChild?
            proper rootEntry childLabel.1 with
        | none =>
            simp only [selectedEq] at subtreeLogEq
            subst subtreeLog
            simp at targetInSubtree
        | some child =>
            have childEntryMember : child.1.entry ∈ parentedEntries nodes := by
              change child.1.entry ∈
                nodes.map ParentedWitnessNode.entry
              exact List.mem_map_of_mem child.2.1
            simp only [selectedEq] at subtreeLogEq
            subst subtreeLog
            exact inductionHypothesis child.1.entry childEntryMember
              targetEntry targetInSubtree
      · simp only [List.mem_singleton] at atRoot
        rwa [atRoot]

end TernarySyncAudit
