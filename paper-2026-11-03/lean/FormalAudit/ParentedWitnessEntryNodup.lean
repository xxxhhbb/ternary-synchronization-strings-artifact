import Mathlib
import FormalAudit.ParentedWitnessCompleteness

namespace TernarySyncAudit

/-- A chain of actual parent pointers, directed from a descendant entry up to
an ancestor entry. -/
inductive ParentedEntryChain
    {E : Type*} (nodes : List (ParentedWitnessNode E)) :
    ℕ → WitnessScanEntry E → WitnessScanEntry E → Prop
  | refl (entry) : ParentedEntryChain nodes 0 entry entry
  | step {steps target parent root}
      (node : ParentedWitnessNode E) (nodeMember : node ∈ nodes)
      (entryEq : node.entry = target) (parentEq : node.parent = some parent)
      (rest : ParentedEntryChain nodes steps parent root) :
      ParentedEntryChain nodes (steps + 1) target root

/-- Append one parent edge at the ancestor end of a chain. -/
theorem ParentedEntryChain.append_parent
    {E : Type*} {nodes : List (ParentedWitnessNode E)} :
    ∀ {steps : ℕ} {target endpoint parent : WitnessScanEntry E},
      ParentedEntryChain nodes steps target endpoint →
      ∀ (endpointNode : ParentedWitnessNode E), endpointNode ∈ nodes →
        endpointNode.entry = endpoint → endpointNode.parent = some parent →
        ParentedEntryChain nodes (steps + 1) target parent := by
  intro steps target endpoint parent chain
  induction chain with
  | refl entry =>
      intro endpointNode endpointMember endpointEq parentEq
      exact ParentedEntryChain.step endpointNode endpointMember endpointEq
        parentEq (ParentedEntryChain.refl parent)
  | step firstNode firstMember firstEntryEq firstParentEq rest
      inductionHypothesis =>
      intro endpointNode endpointMember endpointEq parentEq
      exact ParentedEntryChain.step firstNode firstMember firstEntryEq
        firstParentEq
        (inductionHypothesis endpointNode endpointMember endpointEq parentEq)

/-- Every component-containment proof yields a genuine upward parent chain. -/
theorem componentContains_parentedEntryChain
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ height rootEntry targetEntry,
      ParentedComponentContains proper height rootEntry targetEntry →
      ∃ steps, ParentedEntryChain nodes steps targetEntry rootEntry := by
  intro height
  induction height with
  | zero =>
      intro rootEntry targetEntry contained
      have targetEq : targetEntry = rootEntry := contained
      subst targetEntry
      exact ⟨0, ParentedEntryChain.refl rootEntry⟩
  | succ height inductionHypothesis =>
      intro rootEntry targetEntry contained
      rcases contained with targetEq |
        ⟨childNode, childMember, parentEq, subpath⟩
      · subst targetEntry
        exact ⟨0, ParentedEntryChain.refl rootEntry⟩
      · obtain ⟨steps, chain⟩ := inductionHypothesis
          childNode.entry targetEntry subpath
        exact ⟨steps + 1,
          chain.append_parent childNode childMember rfl parentEq⟩

/-- Chain length is exactly the drop in recorded depth. -/
theorem ParentedEntryChain.depth_eq
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ {steps : ℕ} {target root : WitnessScanEntry E},
      ParentedEntryChain nodes steps target root →
      target.depth = root.depth + steps := by
  intro steps target root chain
  induction chain with
  | refl entry => simp
  | @step previousSteps previousTarget parent previousRoot node nodeMember
      entryEq parentEq rest inductionHypothesis =>
      have edgeDepth := proper.parent_depth node nodeMember parent parentEq
      rw [entryEq] at edgeDepth
      omega

/-- Duplicate-free entry keys make the endpoint of a fixed-length upward
chain unique. -/
theorem ParentedEntryChain.endpoint_unique
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ {steps : ℕ} {target leftRoot rightRoot : WitnessScanEntry E},
      ParentedEntryChain nodes steps target leftRoot →
      ParentedEntryChain nodes steps target rightRoot →
      leftRoot = rightRoot := by
  intro steps
  induction steps with
  | zero =>
      intro target leftRoot rightRoot leftChain rightChain
      cases leftChain
      cases rightChain
      rfl
  | succ steps inductionHypothesis =>
      intro target leftRoot rightRoot leftChain rightChain
      cases leftChain with
      | @step leftSteps leftTarget leftParent leftRoot' leftNode leftMember
          leftEntryEq leftParentEq leftRest =>
          cases rightChain with
          | @step rightSteps rightTarget rightParent rightRoot' rightNode
              rightMember rightEntryEq rightParentEq rightRest =>
              have nodeEq : leftNode = rightNode := by
                apply List.inj_on_of_nodup_map proper.entries_nodup
                  leftMember rightMember
                exact leftEntryEq.trans rightEntryEq.symm
              subst rightNode
              have parentEq : leftParent = rightParent := by
                exact Option.some.inj (leftParentEq.symm.trans rightParentEq)
              subst rightParent
              exact inductionHypothesis leftRest rightRest

/-- Two same-depth component roots containing the same target entry coincide. -/
theorem componentContains_same_depth_root
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes)
    {leftHeight rightHeight : ℕ}
    {leftRoot rightRoot target : WitnessScanEntry E}
    (leftContains : ParentedComponentContains proper
      leftHeight leftRoot target)
    (rightContains : ParentedComponentContains proper
      rightHeight rightRoot target)
    (sameDepth : leftRoot.depth = rightRoot.depth) :
    leftRoot = rightRoot := by
  obtain ⟨leftSteps, leftChain⟩ := componentContains_parentedEntryChain
    proper leftHeight leftRoot target leftContains
  obtain ⟨rightSteps, rightChain⟩ := componentContains_parentedEntryChain
    proper rightHeight rightRoot target rightContains
  have leftDepth := leftChain.depth_eq proper
  have rightDepth := rightChain.depth_eq proper
  have stepsEq : leftSteps = rightSteps := by omega
  subst rightSteps
  exact leftChain.endpoint_unique proper rightChain

/-- Membership in the deterministic entry linearization implies component
containment. -/
theorem mem_parentedWitnessEntryLog_componentContains
    {E : Type*} [Fintype E] [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ height rootEntry targetEntry,
      targetEntry ∈ parentedWitnessEntryLog proper height rootEntry →
      ParentedComponentContains proper height rootEntry targetEntry := by
  intro height
  induction height with
  | zero =>
      intro rootEntry targetEntry member
      simp only [parentedWitnessEntryLog, List.mem_singleton] at member
      exact member
  | succ height inductionHypothesis =>
      intro rootEntry targetEntry member
      rw [parentedWitnessEntryLog, List.mem_append] at member
      rcases member with inChildren | atRoot
      · rw [List.mem_flatten] at inChildren
        obtain ⟨subtreeLog, subtreeLogMember, targetMember⟩ := inChildren
        rw [List.mem_map] at subtreeLogMember
        obtain ⟨childLabel, childLabelMember, subtreeEq⟩ := subtreeLogMember
        cases selectedEq : directParentedChild?
            proper rootEntry childLabel.1 with
        | none =>
            simp only [selectedEq] at subtreeEq
            subst subtreeLog
            simp at targetMember
        | some child =>
            simp only [selectedEq] at subtreeEq
            subst subtreeLog
            exact Or.inr ⟨child.1, child.2.1, child.2.2.1,
              inductionHypothesis child.1.entry targetEntry targetMember⟩
      · exact Or.inl (by simpa using atRoot)

/-- The deterministic entry linearization of a proper parented structure has
no duplicate labelled-depth entries. -/
theorem parentedWitnessEntryLog_nodup
    {E : Type*} [Fintype E] [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ height rootEntry,
      rootEntry ∈ parentedEntries nodes →
      (parentedWitnessEntryLog proper height rootEntry).Nodup := by
  intro height
  induction height with
  | zero =>
      intro rootEntry rootMember
      simp [parentedWitnessEntryLog]
  | succ height inductionHypothesis =>
      intro rootEntry rootMember
      let childLogs := Finset.univ.toList.map (fun childLabel :
          {candidate : E //
            candidate ∈ closedNeighbors neighbors rootEntry.label} =>
        match directParentedChild? proper rootEntry childLabel.1 with
        | none => []
        | some child => parentedWitnessEntryLog proper height child.1.entry)
      have eachNodup : ∀ log ∈ childLogs, log.Nodup := by
        intro log logMember
        simp only [childLogs, List.mem_map] at logMember
        obtain ⟨childLabel, childLabelMember, logEq⟩ := logMember
        cases selectedEq : directParentedChild?
            proper rootEntry childLabel.1 with
        | none =>
            simp only [selectedEq] at logEq
            subst log
            simp
        | some child =>
            simp only [selectedEq] at logEq
            subst log
            apply inductionHypothesis child.1.entry
            change child.1.entry ∈ nodes.map ParentedWitnessNode.entry
            exact List.mem_map_of_mem child.2.1
      have pairwiseDisjoint : childLogs.Pairwise List.Disjoint := by
        dsimp [childLogs]
        rw [List.pairwise_map]
        apply (Finset.nodup_toList Finset.univ).imp
        intro leftLabel rightLabel labelNe
        cases leftSelected : directParentedChild?
            proper rootEntry leftLabel.1 with
        | none => simp
        | some leftChild =>
            cases rightSelected : directParentedChild?
                proper rootEntry rightLabel.1 with
            | none => simp
            | some rightChild =>
                rw [List.disjoint_left]
                intro target targetLeft targetRight
                have leftPath := mem_parentedWitnessEntryLog_componentContains
                  proper height leftChild.1.entry target targetLeft
                have rightPath := mem_parentedWitnessEntryLog_componentContains
                  proper height rightChild.1.entry target targetRight
                have leftDepth := proper.parent_depth leftChild.1
                  leftChild.2.1 rootEntry leftChild.2.2.1
                have rightDepth := proper.parent_depth rightChild.1
                  rightChild.2.1 rootEntry rightChild.2.2.1
                have rootsEq := componentContains_same_depth_root proper
                  leftPath rightPath (by omega)
                have labelsEq : leftLabel = rightLabel := by
                  apply Subtype.ext
                  calc
                    leftLabel.1 = leftChild.1.entry.label :=
                      leftChild.2.2.2.symm
                    _ = rightChild.1.entry.label :=
                      congrArg WitnessScanEntry.label rootsEq
                    _ = rightLabel.1 := rightChild.2.2.2
                exact labelNe labelsEq
      have flattenedNodup : childLogs.flatten.Nodup :=
        List.nodup_flatten.mpr ⟨eachNodup, pairwiseDisjoint⟩
      rw [parentedWitnessEntryLog]
      change (childLogs.flatten ++ [rootEntry]).Nodup
      apply List.Nodup.append flattenedNodup (by simp)
      rw [List.disjoint_left]
      intro target targetInChildren targetAtRoot
      simp only [List.mem_singleton] at targetAtRoot
      subst target
      rw [List.mem_flatten] at targetInChildren
      obtain ⟨subtreeLog, subtreeMember, rootInSubtree⟩ := targetInChildren
      simp only [childLogs, List.mem_map] at subtreeMember
      obtain ⟨childLabel, childLabelMember, subtreeEq⟩ := subtreeMember
      cases selectedEq : directParentedChild?
          proper rootEntry childLabel.1 with
      | none =>
          simp only [selectedEq] at subtreeEq
          subst subtreeLog
          simp at rootInSubtree
      | some child =>
          simp only [selectedEq] at subtreeEq
          subst subtreeLog
          have path := mem_parentedWitnessEntryLog_componentContains
            proper height child.1.entry rootEntry rootInSubtree
          obtain ⟨steps, chain⟩ := componentContains_parentedEntryChain
            proper height child.1.entry rootEntry path
          have chainDepth := chain.depth_eq proper
          have childDepth := proper.parent_depth child.1 child.2.1
            rootEntry child.2.2.1
          omega

end TernarySyncAudit
