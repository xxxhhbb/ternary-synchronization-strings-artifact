import Mathlib
import FormalAudit.DeepestWitnessScan

namespace TernarySyncAudit

/-- A deepest-scan node together with the labelled-depth key of its selected
parent.  The root has no parent. -/
structure ParentedWitnessNode (E : Type*) where
  entry : WitnessScanEntry E
  parent : Option (WitnessScanEntry E)
deriving DecidableEq

/-- Forget parent pointers. -/
def parentedEntries
    {E : Type*} (nodes : List (ParentedWitnessNode E)) :
    List (WitnessScanEntry E) :=
  nodes.map ParentedWitnessNode.entry

/-- A maximum-depth dependent node exists whenever the maximum depth does. -/
theorem deepestParentNode_exists
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (nodes : List (ParentedWitnessNode E)) (maximum : ℕ)
    (maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel (parentedEntries nodes)) =
        some maximum) :
    ∃ parentNode ∈ nodes,
      newLabel ∈ closedNeighbors neighbors parentNode.entry.label ∧
      parentNode.entry.depth = maximum := by
  obtain ⟨parentEntry, parentEntryMember, dependent, depthEq⟩ :=
    deepestWitnessStep_parent_exists neighbors newLabel
      (parentedEntries nodes) maximum maximumEq
  have parentEntryMember' :
      parentEntry ∈ nodes.map ParentedWitnessNode.entry := by
    simpa [parentedEntries] using parentEntryMember
  obtain ⟨parentNode, parentNodeMember, parentNodeEq⟩ :=
    List.mem_map.mp parentEntryMember'
  subst parentEntry
  exact ⟨parentNode, parentNodeMember, dependent, depthEq⟩

/-- A fixed classical choice of maximum-depth dependent parent. -/
noncomputable def deepestParentNode
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (nodes : List (ParentedWitnessNode E)) (maximum : ℕ)
    (maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel (parentedEntries nodes)) =
        some maximum) : ParentedWitnessNode E :=
  Classical.choose
    (deepestParentNode_exists neighbors newLabel nodes maximum maximumEq)

theorem deepestParentNode_mem
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (nodes : List (ParentedWitnessNode E)) (maximum : ℕ)
    (maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel (parentedEntries nodes)) =
        some maximum) :
    deepestParentNode neighbors newLabel nodes maximum maximumEq ∈ nodes :=
  (Classical.choose_spec
    (deepestParentNode_exists neighbors newLabel nodes maximum maximumEq)).1

theorem deepestParentNode_dependent
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (nodes : List (ParentedWitnessNode E)) (maximum : ℕ)
    (maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel (parentedEntries nodes)) =
        some maximum) :
    newLabel ∈ closedNeighbors neighbors
      (deepestParentNode neighbors newLabel nodes maximum maximumEq).entry.label :=
  (Classical.choose_spec
    (deepestParentNode_exists neighbors newLabel nodes maximum maximumEq)).2.1

theorem deepestParentNode_depth
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (nodes : List (ParentedWitnessNode E)) (maximum : ℕ)
    (maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel (parentedEntries nodes)) =
        some maximum) :
    (deepestParentNode neighbors newLabel nodes maximum maximumEq).entry.depth =
      maximum :=
  (Classical.choose_spec
    (deepestParentNode_exists neighbors newLabel nodes maximum maximumEq)).2.2

/-- One deepest-dependent insertion with an actual maximum-depth parent
recorded. -/
noncomputable def deepestParentedWitnessStep
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (nodes : List (ParentedWitnessNode E)) :
    List (ParentedWitnessNode E) :=
  match maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel (parentedEntries nodes)) with
  | none => nodes
  | some maximum =>
      let parentNode := deepestParentNode
        neighbors newLabel nodes maximum maximumEq
      ⟨⟨newLabel, maximum + 1⟩, some parentNode.entry⟩ :: nodes

/-- Forgetting parent pointers commutes exactly with one deepest scan step. -/
theorem parentedEntries_deepestParentedWitnessStep
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (nodes : List (ParentedWitnessNode E)) :
    parentedEntries
        (deepestParentedWitnessStep neighbors newLabel nodes) =
      deepestWitnessStep neighbors newLabel (parentedEntries nodes) := by
  classical
  unfold deepestParentedWitnessStep deepestWitnessStep
  dsimp only
  split <;> rename_i maximumEq
  · have maximumEq' := maximumEq
    simp only [parentedEntries] at maximumEq'
    simp only [parentedEntries]
    rw [maximumEq']
  · have maximumEq' := maximumEq
    simp only [parentedEntries] at maximumEq'
    simp only [parentedEntries, List.map_cons]
    rw [maximumEq']

/-- Parent pointers chosen by an insertion refer to a pre-existing dependent
node exactly one depth level above the new node. -/
theorem deepestParentedWitnessStep_head_parent
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (nodes : List (ParentedWitnessNode E)) (maximum : ℕ)
    (maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel (parentedEntries nodes)) =
        some maximum) :
    ∃ parentNode ∈ nodes,
      (deepestParentedWitnessStep neighbors newLabel nodes).head? =
        some ⟨⟨newLabel, maximum + 1⟩, some parentNode.entry⟩ ∧
      newLabel ∈ closedNeighbors neighbors parentNode.entry.label ∧
      parentNode.entry.depth = maximum := by
  classical
  unfold deepestParentedWitnessStep
  split
  · next absentEq => simp_all
  · next selectedMaximum selectedEq =>
      have maximumSame : selectedMaximum = maximum := by
        exact Option.some.inj (selectedEq.symm.trans maximumEq)
      subst selectedMaximum
      let parentNode := deepestParentNode
        neighbors newLabel nodes maximum selectedEq
      refine ⟨parentNode,
        deepestParentNode_mem neighbors newLabel nodes maximum selectedEq,
        rfl,
        deepestParentNode_dependent neighbors newLabel nodes maximum selectedEq,
        deepestParentNode_depth neighbors newLabel nodes maximum selectedEq⟩

/-- Run the parented deepest scan on reverse-chronological labels. -/
noncomputable def deepestParentedWitnessScanReversed
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) : List E → List (ParentedWitnessNode E)
  | [] => []
  | root :: older =>
      older.foldl (fun nodes label =>
        deepestParentedWitnessStep neighbors label nodes)
        [⟨⟨root, 0⟩, none⟩]

/-- Forgetting parent pointers commutes with every fold step. -/
theorem parentedEntries_foldl_deepestParentedWitnessStep
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (labels : List E)
    (nodes : List (ParentedWitnessNode E)) :
    parentedEntries
        (labels.foldl (fun current label =>
          deepestParentedWitnessStep neighbors label current) nodes) =
      labels.foldl (fun current label =>
        deepestWitnessStep neighbors label current) (parentedEntries nodes) := by
  induction labels generalizing nodes with
  | nil => rfl
  | cons label rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      exact congrArg
        (fun initial => rest.foldl
          (fun current nextLabel =>
            deepestWitnessStep neighbors nextLabel current) initial)
        (parentedEntries_deepestParentedWitnessStep
          neighbors label nodes)

/-- The parented scan projects to the already verified deepest-entry scan. -/
theorem parentedEntries_deepestParentedWitnessScanReversed
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (reversed : List E) :
    parentedEntries (deepestParentedWitnessScanReversed neighbors reversed) =
      deepestWitnessScanReversed neighbors reversed := by
  cases reversed with
  | nil => rfl
  | cons root older =>
      simpa [deepestParentedWitnessScanReversed,
        deepestWitnessScanReversed, parentedEntries] using
        parentedEntries_foldl_deepestParentedWitnessStep
          neighbors older [⟨⟨root, 0⟩, none⟩]

end TernarySyncAudit
