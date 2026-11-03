import Mathlib
import FormalAudit.ParentedWitnessInvariant
import FormalAudit.ProperWitnessShape

namespace TernarySyncAudit

/-- A direct child of a labelled-depth root entry with one prescribed label. -/
abbrev DirectParentedChild
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (_proper : ProperParentedWitnessNodes neighbors nodes)
    (rootEntry : WitnessScanEntry E) (childLabel : E) :=
  {node : ParentedWitnessNode E //
    node ∈ nodes ∧ node.parent = some rootEntry ∧
      node.entry.label = childLabel}

/-- Properness plus duplicate-free entries makes the direct child in one
label slot unique. -/
theorem directParentedChild_subsingleton
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes)
    (rootEntry : WitnessScanEntry E) (childLabel : E)
    (left right : DirectParentedChild proper rootEntry childLabel) :
    left = right := by
  apply Subtype.ext
  apply List.inj_on_of_nodup_map proper.entries_nodup
    left.2.1 right.2.1
  exact proper.children_label_injective
    left.1 left.2.1 right.1 right.2.1 rootEntry
      left.2.2.1 right.2.2.1
      (left.2.2.2.trans right.2.2.2.symm)

/-- The unique direct child in a label slot, when it exists. -/
noncomputable def directParentedChild?
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes)
    (rootEntry : WitnessScanEntry E) (childLabel : E) :
    Option (DirectParentedChild proper rootEntry childLabel) := by
  classical
  exact if existsChild : Nonempty
      (DirectParentedChild proper rootEntry childLabel) then
    some (Classical.choice existsChild)
  else none

/-- Any supplied direct child is exactly the child returned by the selector. -/
theorem directParentedChild?_eq_some
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes)
    (rootEntry : WitnessScanEntry E) (childLabel : E)
    (child : DirectParentedChild proper rootEntry childLabel) :
    directParentedChild? proper rootEntry childLabel = some child := by
  classical
  unfold directParentedChild?
  have nonempty : Nonempty
      (DirectParentedChild proper rootEntry childLabel) := ⟨child⟩
  simp only [nonempty, dite_true, Option.some.injEq]
  exact directParentedChild_subsingleton proper rootEntry childLabel _ child

/-- Encode the component below a root entry into the dependent proper witness
shape type.  Height zero below the root keeps only that root. -/
noncomputable def parentedWitnessShape
    {E : Type u} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes) :
    ∀ height (rootEntry : WitnessScanEntry E),
      ProperWitnessShape neighbors (height + 1) rootEntry.label
  | 0, _rootEntry => fun _ => none
  | height + 1, rootEntry => fun childLabel =>
      match directParentedChild? proper rootEntry childLabel.1 with
      | none => none
      | some child =>
          some (child.2.2.2 ▸
            parentedWitnessShape proper height child.1.entry)

/-- Every actual direct child is present in the corresponding slot of the
encoding as soon as one recursive level is available. -/
theorem parentedWitnessShape_child_present
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes)
    (height : ℕ) (rootEntry : WitnessScanEntry E)
    (childNode : ParentedWitnessNode E) (childMember : childNode ∈ nodes)
    (parentEq : childNode.parent = some rootEntry) :
    ∃ childLabel : {candidate : E //
        candidate ∈ closedNeighbors neighbors rootEntry.label},
      (parentedWitnessShape proper (height + 1) rootEntry childLabel).isSome := by
  have neighbor := proper.parent_neighbor
    childNode childMember rootEntry parentEq
  let childLabel : {candidate : E //
      candidate ∈ closedNeighbors neighbors rootEntry.label} :=
    ⟨childNode.entry.label, neighbor⟩
  let child : DirectParentedChild proper rootEntry childLabel.1 :=
    ⟨childNode, childMember, parentEq, rfl⟩
  refine ⟨childLabel, ?_⟩
  simp only [parentedWitnessShape]
  rw [directParentedChild?_eq_some proper rootEntry childLabel.1 child]
  simp

/-- Every encoded scan tree is one of the finite proper shapes enumerated in
the witness-tree weight calculation. -/
theorem parentedWitnessShape_mem
    {E : Type*} [Fintype E] [DecidableEq E]
    {neighbors : E → Finset E}
    {nodes : List (ParentedWitnessNode E)}
    (proper : ProperParentedWitnessNodes neighbors nodes)
    (height : ℕ) (rootEntry : WitnessScanEntry E) :
    parentedWitnessShape proper height rootEntry ∈
      properWitnessShapes neighbors (height + 1) rootEntry.label := by
  exact mem_properWitnessShapes neighbors (height + 1) rootEntry.label
    (parentedWitnessShape proper height rootEntry)

end TernarySyncAudit
