import Mathlib
import FormalAudit.WitnessForest
import FormalAudit.ProperWitnessShape

namespace TernarySyncAudit

/-- Occurrences that are direct children of `root` and have one prescribed
label in a certified proper witness forest. -/
abbrev DirectWitnessChild
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E} {log : List E}
    (forest : ProperWitnessForest neighbors log)
    (root : Fin log.length) (childLabel : E) :=
  {index : Fin log.length //
    forest.parent index = some root ∧ log.get index = childLabel}

/-- The unique direct child with a prescribed label, when it exists. -/
noncomputable def directWitnessChild?
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E} {log : List E}
    (forest : ProperWitnessForest neighbors log)
    (root : Fin log.length) (childLabel : E) :
    Option (DirectWitnessChild forest root childLabel) := by
  classical
  exact if existsChild : Nonempty (DirectWitnessChild forest root childLabel) then
    some (Classical.choice existsChild)
  else none

/-- Direct children with a fixed label are unique by forest properness. -/
theorem directWitnessChild_subsingleton
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E} {log : List E}
    (forest : ProperWitnessForest neighbors log)
    (root : Fin log.length) (childLabel : E)
    (left right : DirectWitnessChild forest root childLabel) :
    left = right := by
  apply Subtype.ext
  exact forest.children_label_injective root left.1 right.1
    left.2.1 right.2.1 (left.2.2.trans right.2.2.symm)

/-- A selected direct child carries the advertised parent and label facts. -/
theorem directWitnessChild_selected
    {E : Type*} [DecidableEq E]
    {neighbors : E → Finset E} {log : List E}
    (forest : ProperWitnessForest neighbors log)
    (root : Fin log.length) (childLabel : E)
    (child : DirectWitnessChild forest root childLabel)
    (_selected : directWitnessChild? forest root childLabel = some child) :
    forest.parent child.1 = some root ∧ log.get child.1 = childLabel :=
  child.2

/-- Finite-height encoding of one component of a proper auxiliary forest into
the dependent proper-shape type.  Height one keeps only the root; each extra
height recursively includes the unique direct child of every allowed label. -/
noncomputable def witnessForestShape
    {E : Type u} [Fintype E] [DecidableEq E]
    {neighbors : E → Finset E} {log : List E}
    (forest : ProperWitnessForest neighbors log) :
    ∀ height (root : Fin log.length),
      ProperWitnessShape neighbors (height + 1) (log.get root)
  | 0, _root => fun _ => none
  | height + 1, root => fun childLabel =>
      match directWitnessChild? forest root childLabel.1 with
      | none => none
      | some child =>
          some (child.2.2 ▸ witnessForestShape forest height child.1)

/-- The forest encoding is one of the explicitly enumerated proper shapes. -/
theorem witnessForestShape_mem
    {E : Type*} [Fintype E] [DecidableEq E]
    {neighbors : E → Finset E} {log : List E}
    (forest : ProperWitnessForest neighbors log)
    (height : ℕ) (root : Fin log.length) :
    witnessForestShape forest height root ∈
      properWitnessShapes neighbors (height + 1) (log.get root) := by
  exact mem_properWitnessShapes neighbors (height + 1)
    (log.get root) (witnessForestShape forest height root)

/-- At positive truncation height, every existing direct child is represented
in its unique label slot by a recursively encoded subtree. -/
theorem witnessForestShape_child_present
    {E : Type*} [Fintype E] [DecidableEq E]
    {neighbors : E → Finset E} {log : List E}
    (forest : ProperWitnessForest neighbors log)
    (height : ℕ) (root childIndex : Fin log.length)
    (parentEq : forest.parent childIndex = some root) :
    ∃ childLabel : {candidate : E //
        candidate ∈ closedNeighbors neighbors (log.get root)},
      (witnessForestShape forest (height + 1) root childLabel).isSome := by
  have neighbor := forest.parent_neighbor childIndex root parentEq
  let childLabel : {candidate : E //
      candidate ∈ closedNeighbors neighbors (log.get root)} :=
    ⟨log.get childIndex, neighbor⟩
  let child : DirectWitnessChild forest root childLabel.1 :=
    ⟨childIndex, parentEq, rfl⟩
  have nonempty : Nonempty (DirectWitnessChild forest root childLabel.1) :=
    ⟨child⟩
  have selectedSome : (directWitnessChild? forest root childLabel.1).isSome := by
    simp [directWitnessChild?, nonempty]
  refine ⟨childLabel, ?_⟩
  simp only [witnessForestShape]
  cases selectedEq : directWitnessChild? forest root childLabel.1 with
  | none => simp [selectedEq] at selectedSome
  | some selected => simp

end TernarySyncAudit
