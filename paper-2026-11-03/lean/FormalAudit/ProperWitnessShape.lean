import Mathlib
import FormalAudit.WitnessTreeWeight

namespace TernarySyncAudit

/-- A proper rooted witness-tree shape of bounded height.  At a node labelled
`event`, there is at most one child of each label in its closed dependency
neighborhood.  Height zero has no trees. -/
def ProperWitnessShape
    {E : Type u} [DecidableEq E] (neighbors : E → Finset E) :
    ℕ → E → Type u
  | 0, _ => PEmpty
  | height + 1, event =>
      ∀ child : {candidate : E //
        candidate ∈ closedNeighbors neighbors event},
        Option (ProperWitnessShape neighbors height child.1)

/-- Explicit finite enumeration of all bounded proper witness shapes. -/
@[reducible] noncomputable def properWitnessShapeFintype
    {E : Type u} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) :
    ∀ height event, Fintype (ProperWitnessShape neighbors height event)
  | 0, event => by
      change Fintype PEmpty
      infer_instance
  | height + 1, event => by
      change Fintype (∀ child : {candidate : E //
        candidate ∈ closedNeighbors neighbors event},
          Option (ProperWitnessShape neighbors height child.1))
      letI (child : {candidate : E //
          candidate ∈ closedNeighbors neighbors event}) :
          Fintype (ProperWitnessShape neighbors height child.1) :=
        properWitnessShapeFintype neighbors height child.1
      infer_instance

@[reducible] noncomputable instance properWitnessShape_instFintype
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) (height : ℕ) (event : E) :
    Fintype (ProperWitnessShape neighbors height event) :=
  properWitnessShapeFintype neighbors height event

/-- Product of event masses over all nodes of a proper witness shape. -/
noncomputable def properWitnessShapeMass
    {E : Type*} [DecidableEq E]
    (eventMass : E → ℝ) (neighbors : E → Finset E) :
    ∀ height event, ProperWitnessShape neighbors height event → ℝ
  | 0, _, shape => nomatch shape
  | height + 1, event, children =>
      eventMass event *
        ∏ child, match children child with
          | none => 1
          | some subtree =>
              properWitnessShapeMass eventMass neighbors height child.1 subtree

/-- Explicit finite set of every proper witness shape of a given height and
root label. -/
noncomputable def properWitnessShapes
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) :
    ∀ height event, Finset (ProperWitnessShape neighbors height event)
  | 0, _ => ∅
  | height + 1, event => by
      classical
      exact Fintype.piFinset fun child =>
        insert none ((properWitnessShapes neighbors height child.1).image some)

/-- The explicit enumeration contains every bounded proper witness shape. -/
theorem mem_properWitnessShapes
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) :
    ∀ height event (shape : ProperWitnessShape neighbors height event),
      shape ∈ properWitnessShapes neighbors height event := by
  intro height
  induction height with
  | zero =>
      intro event shape
      exact PEmpty.elim shape
  | succ height inductionHypothesis =>
      intro event shape
      rw [properWitnessShapes]
      apply Fintype.mem_piFinset.mpr
      intro child
      cases subtreeEquality : shape child with
      | none => simp
      | some subtree =>
          simp only [Finset.mem_insert, Option.some_ne_none, Finset.mem_image]
          right
          exact ⟨subtree, inductionHypothesis child.1 subtree, rfl⟩

/-- The recursive quantity `witnessTreeWeight` is exactly the total mass of
all bounded proper witness shapes, not merely an algebraic upper bound. -/
theorem sum_properWitnessShapeMass_eq_witnessTreeWeight
    {E : Type*} [Fintype E] [DecidableEq E]
    (eventMass : E → ℝ) (neighbors : E → Finset E) :
    ∀ height event,
      (∑ shape ∈ properWitnessShapes neighbors height event,
        properWitnessShapeMass eventMass neighbors height event shape) =
      witnessTreeWeight eventMass neighbors height event := by
  intro height
  induction height with
  | zero =>
      intro event
      simp [properWitnessShapes, witnessTreeWeight]
  | succ height inductionHypothesis =>
      intro event
      classical
      let Child := {candidate : E //
        candidate ∈ closedNeighbors neighbors event}
      let choices : ∀ child : Child,
          Finset (Option (ProperWitnessShape neighbors height child.1)) :=
        fun child => insert none
          ((properWitnessShapes neighbors height child.1).image some)
      let factor : ∀ child : Child,
          Option (ProperWitnessShape neighbors height child.1) → ℝ :=
        fun child choice => match choice with
          | none => 1
          | some subtree => properWitnessShapeMass
              eventMass neighbors height child.1 subtree
      have optionSum (child : {candidate : E //
          candidate ∈ closedNeighbors neighbors event}) :
          (∑ choice ∈ choices child, factor child choice) =
            1 + witnessTreeWeight eventMass neighbors height child.1 := by
        simp [choices, factor, inductionHypothesis child.1]
      have productExpansion :
          (∑ children ∈ Fintype.piFinset choices,
              ∏ child, factor child (children child)) =
            ∏ child, ∑ choice ∈ choices child, factor child choice := by
        exact (Finset.prod_univ_sum choices factor).symm
      simp only [properWitnessShapes, properWitnessShapeMass,
        witnessTreeWeight]
      rw [← Finset.mul_sum]
      congr 1
      change (∑ children ∈ Fintype.piFinset choices,
          ∏ child, factor child (children child)) = _
      rw [productExpansion]
      simp_rw [optionSum]
      exact Finset.prod_attach (closedNeighbors neighbors event)
        (fun child => (1 +
          witnessTreeWeight eventMass neighbors height child : ℝ))

/-- Under the asymmetric LLL criterion, the total mass of all explicitly
enumerated proper witness shapes at any finite height is at most `x/(1-x)`. -/
theorem sum_properWitnessShapeMass_le_charge_ratio
    {E : Type*} [Fintype E] [DecidableEq E]
    (eventMass charge : E → ℝ) (neighbors : E → Finset E)
    (massNonnegative : ∀ event, 0 ≤ eventMass event)
    (chargeNonnegative : ∀ event, 0 ≤ charge event)
    (chargeLtOne : ∀ event, charge event < 1)
    (selfNotNeighbor : ∀ event, event ∉ neighbors event)
    (criterion : ∀ event,
      eventMass event ≤
        charge event * ∏ child ∈ neighbors event, (1 - charge child))
    (height : ℕ) (event : E) :
    (∑ shape ∈ properWitnessShapes neighbors height event,
      properWitnessShapeMass eventMass neighbors height event shape) ≤
      charge event / (1 - charge event) := by
  rw [sum_properWitnessShapeMass_eq_witnessTreeWeight]
  exact witnessTreeWeight_le_charge_ratio
    eventMass charge neighbors massNonnegative chargeNonnegative
      chargeLtOne selfNotNeighbor criterion height event

end TernarySyncAudit
