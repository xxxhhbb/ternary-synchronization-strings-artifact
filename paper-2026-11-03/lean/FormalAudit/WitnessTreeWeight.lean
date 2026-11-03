import Mathlib

namespace TernarySyncAudit

open Finset

/-- Closed dependency neighborhood used for possible child labels in a proper
witness tree. -/
def closedNeighbors
    {E : Type*} [DecidableEq E] (neighbors : E → Finset E) (event : E) :
    Finset E :=
  insert event (neighbors event)

/-- Total weight of all proper rooted witness trees of height at most the
given truncation, encoded by its exact recursive generating function. -/
noncomputable def witnessTreeWeight
    {E : Type*} [DecidableEq E]
    (eventMass : E → ℝ) (neighbors : E → Finset E) : ℕ → E → ℝ
  | 0, _ => 0
  | height + 1, event =>
      eventMass event *
        ∏ child ∈ closedNeighbors neighbors event,
          (1 + witnessTreeWeight eventMass neighbors height child)

theorem witnessTreeWeight_nonnegative
    {E : Type*} [DecidableEq E]
    (eventMass : E → ℝ) (neighbors : E → Finset E)
    (massNonnegative : ∀ event, 0 ≤ eventMass event) :
    ∀ height event, 0 ≤ witnessTreeWeight eventMass neighbors height event := by
  intro height
  induction height with
  | zero =>
      intro event
      simp [witnessTreeWeight]
  | succ height inductionHypothesis =>
      intro event
      simp only [witnessTreeWeight]
      apply mul_nonneg (massNonnegative event)
      apply Finset.prod_nonneg
      intro child childIn
      linarith [inductionHypothesis child]

theorem one_add_charge_ratio
    {x : ℝ} (xLtOne : x < 1) :
    1 + x / (1 - x) = (1 - x)⁻¹ := by
  have denominatorNe : 1 - x ≠ 0 := by linarith
  field_simp
  ring

private theorem neighbor_complement_product_pos
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (charge : E → ℝ)
    (chargeLtOne : ∀ event, charge event < 1) (event : E) :
    0 < ∏ child ∈ neighbors event, (1 - charge child) := by
  apply Finset.prod_pos
  intro child childIn
  linarith [chargeLtOne child]

/-- The branching-process/witness-tree sum bound.  This is the numerical half
of the Moser--Tardos theorem: under the asymmetric LLL criterion, the total
proper-tree weight rooted at `event` is uniformly at most `x/(1-x)` at every
finite height. -/
theorem witnessTreeWeight_le_charge_ratio
    {E : Type*} [DecidableEq E]
    (eventMass charge : E → ℝ) (neighbors : E → Finset E)
    (massNonnegative : ∀ event, 0 ≤ eventMass event)
    (chargeNonnegative : ∀ event, 0 ≤ charge event)
    (chargeLtOne : ∀ event, charge event < 1)
    (selfNotNeighbor : ∀ event, event ∉ neighbors event)
    (criterion : ∀ event,
      eventMass event ≤
        charge event * ∏ child ∈ neighbors event, (1 - charge child)) :
    ∀ height event,
      witnessTreeWeight eventMass neighbors height event ≤
        charge event / (1 - charge event) := by
  intro height
  induction height with
  | zero =>
      intro event
      simp only [witnessTreeWeight]
      exact div_nonneg (chargeNonnegative event) (by linarith [chargeLtOne event])
  | succ height inductionHypothesis =>
      intro event
      let neighborhood := neighbors event
      let complementProduct : ℝ :=
        ∏ child ∈ neighborhood, (1 - charge child)
      have complementPositive : 0 < complementProduct := by
        dsimp [complementProduct, neighborhood]
        exact neighbor_complement_product_pos neighbors charge chargeLtOne event
      have eventComplementPositive : 0 < 1 - charge event := by
        linarith [chargeLtOne event]
      have factorBound :
          ∏ child ∈ closedNeighbors neighbors event,
              (1 + witnessTreeWeight eventMass neighbors height child) ≤
            ∏ child ∈ closedNeighbors neighbors event,
              (1 - charge child)⁻¹ := by
        apply Finset.prod_le_prod
        · intro child childIn
          linarith [witnessTreeWeight_nonnegative eventMass neighbors
            massNonnegative height child]
        · intro child childIn
          calc
            1 + witnessTreeWeight eventMass neighbors height child ≤
                1 + charge child / (1 - charge child) := by
              linarith [inductionHypothesis child]
            _ = (1 - charge child)⁻¹ :=
              one_add_charge_ratio (chargeLtOne child)
      have closedProductIdentity :
          (∏ child ∈ closedNeighbors neighbors event,
              (1 - charge child)⁻¹) =
            (1 - charge event)⁻¹ * complementProduct⁻¹ := by
        rw [closedNeighbors, Finset.prod_insert (selfNotNeighbor event)]
        change (1 - charge event)⁻¹ *
            (∏ child ∈ neighborhood, (1 - charge child)⁻¹) = _
        rw [Finset.prod_inv_distrib]
      have multiplierNonnegative :
          0 ≤ (1 - charge event)⁻¹ * complementProduct⁻¹ := by
        positivity
      calc
        witnessTreeWeight eventMass neighbors (height + 1) event =
            eventMass event *
              ∏ child ∈ closedNeighbors neighbors event,
                (1 + witnessTreeWeight eventMass neighbors height child) := by
          rfl
        _ ≤ eventMass event *
              ((1 - charge event)⁻¹ * complementProduct⁻¹) := by
          apply mul_le_mul_of_nonneg_left
          · exact factorBound.trans_eq closedProductIdentity
          · exact massNonnegative event
        _ ≤ (charge event * complementProduct) *
              ((1 - charge event)⁻¹ * complementProduct⁻¹) := by
          exact mul_le_mul_of_nonneg_right (by
            simpa [complementProduct, neighborhood] using criterion event)
            multiplierNonnegative
        _ = charge event / (1 - charge event) := by
          field_simp

end TernarySyncAudit
