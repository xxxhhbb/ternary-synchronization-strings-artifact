import Mathlib

namespace TernarySyncAudit

open Finset

/-- One-step conditional avoidance bounds telescope to the LLL product bound. -/
theorem avoidance_mass_ge_product
    {ι : Type*} [DecidableEq ι]
    (mass : Finset ι → ℝ) (charge : ι → ℝ)
    (emptyMass : mass ∅ = 1)
    (chargeAtMostOne : ∀ e, charge e ≤ 1)
    (step : ∀ e S, e ∉ S → (1 - charge e) * mass S ≤ mass (insert e S))
    (S : Finset ι) :
    (∏ e ∈ S, (1 - charge e)) ≤ mass S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [emptyMass]
  | @insert e S he ih =>
      rw [Finset.prod_insert he]
      exact (mul_le_mul_of_nonneg_left ih (by
        linarith [chargeAtMostOne e])).trans (step e S he)

/-- The usual conditional event estimate implies the one-step recurrence. -/
theorem avoidance_step_of_bad_mass_bound
    {ι : Type*} [DecidableEq ι]
    (mass : Finset ι → ℝ) (badMass : ι → Finset ι → ℝ)
    (charge : ι → ℝ)
    (decomposition : ∀ e S, e ∉ S →
      mass (insert e S) = mass S - badMass e S)
    (conditionalBound : ∀ e S, e ∉ S →
      badMass e S ≤ charge e * mass S)
    (e : ι) (S : Finset ι) (he : e ∉ S) :
    (1 - charge e) * mass S ≤ mass (insert e S) := by
  rw [decomposition e S he]
  have := conditionalBound e S he
  nlinarith

/-- Product conclusion in the exact interface used by Appendix D. -/
theorem conditional_bounds_imply_product
    {ι : Type*} [DecidableEq ι]
    (mass : Finset ι → ℝ) (badMass : ι → Finset ι → ℝ)
    (charge : ι → ℝ)
    (emptyMass : mass ∅ = 1)
    (chargeAtMostOne : ∀ e, charge e ≤ 1)
    (decomposition : ∀ e S, e ∉ S →
      mass (insert e S) = mass S - badMass e S)
    (conditionalBound : ∀ e S, e ∉ S →
      badMass e S ≤ charge e * mass S)
    (S : Finset ι) :
    (∏ e ∈ S, (1 - charge e)) ≤ mass S := by
  apply avoidance_mass_ge_product mass charge emptyMass chargeAtMostOne
  intro e T he
  exact avoidance_step_of_bad_mass_bound mass badMass charge
    decomposition conditionalBound e T he

/-- For `0 ≤ u ≤ 1/2`, the paper's elementary factor estimate. -/
theorem exp_neg_two_mul_le_one_sub
    {u : ℝ} (hu : 0 ≤ u) (huHalf : u ≤ 1 / 2) :
    Real.exp (-2 * u) ≤ 1 - u := by
  have exponentIdentity : -2 * u = -(2 * u) := by ring
  rw [exponentIdentity, Real.exp_neg,
    inv_le_comm₀ (Real.exp_pos (2 * u)) (by linarith : 0 < 1 - u)]
  have expLinear : 1 + 2 * u ≤ Real.exp (2 * u) := by
    linarith [Real.add_one_le_exp (2 * u)]
  have factorNonnegative : 0 ≤ 1 - u := by linarith
  have algebraic : 1 ≤ (1 - u) * (1 + 2 * u) := by
    nlinarith [mul_nonneg hu (by linarith : 0 ≤ 1 - 2 * u)]
  have hdiv : 1 / (1 - u) ≤ Real.exp (2 * u) := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - u)).2
    simpa [mul_comm] using algebraic.trans
      (mul_le_mul_of_nonneg_left expLinear factorNonnegative)
  simpa [one_div] using hdiv

/-- The logarithm-free form of `∏(1-x(E)) ≥ exp(-2∑x(E))`. -/
theorem exp_neg_two_sum_le_product
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (charge : ι → ℝ)
    (chargeNonnegative : ∀ e ∈ S, 0 ≤ charge e)
    (chargeHalf : ∀ e ∈ S, charge e ≤ 1 / 2) :
    Real.exp (-2 * ∑ e ∈ S, charge e) ≤
      ∏ e ∈ S, (1 - charge e) := by
  calc
    Real.exp (-2 * ∑ e ∈ S, charge e) =
        ∏ e ∈ S, Real.exp (-2 * charge e) := by
          rw [Finset.mul_sum]
          simp only [Real.exp_sum]
    _ ≤ ∏ e ∈ S, (1 - charge e) := by
      exact Finset.prod_le_prod (fun e he => Real.exp_nonneg _) fun e he =>
        exp_neg_two_mul_le_one_sub (chargeNonnegative e he) (chargeHalf e he)

/-- Uniform finite probability turns a survival-probability bound into a count. -/
theorem uniform_survival_probability_to_count
    {good total : ℕ} {lower : ℝ} (totalPositive : 0 < total)
    (survivalLower : lower ≤ (good : ℝ) / total) :
    lower * total ≤ good := by
  exact (le_div_iff₀ (by exact_mod_cast totalPositive)).mp survivalLower

end TernarySyncAudit
