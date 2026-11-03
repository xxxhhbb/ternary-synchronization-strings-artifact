import Mathlib
import FormalAudit.Abundance

namespace TernarySyncAudit

open Finset

/-- The one-step ratio in the Moser--Tardos expectation bound. -/
theorem charge_div_one_sub_le_two_mul
    {x : ℝ} (hx : 0 ≤ x) (hxHalf : x ≤ 1 / 2) :
    x / (1 - x) ≤ 2 * x := by
  have denominatorPositive : 0 < 1 - x := by linarith
  apply (div_le_iff₀ denominatorPositive).2
  nlinarith [mul_nonneg hx (by linarith : 0 ≤ 1 - 2 * x)]

/-- Summing the per-event Moser--Tardos estimate costs at most a factor two. -/
theorem total_resampling_charge_le_two_sum
    {ι : Type*} [DecidableEq ι]
    (events : Finset ι) (charge : ι → ℝ)
    (chargeNonnegative : ∀ e ∈ events, 0 ≤ charge e)
    (chargeHalf : ∀ e ∈ events, charge e ≤ 1 / 2) :
    (∑ e ∈ events, charge e / (1 - charge e)) ≤
      2 * ∑ e ∈ events, charge e := by
  calc
    (∑ e ∈ events, charge e / (1 - charge e))
        ≤ ∑ e ∈ events, 2 * charge e := by
          exact Finset.sum_le_sum fun e he =>
            charge_div_one_sub_le_two_mul
              (chargeNonnegative e he) (chargeHalf e he)
    _ = 2 * ∑ e ∈ events, charge e := by rw [Finset.mul_sum]

/-- The base `q=e^{-1/100}` is strictly below the rational `100/101`. -/
theorem explicit_charge_base_lt :
    Real.exp (-(1 : ℝ) / 100) < (100 : ℝ) / 101 := by
  have expLower : (101 : ℝ) / 100 < Real.exp ((1 : ℝ) / 100) := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) / 100 ≠ 0)
    norm_num at h ⊢
    exact h
  have exponentIdentity : -(1 : ℝ) / 100 = -((1 : ℝ) / 100) := by ring
  rw [exponentIdentity, Real.exp_neg]
  have leftPositive : 0 < Real.exp ((1 : ℝ) / 100) := Real.exp_pos _
  have rightPositive : (0 : ℝ) < 100 / 101 := by norm_num
  rw [inv_lt_comm₀ leftPositive rightPositive]
  norm_num
  exact expLower

/-- The geometric multiplier in the explicit charge tail is below `101`. -/
theorem explicit_geometric_multiplier_lt :
    (∑' k : ℕ, (Real.exp (-(1 : ℝ) / 100)) ^ k) < 101 := by
  let q := Real.exp (-(1 : ℝ) / 100)
  have qNonnegative : 0 ≤ q := Real.exp_nonneg _
  have qLt : q < 1 := (show q < (100 : ℝ) / 101 from explicit_charge_base_lt).trans
    (by norm_num)
  rw [tsum_geometric_of_lt_one qNonnegative qLt]
  have oneSubPositive : 0 < 1 - q := sub_pos.mpr qLt
  have hundredOnePositive : (0 : ℝ) < 101 := by norm_num
  rw [inv_lt_comm₀ oneSubPositive hundredOnePositive]
  dsimp [q]
  have qBound := explicit_charge_base_lt
  norm_num at qBound ⊢
  linarith

/-- The infinite tail that upper-bounds every finite family of event lengths. -/
theorem explicit_charge_tail_lt :
    (∑' k : ℕ, Real.exp (-((2000 + k : ℕ) : ℝ) / 100)) <
      101 * Real.exp (-20) := by
  have termIdentity (k : ℕ) :
      Real.exp (-((2000 + k : ℕ) : ℝ) / 100) =
        Real.exp (-20) * (Real.exp (-(1 : ℝ) / 100)) ^ k := by
    rw [show -((2000 + k : ℕ) : ℝ) / 100 =
        -20 + (k : ℝ) * (-(1 : ℝ) / 100) by
          push_cast
          ring]
    rw [Real.exp_add, Real.exp_nat_mul]
  calc
    (∑' k : ℕ, Real.exp (-((2000 + k : ℕ) : ℝ) / 100)) =
        ∑' k : ℕ, Real.exp (-20) *
          (Real.exp (-(1 : ℝ) / 100)) ^ k := by
            exact tsum_congr termIdentity
    _ = Real.exp (-20) *
          ∑' k : ℕ, (Real.exp (-(1 : ℝ) / 100)) ^ k := by
            rw [tsum_mul_left]
    _ < Real.exp (-20) * 101 := by
      exact mul_lt_mul_of_pos_left explicit_geometric_multiplier_lt
        (Real.exp_pos _)
    _ = 101 * Real.exp (-20) := by ring

/-- The paper's total expected resampling bound is in particular at most `M`. -/
theorem explicit_total_resampling_le_length
    {ι : Type*} [DecidableEq ι]
    (events : Finset ι) (charge : ι → ℝ) {M : ℝ}
    (Mnonnegative : 0 ≤ M)
    (chargeNonnegative : ∀ e ∈ events, 0 ≤ charge e)
    (chargeHalf : ∀ e ∈ events, charge e ≤ 1 / 2)
    (chargeSum : (∑ e ∈ events, charge e) ≤ 101 * Real.exp (-20) * M) :
    (∑ e ∈ events, charge e / (1 - charge e)) ≤ M := by
  have ratioBound := total_resampling_charge_le_two_sum
    events charge chargeNonnegative chargeHalf
  have expSmall : 202 * Real.exp (-20) < (1 : ℝ) := by
    rw [Real.exp_neg]
    have invBound : (Real.exp 20)⁻¹ < (1 : ℝ) / 624000 := by
      simpa [one_div] using
        (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 624000)
          exp_twenty_gt_624000)
    nlinarith
  calc
    (∑ e ∈ events, charge e / (1 - charge e))
        ≤ 2 * ∑ e ∈ events, charge e := ratioBound
    _ ≤ 202 * Real.exp (-20) * M := by nlinarith
    _ ≤ M := by nlinarith

/-- Algebraic Markov bound used to turn finite expectation into vanishing tails. -/
theorem termination_tail_bound
    {expected tailProbability steps : ℝ}
    (stepsPositive : 0 < steps)
    (markovNumerator : tailProbability * steps ≤ expected) :
    tailProbability ≤ expected / steps := by
  exact (le_div_iff₀ stepsPositive).2 markovNumerator

end TernarySyncAudit
