import Mathlib

namespace TernarySyncAudit

/--
The numerical core of the equal-block to arbitrary-interval lemma.  Here `a`
is the shorter interval length and `z` is the length difference.  The two
lower bounds on edit distance are `z` and `2 * eta * a - z`.
-/
theorem unequal_interval_max_bound
    {eta a z : ℝ} (etaNonnegative : 0 ≤ eta)
    (_aNonnegative : 0 ≤ a) (_zNonnegative : 0 ≤ z) :
    eta / (2 + eta) * (2 * a + z) ≤ max z (2 * eta * a - z) := by
  have denominatorPositive : 0 < 2 + eta := by linarith
  by_cases shortDifference : z ≤ eta * a
  · have secondTermBound :
        eta / (2 + eta) * (2 * a + z) ≤ 2 * eta * a - z := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ denominatorPositive).2
      have productNonnegative :
          0 ≤ (1 + eta) * (eta * a - z) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    exact secondTermBound.trans (le_max_right _ _)
  · have longDifference : eta * a ≤ z := by linarith
    have firstTermBound : eta / (2 + eta) * (2 * a + z) ≤ z := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ denominatorPositive).2
      nlinarith
    exact firstTermBound.trans (le_max_left _ _)

/-- Any smaller normalized gap is strict once the shorter interval is nonempty. -/
theorem strict_gap_from_unequal_interval_bounds
    {eta gap a z editDistance : ℝ}
    (etaNonnegative : 0 ≤ eta) (aPositive : 0 < a) (zNonnegative : 0 ≤ z)
    (gapStrict : gap < eta / (2 + eta))
    (editLower : max z (2 * eta * a - z) ≤ editDistance) :
    gap * (2 * a + z) < editDistance := by
  have totalPositive : 0 < 2 * a + z := by linarith
  have ratioStrict :
      gap * (2 * a + z) < eta / (2 + eta) * (2 * a + z) := by
    exact mul_lt_mul_of_pos_right gapStrict totalPositive
  have ratioLower :=
    unequal_interval_max_bound etaNonnegative (le_of_lt aPositive) zNonnegative
  exact ratioStrict.trans_le (ratioLower.trans editLower)

/-- The paper's convenient gap `eta/3` is strictly below the sharp ratio. -/
theorem eta_over_three_is_strict
    {eta : ℝ} (etaPositive : 0 < eta) (etaLessThanOne : eta < 1) :
    eta / 3 < eta / (2 + eta) := by
  have denominatorPositive : 0 < 2 + eta := by linarith
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 3) denominatorPositive]
  nlinarith

/-- Exact specialization used in the headline theorem. -/
theorem headline_gap_is_strict :
    (1 : ℝ) / 6000 < ((1 : ℝ) / 2000) / (2 + (1 : ℝ) / 2000) := by
  norm_num

end TernarySyncAudit
