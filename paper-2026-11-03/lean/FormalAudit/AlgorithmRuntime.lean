import Mathlib

namespace TernarySyncAudit

open Finset

/-- A deliberately conservative operation count for one exhaustive LCS scan. -/
def fullScanWork (M : ℕ) : ℕ :=
  ∑ ell ∈ Finset.range (M + 1), M * ell ^ 2

/-- There are at most `M(M+1)` candidate start/length pairs. -/
theorem candidate_event_count_le (M : ℕ) :
    (∑ _ell ∈ Finset.range (M + 1), M) ≤ M * (M + 1) := by
  simp [Nat.mul_comm]

/-- The direct dynamic-programming scan has a uniform quartic bound. -/
theorem fullScanWork_le_two_mul_fourth
    {M : ℕ} (hM : 1 ≤ M) :
    fullScanWork M ≤ 2 * M ^ 4 := by
  unfold fullScanWork
  calc
    (∑ ell ∈ Finset.range (M + 1), M * ell ^ 2)
        ≤ ∑ _ell ∈ Finset.range (M + 1), M ^ 3 := by
          apply Finset.sum_le_sum
          intro ell hell
          have hellLe : ell ≤ M := by
            exact Nat.le_of_lt_succ (Finset.mem_range.mp hell)
          nlinarith [Nat.mul_self_le_mul_self hellLe]
    _ = (M + 1) * M ^ 3 := by simp
    _ ≤ 2 * M ^ 4 := by
      have : M + 1 ≤ 2 * M := by omega
      nlinarith [Nat.zero_le (M ^ 3)]

/-- A two-dimensional LCS table uses at most a constant times `M²` cells. -/
theorem lcs_table_space_le_four_mul_sq
    {M : ℕ} (hM : 1 ≤ M) :
    (M + 1) ^ 2 ≤ 4 * M ^ 2 := by
  have h : M + 1 ≤ 2 * M := by omega
  nlinarith [Nat.mul_self_le_mul_self h]

/--
The algebraic runtime envelope after the Moser--Tardos estimate is supplied.
`R` is the expected number of resamplings.  Each resampling triggers one new
scan, and the extra linear rebuild cost is included.
-/
theorem expected_runtime_le_six_mul_fifth
    {M : ℝ} {R expectedTime : ℝ}
    (hM : 1 ≤ M) (hR : R ≤ M)
    (timeAccounting :
      expectedTime ≤ (R + 1) * (2 * M ^ 4 + M)) :
    expectedTime ≤ 6 * M ^ 5 := by
  have scans : R + 1 ≤ 2 * M := by linarith
  have fourthNonnegative : 0 ≤ M ^ 4 := by positivity
  have scanBound : 2 * M ^ 4 + M ≤ 3 * M ^ 4 := by
    have mLeFourth : M ≤ M ^ 4 := by
      simpa using (pow_le_pow_right₀ hM (by norm_num : 1 ≤ (4 : ℕ)))
    linarith
  calc
    expectedTime ≤ (R + 1) * (2 * M ^ 4 + M) := timeAccounting
    _ ≤ (2 * M) * (3 * M ^ 4) :=
      mul_le_mul scans scanBound (by positivity) (by linarith)
    _ = 6 * M ^ 5 := by ring

/-- Fixed macroblock expansion preserves the fifth-degree asymptotic scale. -/
theorem padded_length_fifth_bound
    {n M m : ℝ} (hn : 1 ≤ n) (hMnonnegative : 0 ≤ M)
    (hm : 0 ≤ m) (hM : M < n + m) :
    M ^ 5 ≤ (1 + m) ^ 5 * n ^ 5 := by
  have nPositive : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have upper : M < (1 + m) * n := by
    have : n + m ≤ n + m * n := by
      have : m ≤ m * n := by nlinarith
      linarith
    nlinarith
  have := pow_le_pow_left₀ hMnonnegative (le_of_lt upper) 5
  nlinarith [this]

end TernarySyncAudit
