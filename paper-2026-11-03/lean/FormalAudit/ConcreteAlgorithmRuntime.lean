import Mathlib
import FormalAudit.AlgorithmRuntime
import FormalAudit.ConcreteMTExpectationClosed

namespace TernarySyncAudit

/-- Conservative real-valued work envelope for the concrete bounded MT run:
one exhaustive scan initially and after every resampling, with the direct LCS
scan and linear rebuild costs included. -/
noncomputable def concreteBoundedRuntimeWork
    (N : ℕ) (outer : ℕ → Symbol) (steps : ℕ)
    (table : Fin N × Fin (steps + 1) → Choice) : ℝ :=
  (((concreteBoundedMTLog N outer steps table).length : ℝ) + 1) *
    (2 * (18 * N : ℝ) ^ 4 + (18 * N : ℝ))

/-- Uniform expectation commutes with the affine scan-count envelope. -/
theorem uniformExpectation_add_one_mul_const
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (value : Ω → ℝ) (constant : ℝ) :
    uniformExpectation (fun outcome => (value outcome + 1) * constant) =
      (uniformExpectation value + 1) * constant := by
  classical
  unfold uniformExpectation
  change (∑ outcome : Ω, (value outcome + 1) * constant) /
      Fintype.card Ω = _
  rw [← Finset.sum_mul, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have cardPositive : (0 : ℝ) < Fintype.card Ω := by positivity
  field_simp

/-- Exact expectation identity for the concrete runtime envelope. -/
theorem concreteBoundedRuntimeWork_expectation_eq
    (N : ℕ) (outer : ℕ → Symbol) (steps : ℕ) :
    uniformExpectation
        (concreteBoundedRuntimeWork N outer steps) =
      (uniformExpectation (fun table =>
          ((concreteBoundedMTLog N outer steps table).length : ℝ)) + 1) *
        (2 * (18 * N : ℝ) ^ 4 + (18 * N : ℝ)) := by
  unfold concreteBoundedRuntimeWork
  exact uniformExpectation_add_one_mul_const _ _

/-- Fully unconditional polynomial runtime guarantee for the finite-horizon
concrete algorithm. -/
theorem concreteBounded_expected_runtime_le
    {N : ℕ} (positive : 0 < N) (outer : ℕ → Symbol) (steps : ℕ) :
    uniformExpectation (concreteBoundedRuntimeWork N outer steps) ≤
      6 * (18 * N : ℝ) ^ 5 := by
  let expectedResamplings := uniformExpectation (fun table =>
    ((concreteBoundedMTLog N outer steps table).length : ℝ))
  have lengthBound : expectedResamplings ≤ (18 * N : ℝ) := by
    simpa [expectedResamplings] using
      concreteBounded_expected_log_length_le_unconditional N outer steps
  have sizeAtLeastOne : (1 : ℝ) ≤ 18 * N := by
    exact_mod_cast (by omega : 1 ≤ 18 * N)
  apply expected_runtime_le_six_mul_fifth sizeAtLeastOne lengthBound
  rw [concreteBoundedRuntimeWork_expectation_eq]

/-- Expanded constant form of the `O(N^5)` runtime guarantee. -/
theorem concreteBounded_expected_runtime_le_explicit
    {N : ℕ} (positive : 0 < N) (outer : ℕ → Symbol) (steps : ℕ) :
    uniformExpectation (concreteBoundedRuntimeWork N outer steps) ≤
      11337408 * (N : ℝ) ^ 5 := by
  calc
    uniformExpectation (concreteBoundedRuntimeWork N outer steps) ≤
        6 * (18 * N : ℝ) ^ 5 :=
      concreteBounded_expected_runtime_le positive outer steps
    _ = 11337408 * (N : ℝ) ^ 5 := by ring

/-- The actual natural-number work using `fullScanWork` is pointwise bounded
by the conservative real envelope. -/
theorem concreteBounded_actual_work_le_runtimeWork
    {N : ℕ} (positive : 0 < N) (outer : ℕ → Symbol) (steps : ℕ)
    (table : Fin N × Fin (steps + 1) → Choice) :
    (((concreteBoundedMTLog N outer steps table).length + 1) *
        (fullScanWork (18 * N) + 18 * N) : ℕ) ≤
      concreteBoundedRuntimeWork N outer steps table := by
  have scanBound := fullScanWork_le_two_mul_fourth
    (M := 18 * N) (by omega)
  unfold concreteBoundedRuntimeWork
  exact_mod_cast Nat.mul_le_mul_left
    ((concreteBoundedMTLog N outer steps table).length + 1)
      (Nat.add_le_add_right scanBound (18 * N))

end TernarySyncAudit
