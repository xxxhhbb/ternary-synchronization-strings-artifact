import Mathlib
import FormalAudit.ConcreteMTProcess
import FormalAudit.BoundedMTTermination
import FormalAudit.MTEventExpectation

namespace TernarySyncAudit

/-- Concrete finite-table MT log for the ternary synchronization instance. -/
noncomputable def concreteBoundedMTLog
    (N : ℕ) (outer : ℕ → Symbol) (steps : ℕ)
    (table : Fin N × Fin (steps + 1) → Choice) :
    List (LongIntervalIndex N) :=
  (concreteMTRun N outer
    (extendBoundedTable (steps + 1) (0 : Choice) table) steps).2

/-- Exact finite-uniform expected number of resamplings of one long-interval
event. -/
noncomputable def concreteBoundedEventExpectation
    (N : ℕ) (outer : ℕ → Symbol) (steps : ℕ)
    (event : LongIntervalIndex N) : ℝ :=
  uniformExpectation fun table =>
    (logEventCount event (concreteBoundedMTLog N outer steps table) : ℝ)

/-- Once the per-event witness estimate is established, the exact concrete
finite-table expected total resampling count is at most `18N`. -/
theorem concreteBounded_expected_log_length_le
    (N : ℕ) (outer : ℕ → Symbol) (steps : ℕ)
    (perEvent : ∀ event : LongIntervalIndex N,
      concreteBoundedEventExpectation N outer steps event ≤
        longIntervalCharge event / (1 - longIntervalCharge event)) :
    uniformExpectation (fun table =>
      ((concreteBoundedMTLog N outer steps table).length : ℝ)) ≤ 18 * N := by
  rw [uniformExpectation_log_length_eq_sum_events]
  calc
    (∑ event : LongIntervalIndex N,
        uniformExpectation fun table =>
          (logEventCount event
            (concreteBoundedMTLog N outer steps table) : ℝ)) ≤
      ∑ event : LongIntervalIndex N,
        longIntervalCharge event / (1 - longIntervalCharge event) := by
          exact Finset.sum_le_sum fun event eventIn => perEvent event
    _ ≤ 18 * N := concrete_total_resampling_ratio_le N

/-- The remaining per-event witness estimate also immediately yields a
concrete `18N/t` finite-horizon nontermination bound. -/
theorem concreteBounded_nontermination_mass_le
    (N : ℕ) (outer : ℕ → Symbol) {steps : ℕ}
    (stepsPositive : 0 < steps)
    (perEvent : ∀ event : LongIntervalIndex N,
      concreteBoundedEventExpectation N outer steps event ≤
        longIntervalCharge event / (1 - longIntervalCharge event)) :
    uniformFinsetMass
        (boundedMTNonterminationEvent (longIntervalSupport N)
          (firstViolatedLongInterval N outer) steps (0 : Choice)
          (initialMTState N)) ≤
      (18 * N : ℝ) / steps := by
  have tail := boundedMTNontermination_mass_le_expectation_div
    (longIntervalSupport N) (firstViolatedLongInterval N outer)
      stepsPositive (0 : Choice) (initialMTState N) rfl
  have expectationBound := concreteBounded_expected_log_length_le
    N outer steps perEvent
  calc
    uniformFinsetMass
        (boundedMTNonterminationEvent (longIntervalSupport N)
          (firstViolatedLongInterval N outer) steps (0 : Choice)
          (initialMTState N)) ≤
      uniformExpectation (fun table =>
        (boundedMTLogLength (longIntervalSupport N)
          (firstViolatedLongInterval N outer) steps (0 : Choice)
          (initialMTState N) table : ℝ)) / steps := tail
    _ ≤ (18 * N : ℝ) / steps := by
      apply div_le_div_of_nonneg_right
      · simpa [boundedMTLogLength, concreteBoundedMTLog,
          concreteMTRun] using expectationBound
      · positivity

end TernarySyncAudit
