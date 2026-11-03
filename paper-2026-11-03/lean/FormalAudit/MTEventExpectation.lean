import Mathlib
import FormalAudit.FiniteExpectationCertificates

namespace TernarySyncAudit

/-- Number of occurrences of one event label in a resampling log. -/
def logEventCount
    {E : Type*} [DecidableEq E] (event : E) (log : List E) : ℕ :=
  (log.filter fun candidate => decide (candidate = event)).length

@[simp] theorem logEventCount_nil
    {E : Type*} [DecidableEq E] (event : E) :
    logEventCount event [] = 0 := by
  simp [logEventCount]

@[simp] theorem logEventCount_cons
    {E : Type*} [DecidableEq E]
    (event head : E) (rest : List E) :
    logEventCount event (head :: rest) =
      logEventCount event rest + if head = event then 1 else 0 := by
  by_cases equality : head = event <;>
    simp [logEventCount, equality, Nat.add_comm]

/-- Summing occurrence counts over all labels gives the exact log length. -/
theorem sum_logEventCount_eq_length
    {E : Type*} [Fintype E] [DecidableEq E] (log : List E) :
    (∑ event : E, logEventCount event log) = log.length := by
  induction log with
  | nil => simp
  | cons head rest inductionHypothesis =>
      simp_rw [logEventCount_cons]
      rw [Finset.sum_add_distrib, inductionHypothesis]
      have oneMatch : (∑ event : E, if head = event then 1 else 0) = 1 := by
        simp
      rw [oneMatch]
      simp

/-- Uniform expected log length is exactly the sum of the per-event expected
resampling counts. -/
theorem uniformExpectation_log_length_eq_sum_events
    {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (log : Ω → List E) :
    uniformExpectation (fun outcome => ((log outcome).length : ℝ)) =
      ∑ event : E,
        uniformExpectation (fun outcome =>
          (logEventCount event (log outcome) : ℝ)) := by
  classical
  unfold uniformExpectation
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome outcomeIn
  simpa only [Nat.cast_sum] using
    congrArg (fun value : ℕ => (value : ℝ))
      (sum_logEventCount_eq_length (log outcome)).symm

/-- If every per-event expectation obeys its witness-tree bound, then the
total expected resampling count obeys the sum of those bounds. -/
theorem uniformExpectation_log_length_le_per_event_bounds
    {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (log : Ω → List E) (bound : E → ℝ)
    (perEvent : ∀ event,
      uniformExpectation (fun outcome =>
        (logEventCount event (log outcome) : ℝ)) ≤ bound event) :
    uniformExpectation (fun outcome => ((log outcome).length : ℝ)) ≤
      ∑ event : E, bound event := by
  rw [uniformExpectation_log_length_eq_sum_events]
  exact Finset.sum_le_sum fun event eventIn => perEvent event

end TernarySyncAudit
