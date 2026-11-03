import Mathlib
import FormalAudit.ConcreteDependency
import FormalAudit.LocalLemmaProduct
import FormalAudit.MoserTardosConsequences

namespace TernarySyncAudit

open Finset

/-- The asymmetric LLL charge assigned to a long interval event. -/
noncomputable def longIntervalCharge {N : ℕ} (event : LongIntervalIndex N) : ℝ :=
  Real.exp (-(event.length : ℝ) / 100)

theorem longIntervalCharge_pos {N : ℕ} (event : LongIntervalIndex N) :
    0 < longIntervalCharge event := Real.exp_pos _

theorem longIntervalCharge_nonnegative {N : ℕ} (event : LongIntervalIndex N) :
    0 ≤ longIntervalCharge event := (longIntervalCharge_pos event).le

/-- Every charge is far below `1/2`; the proof uses only the paper's explicit
rational certificate `624000 < exp 20`. -/
theorem longIntervalCharge_lt_half {N : ℕ} (event : LongIntervalIndex N) :
    longIntervalCharge event < (1 : ℝ) / 2 := by
  have lengthReal : (2000 : ℝ) < event.length := by
    exact_mod_cast event.long
  have exponentBound : -(event.length : ℝ) / 100 < -20 := by
    linarith
  have expBound : longIntervalCharge event < Real.exp (-20) := by
    exact Real.exp_strictMono exponentBound
  have expTwentyGtTwo : (2 : ℝ) < Real.exp 20 :=
    (by norm_num : (2 : ℝ) < 624000).trans exp_twenty_gt_624000
  have inverseBound : Real.exp (-20) < (1 : ℝ) / 2 := by
    rw [Real.exp_neg]
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) expTwentyGtTwo)
  exact expBound.trans inverseBound

/-- The global-space event mass is exactly the concrete mass bounded by the
deletion-ball entropy argument. -/
theorem longIntervalEvent_mass_lt
    (N : ℕ) (outer : ℕ → Symbol) (event : LongIntervalIndex N) :
    finiteEventMass (longIntervalEvent N outer) event <
      Real.exp (-(event.length : ℝ) / 71) := by
  exact finite_interval_bad_mass_lt outer event.long event.fits

/-- Once the neighbor-charge estimate is supplied, all remaining numerical
inequalities in the asymmetric LLL criterion are formally closed. -/
theorem concrete_lll_criterion_of_neighbor_charge
    (N : ℕ) (outer : ℕ → Symbol) (event : LongIntervalIndex N)
    (neighborCharge :
      (∑ other ∈ longIntervalNeighbors N event, longIntervalCharge other) ≤
        (event.length : ℝ) / 1000) :
    finiteEventMass (longIntervalEvent N outer) event ≤
      longIntervalCharge event *
        ∏ other ∈ longIntervalNeighbors N event,
          (1 - longIntervalCharge other) := by
  have productLower := exp_neg_two_sum_le_product
    (longIntervalNeighbors N event) longIntervalCharge
    (fun other _ => longIntervalCharge_nonnegative other)
    (fun other _ => (longIntervalCharge_lt_half other).le)
  have exponentFromSum :
      Real.exp (-(event.length : ℝ) / 500) ≤
        Real.exp
          (-2 * ∑ other ∈ longIntervalNeighbors N event,
            longIntervalCharge other) := by
    apply Real.exp_monotone
    nlinarith
  have chargedProductLower :
      Real.exp (-(event.length : ℝ) * (3 / 250 : ℝ)) ≤
        longIntervalCharge event *
          ∏ other ∈ longIntervalNeighbors N event,
            (1 - longIntervalCharge other) := by
    calc
      Real.exp (-(event.length : ℝ) * (3 / 250 : ℝ)) =
          longIntervalCharge event *
            Real.exp (-(event.length : ℝ) / 500) := by
        unfold longIntervalCharge
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ longIntervalCharge event *
          Real.exp
            (-2 * ∑ other ∈ longIntervalNeighbors N event,
              longIntervalCharge other) := by
        exact mul_le_mul_of_nonneg_left exponentFromSum
          (longIntervalCharge_nonnegative event)
      _ ≤ longIntervalCharge event *
          ∏ other ∈ longIntervalNeighbors N event,
            (1 - longIntervalCharge other) := by
        exact mul_le_mul_of_nonneg_left productLower
          (longIntervalCharge_nonnegative event)
  have exponentComparison :
      Real.exp (-(event.length : ℝ) / 71) ≤
        Real.exp (-(event.length : ℝ) * (3 / 250 : ℝ)) := by
    apply Real.exp_monotone
    have lengthNonnegative : (0 : ℝ) ≤ event.length := by positivity
    nlinarith
  exact (longIntervalEvent_mass_lt N outer event).le.trans
    (exponentComparison.trans chargedProductLower)

end TernarySyncAudit
