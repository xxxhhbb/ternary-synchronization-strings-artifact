import Mathlib
import FormalAudit.WitnessTreeWeight
import FormalAudit.ConcreteLLLExistence

namespace TernarySyncAudit

theorem longInterval_self_not_neighbor
    {N : ℕ} (event : LongIntervalIndex N) :
    event ∉ longIntervalNeighbors N event := by
  simp [longIntervalNeighbors]

/-- Concrete finite-height witness-tree sum bound for every long interval
event. -/
theorem concrete_witnessTreeWeight_le
    (N : ℕ) (outer : ℕ → Symbol) (height : ℕ)
    (event : LongIntervalIndex N) :
    witnessTreeWeight
        (finiteEventMass (longIntervalEvent N outer))
        (longIntervalNeighbors N) height event ≤
      longIntervalCharge event / (1 - longIntervalCharge event) := by
  apply witnessTreeWeight_le_charge_ratio
    (finiteEventMass (longIntervalEvent N outer)) longIntervalCharge
    (longIntervalNeighbors N)
  · intro candidate
    exact uniformFinsetMass_nonnegative _
  · intro candidate
    exact longIntervalCharge_nonnegative candidate
  · intro candidate
    exact (longIntervalCharge_lt_half candidate).trans (by norm_num)
  · exact longInterval_self_not_neighbor
  · exact concrete_long_interval_lll_criterion N outer

end TernarySyncAudit
