import Mathlib
import FormalAudit.ProperWitnessShape
import FormalAudit.ConcreteWitnessTreeWeight

namespace TernarySyncAudit

/-- Concrete ternary-sync instance: the total probability-product mass of all
proper long-interval witness shapes rooted at one event is uniformly bounded
by the paper's explicit charge ratio. -/
theorem concrete_properWitnessShape_mass_sum_le
    (N : ℕ) (outer : ℕ → Symbol) (height : ℕ)
    (event : LongIntervalIndex N) :
    (∑ shape ∈ properWitnessShapes (longIntervalNeighbors N) height event,
      properWitnessShapeMass
        (finiteEventMass (longIntervalEvent N outer))
        (longIntervalNeighbors N) height event shape) ≤
      longIntervalCharge event / (1 - longIntervalCharge event) := by
  rw [sum_properWitnessShapeMass_eq_witnessTreeWeight]
  exact concrete_witnessTreeWeight_le N outer height event

end TernarySyncAudit
