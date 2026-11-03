import Mathlib
import FormalAudit.MTPerEventExpectation
import FormalAudit.ConcreteBoundedMT
import FormalAudit.ConcreteWitnessTreeWeight
import FormalAudit.ConcreteFiniteSuccess

namespace TernarySyncAudit

/-- The previously conditional per-event Moser--Tardos estimate is now fully
instantiated for the concrete long-interval event family. -/
theorem concreteBounded_per_event_expectation_le
    (N : ℕ) (outer : ℕ → Symbol) (steps : ℕ)
    (root : LongIntervalIndex N) :
    concreteBoundedEventExpectation N outer steps root ≤
      longIntervalCharge root / (1 - longIntervalCharge root) := by
  unfold concreteBoundedEventExpectation
  apply uniformLogEventExpectation_le_charge_ratio
    (longIntervalSupport N) (longIntervalEvent N outer)
    (longIntervalEvent_dependsOn N outer)
    (longIntervalNeighbors N)
    (longIntervalSupport_overlap_closedNeighbor)
    longIntervalCharge
    (fun candidate => longIntervalCharge_nonnegative candidate)
    (fun candidate => (longIntervalCharge_lt_half candidate).trans
      (by norm_num))
    (longInterval_self_not_neighbor)
    (fun candidate => by
      simpa [finiteEventMass] using
        concrete_long_interval_lll_criterion N outer candidate)
    (steps + 1) steps (0 : Choice)
    (concreteBoundedMTLog N outer steps)
  · intro table
    exact concreteMTRun_log_length_le N outer
      (extendBoundedTable (steps + 1) (0 : Choice) table) steps
  · intro table
    have bound := concreteMTRun_log_length_le N outer
      (extendBoundedTable (steps + 1) (0 : Choice) table) steps
    change (concreteBoundedMTLog N outer steps table).length ≤ steps at bound
    omega
  · intro table
    simpa [concreteBoundedMTLog, concreteMTRun, initialMTState] using
      (mtRun_logCompatible
        (longIntervalSupport N)
        (fun candidate =>
          (longIntervalEvent N outer candidate : Set (Fin N → Choice)))
        (firstViolatedLongInterval N outer)
        (fun assignment candidate selected =>
          firstViolatedLongInterval_sound outer assignment candidate selected)
        (extendBoundedTable (steps + 1) (0 : Choice) table)
        steps (initialMTState N))

/-- Unconditional concrete expected total resampling bound. -/
theorem concreteBounded_expected_log_length_le_unconditional
    (N : ℕ) (outer : ℕ → Symbol) (steps : ℕ) :
    uniformExpectation (fun table =>
      ((concreteBoundedMTLog N outer steps table).length : ℝ)) ≤ 18 * N :=
  concreteBounded_expected_log_length_le N outer steps
    (concreteBounded_per_event_expectation_le N outer steps)

/-- Unconditional finite-horizon nontermination tail bound. -/
theorem concreteBounded_nontermination_mass_le_unconditional
    (N : ℕ) (outer : ℕ → Symbol) {steps : ℕ}
    (stepsPositive : 0 < steps) :
    uniformFinsetMass
        (boundedMTNonterminationEvent (longIntervalSupport N)
          (firstViolatedLongInterval N outer) steps (0 : Choice)
          (initialMTState N)) ≤
      (18 * N : ℝ) / steps :=
  concreteBounded_nontermination_mass_le N outer stepsPositive
    (concreteBounded_per_event_expectation_le N outer steps)

/-- Every transition budget above `18N` admits a finite table on which the
concrete MT run halts and its final branch avoids every long event. -/
theorem exists_concreteBoundedMT_halted_avoids_unconditional
    (N : ℕ) (outer : ℕ → Symbol) (steps : ℕ)
    (budgetLarge : 18 * N < steps) :
    ∃ table : Fin N × Fin (steps + 1) → Choice,
      (concreteMTRun N outer
        (extendBoundedTable (steps + 1) (0 : Choice) table) steps).1.halted =
          true ∧
      tableAssignment (extendBoundedTable (steps + 1) (0 : Choice) table)
          (concreteMTRun N outer
            (extendBoundedTable (steps + 1) (0 : Choice) table) steps).1 ∈
        avoidOutcomes (longIntervalEvent N outer)
          (Finset.univ : Finset (LongIntervalIndex N)) :=
  exists_concreteBoundedMT_halted_avoids N outer steps budgetLarge
    (concreteBounded_per_event_expectation_le N outer steps)

/-- Projected unconditional finite-table success theorem. -/
theorem exists_concreteBoundedMT_avoiding_branch_unconditional
    (N : ℕ) (outer : ℕ → Symbol) (steps : ℕ)
    (budgetLarge : 18 * N < steps) :
    ∃ branch : Fin N → Choice,
      branch ∈ avoidOutcomes (longIntervalEvent N outer)
        (Finset.univ : Finset (LongIntervalIndex N)) :=
  exists_concreteBoundedMT_avoiding_branch N outer steps budgetLarge
    (concreteBounded_per_event_expectation_le N outer steps)

end TernarySyncAudit
