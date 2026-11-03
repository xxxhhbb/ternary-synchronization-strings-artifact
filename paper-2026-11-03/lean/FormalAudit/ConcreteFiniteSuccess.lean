import Mathlib
import FormalAudit.ConcreteBoundedMT
import FormalAudit.MTHaltingCorrectness

namespace TernarySyncAudit

/-- A finite event of uniform mass strictly below one omits at least one
outcome. -/
theorem exists_outside_of_uniformFinsetMass_lt_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : Finset Ω) (massLtOne : uniformFinsetMass event < 1) :
    ∃ outcome : Ω, outcome ∉ event := by
  by_contra noOutside
  push Not at noOutside
  have eventEq : event = Finset.univ := by
    exact Finset.eq_univ_of_forall noOutside
  subst event
  simp [uniformFinsetMass] at massLtOne

/-- Conditional on the remaining per-event witness estimate, any transition
budget strictly above `18N` has a concrete finite resampling table on which
the MT execution halts and avoids every long-interval event. -/
theorem exists_concreteBoundedMT_halted_avoids
    (N : ℕ) (outer : ℕ → Symbol) (steps : ℕ)
    (budgetLarge : 18 * N < steps)
    (perEvent : ∀ event : LongIntervalIndex N,
      concreteBoundedEventExpectation N outer steps event ≤
        longIntervalCharge event / (1 - longIntervalCharge event)) :
    ∃ table : Fin N × Fin (steps + 1) → Choice,
      (concreteMTRun N outer
        (extendBoundedTable (steps + 1) (0 : Choice) table) steps).1.halted =
          true ∧
      tableAssignment (extendBoundedTable (steps + 1) (0 : Choice) table)
          (concreteMTRun N outer
            (extendBoundedTable (steps + 1) (0 : Choice) table) steps).1 ∈
        avoidOutcomes (longIntervalEvent N outer)
          (Finset.univ : Finset (LongIntervalIndex N)) := by
  have stepsPositive : 0 < steps := by omega
  have massBound := concreteBounded_nontermination_mass_le
    N outer stepsPositive perEvent
  have ratioLtOne : (18 * N : ℝ) / steps < 1 := by
    rw [div_lt_one (by exact_mod_cast stepsPositive)]
    exact_mod_cast budgetLarge
  have massLtOne :
      uniformFinsetMass
          (boundedMTNonterminationEvent (longIntervalSupport N)
            (firstViolatedLongInterval N outer) steps (0 : Choice)
            (initialMTState N)) < 1 :=
    massBound.trans_lt ratioLtOne
  obtain ⟨table, outside⟩ := exists_outside_of_uniformFinsetMass_lt_one
    (boundedMTNonterminationEvent (longIntervalSupport N)
      (firstViolatedLongInterval N outer) steps (0 : Choice)
      (initialMTState N)) massLtOne
  have halted :
      (concreteMTRun N outer
        (extendBoundedTable (steps + 1) (0 : Choice) table) steps).1.halted =
          true := by
    cases haltedEq : (concreteMTRun N outer
        (extendBoundedTable (steps + 1) (0 : Choice) table) steps).1.halted with
    | false =>
        exfalso
        apply outside
        simp only [boundedMTNonterminationEvent, Finset.mem_filter,
          Finset.mem_univ, true_and]
        simpa [concreteMTRun] using haltedEq
    | true => rfl
  refine ⟨table, halted, ?_⟩
  exact concreteMTRun_halted_avoids N outer
    (extendBoundedTable (steps + 1) (0 : Choice) table) steps halted

/-- The same finite success theorem, projected to the final branch vector. -/
theorem exists_concreteBoundedMT_avoiding_branch
    (N : ℕ) (outer : ℕ → Symbol) (steps : ℕ)
    (budgetLarge : 18 * N < steps)
    (perEvent : ∀ event : LongIntervalIndex N,
      concreteBoundedEventExpectation N outer steps event ≤
        longIntervalCharge event / (1 - longIntervalCharge event)) :
    ∃ branch : Fin N → Choice,
      branch ∈ avoidOutcomes (longIntervalEvent N outer)
        (Finset.univ : Finset (LongIntervalIndex N)) := by
  obtain ⟨table, halted, avoids⟩ :=
    exists_concreteBoundedMT_halted_avoids
      N outer steps budgetLarge perEvent
  exact ⟨tableAssignment
    (extendBoundedTable (steps + 1) (0 : Choice) table)
    (concreteMTRun N outer
      (extendBoundedTable (steps + 1) (0 : Choice) table) steps).1, avoids⟩

end TernarySyncAudit
