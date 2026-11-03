import Mathlib
import FormalAudit.MTLogCompatibility
import FormalAudit.BoundedLogProbability
import FormalAudit.FiniteExpectationCertificates
import FormalAudit.FiniteLLLModel

namespace TernarySyncAudit

/-- Resampling-log length for a bounded run driven by a genuinely finite
table.  One extra row is available beyond the transition budget. -/
def boundedMTLogLength
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (steps : ℕ) (default : A) (state : MTState V)
    (table : V × Fin (steps + 1) → A) : ℕ :=
  (mtRun support pick
    (extendBoundedTable (steps + 1) default table) steps state).2.length

/-- Finite-table outcomes on which the bounded run remains active after all
transitions. -/
def boundedMTNonterminationEvent
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (steps : ℕ) (default : A) (state : MTState V) :
    Finset ((V × Fin (steps + 1)) → A) :=
  Finset.univ.filter fun table =>
    (mtRun support pick
      (extendBoundedTable (steps + 1) default table) steps state).1.halted = false

/-- From an active initial state, nontermination forces the resampling count
to hit the complete transition budget. -/
theorem boundedMTNontermination_subset_tail
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (steps : ℕ) (default : A) (state : MTState V)
    (initialActive : state.halted = false) :
    boundedMTNonterminationEvent support pick steps default state ⊆
      uniformNatTailEvent
        (boundedMTLogLength support pick steps default state) steps := by
  intro table nonterminating
  have finalActive := (Finset.mem_filter.mp nonterminating).2
  have fullLength := mtRun_active_log_length_eq_steps
    support pick (extendBoundedTable (steps + 1) default table)
      steps state initialActive finalActive
  simp only [uniformNatTailEvent, Finset.mem_filter,
    Finset.mem_univ, true_and, boundedMTLogLength]
  omega

/-- Finite-table nontermination probability is bounded by expected
resamplings divided by the transition budget. -/
theorem boundedMTNontermination_mass_le_expectation_div
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (support : E → Finset V) (pick : (V → A) → Option E)
    {steps : ℕ} (stepsPositive : 0 < steps)
    (default : A) (state : MTState V)
    (initialActive : state.halted = false) :
    uniformFinsetMass
        (boundedMTNonterminationEvent support pick steps default state) ≤
      uniformExpectation (fun table =>
        (boundedMTLogLength support pick steps default state table : ℝ)) /
          steps := by
  calc
    uniformFinsetMass
        (boundedMTNonterminationEvent support pick steps default state) ≤
      uniformFinsetMass
        (uniformNatTailEvent
          (boundedMTLogLength support pick steps default state) steps) :=
      uniformFinsetMass_mono
        (boundedMTNontermination_subset_tail support pick steps default state
          initialActive)
    _ ≤ uniformExpectation (fun table =>
          (boundedMTLogLength support pick steps default state table : ℝ)) /
            steps :=
      uniformNatTailEvent_mass_le
        (boundedMTLogLength support pick steps default state) stepsPositive

end TernarySyncAudit
