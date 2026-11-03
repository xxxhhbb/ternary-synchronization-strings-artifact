import Mathlib
import FormalAudit.NeighborCharge

namespace TernarySyncAudit

open Finset

/-- The concrete interval family satisfies the asymmetric LLL criterion with
no remaining probabilistic or numerical hypotheses. -/
theorem concrete_long_interval_lll_criterion
    (N : ℕ) (outer : ℕ → Symbol) (event : LongIntervalIndex N) :
    finiteEventMass (longIntervalEvent N outer) event ≤
      longIntervalCharge event *
        ∏ other ∈ longIntervalNeighbors N event,
          (1 - longIntervalCharge other) := by
  exact concrete_lll_criterion_of_neighbor_charge N outer event
    (concrete_neighbor_charge_sum_lt event).le

/-- The fully instantiated finite asymmetric LLL.  It produces a global choice
vector avoiding every long adjacent-pair deletion-ball event at once. -/
theorem exists_choices_avoiding_all_long_events
    (N : ℕ) (outer : ℕ → Symbol) :
    (avoidOutcomes (longIntervalEvent N outer)
      (Finset.univ : Finset (LongIntervalIndex N))).Nonempty := by
  apply finite_asymmetric_lll_exists
    (Finset.univ : Finset (LongIntervalIndex N))
    (longIntervalEvent N outer)
    (longIntervalNeighbors N)
    longIntervalCharge
  · intro event
    exact longIntervalCharge_nonnegative event
  · intro event
    exact (longIntervalCharge_lt_half event).trans (by norm_num)
  · intro event S eventNotIn nonneighbors
    exact concrete_long_interval_dependency N outer event S eventNotIn nonneighbors
  · exact concrete_long_interval_lll_criterion N outer

/-- Elementwise form of the same theorem, convenient for the synchronization
conclusion: no indexed long event contains the selected branch vector. -/
theorem exists_choice_vector_with_no_long_bad_interval
    (N : ℕ) (outer : ℕ → Symbol) :
    ∃ branch : Fin N → Choice,
      ∀ event : LongIntervalIndex N,
        branch ∉ longIntervalEvent N outer event := by
  rcases exists_choices_avoiding_all_long_events N outer with ⟨branch, branchAvoids⟩
  refine ⟨branch, ?_⟩
  have avoidsEvery :
      ∀ event ∈ (Finset.univ : Finset (LongIntervalIndex N)),
        branch ∉ longIntervalEvent N outer event := by
    simpa only [avoidOutcomes, Finset.mem_filter, Finset.mem_univ, true_and]
      using branchAvoids
  intro event
  exact avoidsEvery event (Finset.mem_univ event)

end TernarySyncAudit
