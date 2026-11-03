import Mathlib
import FormalAudit.MoserTardosProcess
import FormalAudit.ConcreteResampling

namespace TernarySyncAudit

/-- Fixed deterministic event order: choose the least currently violated
long interval, if one exists. -/
noncomputable def firstViolatedLongInterval
    (N : ℕ) (outer : ℕ → Symbol) (branch : Fin N → Choice) :
    Option (LongIntervalIndex N) := by
  classical
  let violated := violatedLongIntervalsB N outer branch
  exact if nonempty : violated.Nonempty then some nonempty.choose else none

theorem firstViolatedLongInterval_some_mem
    {N : ℕ} (outer : ℕ → Symbol) (branch : Fin N → Choice)
    (event : LongIntervalIndex N)
    (selected : firstViolatedLongInterval N outer branch = some event) :
    event ∈ violatedLongIntervalsB N outer branch := by
  classical
  simp only [firstViolatedLongInterval] at selected
  split at selected
  · rename_i nonempty
    simp only [Option.some.injEq] at selected
    subst event
    exact Exists.choose_spec nonempty
  · simp at selected

theorem firstViolatedLongInterval_sound
    {N : ℕ} (outer : ℕ → Symbol) (branch : Fin N → Choice)
    (event : LongIntervalIndex N)
    (selected : firstViolatedLongInterval N outer branch = some event) :
    branch ∈ longIntervalEvent N outer event := by
  have inScan := firstViolatedLongInterval_some_mem outer branch event selected
  rw [violatedLongIntervalsB_eq] at inScan
  exact (Finset.mem_filter.mp inScan).2

theorem firstViolatedLongInterval_none_iff
    (N : ℕ) (outer : ℕ → Symbol) (branch : Fin N → Choice) :
    firstViolatedLongInterval N outer branch = none ↔
      violatedLongIntervalsB N outer branch = ∅ := by
  classical
  unfold firstViolatedLongInterval
  dsimp only
  by_cases nonempty : (violatedLongIntervalsB N outer branch).Nonempty
  · simp [nonempty, nonempty.ne_empty]
  · have empty : violatedLongIntervalsB N outer branch = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp nonempty
    simp [empty]

theorem firstViolatedLongInterval_none_iff_avoids
    (N : ℕ) (outer : ℕ → Symbol) (branch : Fin N → Choice) :
    firstViolatedLongInterval N outer branch = none ↔
      branch ∈ avoidOutcomes (longIntervalEvent N outer)
        (Finset.univ : Finset (LongIntervalIndex N)) := by
  rw [firstViolatedLongInterval_none_iff,
    violatedLongIntervalsB_empty_iff]

/-- The all-zero counter state before the initial sample is read. -/
def initialMTState (N : ℕ) : MTState (Fin N) :=
  ⟨fun _ => 0, false⟩

/-- Concrete resampling-table transition for the ternary construction. -/
noncomputable def concreteMTTransition
    (N : ℕ) (outer : ℕ → Symbol)
    (table : Fin N → ℕ → Choice) (state : MTState (Fin N)) :
    MTState (Fin N) × Option (LongIntervalIndex N) :=
  mtTransition (longIntervalSupport N)
    (firstViolatedLongInterval N outer) table state

/-- Concrete finite-horizon resampling execution. -/
noncomputable def concreteMTRun
    (N : ℕ) (outer : ℕ → Symbol)
    (table : Fin N → ℕ → Choice) (steps : ℕ) :
    MTState (Fin N) × List (LongIntervalIndex N) :=
  mtRun (longIntervalSupport N) (firstViolatedLongInterval N outer)
    table steps (initialMTState N)

theorem concreteMTTransition_selected_is_bad
    {N : ℕ} (outer : ℕ → Symbol)
    (table : Fin N → ℕ → Choice)
    (state next : MTState (Fin N)) (event : LongIntervalIndex N)
    (transition : concreteMTTransition N outer table state = (next, some event)) :
    tableAssignment table state ∈ longIntervalEvent N outer event := by
  apply mtTransition_selected_is_bad
    (longIntervalSupport N)
    (fun event => (longIntervalEvent N outer event : Set (Fin N → Choice)))
    (firstViolatedLongInterval N outer)
    (fun assignment event selected =>
      firstViolatedLongInterval_sound outer assignment event selected)
    table state next event
  exact transition

theorem concreteMTRun_log_length_le
    (N : ℕ) (outer : ℕ → Symbol)
    (table : Fin N → ℕ → Choice) (steps : ℕ) :
    (concreteMTRun N outer table steps).2.length ≤ steps := by
  exact mtRun_log_length_le (longIntervalSupport N)
    (firstViolatedLongInterval N outer) table steps (initialMTState N)

theorem concreteMTRun_counter_eq
    (N : ℕ) (outer : ℕ → Symbol)
    (table : Fin N → ℕ → Choice) (steps : ℕ)
    (coordinate : Fin N) :
    (concreteMTRun N outer table steps).1.count coordinate =
      supportOccurrenceCount (longIntervalSupport N) coordinate
        (concreteMTRun N outer table steps).2 := by
  simpa [concreteMTRun, initialMTState] using
    (mtRun_count_eq (longIntervalSupport N)
      (firstViolatedLongInterval N outer) table steps
      (initialMTState N) coordinate)

theorem concreteMTRun_counter_le_steps
    (N : ℕ) (outer : ℕ → Symbol)
    (table : Fin N → ℕ → Choice) (steps : ℕ)
    (coordinate : Fin N) :
    (concreteMTRun N outer table steps).1.count coordinate ≤ steps := by
  simpa [concreteMTRun, initialMTState] using
    (mtRun_count_le (longIntervalSupport N)
      (firstViolatedLongInterval N outer) table steps
      (initialMTState N) coordinate)

end TernarySyncAudit
