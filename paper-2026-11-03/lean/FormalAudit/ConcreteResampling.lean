import Mathlib
import FormalAudit.SynchronizationHeadline
import FormalAudit.MoserTardosConsequences
import FormalAudit.AlgorithmRuntime
import FormalAudit.ConcreteEventOracle

namespace TernarySyncAudit

open Finset

/-- Replace exactly the coordinates in `support` by fresh values. -/
def resampleCoordinates
    {V A : Type*} [DecidableEq V]
    (support : Finset V) (current fresh : V → A) : V → A := fun coordinate =>
  if coordinate ∈ support then fresh coordinate else current coordinate

@[simp] theorem resampleCoordinates_inside
    {V A : Type*} [DecidableEq V]
    (support : Finset V) (current fresh : V → A)
    {coordinate : V} (inside : coordinate ∈ support) :
    resampleCoordinates support current fresh coordinate = fresh coordinate := by
  simp [resampleCoordinates, inside]

@[simp] theorem resampleCoordinates_outside
    {V A : Type*} [DecidableEq V]
    (support : Finset V) (current fresh : V → A)
    {coordinate : V} (outside : coordinate ∉ support) :
    resampleCoordinates support current fresh coordinate = current coordinate := by
  simp [resampleCoordinates, outside]

/-- The concrete Moser--Tardos update for one long interval event. -/
def resampleLongInterval
    {N : ℕ} (event : LongIntervalIndex N)
    (current fresh : Fin N → Choice) : Fin N → Choice :=
  resampleCoordinates (longIntervalSupport N event) current fresh

theorem resampleLongInterval_inside
    {N : ℕ} (event : LongIntervalIndex N)
    (current fresh : Fin N → Choice) {coordinate : Fin N}
    (inside : coordinate ∈ longIntervalSupport N event) :
    resampleLongInterval event current fresh coordinate = fresh coordinate :=
  resampleCoordinates_inside _ _ _ inside

theorem resampleLongInterval_outside
    {N : ℕ} (event : LongIntervalIndex N)
    (current fresh : Fin N → Choice) {coordinate : Fin N}
    (outside : coordinate ∉ longIntervalSupport N event) :
    resampleLongInterval event current fresh coordinate = current coordinate :=
  resampleCoordinates_outside _ _ _ outside

/-- A concrete bad event after resampling is determined only by the newly
sampled values on its declared support, independently of old supported values. -/
theorem resampled_event_forgets_old_support
    {N : ℕ} (outer : ℕ → Symbol) (event : LongIntervalIndex N)
    (oldLeft oldRight fresh : Fin N → Choice)
    (_outsideEqual : ∀ coordinate,
      coordinate ∉ longIntervalSupport N event →
        oldLeft coordinate = oldRight coordinate) :
    resampleLongInterval event oldLeft fresh ∈ longIntervalEvent N outer event ↔
      resampleLongInterval event oldRight fresh ∈ longIntervalEvent N outer event := by
  apply longIntervalEvent_dependsOn N outer event
  intro coordinate coordinateIn
  rw [resampleLongInterval_inside event oldLeft fresh coordinateIn,
    resampleLongInterval_inside event oldRight fresh coordinateIn]

/-- All currently violated events, i.e. the exact exhaustive scan result. -/
noncomputable def violatedLongIntervals
    (N : ℕ) (outer : ℕ → Symbol) (branch : Fin N → Choice) :
    Finset (LongIntervalIndex N) := by
  classical
  exact Finset.univ.filter fun event => branch ∈ longIntervalEvent N outer event

/-- Computable implementation of the same exhaustive scan, using the verified
LCS oracle rather than proposition-valued finite-set membership. -/
def violatedLongIntervalsB
    (N : ℕ) (outer : ℕ → Symbol) (branch : Fin N → Choice) :
    Finset (LongIntervalIndex N) :=
  Finset.univ.filter fun event => longIntervalBadB outer branch event

theorem violatedLongIntervalsB_eq
    (N : ℕ) (outer : ℕ → Symbol) (branch : Fin N → Choice) :
    violatedLongIntervalsB N outer branch =
      violatedLongIntervals N outer branch := by
  classical
  ext event
  simp only [violatedLongIntervalsB, violatedLongIntervals,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact longIntervalBadB_eq_true_iff outer branch event

/-- A complete scan is empty exactly when every long event is avoided. -/
theorem violatedLongIntervals_empty_iff
    (N : ℕ) (outer : ℕ → Symbol) (branch : Fin N → Choice) :
    violatedLongIntervals N outer branch = ∅ ↔
      branch ∈ avoidOutcomes (longIntervalEvent N outer)
        (Finset.univ : Finset (LongIntervalIndex N)) := by
  classical
  constructor
  · intro emptyScan
    simp only [avoidOutcomes, Finset.mem_filter, Finset.mem_univ, true_and]
    intro event eventIn bad
    have eventInScan : event ∈ violatedLongIntervals N outer branch := by
      simp [violatedLongIntervals, bad]
    rw [emptyScan] at eventInScan
    simp at eventInScan
  · intro avoids
    ext event
    constructor
    · intro eventIn
      have bad : branch ∈ longIntervalEvent N outer event :=
        (Finset.mem_filter.mp eventIn).2
      have avoidsEvery : ∀ candidate ∈
          (Finset.univ : Finset (LongIntervalIndex N)),
          branch ∉ longIntervalEvent N outer candidate := by
        simpa only [avoidOutcomes, Finset.mem_filter, Finset.mem_univ,
          true_and] using avoids
      exact (avoidsEvery event (Finset.mem_univ event) bad).elim
    · simp

theorem violatedLongIntervalsB_empty_iff
    (N : ℕ) (outer : ℕ → Symbol) (branch : Fin N → Choice) :
    violatedLongIntervalsB N outer branch = ∅ ↔
      branch ∈ avoidOutcomes (longIntervalEvent N outer)
        (Finset.univ : Finset (LongIntervalIndex N)) := by
  rw [violatedLongIntervalsB_eq]
  exact violatedLongIntervals_empty_iff N outer branch

/-- The exact concrete sum of Moser--Tardos per-event expectation bounds is at
most the encoded length.  Only the witness-tree theorem is upstream of this. -/
theorem concrete_total_resampling_ratio_le (N : ℕ) :
    (∑ event : LongIntervalIndex N,
      longIntervalCharge event / (1 - longIntervalCharge event)) ≤ 18 * N := by
  apply explicit_total_resampling_le_length
    (Finset.univ : Finset (LongIntervalIndex N)) longIntervalCharge
    (M := (18 : ℝ) * N)
  · positivity
  · intro event eventIn
    exact longIntervalCharge_nonnegative event
  · intro event eventIn
    exact (longIntervalCharge_lt_half event).le
  · exact total_long_interval_charge_le N

/-- Linearity-of-expectation consequence of the per-event Moser--Tardos
bound, specialized to the actual event family. -/
theorem concrete_expected_resamplings_le
    {N : ℕ} (expected : LongIntervalIndex N → ℝ)
    (perEvent : ∀ event,
      expected event ≤ longIntervalCharge event / (1 - longIntervalCharge event)) :
    (∑ event : LongIntervalIndex N, expected event) ≤ 18 * N := by
  calc
    (∑ event : LongIntervalIndex N, expected event) ≤
        ∑ event : LongIntervalIndex N,
          longIntervalCharge event / (1 - longIntervalCharge event) := by
      exact Finset.sum_le_sum fun event _ => perEvent event
    _ ≤ 18 * N := concrete_total_resampling_ratio_le N

/-- Padding by complete 18-letter blocks costs fewer than 18 symbols. -/
theorem explicit_padded_length_lt
    {n : ℕ} :
    18 * macroblockCount n < n + 18 := by
  have divisionBound : 18 * ((n + 17) / 18) ≤ n + 17 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n + 17) 18
  dsimp [macroblockCount]
  omega

/-- Fully explicit fifth-degree envelope after the MT expectation inequality. -/
theorem explicit_expected_runtime_from_resamplings
    {n : ℕ} (nPositive : 0 < n) {expectedTime : ℝ}
    (timeAccounting :
      expectedTime ≤ ((18 * macroblockCount n : ℕ) + 1) *
        (2 * ((18 * macroblockCount n : ℕ) : ℝ) ^ 4 +
          (18 * macroblockCount n : ℕ))) :
    expectedTime ≤ 6 * 19 ^ 5 * (n : ℝ) ^ 5 := by
  let M : ℝ := 18 * macroblockCount n
  have MAtLeastOne : 1 ≤ M := by
    have nLe := prefix_fits_macroblocks n
    dsimp [M]
    exact_mod_cast (show 1 ≤ 18 * macroblockCount n by omega)
  have runtimeM : expectedTime ≤ 6 * M ^ 5 := by
    apply expected_runtime_le_six_mul_fifth MAtLeastOne (R := M)
    · exact le_rfl
    · simpa [M] using timeAccounting
  have padded : M < (n : ℝ) + 18 := by
    dsimp [M]
    exact_mod_cast (explicit_padded_length_lt (n := n))
  have fifth := padded_length_fifth_bound
    (n := (n : ℝ)) (M := M) (m := (18 : ℝ))
    (by exact_mod_cast nPositive) (by positivity) (by norm_num) padded
  nlinarith

end TernarySyncAudit
