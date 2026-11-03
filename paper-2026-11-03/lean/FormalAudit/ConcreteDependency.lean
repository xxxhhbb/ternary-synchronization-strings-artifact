import Mathlib
import FormalAudit.ConcreteIntervalEntropy
import FormalAudit.VariableIndependence
import FormalAudit.WitnessTreeWeight

namespace TernarySyncAudit

open Finset

/-- Macroblocks whose character ranges meet the adjacent interval pair
`[start,start+2*ell)`.  This is the exact variable support used by the LLL. -/
def intervalBlockSupport (N start ell : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun block =>
    18 * block.val < start + 2 * ell ∧ start < 18 * (block.val + 1)

/-- Every character in the adjacent pair is carried by a block in its support. -/
theorem character_block_mem_intervalBlockSupport
    {N start ell position : ℕ}
    (positionLt : position < 2 * ell)
    (supportFits : start + 2 * ell ≤ 18 * N) :
    let character := start + position
    let block : Fin N := ⟨character / 18, by omega⟩
    block ∈ intervalBlockSupport N start ell := by
  dsimp only
  let character := start + position
  have characterLt : character < 18 * N := by
    dsimp [character]
    omega
  let block : Fin N := ⟨character / 18, by omega⟩
  have blockStart : 18 * block.val ≤ character := by
    dsimp [block]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self character 18
  have characterMod : character % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have characterDecomp :
      character % 18 + 18 * (character / 18) = character := Nat.mod_add_div _ _
  simp only [intervalBlockSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · dsimp [character] at blockStart ⊢
    omega
  · omega

/-- Agreement on the interval-pair support gives agreement of every encoded
character in that pair. -/
theorem codeStream_eq_on_intervalBlockSupport
    {N start ell position : ℕ} (outer : ℕ → Symbol)
    (left right : Fin N → Choice)
    (positionLt : position < 2 * ell)
    (supportFits : start + 2 * ell ≤ 18 * N)
    (agree : ∀ block ∈ intervalBlockSupport N start ell,
      left block = right block) :
    codeStream outer (extendFiniteChoices left) (start + position) =
      codeStream outer (extendFiniteChoices right) (start + position) := by
  let character := start + position
  have characterLt : character < 18 * N := by
    dsimp [character]
    omega
  have blockLt : character / 18 < N := by omega
  let block : Fin N := ⟨character / 18, blockLt⟩
  have blockMem : block ∈ intervalBlockSupport N start ell := by
    exact character_block_mem_intervalBlockSupport positionLt supportFits
  have branchEquality :
      extendFiniteChoices left (character / 18) =
        extendFiniteChoices right (character / 18) := by
    rw [extendFiniteChoices_at left blockLt, extendFiniteChoices_at right blockLt]
    exact agree block blockMem
  unfold codeStream
  dsimp [character] at branchEquality ⊢
  rw [branchEquality]

/-- Both concrete adjacent intervals are functions only of the macroblocks in
`intervalBlockSupport`. -/
theorem finiteIntervalBadEvent_dependsOn
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (supportFits : start + 2 * ell ≤ 18 * N) :
    DependsOn
      (finiteIntervalBadEvent (N := N) (start := start) (ell := ell) outer)
      (intervalBlockSupport N start ell) := by
  classical
  intro left right agree
  have firstEquality :
      finiteFirstInterval (N := N) (start := start) (ell := ell) outer left =
        finiteFirstInterval (N := N) (start := start) (ell := ell) outer right := by
    funext position
    exact codeStream_eq_on_intervalBlockSupport outer left right
      (by omega) supportFits agree
  have secondEquality :
      finiteSecondInterval (N := N) (start := start) (ell := ell) outer left =
        finiteSecondInterval (N := N) (start := start) (ell := ell) outer right := by
    funext position
    simpa [finiteSecondInterval, streamInterval, Nat.add_assoc] using
      (codeStream_eq_on_intervalBlockSupport outer left right
        (position := ell + position.val) (by omega) supportFits agree)
  simp only [finiteIntervalBadEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [firstEquality, secondEquality]

/-- A finite index for every long adjacent-pair event that fits in `18*N`
characters.  The redundant finite bounds make the event family manifestly finite. -/
abbrev LongIntervalIndex (N : ℕ) :=
  {pair : Fin (18 * N + 1) × Fin (18 * N + 1) //
    2000 < pair.2.val ∧ pair.1.val + 2 * pair.2.val ≤ 18 * N}

def LongIntervalIndex.start {N : ℕ} (event : LongIntervalIndex N) : ℕ :=
  event.val.1.val

def LongIntervalIndex.length {N : ℕ} (event : LongIntervalIndex N) : ℕ :=
  event.val.2.val

theorem LongIntervalIndex.long {N : ℕ} (event : LongIntervalIndex N) :
    2000 < event.length := event.property.1

theorem LongIntervalIndex.fits {N : ℕ} (event : LongIntervalIndex N) :
    event.start + 2 * event.length ≤ 18 * N := event.property.2

/-- Actual event family used in the finite variable-model LLL. -/
noncomputable def longIntervalEvent
    (N : ℕ) (outer : ℕ → Symbol) (event : LongIntervalIndex N) :
    Finset (Fin N → Choice) :=
  finiteIntervalBadEvent (N := N) (start := event.start)
    (ell := event.length) outer

def longIntervalSupport
    (N : ℕ) (event : LongIntervalIndex N) : Finset (Fin N) :=
  intervalBlockSupport N event.start event.length

theorem longIntervalEvent_dependsOn
    (N : ℕ) (outer : ℕ → Symbol) (event : LongIntervalIndex N) :
    DependsOn (longIntervalEvent N outer event) (longIntervalSupport N event) := by
  exact finiteIntervalBadEvent_dependsOn outer event.fits

/-- Two different events are neighbors exactly when their macroblock supports meet. -/
def longIntervalNeighbors
    (N : ℕ) (event : LongIntervalIndex N) : Finset (LongIntervalIndex N) :=
  Finset.univ.filter fun other =>
    other ≠ event ∧ ¬Disjoint (longIntervalSupport N event) (longIntervalSupport N other)

/-- Intersecting concrete supports are related by the closed dependency
neighborhood used by the witness scan. -/
theorem longIntervalSupport_overlap_closedNeighbor
    {N : ℕ} (left right : LongIntervalIndex N)
    (overlaps :
      ¬Disjoint (longIntervalSupport N left) (longIntervalSupport N right)) :
    left ∈ closedNeighbors (longIntervalNeighbors N) right := by
  by_cases same : left = right
  · subst left
    exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    simp only [longIntervalNeighbors, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨same, fun disjoint => overlaps disjoint.symm⟩

theorem nonneighbor_support_disjoint
    {N : ℕ} (event : LongIntervalIndex N) (S : Finset (LongIntervalIndex N))
    (eventNotIn : event ∉ S) (nonneighbors : Disjoint S (longIntervalNeighbors N event)) :
    ∀ other ∈ S,
      Disjoint (longIntervalSupport N event) (longIntervalSupport N other) := by
  intro other otherIn
  by_contra notDisjoint
  have otherNe : other ≠ event := by
    intro equality
    subst equality
    exact eventNotIn otherIn
  have otherNeighbor : other ∈ longIntervalNeighbors N event := by
    simp [longIntervalNeighbors, otherNe, notDisjoint]
  exact Finset.disjoint_left.mp nonneighbors otherIn otherNeighbor

/-- The precise dependency equality required by the asymmetric LLL, now derived
from disjoint macroblock coordinates rather than postulated. -/
theorem concrete_long_interval_dependency
    (N : ℕ) (outer : ℕ → Symbol)
    (event : LongIntervalIndex N) (S : Finset (LongIntervalIndex N))
    (eventNotIn : event ∉ S)
    (nonneighbors : Disjoint S (longIntervalNeighbors N event)) :
    finiteBadAvoidMass (longIntervalEvent N outer) event S =
      finiteEventMass (longIntervalEvent N outer) event *
        finiteAvoidMass (longIntervalEvent N outer) S := by
  apply variable_dependency_equality
    (longIntervalEvent N outer) (longIntervalSupport N)
    (longIntervalEvent_dependsOn N outer) event S
  exact nonneighbor_support_disjoint event S eventNotIn nonneighbors

end TernarySyncAudit
