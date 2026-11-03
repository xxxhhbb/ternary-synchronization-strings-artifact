import Mathlib
import FormalAudit.ConcreteLLLExistence

namespace TernarySyncAudit

/-- A fixed-length factor of an already formed symbol stream. -/
def symbolInterval (stream : ℕ → Symbol) (start ell : ℕ) :
    FixedWord Symbol ell := fun position => stream (start + position.val)

/-- Exact equal-block property produced by the probabilistic construction:
no adjacent equal-length pair has a common subsequence after `d` deletions
when `2000*d < ell`. -/
def NoSmallEqualBlockDeletion
    (stream : ℕ → Symbol) (limit : ℕ) : Prop :=
  ∀ start ell, 0 < ell → start + 2 * ell ≤ limit →
    ∀ d (hd : d ≤ ell), 2000 * d < ell →
      ¬HasCommonSubsequenceAfterDeleting hd
        (symbolInterval stream start ell)
        (symbolInterval stream (start + ell) ell)

/-- Square-freeness rules out every short bad event: for `ell ≤ 2000`, the
integer inequality `2000*d < ell` forces `d=0`. -/
theorem no_short_bad_interval_of_squarefree
    {stream : ℕ → Symbol}
    (squarefree : ∀ start period, ¬IsSquareAt stream start period)
    {start ell d : ℕ} (ellPositive : 0 < ell) (ellShort : ell ≤ 2000)
    (smallDeletion : 2000 * d < ell) (hd : d ≤ ell) :
    ¬HasCommonSubsequenceAfterDeleting hd
      (symbolInterval stream start ell)
      (symbolInterval stream (start + ell) ell) := by
  have dZero : d = 0 := by omega
  subst d
  intro common
  have intervalEquality :
      symbolInterval stream start ell =
        symbolInterval stream (start + ell) ell :=
    (commonSubsequenceAfterDeleting_zero_iff _ _).mp common
  apply squarefree start ell
  refine ⟨ellPositive, ?_⟩
  intro offset offsetLt
  let position : Fin ell := ⟨offset, offsetLt⟩
  have equalityAt := congrFun intervalEquality position
  simpa [symbolInterval, Nat.add_assoc] using equalityAt

/-- A branch avoiding all indexed long events satisfies the long equal-block
deletion property on the entire finite encoded word. -/
theorem no_long_bad_interval_of_avoiding_events
    {N : ℕ} (outer : ℕ → Symbol) (branch : Fin N → Choice)
    (avoids : ∀ event : LongIntervalIndex N,
      branch ∉ longIntervalEvent N outer event)
    {start ell d : ℕ} (ellLong : 2000 < ell)
    (fits : start + 2 * ell ≤ 18 * N) (hd : d ≤ ell)
    (smallDeletion : 2000 * d < ell) :
    ¬HasCommonSubsequenceAfterDeleting hd
      (symbolInterval (codeStream outer (extendFiniteChoices branch)) start ell)
      (symbolInterval (codeStream outer (extendFiniteChoices branch))
        (start + ell) ell) := by
  change ¬HasCommonSubsequenceAfterDeleting hd
    (finiteFirstInterval (N := N) (start := start) (ell := ell) outer branch)
    (finiteSecondInterval (N := N) (start := start) (ell := ell) outer branch)
  have startBound : start < 18 * N + 1 := by omega
  have ellBound : ell < 18 * N + 1 := by omega
  let event : LongIntervalIndex N :=
    ⟨(⟨start, startBound⟩, ⟨ell, ellBound⟩), ellLong, fits⟩
  intro common
  apply avoids event
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply (mem_explicit_ternary_deletionBall_iff _ _).mpr
  refine ⟨d, smallDeletion, hd, ?_⟩
  simpa [event, LongIntervalIndex.start, LongIntervalIndex.length] using common

/-- Any particular branch avoiding every long event satisfies the exact
equal-block deletion gap; the square-free codebook handles all short events. -/
theorem equal_block_synchronizing_of_avoids
    {N : ℕ} (outer : ℕ → Symbol) (branch : Fin N → Choice)
    (outerSquareFree : OuterSquareFree outer)
    (avoids : ∀ event : LongIntervalIndex N,
      branch ∉ longIntervalEvent N outer event) :
    NoSmallEqualBlockDeletion
      (codeStream outer (extendFiniteChoices branch)) (18 * N) := by
  intro start ell ellPositive fits d hd smallDeletion
  by_cases ellLong : 2000 < ell
  · exact no_long_bad_interval_of_avoiding_events outer branch avoids
      ellLong fits hd smallDeletion
  · apply no_short_bad_interval_of_squarefree
      (fun squareStart period =>
        codeStream_has_no_square outer (extendFiniteChoices branch)
          outerSquareFree squareStart period)
      ellPositive (by omega) smallDeletion hd

/-- Conditional equal-block headline: the finite LLL branch plus any infinite
ternary square-free outer stream gives the exact `1/2000` deletion gap on all
equal adjacent blocks inside the encoded prefix. -/
theorem exists_equal_block_synchronizing_choice
    (N : ℕ) (outer : ℕ → Symbol) (outerSquareFree : OuterSquareFree outer) :
    ∃ branch : Fin N → Choice,
      NoSmallEqualBlockDeletion
        (codeStream outer (extendFiniteChoices branch)) (18 * N) := by
  rcases exists_choice_vector_with_no_long_bad_interval N outer with
    ⟨branch, avoids⟩
  exact ⟨branch,
    equal_block_synchronizing_of_avoids outer branch outerSquareFree avoids⟩

end TernarySyncAudit
