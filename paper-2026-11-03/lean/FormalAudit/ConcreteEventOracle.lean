import Mathlib
import FormalAudit.LCSRecurrence
import FormalAudit.ConcreteDependency

namespace TernarySyncAudit

/-- Executable Boolean version of one concrete finite interval event. -/
def finiteIntervalBadB
    {N start ell : ℕ} (outer : ℕ → Symbol) (branch : Fin N → Choice) : Bool :=
  equalDeletionBadRecB
    (fixedWordList
      (finiteFirstInterval (start := start) (ell := ell) outer branch))
    (fixedWordList
      (finiteSecondInterval (start := start) (ell := ell) outer branch))

theorem finiteIntervalBadB_eq_true_iff
    {N start ell : ℕ} (outer : ℕ → Symbol) (branch : Fin N → Choice) :
    finiteIntervalBadB (start := start) (ell := ell) outer branch = true ↔
      branch ∈ finiteIntervalBadEvent
        (start := start) (ell := ell) outer := by
  rw [finiteIntervalBadB, equalDeletionBadRecB_eq_equalDeletionBadB,
    equalDeletionBadB_eq_true_iff]
  simp only [finiteIntervalBadEvent, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [mem_explicit_ternary_deletionBall_iff]
  constructor
  · rintro ⟨d, hd, small, common⟩
    exact ⟨d, small, hd, common⟩
  · rintro ⟨d, small, hd, common⟩
    exact ⟨d, hd, small, common⟩

/-- Executable Boolean version of an indexed long event. -/
def longIntervalBadB
    {N : ℕ} (outer : ℕ → Symbol) (branch : Fin N → Choice)
    (event : LongIntervalIndex N) : Bool :=
  finiteIntervalBadB (start := event.start) (ell := event.length) outer branch

theorem longIntervalBadB_eq_true_iff
    {N : ℕ} (outer : ℕ → Symbol) (branch : Fin N → Choice)
    (event : LongIntervalIndex N) :
    longIntervalBadB outer branch event = true ↔
      branch ∈ longIntervalEvent N outer event := by
  exact finiteIntervalBadB_eq_true_iff outer branch

end TernarySyncAudit
