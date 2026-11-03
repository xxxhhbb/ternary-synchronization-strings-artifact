import Mathlib
import FormalAudit.SynchronizationHeadline
import FormalAudit.CurrentNumerics

namespace TernarySyncAudit

/-! Kernel-checked deterministic endgame for the current `2001/2002`
theorem.  The probabilistic construction only has to supply the equal-block
premise below. -/

def CurrentEqualBlockGap (stream : ℕ → Symbol) (limit : ℕ) : Prop :=
  ∀ start length,
    0 < length → start + 2 * length ≤ limit →
      ListPairGapAtLeast ((1 : ℝ) / 1000)
        (streamFactorList stream start length)
        (streamFactorList stream (start + length) length)

/-- The exact current equal-to-unequal lift, including both orientations of
the unequal adjacent pair and the strict advertised slack. -/
theorem current_synchronization_gap_of_equal_gap
    {stream : ℕ → Symbol} {limit : ℕ}
    (equalGap : CurrentEqualBlockGap stream limit) :
    IsSynchronizationStringGap stream limit ((1 : ℝ) / 2002) := by
  intro left boundary right leftBoundary boundaryRight rightLimit
  let a := boundary - left
  let b := right - boundary
  have aPositive : 0 < a := by dsimp [a]; omega
  have bPositive : 0 < b := by dsimp [b]; omega
  have boundaryEq : left + a = boundary := by dsimp [a]; omega
  have rightEq : boundary + b = right := by dsimp [b]; omega
  change ListPairGapStrict ((1 : ℝ) / 2002)
    (streamFactorList stream left a) (streamFactorList stream boundary b)
  by_cases shorterLeft : a ≤ b
  · let z := b - a
    have bEq : b = a + z := by dsimp [z]; omega
    have equalFits : left + 2 * a ≤ limit := by omega
    have localEqualGap := equalGap left a aPositive equalFits
    have localEqualGap' :
        ListPairGapAtLeast ((1 : ℝ) / 1000)
          (streamFactorList stream left a)
          (streamFactorList stream boundary a) := by
      simpa [boundaryEq] using localEqualGap
    have suffixDecomposition :
        streamFactorList stream boundary b =
          streamFactorList stream boundary a ++
            streamFactorList stream (boundary + a) z := by
      rw [bEq]
      exact streamFactorList_add stream boundary a z
    have lifted := right_extension_gap
      (eta := (1 : ℝ) / 1000) (gap := (1 : ℝ) / 2002)
      (streamFactorList stream left a)
      (streamFactorList stream boundary a)
      (streamFactorList stream (boundary + a) z)
      (by simp) (by simp [aPositive]) (by norm_num)
      (by
        rw [current_equal_to_arbitrary_gap]
        exact current_advertised_gap_strict)
      localEqualGap'
    rw [suffixDecomposition]
    exact lifted
  · have shorterRight : b < a := by omega
    let z := a - b
    have aEq : a = z + b := by dsimp [z]; omega
    have suffixStartEq : left + z + b = boundary := by omega
    have equalStartFits : left + z + 2 * b ≤ limit := by omega
    have localEqualGap := equalGap (left + z) b bPositive equalStartFits
    have prefixDecomposition :
        streamFactorList stream left a =
          streamFactorList stream left z ++
            streamFactorList stream (left + z) b := by
      rw [aEq]
      exact streamFactorList_add stream left z b
    have lifted := left_extension_gap
      (eta := (1 : ℝ) / 1000) (gap := (1 : ℝ) / 2002)
      (streamFactorList stream left z)
      (streamFactorList stream (left + z) b)
      (streamFactorList stream boundary b)
      (by simp) (by simp [bPositive]) (by norm_num)
      (by
        rw [current_equal_to_arbitrary_gap]
        exact current_advertised_gap_strict)
      (by simpa [suffixStartEq] using localEqualGap)
    rw [prefixDecomposition]
    exact lifted

theorem current_epsilon_synchronization_of_equal_gap
    {stream : ℕ → Symbol} {limit : ℕ}
    (equalGap : CurrentEqualBlockGap stream limit) :
    IsEpsilonSynchronizationString stream limit ((2001 : ℝ) / 2002) := by
  rw [IsEpsilonSynchronizationString, current_headline_gap_identity]
  exact current_synchronization_gap_of_equal_gap equalGap

/-- Exact quantifier closure for the current headline, conditional only on
the equal-block output supplied by the LLL construction. -/
theorem current_headline_from_equal_block_existence
    (existence : ∀ n, ∃ stream : ℕ → Symbol,
      CurrentEqualBlockGap stream n) :
    ∃ epsilon : ℝ, epsilon < 1 ∧
      ∀ n, ∃ stream : ℕ → Symbol,
        IsEpsilonSynchronizationString stream n epsilon := by
  refine ⟨(2001 : ℝ) / 2002, current_headline_epsilon_lt_one, ?_⟩
  intro n
  rcases existence n with ⟨stream, equalGap⟩
  exact ⟨stream, current_epsilon_synchronization_of_equal_gap equalGap⟩

end TernarySyncAudit
