import Mathlib
import Mathlib.Data.List.OfFn
import FormalAudit.ListGapLift
import FormalAudit.ConcretePrefixAbundance

namespace TernarySyncAudit

/-- Standard list factor of a symbol stream. -/
def streamFactorList (stream : ℕ → Symbol) (start length : ℕ) : List Symbol :=
  fixedWordList (symbolInterval stream start length)

@[simp] theorem streamFactorList_length
    (stream : ℕ → Symbol) (start length : ℕ) :
    (streamFactorList stream start length).length = length := by
  simp [streamFactorList]

/-- Consecutive stream factors concatenate exactly. -/
theorem streamFactorList_add
    (stream : ℕ → Symbol) (start leftLength rightLength : ℕ) :
    streamFactorList stream start (leftLength + rightLength) =
      streamFactorList stream start leftLength ++
        streamFactorList stream (start + leftLength) rightLength := by
  unfold streamFactorList fixedWordList symbolInterval
  rw [← List.ofFn_fin_append]
  congr 1
  funext position
  refine Fin.addCases
    (motive := fun p =>
      stream (start + p.val) =
        Fin.append
          (fun q : Fin leftLength => stream (start + q.val))
          (fun q : Fin rightLength => stream (start + leftLength + q.val)) p)
    ?_ ?_ position
  · intro leftPosition
    simp [Fin.append_left]
  · intro rightPosition
    simp [Fin.append_right]
    congr 1
    omega

/-- Standard synchronization-string condition in its LCS-equivalent form:
every common subsequence gives strict normalized insertion/deletion cost. -/
def IsSynchronizationStringGap
    (stream : ℕ → Symbol) (limit : ℕ) (gap : ℝ) : Prop :=
  ∀ left boundary right,
    left < boundary → boundary < right → right ≤ limit →
      ListPairGapStrict gap
        (streamFactorList stream left (boundary - left))
        (streamFactorList stream boundary (right - boundary))

/-- Conventional epsilon-parameterization: the edit-distance gap is
`1 - epsilon`. -/
def IsEpsilonSynchronizationString
    (stream : ℕ → Symbol) (limit : ℕ) (epsilon : ℝ) : Prop :=
  IsSynchronizationStringGap stream limit (1 - epsilon)

theorem headline_epsilon_lt_one :
    ((5999 : ℝ) / 6000) < 1 := by
  norm_num

theorem headline_epsilon_gap_identity :
    1 - ((5999 : ℝ) / 6000) = (1 : ℝ) / 6000 := by
  norm_num

/-- Equal deletion gaps imply the standard equal-length list gap. -/
theorem equal_stream_list_gap
    {stream : ℕ → Symbol} {limit start length : ℕ}
    (noSmall : NoSmallEqualBlockDeletion stream limit)
    (lengthPositive : 0 < length) (fits : start + 2 * length ≤ limit) :
    ListPairGapAtLeast ((1 : ℝ) / 2000)
      (streamFactorList stream start length)
      (streamFactorList stream (start + length) length) := by
  apply equal_list_gap_of_no_small_deletion
  intro d hd small
  exact noSmall start length lengthPositive fits d hd small

/-- Fully formal equal-to-unequal interval lift at the paper's explicit
constant.  This closes the standard synchronization-string definition, not
only the equal-block surrogate. -/
theorem synchronization_gap_of_equal_deletion_gap
    {stream : ℕ → Symbol} {limit : ℕ}
    (noSmall : NoSmallEqualBlockDeletion stream limit) :
    IsSynchronizationStringGap stream limit ((1 : ℝ) / 6000) := by
  intro left boundary right leftBoundary boundaryRight rightLimit
  let a := boundary - left
  let b := right - boundary
  have aPositive : 0 < a := by dsimp [a]; omega
  have bPositive : 0 < b := by dsimp [b]; omega
  have boundaryEq : left + a = boundary := by dsimp [a]; omega
  have rightEq : boundary + b = right := by dsimp [b]; omega
  change ListPairGapStrict ((1 : ℝ) / 6000)
    (streamFactorList stream left a) (streamFactorList stream boundary b)
  by_cases shorterLeft : a ≤ b
  · let z := b - a
    have bEq : b = a + z := by dsimp [z]; omega
    have equalFits : left + 2 * a ≤ limit := by omega
    have equalGap := equal_stream_list_gap noSmall aPositive equalFits
    have equalGap' :
        ListPairGapAtLeast ((1 : ℝ) / 2000)
          (streamFactorList stream left a)
          (streamFactorList stream boundary a) := by
      simpa [boundaryEq] using equalGap
    have suffixDecomposition :
        streamFactorList stream boundary b =
          streamFactorList stream boundary a ++
            streamFactorList stream (boundary + a) z := by
      rw [bEq]
      exact streamFactorList_add stream boundary a z
    have lifted := right_extension_gap
      (streamFactorList stream left a)
      (streamFactorList stream boundary a)
      (streamFactorList stream (boundary + a) z)
      (by simp) (by simp [aPositive]) (by norm_num)
      headline_gap_is_strict equalGap'
    rw [suffixDecomposition]
    exact lifted
  · have shorterRight : b < a := by omega
    let z := a - b
    have aEq : a = z + b := by dsimp [z]; omega
    have suffixStartEq : left + z + b = boundary := by omega
    have equalStartFits : left + z + 2 * b ≤ limit := by omega
    have equalGap := equal_stream_list_gap noSmall bPositive equalStartFits
    have prefixDecomposition :
        streamFactorList stream left a =
          streamFactorList stream left z ++
            streamFactorList stream (left + z) b := by
      rw [aEq]
      exact streamFactorList_add stream left z b
    have lifted := left_extension_gap
      (streamFactorList stream left z)
      (streamFactorList stream (left + z) b)
      (streamFactorList stream boundary b)
      (by simp) (by simp [bPositive]) (by norm_num)
      headline_gap_is_strict (by
        simpa [suffixStartEq] using equalGap)
    rw [prefixDecomposition]
    exact lifted

/-- Conditional standard headline for a finite encoded word. -/
theorem exists_synchronizing_choice
    (N : ℕ) (outer : ℕ → Symbol) (outerSquareFree : OuterSquareFree outer) :
    ∃ branch : Fin N → Choice,
      IsSynchronizationStringGap
        (codeStream outer (extendFiniteChoices branch))
        (18 * N) ((1 : ℝ) / 6000) := by
  rcases exists_equal_block_synchronizing_choice N outer outerSquareFree with
    ⟨branch, equalGap⟩
  exact ⟨branch, synchronization_gap_of_equal_deletion_gap equalGap⟩

/-- Arbitrary-branch form used by the abundance theorem. -/
theorem epsilon_synchronizing_of_avoids
    {N : ℕ} (outer : ℕ → Symbol) (branch : Fin N → Choice)
    (outerSquareFree : OuterSquareFree outer)
    (avoids : ∀ event : LongIntervalIndex N,
      branch ∉ longIntervalEvent N outer event) :
    IsEpsilonSynchronizationString
      (codeStream outer (extendFiniteChoices branch)) (18 * N)
      ((5999 : ℝ) / 6000) := by
  rw [IsEpsilonSynchronizationString, headline_epsilon_gap_identity]
  apply synchronization_gap_of_equal_deletion_gap
  exact equal_block_synchronizing_of_avoids
    outer branch outerSquareFree avoids

/-- Synchronization is inherited by every shorter prefix. -/
theorem synchronization_gap_mono
    {stream : ℕ → Symbol} {short long : ℕ} {gap : ℝ}
    (shortLeLong : short ≤ long)
    (synchronizing : IsSynchronizationStringGap stream long gap) :
    IsSynchronizationStringGap stream short gap := by
  intro left boundary right leftBoundary boundaryRight rightShort
  exact synchronizing left boundary right leftBoundary boundaryRight
    (rightShort.trans shortLeLong)

/-- Main finite-length conclusion conditional only on the classical existence
of one infinite ternary square-free outer stream. -/
theorem ternary_synchronization_string_of_outer_squarefree
    (n : ℕ) (outer : ℕ → Symbol) (outerSquareFree : OuterSquareFree outer) :
    ∃ stream : ℕ → Symbol,
      IsSynchronizationStringGap stream n ((1 : ℝ) / 6000) := by
  let N := macroblockCount n
  rcases exists_synchronizing_choice N outer outerSquareFree with
    ⟨branch, synchronizing⟩
  refine ⟨codeStream outer (extendFiniteChoices branch), ?_⟩
  apply synchronization_gap_mono (prefix_fits_macroblocks n)
  exact synchronizing

/-- Once a concrete infinite ternary square-free stream is supplied, the
headline holds uniformly for every requested length. -/
theorem ternary_synchronization_strings_from_squarefree_stream
    (outer : ℕ → Symbol) (outerSquareFree : OuterSquareFree outer) :
    ∀ n, ∃ stream : ℕ → Symbol,
      IsSynchronizationStringGap stream n ((1 : ℝ) / 6000) := by
  intro n
  exact ternary_synchronization_string_of_outer_squarefree n outer outerSquareFree

/-- Exact conventional epsilon-form of the headline: a single fixed
`epsilon = 5999/6000 < 1` works for every requested length. -/
theorem ternary_epsilon_synchronization_strings_from_squarefree_stream
    (outer : ℕ → Symbol) (outerSquareFree : OuterSquareFree outer) :
    ∀ n, ∃ stream : ℕ → Symbol,
      IsEpsilonSynchronizationString stream n ((5999 : ℝ) / 6000) := by
  intro n
  rcases ternary_synchronization_string_of_outer_squarefree
    n outer outerSquareFree with ⟨stream, synchronizing⟩
  refine ⟨stream, ?_⟩
  simpa [IsEpsilonSynchronizationString, headline_epsilon_gap_identity] using
    synchronizing

/-- The paper's existential target with its sole classical combinatorics input
made explicit.  Supplying Thue's theorem closes the exact quantifier pattern
`exists epsilon < 1, forall n, exists ternary synchronization string`. -/
theorem ternary_synchronization_headline_of_thue
    (thue : ∃ outer : ℕ → Symbol, OuterSquareFree outer) :
    ∃ epsilon : ℝ, epsilon < 1 ∧
      ∀ n, ∃ stream : ℕ → Symbol,
        IsEpsilonSynchronizationString stream n epsilon := by
  rcases thue with ⟨outer, outerSquareFree⟩
  refine ⟨(5999 : ℝ) / 6000, headline_epsilon_lt_one, ?_⟩
  exact ternary_epsilon_synchronization_strings_from_squarefree_stream
    outer outerSquareFree

end TernarySyncAudit
