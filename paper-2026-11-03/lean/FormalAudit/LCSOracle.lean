import Mathlib
import Mathlib.Data.List.MinMax
import FormalAudit.CommonSubsequence

namespace TernarySyncAudit

/-- The finite list of all subsequences of `left` that are also subsequences
of `right`.  It may contain duplicates, which are harmless for maximization. -/
def commonSubsequenceCandidates
    {alpha : Type*} [DecidableEq alpha] (left right : List alpha) :
    List (List alpha) :=
  left.sublists.filter fun candidate => decide (List.Sublist candidate right)

theorem mem_commonSubsequenceCandidates_iff
    {alpha : Type*} [DecidableEq alpha]
    {candidate left right : List alpha} :
    candidate ∈ commonSubsequenceCandidates left right ↔
      IsCommonSubsequence candidate left right := by
  simp [commonSubsequenceCandidates, IsCommonSubsequence]

theorem commonSubsequenceCandidates_nonempty
    {alpha : Type*} [DecidableEq alpha] (left right : List alpha) :
    (commonSubsequenceCandidates left right).length > 0 := by
  have emptyMem : [] ∈ commonSubsequenceCandidates left right := by
    apply mem_commonSubsequenceCandidates_iff.mpr
    exact ⟨List.nil_sublist _, List.nil_sublist _⟩
  exact List.length_pos_of_mem emptyMem

/-- A directly executable LCS oracle: enumerate all subsequences of the first
word, keep the common ones, and take the largest length.  This is exponential,
but its specification is small and kernel-checkable. -/
def lcsLength {alpha : Type*} [DecidableEq alpha]
    (left right : List alpha) : ℕ :=
  let lengths : List ℕ :=
    (commonSubsequenceCandidates left right).map fun candidate => candidate.length
  lengths.maximum_of_length_pos (by
    have zeroMem : 0 ∈ lengths := by
      apply List.mem_map.mpr
      exact ⟨[], by
        apply mem_commonSubsequenceCandidates_iff.mpr
        exact ⟨List.nil_sublist _, List.nil_sublist _⟩, rfl⟩
    exact List.length_pos_of_mem zeroMem)

theorem commonSubsequence_length_le_lcsLength
    {alpha : Type*} [DecidableEq alpha]
    {candidate left right : List alpha}
    (common : IsCommonSubsequence candidate left right) :
    candidate.length ≤ lcsLength left right := by
  unfold lcsLength
  apply List.le_maximum_of_length_pos_of_mem
  apply List.mem_map.mpr
  exact ⟨candidate, mem_commonSubsequenceCandidates_iff.mpr common, rfl⟩

theorem exists_commonSubsequence_length_eq_lcsLength
    {alpha : Type*} [DecidableEq alpha] (left right : List alpha) :
    ∃ candidate,
      IsCommonSubsequence candidate left right ∧
        candidate.length = lcsLength left right := by
  unfold lcsLength
  let candidates := commonSubsequenceCandidates left right
  let lengths : List ℕ := candidates.map fun candidate => candidate.length
  have lengthsPositive : lengths.length > 0 := by
    dsimp [lengths, candidates]
    simpa using commonSubsequenceCandidates_nonempty left right
  have maximumMem : lengths.maximum_of_length_pos lengthsPositive ∈ lengths :=
    List.maximum_of_length_pos_mem lengthsPositive
  rcases List.mem_map.mp maximumMem with ⟨candidate, candidateMem, lengthEq⟩
  refine ⟨candidate, mem_commonSubsequenceCandidates_iff.mp candidateMem, ?_⟩
  exact lengthEq

theorem lcsLength_le_left_length
    {alpha : Type*} [DecidableEq alpha] (left right : List alpha) :
    lcsLength left right ≤ left.length := by
  rcases exists_commonSubsequence_length_eq_lcsLength left right with
    ⟨candidate, common, lengthEq⟩
  rw [← lengthEq]
  exact List.Sublist.length_le common.1

theorem lcsLength_le_right_length
    {alpha : Type*} [DecidableEq alpha] (left right : List alpha) :
    lcsLength left right ≤ right.length := by
  rcases exists_commonSubsequence_length_eq_lcsLength left right with
    ⟨candidate, common, lengthEq⟩
  rw [← lengthEq]
  exact List.Sublist.length_le common.2

/-- Boolean query for the existence of a common subsequence strictly longer
than `threshold`. -/
def hasCommonSubsequenceLongerB
    {alpha : Type*} [DecidableEq alpha]
    (left right : List alpha) (threshold : ℕ) : Bool :=
  decide (threshold < lcsLength left right)

theorem hasCommonSubsequenceLongerB_eq_true_iff
    {alpha : Type*} [DecidableEq alpha]
    (left right : List alpha) (threshold : ℕ) :
    hasCommonSubsequenceLongerB left right threshold = true ↔
      ∃ candidate, IsCommonSubsequence candidate left right ∧
        threshold < candidate.length := by
  rw [hasCommonSubsequenceLongerB, decide_eq_true_eq]
  constructor
  · intro thresholdLt
    rcases exists_commonSubsequence_length_eq_lcsLength left right with
      ⟨candidate, common, lengthEq⟩
    exact ⟨candidate, common, by simpa [lengthEq] using thresholdLt⟩
  · rintro ⟨candidate, common, thresholdLt⟩
    exact thresholdLt.trans_le (commonSubsequence_length_le_lcsLength common)

/-- Executable equal-block bad-event predicate in the paper's exact integer
normalization. -/
def equalDeletionBadB
    {alpha : Type*} [DecidableEq alpha]
    (left right : List alpha) : Bool :=
  decide (2000 * (left.length - lcsLength left right) < left.length)

theorem equalDeletionBadB_eq_true_iff
    {alpha : Type*} [DecidableEq alpha]
    {n : ℕ} (left right : FixedWord alpha n) :
    equalDeletionBadB (fixedWordList left) (fixedWordList right) = true ↔
      ∃ d, ∃ hd : d ≤ n, 2000 * d < n ∧
        HasCommonSubsequenceAfterDeleting hd left right := by
  rw [equalDeletionBadB, decide_eq_true_eq]
  let leftList := fixedWordList left
  let rightList := fixedWordList right
  let maximum := lcsLength leftList rightList
  have maximumLe : maximum ≤ n := by
    dsimp [maximum, leftList]
    simpa using lcsLength_le_left_length (fixedWordList left) (fixedWordList right)
  have maximumWitness :=
    exists_commonSubsequence_length_eq_lcsLength leftList rightList
  constructor
  · intro small
    let d := n - maximum
    have dLe : d ≤ n := Nat.sub_le _ _
    have maximumEq : maximum = n - d := by dsimp [d]; omega
    rcases maximumWitness with ⟨candidate, common, candidateLength⟩
    refine ⟨d, dLe, ?_, ?_⟩
    · simpa [leftList, fixedWordList_length, maximum, d] using small
    · apply (commonSubsequenceAfterDeleting_iff_list dLe left right).mpr
      exact ⟨candidate, candidateLength.trans maximumEq, common⟩
  · rintro ⟨d, dLe, small, common⟩
    rcases (commonSubsequenceAfterDeleting_iff_list dLe left right).mp common with
      ⟨candidate, candidateLength, candidateCommon⟩
    have candidateLeMaximum : candidate.length ≤ maximum := by
      simpa [maximum, leftList, rightList] using
        (commonSubsequence_length_le_lcsLength candidateCommon)
    have deletionComparison : n - maximum ≤ d := by omega
    simpa [leftList, fixedWordList_length, maximum] using
      (lt_of_le_of_lt (Nat.mul_le_mul_left 2000 deletionComparison) small)

end TernarySyncAudit
