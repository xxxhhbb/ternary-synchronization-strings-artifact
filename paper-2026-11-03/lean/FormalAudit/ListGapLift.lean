import Mathlib
import FormalAudit.CommonSubsequence
import FormalAudit.DeterministicLift

namespace TernarySyncAudit

/-- Real-valued insertion/deletion cost associated with a common subsequence. -/
def commonSubsequenceCost
    {alpha : Type*} (left right subsequence : List alpha) : ℝ :=
  left.length + right.length - 2 * subsequence.length

/-- Every common subsequence certifies at least the stated normalized gap. -/
def ListPairGapAtLeast
    {alpha : Type*} (eta : ℝ) (left right : List alpha) : Prop :=
  ∀ subsequence, IsCommonSubsequence subsequence left right →
    eta * (left.length + right.length) ≤
      commonSubsequenceCost left right subsequence

/-- Strict form used in the synchronization-string definition. -/
def ListPairGapStrict
    {alpha : Type*} (gap : ℝ) (left right : List alpha) : Prop :=
  ∀ subsequence, IsCommonSubsequence subsequence left right →
    gap * (left.length + right.length) <
      commonSubsequenceCost left right subsequence

/-- The deletion-witness gap is exactly the standard equal-length LCS gap. -/
theorem equal_list_gap_of_no_small_deletion
    {alpha : Type*} {n : ℕ} (left right : FixedWord alpha n)
    (noSmall : ∀ d (hd : d ≤ n), 2000 * d < n →
      ¬HasCommonSubsequenceAfterDeleting hd left right) :
    ListPairGapAtLeast ((1 : ℝ) / 2000)
      (fixedWordList left) (fixedWordList right) := by
  intro subsequence common
  have subsequenceLe : subsequence.length ≤ n := by
    exact (List.Sublist.length_le common.1).trans_eq (fixedWordList_length left)
  let d := n - subsequence.length
  have dLe : d ≤ n := Nat.sub_le _ _
  have lengthIdentity : subsequence.length = n - d := by
    dsimp [d]
    omega
  have notSmall : ¬2000 * d < n := by
    intro small
    apply noSmall d dLe small
    apply (commonSubsequenceAfterDeleting_iff_list dLe left right).mpr
    exact ⟨subsequence, lengthIdentity, common⟩
  have deletionLower : n ≤ 2000 * d := by omega
  have costIdentity :
      commonSubsequenceCost (fixedWordList left) (fixedWordList right) subsequence =
        (2 * d : ℕ) := by
    unfold commonSubsequenceCost
    rw [fixedWordList_length, fixedWordList_length]
    push_cast
    dsimp [d]
    rw [Nat.cast_sub subsequenceLe]
    ring
  rw [fixedWordList_length, fixedWordList_length, costIdentity]
  have deletionLowerReal : (n : ℝ) ≤ 2000 * d := by exact_mod_cast deletionLower
  push_cast
  nlinarith

/-- A subsequence of an append splits at the append boundary. -/
theorem sublist_append_split
    {alpha : Type*} {subsequence left right : List alpha}
    (h : List.Sublist subsequence (left ++ right)) :
    ∃ leftPart rightPart,
      subsequence = leftPart ++ rightPart ∧
        List.Sublist leftPart left ∧ List.Sublist rightPart right := by
  induction left generalizing subsequence with
  | nil =>
      refine ⟨[], subsequence, by simp, List.Sublist.slnil, ?_⟩
      simpa using h
  | cons head tail ih =>
      change List.Sublist subsequence (head :: (tail ++ right)) at h
      cases h with
      | cons _ skipped =>
          rcases ih skipped with ⟨leftPart, rightPart, equality, leftSub, rightSub⟩
          exact ⟨leftPart, rightPart, equality,
            List.Sublist.cons head leftSub, rightSub⟩
      | cons_cons _ kept =>
          rcases ih kept with ⟨leftPart, rightPart, equality, leftSub, rightSub⟩
          refine ⟨head :: leftPart, rightPart, ?_,
            List.Sublist.cons_cons head leftSub, rightSub⟩
          simp [equality]

/-- Extending the right word by a suffix loses at most the suffix length from
the equal-length insertion/deletion lower bound. -/
theorem right_extension_gap
    {alpha : Type*} {eta gap : ℝ} (left rightPrefix suffix : List alpha)
    (equalLength : left.length = rightPrefix.length)
    (leftPositive : 0 < left.length)
    (etaNonnegative : 0 ≤ eta)
    (gapStrict : gap < eta / (2 + eta))
    (equalGap : ListPairGapAtLeast eta left rightPrefix) :
    ListPairGapStrict gap left (rightPrefix ++ suffix) := by
  intro subsequence common
  rcases sublist_append_split common.2 with
    ⟨prefixPart, suffixPart, subsequenceEq, prefixSub, suffixSub⟩
  have prefixInSubsequence : List.Sublist prefixPart subsequence := by
    rw [subsequenceEq]
    exact List.sublist_append_left _ _
  have prefixCommon : IsCommonSubsequence prefixPart left rightPrefix :=
    ⟨prefixInSubsequence.trans common.1, prefixSub⟩
  have equalLower := equalGap prefixPart prefixCommon
  have suffixLength : suffixPart.length ≤ suffix.length :=
    List.Sublist.length_le suffixSub
  have subsequenceLength :
      subsequence.length = prefixPart.length + suffixPart.length := by
    rw [subsequenceEq, List.length_append]
  have subsequenceLeLeft : subsequence.length ≤ left.length :=
    List.Sublist.length_le common.1
  let a : ℝ := left.length
  let z : ℝ := suffix.length
  let edit : ℝ := commonSubsequenceCost left (rightPrefix ++ suffix) subsequence
  have zNonnegative : 0 ≤ z := by positivity
  have aPositive : 0 < a := by
    dsimp [a]
    exact_mod_cast leftPositive
  have subsequenceLeLeftReal : (subsequence.length : ℝ) ≤ left.length := by
    exact_mod_cast subsequenceLeLeft
  have suffixLengthReal : (suffixPart.length : ℝ) ≤ suffix.length := by
    exact_mod_cast suffixLength
  have subsequenceLengthReal :
      (subsequence.length : ℝ) = prefixPart.length + suffixPart.length := by
    exact_mod_cast subsequenceLength
  have equalLengthReal : (left.length : ℝ) = rightPrefix.length := by
    exact_mod_cast equalLength
  have appendLengthReal : ((rightPrefix ++ suffix).length : ℝ) =
      rightPrefix.length + suffix.length := by
    simp
  have lengthDifferenceLower : z ≤ edit := by
    dsimp [edit, z, a, commonSubsequenceCost]
    nlinarith
  have equalDerivedLower : 2 * eta * a - z ≤ edit := by
    dsimp [edit, z, a, commonSubsequenceCost] at equalLower ⊢
    nlinarith
  have maxLower : max z (2 * eta * a - z) ≤ edit :=
    max_le lengthDifferenceLower equalDerivedLower
  have strict := strict_gap_from_unequal_interval_bounds
    etaNonnegative aPositive zNonnegative gapStrict maxLower
  dsimp [edit, a, z, commonSubsequenceCost] at strict ⊢
  simp only [List.length_append]
  push_cast at strict ⊢
  nlinarith

/-- Symmetric boundary case: extending the left word by a prefix loses at most
the prefix length from the equal-length bound at the common boundary. -/
theorem left_extension_gap
    {alpha : Type*} {eta gap : ℝ} (leftPrefix leftSuffix right : List alpha)
    (equalLength : leftSuffix.length = right.length)
    (rightPositive : 0 < right.length)
    (etaNonnegative : 0 ≤ eta)
    (gapStrict : gap < eta / (2 + eta))
    (equalGap : ListPairGapAtLeast eta leftSuffix right) :
    ListPairGapStrict gap (leftPrefix ++ leftSuffix) right := by
  intro subsequence common
  rcases sublist_append_split common.1 with
    ⟨prefixPart, suffixPart, subsequenceEq, prefixSub, suffixSub⟩
  have suffixInSubsequence : List.Sublist suffixPart subsequence := by
    rw [subsequenceEq]
    exact List.sublist_append_right _ _
  have suffixCommon : IsCommonSubsequence suffixPart leftSuffix right :=
    ⟨suffixSub, suffixInSubsequence.trans common.2⟩
  have equalLower := equalGap suffixPart suffixCommon
  have prefixLength : prefixPart.length ≤ leftPrefix.length :=
    List.Sublist.length_le prefixSub
  have subsequenceLength :
      subsequence.length = prefixPart.length + suffixPart.length := by
    rw [subsequenceEq, List.length_append]
  have subsequenceLeRight : subsequence.length ≤ right.length :=
    List.Sublist.length_le common.2
  let a : ℝ := right.length
  let z : ℝ := leftPrefix.length
  let edit : ℝ := commonSubsequenceCost (leftPrefix ++ leftSuffix) right subsequence
  have zNonnegative : 0 ≤ z := by positivity
  have aPositive : 0 < a := by
    dsimp [a]
    exact_mod_cast rightPositive
  have subsequenceLeRightReal : (subsequence.length : ℝ) ≤ right.length := by
    exact_mod_cast subsequenceLeRight
  have prefixLengthReal : (prefixPart.length : ℝ) ≤ leftPrefix.length := by
    exact_mod_cast prefixLength
  have subsequenceLengthReal :
      (subsequence.length : ℝ) = prefixPart.length + suffixPart.length := by
    exact_mod_cast subsequenceLength
  have equalLengthReal : (leftSuffix.length : ℝ) = right.length := by
    exact_mod_cast equalLength
  have appendLengthReal : ((leftPrefix ++ leftSuffix).length : ℝ) =
      leftPrefix.length + leftSuffix.length := by simp
  have lengthDifferenceLower : z ≤ edit := by
    dsimp [edit, z, a, commonSubsequenceCost]
    nlinarith
  have equalDerivedLower : 2 * eta * a - z ≤ edit := by
    dsimp [edit, z, a, commonSubsequenceCost] at equalLower ⊢
    nlinarith
  have maxLower : max z (2 * eta * a - z) ≤ edit :=
    max_le lengthDifferenceLower equalDerivedLower
  have strict := strict_gap_from_unequal_interval_bounds
    etaNonnegative aPositive zNonnegative gapStrict maxLower
  dsimp [edit, a, z, commonSubsequenceCost] at strict ⊢
  simp only [List.length_append]
  push_cast at strict ⊢
  nlinarith

end TernarySyncAudit
