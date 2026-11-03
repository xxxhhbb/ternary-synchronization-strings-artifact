import Mathlib
import FormalAudit.LCSOracle

namespace TernarySyncAudit

/-- The standard LCS recurrence.  A memoized evaluation of this recurrence is
the quadratic dynamic program used by the algorithm. -/
def lcsRec {alpha : Type*} [DecidableEq alpha] : List alpha → List alpha → ℕ
  | [], _ => 0
  | _, [] => 0
  | headLeft :: tailLeft, headRight :: tailRight =>
      if headLeft = headRight then
        1 + lcsRec tailLeft tailRight
      else
        max (lcsRec tailLeft (headRight :: tailRight))
          (lcsRec (headLeft :: tailLeft) tailRight)
termination_by left right => left.length + right.length
decreasing_by all_goals simp_wf <;> omega

/-- Semantic certificate characterizing an exact LCS value. -/
def IsExactLCS
    {alpha : Type*} (value : ℕ) (left right : List alpha) : Prop :=
  (∃ candidate, IsCommonSubsequence candidate left right ∧
      candidate.length = value) ∧
    ∀ candidate, IsCommonSubsequence candidate left right →
      candidate.length ≤ value

theorem exactLCS_unique
    {alpha : Type*} {left right : List alpha} {first second : ℕ}
    (firstExact : IsExactLCS first left right)
    (secondExact : IsExactLCS second left right) :
    first = second := by
  rcases firstExact.1 with ⟨firstCandidate, firstCommon, firstLength⟩
  rcases secondExact.1 with ⟨secondCandidate, secondCommon, secondLength⟩
  have firstLe : first ≤ second := by
    rw [← firstLength]
    exact secondExact.2 firstCandidate firstCommon
  have secondLe : second ≤ first := by
    rw [← secondLength]
    exact firstExact.2 secondCandidate secondCommon
  omega

theorem lcsLength_isExact
    {alpha : Type*} [DecidableEq alpha] (left right : List alpha) :
    IsExactLCS (lcsLength left right) left right := by
  constructor
  · exact exists_commonSubsequence_length_eq_lcsLength left right
  · intro candidate common
    exact commonSubsequence_length_le_lcsLength common

theorem tail_sublist_of_sublist_cons
    {alpha : Type*} {candidate tail : List alpha} {head : alpha}
    (sublist : List.Sublist candidate (head :: tail)) :
    List.Sublist candidate.tail tail := by
  cases sublist with
  | cons _ skipped =>
      exact (List.tail_sublist candidate).trans skipped
  | cons_cons _ kept =>
      simpa using kept

theorem common_cons_ne_cases
    {alpha : Type*} {candidate leftTail rightTail : List alpha}
    {leftHead rightHead : alpha} (headsNe : leftHead ≠ rightHead)
    (common : IsCommonSubsequence candidate
      (leftHead :: leftTail) (rightHead :: rightTail)) :
    IsCommonSubsequence candidate leftTail (rightHead :: rightTail) ∨
      IsCommonSubsequence candidate (leftHead :: leftTail) rightTail := by
  rcases common with ⟨leftSublist, rightSublist⟩
  cases leftSublist with
  | cons _ leftSkipped =>
      exact Or.inl ⟨leftSkipped, rightSublist⟩
  | cons_cons _ leftKept =>
      cases rightSublist with
      | cons _ rightSkipped =>
          exact Or.inr ⟨List.Sublist.cons_cons _ leftKept, rightSkipped⟩
      | cons_cons _ rightKept =>
          exact (headsNe rfl).elim

/-- The standard recurrence returns a semantically exact LCS value. -/
theorem lcsRec_isExact
    {alpha : Type*} [DecidableEq alpha] (left right : List alpha) :
    IsExactLCS (lcsRec left right) left right := by
  induction left, right using lcsRec.induct with
  | case1 right =>
      constructor
      · refine ⟨[], ⟨List.nil_sublist _, List.nil_sublist _⟩, ?_⟩
        simp [lcsRec]
      · intro candidate common
        have lengthZero : candidate.length = 0 := by
          have := List.Sublist.length_le common.1
          simp at this ⊢
          exact this
        simp [lcsRec, lengthZero]
  | case2 left leftNonempty =>
      constructor
      · refine ⟨[], ⟨List.nil_sublist _, List.nil_sublist _⟩, ?_⟩
        cases left <;> simp_all [lcsRec]
      · intro candidate common
        have lengthZero : candidate.length = 0 := by
          have := List.Sublist.length_le common.2
          simp at this ⊢
          exact this
        cases left <;> simp_all [lcsRec]
  | case3 tail head rightTail tailExact =>
      constructor
      · rcases tailExact.1 with ⟨candidate, common, lengthEq⟩
        refine ⟨head :: candidate, ⟨?_, ?_⟩, ?_⟩
        · exact List.Sublist.cons_cons head common.1
        · exact List.Sublist.cons_cons head common.2
        · simp [lcsRec, lengthEq, Nat.add_comm]
      · intro candidate common
        have tailCommon : IsCommonSubsequence candidate.tail tail rightTail :=
          ⟨tail_sublist_of_sublist_cons common.1,
            tail_sublist_of_sublist_cons common.2⟩
        have tailBound := tailExact.2 candidate.tail tailCommon
        have lengthStep : candidate.length ≤ candidate.tail.length + 1 := by
          cases candidate <;> simp
        simp [lcsRec]
        omega
  | case4 leftHead leftTail rightHead rightTail headsNe leftExact rightExact =>
      have recurrence :
          lcsRec (leftHead :: leftTail) (rightHead :: rightTail) =
            max (lcsRec leftTail (rightHead :: rightTail))
              (lcsRec (leftHead :: leftTail) rightTail) := by
        simp [lcsRec, headsNe]
      constructor
      · by_cases leftLarger :
          lcsRec (leftHead :: leftTail) rightTail ≤
            lcsRec leftTail (rightHead :: rightTail)
        · rcases leftExact.1 with ⟨candidate, common, lengthEq⟩
          refine ⟨candidate, ⟨List.Sublist.cons leftHead common.1, common.2⟩, ?_⟩
          rw [recurrence, max_eq_left leftLarger, lengthEq]
        · have rightLarger :
              lcsRec leftTail (rightHead :: rightTail) ≤
                lcsRec (leftHead :: leftTail) rightTail := by omega
          rcases rightExact.1 with ⟨candidate, common, lengthEq⟩
          refine ⟨candidate, ⟨common.1,
            List.Sublist.cons rightHead common.2⟩, ?_⟩
          rw [recurrence, max_eq_right rightLarger, lengthEq]
      · intro candidate common
        rw [recurrence]
        rcases common_cons_ne_cases headsNe common with leftCase | rightCase
        · exact (leftExact.2 candidate leftCase).trans (Nat.le_max_left _ _)
        · exact (rightExact.2 candidate rightCase).trans (Nat.le_max_right _ _)

theorem lcsRec_eq_lcsLength
    {alpha : Type*} [DecidableEq alpha] (left right : List alpha) :
    lcsRec left right = lcsLength left right :=
  exactLCS_unique (lcsRec_isExact left right) (lcsLength_isExact left right)

/-- The event test written directly with the standard LCS recurrence. -/
def equalDeletionBadRecB
    {alpha : Type*} [DecidableEq alpha]
    (left right : List alpha) : Bool :=
  decide (2000 * (left.length - lcsRec left right) < left.length)

theorem equalDeletionBadRecB_eq_equalDeletionBadB
    {alpha : Type*} [DecidableEq alpha] (left right : List alpha) :
    equalDeletionBadRecB left right = equalDeletionBadB left right := by
  simp [equalDeletionBadRecB, equalDeletionBadB, lcsRec_eq_lcsLength]

end TernarySyncAudit
