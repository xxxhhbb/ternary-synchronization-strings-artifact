import FormalAudit.OffsetArithmetic
import Mathlib

namespace TernarySyncAudit

/-- Equality of two consecutive length-`period` factors in an infinite stream. -/
def IsSquareAt (stream : ℕ → α) (start period : ℕ) : Prop :=
  0 < period ∧
    ∀ offset, offset < period →
      stream (start + offset) = stream (start + period + offset)

/-- The outer stream contains no adjacent repeated block of positive length. -/
def OuterSquareFree (outer : ℕ → β) : Prop :=
  ∀ start period, 0 < period →
    ¬∀ offset, offset < period →
      outer (start + offset) = outer (start + period + offset)

/--
The abstract interface extracted from Appendix A.  The hypotheses correspond
respectively to the finite short-window check, the nonboundary occurrence
check, full-block decoding, and the seven-symbol suffix/prefix signatures.
-/
theorem no_square_from_finite_boundary_interface
    (stream : ℕ → α) (outer : ℕ → β)
    (shortSafe : ∀ start period, period ≤ 34 → ¬IsSquareAt stream start period)
    (nonalignedSafe :
      ∀ aligned period,
        aligned % 18 = 0 → period % 18 ≠ 0 →
        ¬∀ offset, offset < 18 →
          stream (aligned + offset) = stream (aligned + period + offset))
    (wholeBlockDecodes :
      ∀ left right,
        (∀ offset, offset < 18 →
          stream (18 * left + offset) = stream (18 * right + offset)) →
        outer left = outer right)
    (suffixSevenDecodes :
      ∀ left right startOffset,
        startOffset ≤ 11 →
        (∀ offset, startOffset ≤ offset → offset < 18 →
          stream (18 * left + offset) = stream (18 * right + offset)) →
        outer left = outer right)
    (prefixSevenDecodes :
      ∀ left right endOffset,
        7 ≤ endOffset →
        (∀ offset, offset < endOffset →
          stream (18 * left + offset) = stream (18 * right + offset)) →
        outer left = outer right)
    (outerSquareFree : OuterSquareFree outer) :
    ∀ start period, ¬IsSquareAt stream start period := by
  intro start period square
  by_cases short : period ≤ 34
  · exact shortSafe start period short square

  have large : 35 ≤ period := period_after_short_case short
  rcases square with ⟨periodPositive, periodic⟩

  by_cases alignedPeriod : period % 18 = 0
  · let blockIndex := start / 18
    let startOffset := start % 18
    let quotient := period / 18
    have startOffsetLt : startOffset < 18 := by
      exact Nat.mod_lt _ (by omega)
    have startDecomposition : startOffset + 18 * blockIndex = start := by
      exact Nat.mod_add_div start 18
    have startEq : start = 18 * blockIndex + startOffset := by
      omega
    have periodDecomposition : period = 18 * quotient := by
      have raw := Nat.mod_add_div period 18
      omega
    have quotientAtLeastTwo : 2 ≤ quotient := by
      exact aligned_period_has_two_blocks periodDecomposition large

    by_cases startsAtBoundary : startOffset = 0
    · have startAligned : start = 18 * blockIndex := by
        omega
      have repeatedOuter :
          ∀ offset, offset < quotient →
            outer (blockIndex + offset) =
              outer (blockIndex + quotient + offset) := by
          intro outerOffset outerOffsetLt
          apply wholeBlockDecodes
          intro inside insideLt
          let squareOffset := 18 * outerOffset + inside
          have squareOffsetLt : squareOffset < period := by
            dsimp [squareOffset]
            omega
          have equality := periodic squareOffset squareOffsetLt
          have leftArgument :
              18 * (blockIndex + outerOffset) + inside =
                start + squareOffset := by
            dsimp [squareOffset]
            omega
          have rightArgument :
              18 * (blockIndex + quotient + outerOffset) + inside =
                start + period + squareOffset := by
            dsimp [squareOffset]
            omega
          rw [leftArgument, rightArgument]
          exact equality
      exact
        (outerSquareFree blockIndex quotient (by omega)) repeatedOuter

    · have startOffsetPositive : 1 ≤ startOffset := by omega

      have middleEquality :
          ∀ middle, 1 ≤ middle → middle < quotient →
            outer (blockIndex + middle) =
              outer (blockIndex + quotient + middle) := by
        intro middle middlePositive middleLt
        apply wholeBlockDecodes
        intro inside insideLt
        let squareOffset :=
          (18 - startOffset) + 18 * (middle - 1) + inside
        have offsetCompletes : startOffset + (18 - startOffset) = 18 := by
          exact Nat.add_sub_of_le (by omega)
        have middleRestores : middle - 1 + 1 = middle := by
          exact Nat.sub_add_cancel middlePositive
        have squareOffsetLt : squareOffset < period := by
          dsimp [squareOffset]
          omega
        have equality := periodic squareOffset squareOffsetLt
        have leftArgument :
            18 * (blockIndex + middle) + inside =
              start + squareOffset := by
          dsimp [squareOffset]
          omega
        have rightArgument :
            18 * (blockIndex + quotient + middle) + inside =
              start + period + squareOffset := by
          dsimp [squareOffset]
          omega
        rw [leftArgument, rightArgument]
        exact equality

      rcases offset_signature_cover startOffsetPositive (by omega) with
        suffixCase | prefixCase
      · have firstBlockEquality :
            outer blockIndex = outer (blockIndex + quotient) := by
          apply suffixSevenDecodes blockIndex (blockIndex + quotient) startOffset suffixCase
          intro inside insideLower insideUpper
          let squareOffset := inside - startOffset
          have insideRestores :
              startOffset + (inside - startOffset) = inside := by
            exact Nat.add_sub_of_le insideLower
          have squareOffsetLt : squareOffset < period := by
            dsimp [squareOffset]
            omega
          have equality := periodic squareOffset squareOffsetLt
          have leftArgument :
              18 * blockIndex + inside = start + squareOffset := by
            dsimp [squareOffset]
            omega
          have rightArgument :
              18 * (blockIndex + quotient) + inside =
                start + period + squareOffset := by
            dsimp [squareOffset]
            omega
          rw [leftArgument, rightArgument]
          exact equality

        have repeatedOuter :
            ∀ offset, offset < quotient →
              outer (blockIndex + offset) =
                outer (blockIndex + quotient + offset) := by
          intro outerOffset outerOffsetLt
          by_cases first : outerOffset = 0
          · simpa [first] using firstBlockEquality
          · exact middleEquality outerOffset (by omega) outerOffsetLt
        exact
          (outerSquareFree blockIndex quotient (by omega)) repeatedOuter

      · have lastBlockEquality :
            outer (blockIndex + quotient) =
              outer (blockIndex + 2 * quotient) := by
          apply
            prefixSevenDecodes
              (blockIndex + quotient) (blockIndex + 2 * quotient)
              startOffset prefixCase
          intro inside insideLt
          let squareOffset := period - startOffset + inside
          have periodRestores :
              startOffset + (period - startOffset) = period := by
            exact Nat.add_sub_of_le (by omega)
          have squareOffsetLt : squareOffset < period := by
            dsimp [squareOffset]
            omega
          have equality := periodic squareOffset squareOffsetLt
          have leftArgument :
              18 * (blockIndex + quotient) + inside =
                start + squareOffset := by
            dsimp [squareOffset]
            omega
          have rightArgument :
              18 * (blockIndex + 2 * quotient) + inside =
                start + period + squareOffset := by
            dsimp [squareOffset]
            omega
          rw [leftArgument, rightArgument]
          exact equality

        have repeatedOuter :
            ∀ offset, offset < quotient →
              outer (blockIndex + 1 + offset) =
                outer (blockIndex + 1 + quotient + offset) := by
          intro outerOffset outerOffsetLt
          by_cases last : outerOffset + 1 = quotient
          · have leftIndex :
                blockIndex + 1 + outerOffset = blockIndex + quotient := by
              omega
            have rightIndex :
                blockIndex + 1 + quotient + outerOffset =
                  blockIndex + 2 * quotient := by
              omega
            rw [leftIndex, rightIndex]
            exact lastBlockEquality
          · have middleLt : outerOffset + 1 < quotient := by omega
            have leftIndex :
                blockIndex + 1 + outerOffset =
                  blockIndex + (outerOffset + 1) := by
              omega
            have rightIndex :
                blockIndex + 1 + quotient + outerOffset =
                  blockIndex + quotient + (outerOffset + 1) := by
              omega
            rw [leftIndex, rightIndex]
            exact middleEquality (outerOffset + 1) (by omega) middleLt
        exact
          (outerSquareFree (blockIndex + 1) quotient (by omega)) repeatedOuter

  · rcases exists_aligned_eighteen_window large with
      ⟨aligned, alignedMod, alignedLower, alignedUpper⟩
    apply nonalignedSafe aligned period alignedMod alignedPeriod
    intro inside insideLt
    let squareOffset := aligned - start + inside
    have cancelSub : start + (aligned - start) = aligned := by
      exact Nat.add_sub_of_le alignedLower
    have squareOffsetLt : squareOffset < period := by
      dsimp [squareOffset]
      omega
    have equality := periodic squareOffset squareOffsetLt
    have leftArgument : aligned + inside = start + squareOffset := by
      dsimp [squareOffset]
      omega
    have rightArgument :
        aligned + period + inside = start + period + squareOffset := by
      dsimp [squareOffset]
      omega
    rw [leftArgument, rightArgument]
    exact equality

end TernarySyncAudit
