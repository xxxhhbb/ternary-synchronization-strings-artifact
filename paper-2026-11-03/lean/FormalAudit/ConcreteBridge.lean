import FormalAudit.BoundaryReduction
import FormalAudit.FiniteCodebook
import Mathlib

namespace TernarySyncAudit

/--
Exact interface between an infinite character stream and its consecutive
length-18 codewords.  The three fields are aligned-block, crossing-factor,
and five-block views of the same stream.
-/
structure RealizesCodeStream
    (stream : ℕ → Symbol) (outer : ℕ → Symbol) (branch : ℕ → Choice) : Prop where
  aligned :
    ∀ block position, position < 18 →
      stream (18 * block + position) =
        symbolAt (codeword (outer block) (branch block)) position
  crossing :
    ∀ block offset position,
      0 < offset → offset < 18 → position < 18 →
      stream (18 * block + offset + position) =
        symbolAt
          (codeword (outer block) (branch block) ++
            codeword (outer (block + 1)) (branch (block + 1)))
          (offset + position)
  fiveBlocks :
    ∀ block position, position < 90 →
      stream (18 * block + position) =
        symbolAt
          (fiveBlockImage
            (outer block) (outer (block + 1)) (outer (block + 2))
            (outer (block + 3)) (outer (block + 4))
            (branch block) (branch (block + 1)) (branch (block + 2))
            (branch (block + 3)) (branch (block + 4)))
          position

/-- The canonical infinite stream obtained by concatenating the selected blocks. -/
def codeStream (outer : ℕ → Symbol) (branch : ℕ → Choice) (position : ℕ) : Symbol :=
  symbolAt
    (codeword (outer (position / 18)) (branch (position / 18)))
    (position % 18)

theorem codeStream_aligned (outer : ℕ → Symbol) (branch : ℕ → Choice)
    (block position : ℕ) (positionBound : position < 18) :
    codeStream outer branch (18 * block + position) =
      symbolAt (codeword (outer block) (branch block)) position := by
  unfold codeStream
  rw [Nat.mul_add_div (by omega) block position]
  rw [Nat.div_eq_of_lt positionBound, Nat.add_zero]
  rw [Nat.mul_add_mod 18 block position]
  rw [Nat.mod_eq_of_lt positionBound]

theorem codeStream_crossing (outer : ℕ → Symbol) (branch : ℕ → Choice)
    (block offset position : ℕ)
    (offsetPositive : 0 < offset) (offsetBound : offset < 18)
    (positionBound : position < 18) :
    codeStream outer branch (18 * block + offset + position) =
      symbolAt
        (codeword (outer block) (branch block) ++
          codeword (outer (block + 1)) (branch (block + 1)))
        (offset + position) := by
  by_cases staysLeft : offset + position < 18
  · rw [show 18 * block + offset + position =
        18 * block + (offset + position) by omega]
    rw [codeStream_aligned outer branch block (offset + position) staysLeft]
    unfold symbolAt
    symm
    apply List.getD_append
    simpa [all_codewords_have_length_eighteen] using staysLeft
  · have crosses : 18 ≤ offset + position := by omega
    have residualBound : offset + position - 18 < 18 := by omega
    have positionEq :
        18 * block + offset + position =
          18 * (block + 1) + (offset + position - 18) := by
      omega
    rw [positionEq]
    rw [codeStream_aligned outer branch (block + 1)
      (offset + position - 18) residualBound]
    unfold symbolAt
    symm
    rw [List.getD_append_right]
    · congr 1
      rw [all_codewords_have_length_eighteen]
    · rw [all_codewords_have_length_eighteen]
      exact crosses

theorem codeStream_fiveBlocks (outer : ℕ → Symbol) (branch : ℕ → Choice)
    (block position : ℕ) (positionBound : position < 90) :
    codeStream outer branch (18 * block + position) =
      symbolAt
        (fiveBlockImage
          (outer block) (outer (block + 1)) (outer (block + 2))
          (outer (block + 3)) (outer (block + 4))
          (branch block) (branch (block + 1)) (branch (block + 2))
          (branch (block + 3)) (branch (block + 4)))
        position := by
  let w₀ := codeword (outer block) (branch block)
  let w₁ := codeword (outer (block + 1)) (branch (block + 1))
  let w₂ := codeword (outer (block + 2)) (branch (block + 2))
  let w₃ := codeword (outer (block + 3)) (branch (block + 3))
  let w₄ := codeword (outer (block + 4)) (branch (block + 4))
  have len₀ : w₀.length = 18 := by
    exact all_codewords_have_length_eighteen _ _
  have len₁ : w₁.length = 18 := by
    exact all_codewords_have_length_eighteen _ _
  have len₂ : w₂.length = 18 := by
    exact all_codewords_have_length_eighteen _ _
  have len₃ : w₃.length = 18 := by
    exact all_codewords_have_length_eighteen _ _
  change codeStream outer branch (18 * block + position) =
    symbolAt (w₀ ++ w₁ ++ w₂ ++ w₃ ++ w₄) position
  simp only [List.append_assoc]
  by_cases first : position < 18
  · calc
      codeStream outer branch (18 * block + position) = symbolAt w₀ position := by
        exact codeStream_aligned outer branch block position first
      _ = symbolAt (w₀ ++ (w₁ ++ (w₂ ++ (w₃ ++ w₄)))) position := by
        unfold symbolAt
        symm
        exact List.getD_append w₀ (w₁ ++ (w₂ ++ (w₃ ++ w₄))) 0 position (by omega)
  · have afterFirst : 18 ≤ position := by omega
    by_cases second : position < 36
    · have residualBound : position - 18 < 18 := by omega
      have streamEq :
          codeStream outer branch (18 * block + position) =
            symbolAt w₁ (position - 18) := by
        have argumentEq :
            18 * block + position =
              18 * (block + 1) + (position - 18) := by
          omega
        rw [argumentEq]
        exact codeStream_aligned outer branch (block + 1) _ residualBound
      rw [streamEq]
      unfold symbolAt
      symm
      calc
        (w₀ ++ (w₁ ++ (w₂ ++ (w₃ ++ w₄)))).getD position 0 =
            (w₁ ++ (w₂ ++ (w₃ ++ w₄))).getD (position - w₀.length) 0 :=
          List.getD_append_right w₀ (w₁ ++ (w₂ ++ (w₃ ++ w₄))) 0 position (by omega)
        _ = (w₁ ++ (w₂ ++ (w₃ ++ w₄))).getD (position - 18) 0 := by rw [len₀]
        _ = w₁.getD (position - 18) 0 :=
          List.getD_append w₁ (w₂ ++ (w₃ ++ w₄)) 0 (position - 18) (by omega)
    · have afterSecond : 36 ≤ position := by omega
      by_cases third : position < 54
      · have residualBound : position - 36 < 18 := by omega
        have streamEq :
            codeStream outer branch (18 * block + position) =
              symbolAt w₂ (position - 36) := by
          have argumentEq :
              18 * block + position =
                18 * (block + 2) + (position - 36) := by
            omega
          rw [argumentEq]
          exact codeStream_aligned outer branch (block + 2) _ residualBound
        rw [streamEq]
        unfold symbolAt
        symm
        calc
          (w₀ ++ (w₁ ++ (w₂ ++ (w₃ ++ w₄)))).getD position 0 =
              (w₁ ++ (w₂ ++ (w₃ ++ w₄))).getD (position - w₀.length) 0 :=
            List.getD_append_right w₀ (w₁ ++ (w₂ ++ (w₃ ++ w₄))) 0 position (by omega)
          _ = (w₁ ++ (w₂ ++ (w₃ ++ w₄))).getD (position - 18) 0 := by rw [len₀]
          _ = (w₂ ++ (w₃ ++ w₄)).getD ((position - 18) - w₁.length) 0 :=
            List.getD_append_right w₁ (w₂ ++ (w₃ ++ w₄)) 0 (position - 18) (by omega)
          _ = (w₂ ++ (w₃ ++ w₄)).getD (position - 36) 0 := by rw [len₁]; congr 1
          _ = w₂.getD (position - 36) 0 :=
            List.getD_append w₂ (w₃ ++ w₄) 0 (position - 36) (by omega)
      · have afterThird : 54 ≤ position := by omega
        by_cases fourth : position < 72
        · have residualBound : position - 54 < 18 := by omega
          have streamEq :
              codeStream outer branch (18 * block + position) =
                symbolAt w₃ (position - 54) := by
            have argumentEq :
                18 * block + position =
                  18 * (block + 3) + (position - 54) := by
              omega
            rw [argumentEq]
            exact codeStream_aligned outer branch (block + 3) _ residualBound
          rw [streamEq]
          unfold symbolAt
          symm
          calc
            (w₀ ++ (w₁ ++ (w₂ ++ (w₃ ++ w₄)))).getD position 0 =
                (w₁ ++ (w₂ ++ (w₃ ++ w₄))).getD (position - w₀.length) 0 :=
              List.getD_append_right w₀ (w₁ ++ (w₂ ++ (w₃ ++ w₄))) 0 position (by omega)
            _ = (w₁ ++ (w₂ ++ (w₃ ++ w₄))).getD (position - 18) 0 := by rw [len₀]
            _ = (w₂ ++ (w₃ ++ w₄)).getD ((position - 18) - w₁.length) 0 :=
              List.getD_append_right w₁ (w₂ ++ (w₃ ++ w₄)) 0 (position - 18) (by omega)
            _ = (w₂ ++ (w₃ ++ w₄)).getD (position - 36) 0 := by rw [len₁]; congr 1
            _ = (w₃ ++ w₄).getD ((position - 36) - w₂.length) 0 :=
              List.getD_append_right w₂ (w₃ ++ w₄) 0 (position - 36) (by omega)
            _ = (w₃ ++ w₄).getD (position - 54) 0 := by rw [len₂]; congr 1
            _ = w₃.getD (position - 54) 0 :=
              List.getD_append w₃ w₄ 0 (position - 54) (by omega)
        · have afterFourth : 72 ≤ position := by omega
          have residualBound : position - 72 < 18 := by omega
          have streamEq :
              codeStream outer branch (18 * block + position) =
                symbolAt w₄ (position - 72) := by
            have argumentEq :
                18 * block + position =
                  18 * (block + 4) + (position - 72) := by
              omega
            rw [argumentEq]
            exact codeStream_aligned outer branch (block + 4) _ residualBound
          rw [streamEq]
          unfold symbolAt
          symm
          calc
            (w₀ ++ (w₁ ++ (w₂ ++ (w₃ ++ w₄)))).getD position 0 =
                (w₁ ++ (w₂ ++ (w₃ ++ w₄))).getD (position - w₀.length) 0 :=
              List.getD_append_right w₀ (w₁ ++ (w₂ ++ (w₃ ++ w₄))) 0 position (by omega)
            _ = (w₁ ++ (w₂ ++ (w₃ ++ w₄))).getD (position - 18) 0 := by rw [len₀]
            _ = (w₂ ++ (w₃ ++ w₄)).getD ((position - 18) - w₁.length) 0 :=
              List.getD_append_right w₁ (w₂ ++ (w₃ ++ w₄)) 0 (position - 18) (by omega)
            _ = (w₂ ++ (w₃ ++ w₄)).getD (position - 36) 0 := by rw [len₁]; congr 1
            _ = (w₃ ++ w₄).getD ((position - 36) - w₂.length) 0 :=
              List.getD_append_right w₂ (w₃ ++ w₄) 0 (position - 36) (by omega)
            _ = (w₃ ++ w₄).getD (position - 54) 0 := by rw [len₂]; congr 1
            _ = w₄.getD ((position - 54) - w₃.length) 0 :=
              List.getD_append_right w₃ w₄ 0 (position - 54) (by omega)
            _ = w₄.getD (position - 72) 0 := by rw [len₃]; congr 1

theorem codeStream_realizes (outer : ℕ → Symbol) (branch : ℕ → Choice) :
    RealizesCodeStream (codeStream outer branch) outer branch where
  aligned := codeStream_aligned outer branch
  crossing := codeStream_crossing outer branch
  fiveBlocks := codeStream_fiveBlocks outer branch

theorem outer_adjacent_distinct {outer : ℕ → β}
    (outerSquareFree : OuterSquareFree outer) (block : ℕ) :
    outer block ≠ outer (block + 1) := by
  intro adjacentEqual
  apply outerSquareFree block 1 (by omega)
  intro offset offsetLt
  have offsetZero : offset = 0 := by omega
  simpa [offsetZero] using adjacentEqual

theorem five_outer_symbols_are_safe {outer : ℕ → Symbol}
    (outerSquareFree : OuterSquareFree outer) :
    ∀ block,
      squareFreeB
        [outer block, outer (block + 1), outer (block + 2),
          outer (block + 3), outer (block + 4)] = true := by
  intro block
  have periodTwoAt (base : ℕ) :
      outer base ≠ outer (base + 2) ∨
        outer (base + 1) ≠ outer (base + 3) := by
    by_cases firstMismatch : outer base ≠ outer (base + 2)
    · exact Or.inl firstMismatch
    · right
      intro secondEqual
      apply outerSquareFree base 2 (by omega)
      intro offset offsetLt
      have offsetCases : offset = 0 ∨ offset = 1 := by omega
      rcases offsetCases with offsetZero | offsetOne
      · subst offset
        simpa using firstMismatch
      · subst offset
        simpa only [Nat.add_zero, Nat.add_assoc] using secondEqual
  apply five_symbols_square_free_of_local_obstructions
  · exact outer_adjacent_distinct outerSquareFree block
  · simpa [Nat.add_assoc] using outer_adjacent_distinct outerSquareFree (block + 1)
  · simpa [Nat.add_assoc] using outer_adjacent_distinct outerSquareFree (block + 2)
  · simpa [Nat.add_assoc] using outer_adjacent_distinct outerSquareFree (block + 3)
  · exact periodTwoAt block
  · simpa [Nat.add_assoc] using periodTwoAt (block + 1)

theorem wholeBlockDecodes_of_realization
    {stream : ℕ → Symbol} {outer : ℕ → Symbol} {branch : ℕ → Choice}
    (realizes : RealizesCodeStream stream outer branch) :
    ∀ left right,
      (∀ offset, offset < 18 →
        stream (18 * left + offset) = stream (18 * right + offset)) →
      outer left = outer right := by
  intro left right equalBlock
  exact (prefix_signature_injective
    (outer left) (outer right) (branch left) (branch right) (by
      intro position
      calc
        symbolAt (codeword (outer left) (branch left)) position.val =
            stream (18 * left + position.val) :=
          (realizes.aligned left position.val (by omega)).symm
        _ = stream (18 * right + position.val) :=
          equalBlock position.val (by omega)
        _ = symbolAt (codeword (outer right) (branch right)) position.val :=
          realizes.aligned right position.val (by omega))).1

theorem suffixSevenDecodes_of_realization
    {stream : ℕ → Symbol} {outer : ℕ → Symbol} {branch : ℕ → Choice}
    (realizes : RealizesCodeStream stream outer branch) :
    ∀ left right startOffset,
      startOffset ≤ 11 →
      (∀ offset, startOffset ≤ offset → offset < 18 →
        stream (18 * left + offset) = stream (18 * right + offset)) →
      outer left = outer right := by
  intro left right startOffset startOffsetBound equalSuffix
  exact (suffix_signature_injective
    (outer left) (outer right) (branch left) (branch right) (by
      intro position
      have positionBound : 11 + position.val < 18 := by omega
      calc
        symbolAt (codeword (outer left) (branch left)) (11 + position.val) =
            stream (18 * left + (11 + position.val)) :=
          (realizes.aligned left (11 + position.val) positionBound).symm
        _ = stream (18 * right + (11 + position.val)) :=
          equalSuffix (11 + position.val) (by omega) positionBound
        _ = symbolAt (codeword (outer right) (branch right)) (11 + position.val) :=
          realizes.aligned right (11 + position.val) positionBound)).1

theorem prefixSevenDecodes_of_realization
    {stream : ℕ → Symbol} {outer : ℕ → Symbol} {branch : ℕ → Choice}
    (realizes : RealizesCodeStream stream outer branch) :
    ∀ left right endOffset,
      7 ≤ endOffset →
      (∀ offset, offset < endOffset →
        stream (18 * left + offset) = stream (18 * right + offset)) →
      outer left = outer right := by
  intro left right endOffset endOffsetBound equalPrefix
  exact (prefix_signature_injective
    (outer left) (outer right) (branch left) (branch right) (by
      intro position
      calc
        symbolAt (codeword (outer left) (branch left)) position.val =
            stream (18 * left + position.val) :=
          (realizes.aligned left position.val (by omega)).symm
        _ = stream (18 * right + position.val) :=
          equalPrefix position.val (by omega)
        _ = symbolAt (codeword (outer right) (branch right)) position.val :=
          realizes.aligned right position.val (by omega))).1

theorem shortSafe_of_realization
    {stream : ℕ → Symbol} {outer : ℕ → Symbol} {branch : ℕ → Choice}
    (realizes : RealizesCodeStream stream outer branch)
    (fiveOuterSafe :
      ∀ block,
        squareFreeB
          [outer block, outer (block + 1), outer (block + 2),
            outer (block + 3), outer (block + 4)] = true) :
    ∀ start period, period ≤ 34 → ¬IsSquareAt stream start period := by
  intro start period periodBound square
  rcases square with ⟨periodPositive, periodic⟩
  let block := start / 18
  let localStart := start % 18
  have localStartLt : localStart < 18 := by
    exact Nat.mod_lt _ (by omega)
  have startDecomposition : localStart + 18 * block = start := by
    exact Nat.mod_add_div start 18
  let boundedStart : Fin 90 := ⟨localStart, by omega⟩
  let boundedPeriod : Fin 35 := ⟨period, by omega⟩
  obtain ⟨mismatch, mismatchProof⟩ :=
    five_block_short_windows_have_mismatch
      (outer block) (outer (block + 1)) (outer (block + 2))
      (outer (block + 3)) (outer (block + 4))
      (branch block) (branch (block + 1)) (branch (block + 2))
      (branch (block + 3)) (branch (block + 4))
      boundedStart boundedPeriod (fiveOuterSafe block) periodPositive (by
        dsimp [boundedStart, boundedPeriod]
        omega)
  apply mismatchProof
  have firstPositionBound : localStart + mismatch.val < 90 := by
    omega
  have secondPositionBound : localStart + period + mismatch.val < 90 := by
    omega
  calc
    symbolAt
        (fiveBlockImage
          (outer block) (outer (block + 1)) (outer (block + 2))
          (outer (block + 3)) (outer (block + 4))
          (branch block) (branch (block + 1)) (branch (block + 2))
          (branch (block + 3)) (branch (block + 4)))
        (boundedStart.val + mismatch.val) =
        stream (18 * block + (localStart + mismatch.val)) := by
      dsimp [boundedStart]
      exact (realizes.fiveBlocks block _ firstPositionBound).symm
    _ = stream (start + mismatch.val) := by
      congr 1
      omega
    _ = stream (start + period + mismatch.val) :=
      periodic mismatch.val mismatch.isLt
    _ = stream (18 * block + (localStart + period + mismatch.val)) := by
      congr 1
      omega
    _ = symbolAt
        (fiveBlockImage
          (outer block) (outer (block + 1)) (outer (block + 2))
          (outer (block + 3)) (outer (block + 4))
          (branch block) (branch (block + 1)) (branch (block + 2))
          (branch (block + 3)) (branch (block + 4)))
        (boundedStart.val + boundedPeriod.val + mismatch.val) := by
      dsimp [boundedStart, boundedPeriod]
      exact realizes.fiveBlocks block _ secondPositionBound

theorem nonalignedSafe_of_realization
    {stream : ℕ → Symbol} {outer : ℕ → Symbol} {branch : ℕ → Choice}
    (realizes : RealizesCodeStream stream outer branch)
    (outerSquareFree : OuterSquareFree outer) :
    ∀ aligned period,
      aligned % 18 = 0 → period % 18 ≠ 0 →
      ¬∀ offset, offset < 18 →
        stream (aligned + offset) = stream (aligned + period + offset) := by
  intro aligned period alignedMod periodModNonzero equalFactor
  let candidateBlock := aligned / 18
  let target := aligned + period
  let targetBlock := target / 18
  let targetOffset := target % 18
  have alignedDecomposition : aligned % 18 + 18 * candidateBlock = aligned := by
    exact Nat.mod_add_div aligned 18
  have alignedEq : aligned = 18 * candidateBlock := by
    omega
  have targetDecomposition : targetOffset + 18 * targetBlock = target := by
    exact Nat.mod_add_div target 18
  have targetEq : target = 18 * targetBlock + targetOffset := by
    omega
  have periodRemainderLt : period % 18 < 18 := by
    exact Nat.mod_lt _ (by omega)
  have targetOffsetEq : targetOffset = period % 18 := by
    dsimp [targetOffset, target]
    rw [Nat.add_mod]
    simp [alignedMod, Nat.mod_eq_of_lt periodRemainderLt]
  have targetOffsetPositive : 0 < targetOffset := by
    omega
  have targetOffsetLt : targetOffset < 18 := by
    exact Nat.mod_lt _ (by omega)
  have adjacentDistinct : outer targetBlock ≠ outer (targetBlock + 1) := by
    exact outer_adjacent_distinct outerSquareFree targetBlock
  let encodedOffset : Fin 17 := ⟨targetOffset - 1, by omega⟩
  obtain ⟨position, mismatch⟩ :=
    nonboundary_has_mismatch
      (outer targetBlock) (outer (targetBlock + 1)) (outer candidateBlock)
      (branch targetBlock) (branch (targetBlock + 1)) (branch candidateBlock)
      encodedOffset adjacentDistinct
  apply mismatch
  have encodedOffsetEq : encodedOffset.val + 1 = targetOffset := by
    dsimp [encodedOffset]
    omega
  calc
    symbolAt (codeword (outer candidateBlock) (branch candidateBlock)) position.val =
        stream (aligned + position.val) := by
      rw [alignedEq]
      exact (realizes.aligned candidateBlock position.val (by omega)).symm
    _ = stream (aligned + period + position.val) :=
      equalFactor position.val (by omega)
    _ = stream (18 * targetBlock + targetOffset + position.val) := by
      congr 1
      omega
    _ = symbolAt
        (codeword (outer targetBlock) (branch targetBlock) ++
          codeword (outer (targetBlock + 1)) (branch (targetBlock + 1)))
        (encodedOffset.val + 1 + position.val) := by
      rw [encodedOffsetEq]
      exact realizes.crossing targetBlock targetOffset position.val
        targetOffsetPositive targetOffsetLt (by omega)

/-- Code-specific all-length occurrence-wise square-freeness, modulo realization. -/
theorem concrete_stream_has_no_square
    {stream : ℕ → Symbol} {outer : ℕ → Symbol} {branch : ℕ → Choice}
    (realizes : RealizesCodeStream stream outer branch)
    (outerSquareFree : OuterSquareFree outer) :
    ∀ start period, ¬IsSquareAt stream start period := by
  apply no_square_from_finite_boundary_interface stream outer
  · exact shortSafe_of_realization realizes (five_outer_symbols_are_safe outerSquareFree)
  · exact nonalignedSafe_of_realization realizes outerSquareFree
  · exact wholeBlockDecodes_of_realization realizes
  · exact suffixSevenDecodes_of_realization realizes
  · exact prefixSevenDecodes_of_realization realizes
  · exact outerSquareFree

/-- Fully instantiated arbitrary-length occurrence-wise Brinkhuis theorem. -/
theorem codeStream_has_no_square
    (outer : ℕ → Symbol) (branch : ℕ → Choice)
    (outerSquareFree : OuterSquareFree outer) :
    ∀ start period, ¬IsSquareAt (codeStream outer branch) start period := by
  exact concrete_stream_has_no_square
    (codeStream_realizes outer branch) outerSquareFree

end TernarySyncAudit
