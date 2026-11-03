import Mathlib
import FormalAudit.ConcreteBridge
import FormalAudit.FiniteChoiceProbability

namespace TernarySyncAudit

/-- We deliberately skip the macroblock containing the left endpoint. -/
def firstFreeBlock (start : ℕ) : ℕ := start / 18 + 1

/-- A uniform number of complete blocks available in every interval of length `ell`. -/
def freeBlockCount (ell : ℕ) : ℕ := ell / 18 - 1

/-- Finite macroblock indices outside one contiguous free range. -/
abbrev OutsideIndex (N first count : ℕ) :=
  {i : Fin N // ¬(first ≤ i.val ∧ i.val < first + count)}

abbrev OutsideChoices (N first count : ℕ) :=
  OutsideIndex N first count → Choice

/-- Assemble the exposed outside choices and the still-free contiguous choices. -/
def assembleChoices
    {N first count : ℕ}
    (outside : OutsideChoices N first count) (free : Fin count → Choice) :
    Fin N → Choice := fun i =>
  if h : first ≤ i.val ∧ i.val < first + count then
    free ⟨i.val - first, by omega⟩
  else
    outside ⟨i, h⟩

/-- The global finite index corresponding to a free-coordinate index. -/
def freeGlobalIndex
    {N first count : ℕ} (fits : first + count ≤ N) (j : Fin count) : Fin N :=
  ⟨first + j.val, by omega⟩

@[simp] theorem assembleChoices_at_free
    {N first count : ℕ} (fits : first + count ≤ N)
    (outside : OutsideChoices N first count) (free : Fin count → Choice)
    (j : Fin count) :
    assembleChoices outside free (freeGlobalIndex fits j) = free j := by
  unfold assembleChoices freeGlobalIndex
  simp

@[simp] theorem assembleChoices_at_outside
    {N first count : ℕ}
    (outside : OutsideChoices N first count) (free : Fin count → Choice)
    (i : OutsideIndex N first count) :
    assembleChoices outside free i.1 = outside i := by
  unfold assembleChoices
  simp only [dif_neg i.2]

/-- Splitting a finite choice vector into outside and free coordinates is an exact bijection. -/
def choiceSplitEquiv
    {N first count : ℕ} (fits : first + count ≤ N) :
    (OutsideChoices N first count × (Fin count → Choice)) ≃ (Fin N → Choice) where
  toFun pair := assembleChoices pair.1 pair.2
  invFun branch :=
    (fun i => branch i.1, fun j => branch (freeGlobalIndex fits j))
  left_inv pair := by
    rcases pair with ⟨outside, free⟩
    apply Prod.ext
    · funext i
      exact assembleChoices_at_outside outside free i
    · funext j
      exact assembleChoices_at_free fits outside free j
  right_inv branch := by
    funext i
    by_cases hi : first ≤ i.val ∧ i.val < first + count
    · unfold assembleChoices
      simp only [dif_pos hi]
      congr 1
      apply Fin.ext
      unfold freeGlobalIndex
      simp
      omega
    · unfold assembleChoices
      simp only [dif_neg hi]

/-- Extend a finite choice vector by a harmless default beyond the finite outer word. -/
def extendFiniteChoices {N : ℕ} (branch : Fin N → Choice) : ℕ → Choice :=
  fun i => if h : i < N then branch ⟨i, h⟩ else 0

@[simp] theorem extendFiniteChoices_at
    {N i : ℕ} (branch : Fin N → Choice) (hi : i < N) :
    extendFiniteChoices branch i = branch ⟨i, hi⟩ := by
  simp [extendFiniteChoices, hi]

/-- The actual infinite branch stream produced from exposed and free finite coordinates. -/
def assembledBranch
    {N first count : ℕ}
    (outside : OutsideChoices N first count) (free : Fin count → Choice) :
    ℕ → Choice :=
  extendFiniteChoices (assembleChoices outside free)

@[simp] theorem assembledBranch_at_free
    {N first count : ℕ} (fits : first + count ≤ N)
    (outside : OutsideChoices N first count) (free : Fin count → Choice)
    (j : Fin count) :
    assembledBranch outside free (first + j.val) = free j := by
  unfold assembledBranch
  rw [extendFiniteChoices_at _ (by omega)]
  have indexEquality :
      (⟨first + j.val, by omega⟩ : Fin N) = freeGlobalIndex fits j := by
    rfl
  rw [indexEquality, assembleChoices_at_free]

@[simp] theorem assembledBranch_at_outside
    {N first count i : ℕ} (hi : i < N)
    (outsideRange : ¬(first ≤ i ∧ i < first + count))
    (outside : OutsideChoices N first count) (free : Fin count → Choice) :
    assembledBranch outside free i =
      outside ⟨⟨i, hi⟩, outsideRange⟩ := by
  unfold assembledBranch
  rw [extendFiniteChoices_at _ hi]
  unfold assembleChoices
  simp only [dif_neg outsideRange]

/-- A character interval as a fixed-length word. -/
def streamInterval
    (outer : ℕ → Symbol) (branch : ℕ → Choice) (start ell : ℕ) :
    FixedWord Symbol ell := fun position =>
  codeStream outer branch (start + position.val)

/-- The `j`th selected macroblock is fully contained in the interval. -/
theorem selected_free_block_inside
    {start ell : ℕ} (hell : 18 ≤ ell) (j : Fin (freeBlockCount ell)) :
    start ≤ 18 * (firstFreeBlock start + j.val) ∧
      18 * (firstFreeBlock start + j.val + 1) ≤ start + ell := by
  have startMod : start % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have startDecomp : start % 18 + 18 * (start / 18) = start := Nat.mod_add_div _ _
  have ellDivPositive : 1 ≤ ell / 18 := by omega
  have startDivBound : 18 * (start / 18) ≤ start := by omega
  have ellDivBound : 18 * (ell / 18) ≤ ell := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self ell 18
  dsimp [firstFreeBlock, freeBlockCount] at j ⊢
  constructor <;> omega

/-- The selected block count has exactly the paper's `ell/18 - 2` guarantee. -/
theorem selected_free_blocks_whole_bound
    {ell : ℕ} (hell : 18 ≤ ell) :
    ell ≤ 18 * (freeBlockCount ell + 2) := by
  have ellMod : ell % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have ellDecomp : ell % 18 + 18 * (ell / 18) = ell := Nat.mod_add_div _ _
  have ellDivPositive : 1 ≤ ell / 18 := by omega
  dsimp [freeBlockCount]
  omega

/-- All selected free blocks lie inside a finite outer word covering both intervals. -/
theorem selected_free_range_fits
    {N start ell : ℕ} (hell : 18 ≤ ell)
    (supportFits : start + 2 * ell ≤ 18 * N) :
    firstFreeBlock start + freeBlockCount ell ≤ N := by
  have ellDivPositive : 1 ≤ ell / 18 := by omega
  have startDivBound : 18 * (start / 18) ≤ start := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self start 18
  have ellDivBound : 18 * (ell / 18) ≤ ell := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self ell 18
  dsimp [firstFreeBlock, freeBlockCount]
  omega

/-- The concrete first interval after exposing every nonfree branch choice. -/
def concreteFirstInterval
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (outside : OutsideChoices N (firstFreeBlock start) (freeBlockCount ell))
    (free : Fin (freeBlockCount ell) → Choice) : FixedWord Symbol ell :=
  streamInterval outer (assembledBranch outside free) start ell

/-- An exact interval value determines every occurrence choice in its full macroblocks. -/
theorem concreteFirstInterval_injective
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (hell : 18 ≤ ell) (supportFits : start + 2 * ell ≤ 18 * N)
    (outside : OutsideChoices N (firstFreeBlock start) (freeBlockCount ell)) :
    Function.Injective (concreteFirstInterval outer outside) := by
  intro left right intervalEquality
  funext j
  let block := firstFreeBlock start + j.val
  have inside := selected_free_block_inside (start := start) hell j
  have rangeFits := selected_free_range_fits hell supportFits
  have blockLtN : block < N := by
    dsimp [block]
    omega
  have signaturesEqual :
      ∀ position : Fin 7,
        symbolAt (codeword (outer block) (left j)) position.val =
          symbolAt (codeword (outer block) (right j)) position.val := by
    intro position
    let relative := 18 * block - start + position.val
    have relativeLt : relative < ell := by
      dsimp [relative]
      omega
    let intervalPosition : Fin ell := ⟨relative, relativeLt⟩
    have atPosition := congrFun intervalEquality intervalPosition
    change
      codeStream outer (assembledBranch outside left)
          (start + intervalPosition.val) =
        codeStream outer (assembledBranch outside right)
          (start + intervalPosition.val) at atPosition
    have positionIdentity :
        start + intervalPosition.val = 18 * block + position.val := by
      dsimp [intervalPosition, relative]
      omega
    rw [positionIdentity] at atPosition
    rw [codeStream_aligned outer (assembledBranch outside left)
          block position.val (by omega),
        codeStream_aligned outer (assembledBranch outside right)
          block position.val (by omega)] at atPosition
    have leftBranch : assembledBranch outside left block = left j := by
      dsimp [block]
      exact assembledBranch_at_free rangeFits outside left j
    have rightBranch : assembledBranch outside right block = right j := by
      dsimp [block]
      exact assembledBranch_at_free rangeFits outside right j
    simpa [leftBranch, rightBranch] using atPosition
  exact (prefix_signature_injective
    (outer block) (outer block) (left j) (right j) signaturesEqual).2

/-- The adjacent second interval does not inspect any choice freed inside the first. -/
theorem second_interval_block_is_outside
    {N start ell : ℕ} (hell : 18 ≤ ell)
    (supportFits : start + 2 * ell ≤ 18 * N) (position : Fin ell) :
    let character := start + ell + position.val
    let block := character / 18
    block < N ∧
      ¬(firstFreeBlock start ≤ block ∧
        block < firstFreeBlock start + freeBlockCount ell) := by
  dsimp only
  let character := start + ell + position.val
  let block := character / 18
  have characterLt : character < 18 * N := by
    dsimp [character]
    omega
  have characterMod : character % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have characterDecomp :
      character % 18 + 18 * (character / 18) = character := Nat.mod_add_div _ _
  have blockLt : block < N := by
    dsimp [block]
    omega
  refine ⟨blockLt, ?_⟩
  intro inRange
  let j : Fin (freeBlockCount ell) :=
    ⟨block - firstFreeBlock start, by omega⟩
  have inside := selected_free_block_inside (start := start) hell j
  have blockIdentity : firstFreeBlock start + j.val = block := by
    dsimp [j]
    omega
  have blockEnd : 18 * (block + 1) ≤ start + ell := by
    rw [← blockIdentity]
    simpa [Nat.add_assoc] using inside.2
  have characterBeforeEnd : character < 18 * (block + 1) := by
    dsimp [block]
    omega
  have characterAfterBoundary : start + ell ≤ character := by
    dsimp [character]
    omega
  omega

/-- Canonical second interval, with arbitrary zero values inserted in the unused free slots. -/
def concreteSecondInterval
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (outside : OutsideChoices N (firstFreeBlock start) (freeBlockCount ell)) :
    FixedWord Symbol ell :=
  streamInterval outer (assembledBranch outside fun _ => 0) (start + ell) ell

/-- Every free assignment produces the same second interval. -/
theorem concreteSecondInterval_independent
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (hell : 18 ≤ ell) (supportFits : start + 2 * ell ≤ 18 * N)
    (outside : OutsideChoices N (firstFreeBlock start) (freeBlockCount ell))
    (free : Fin (freeBlockCount ell) → Choice) :
    streamInterval outer (assembledBranch outside free) (start + ell) ell =
      concreteSecondInterval outer outside := by
  funext position
  let character := start + ell + position.val
  let block := character / 18
  have outsideFacts := second_interval_block_is_outside hell supportFits position
  have branchEquality :
      assembledBranch outside free block =
        assembledBranch outside (fun _ => 0) block := by
    rw [assembledBranch_at_outside outsideFacts.1 outsideFacts.2,
      assembledBranch_at_outside outsideFacts.1 outsideFacts.2]
  unfold concreteSecondInterval
  unfold streamInterval
  unfold codeStream
  dsimp [character, block] at branchEquality ⊢
  rw [branchEquality]

/-- The concrete high-LCS deletion ball after the outside choices are fixed. -/
noncomputable def concreteBadValues
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (outside : OutsideChoices N (firstFreeBlock start) (freeBlockCount ell)) :
    Finset (FixedWord Symbol ell) :=
  deletionBall (concreteSecondInterval outer outside) (explicitSmallDeletions ell)

/-- Fully concrete conditional-min-entropy event tail for the Brinkhuis stream. -/
theorem concrete_interval_bad_mass_lt
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (hell : 2000 < ell) (supportFits : start + 2 * ell ≤ 18 * N) :
    uniformProductBadMass
        (concreteFirstInterval (N := N) (start := start) (ell := ell) outer)
        (concreteBadValues (N := N) (start := start) (ell := ell) outer) <
      Real.exp (-(ell : ℝ) / 71) := by
  have hellEighteen : 18 ≤ ell := by omega
  apply binaryProductBadMass_lt_exp_neg_one_over_71_realVolume
      hell (selected_free_blocks_whole_bound hellEighteen)
  · intro outside
    exact concreteFirstInterval_injective outer hellEighteen supportFits outside
  · intro outside
    exact explicit_ternary_deletionBall_card_le_exp_hundred hell.le
      (concreteSecondInterval outer outside)

/-- First half of the actual adjacent pair under a finite global choice vector. -/
def finiteFirstInterval
    {N start ell : ℕ} (outer : ℕ → Symbol) (branch : Fin N → Choice) :
    FixedWord Symbol ell :=
  streamInterval outer (extendFiniteChoices branch) start ell

/-- Second half of the actual adjacent pair under the same finite choice vector. -/
def finiteSecondInterval
    {N start ell : ℕ} (outer : ℕ → Symbol) (branch : Fin N → Choice) :
    FixedWord Symbol ell :=
  streamInterval outer (extendFiniteChoices branch) (start + ell) ell

/-- The actual finite bad event, expressed through the exact deletion-witness ball. -/
noncomputable def finiteIntervalBadEvent
    {N start ell : ℕ} (outer : ℕ → Symbol) : Finset (Fin N → Choice) := by
  classical
  exact Finset.univ.filter fun branch =>
    finiteFirstInterval (start := start) (ell := ell) outer branch ∈
      deletionBall
        (finiteSecondInterval (start := start) (ell := ell) outer branch)
        (explicitSmallDeletions ell)

/-- Uniform mass of the actual bad event on the common global choice space. -/
noncomputable def finiteIntervalBadMass
    {N start ell : ℕ} (outer : ℕ → Symbol) : ℝ :=
  (finiteIntervalBadEvent (N := N) (start := start) (ell := ell) outer).card /
    Fintype.card (Fin N → Choice)

/-- The split conditional experiment and the global experiment have exactly the same
bad-event predicate under the choice-vector bijection. -/
theorem split_bad_predicate_iff
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (hell : 18 ≤ ell) (supportFits : start + 2 * ell ≤ 18 * N)
    (pair : OutsideChoices N (firstFreeBlock start) (freeBlockCount ell) ×
      (Fin (freeBlockCount ell) → Choice)) :
    concreteFirstInterval (N := N) (start := start) (ell := ell)
        outer pair.1 pair.2 ∈
      concreteBadValues (N := N) (start := start) (ell := ell) outer pair.1 ↔
      finiteFirstInterval (N := N) (start := start) (ell := ell) outer
          (choiceSplitEquiv (selected_free_range_fits hell supportFits) pair) ∈
        deletionBall
          (finiteSecondInterval (N := N) (start := start) (ell := ell) outer
            (choiceSplitEquiv (selected_free_range_fits hell supportFits) pair))
          (explicitSmallDeletions ell) := by
  rcases pair with ⟨outside, free⟩
  have secondEquality :=
    concreteSecondInterval_independent outer hell supportFits outside free
  have firstEquality :
      finiteFirstInterval (N := N) (start := start) (ell := ell) outer
          (choiceSplitEquiv (selected_free_range_fits hell supportFits)
            (outside, free)) =
        concreteFirstInterval outer outside free := by
    rfl
  have secondGlobalEquality :
      finiteSecondInterval (N := N) (start := start) (ell := ell) outer
          (choiceSplitEquiv (selected_free_range_fits hell supportFits)
            (outside, free)) =
        concreteSecondInterval outer outside := by
    exact secondEquality
  unfold concreteBadValues
  rw [firstEquality, secondGlobalEquality]

/-- Exact cardinal preservation of the event under the outside/free decomposition. -/
theorem split_bad_event_card_eq
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (hell : 18 ≤ ell) (supportFits : start + 2 * ell ≤ 18 * N) :
    (productBadEvent
        (concreteFirstInterval (N := N) (start := start) (ell := ell) outer)
        (concreteBadValues (N := N) (start := start) (ell := ell) outer)).card =
      (finiteIntervalBadEvent (N := N) (start := start) (ell := ell) outer).card := by
  classical
  let fits := selected_free_range_fits hell supportFits
  let split := choiceSplitEquiv fits
  let splitEvent := productBadEvent
    (concreteFirstInterval (N := N) (start := start) (ell := ell) outer)
    (concreteBadValues (N := N) (start := start) (ell := ell) outer)
  let globalEvent := finiteIntervalBadEvent
    (N := N) (start := start) (ell := ell) outer
  have imageEquality : splitEvent.image split = globalEvent := by
    ext branch
    constructor
    · intro hbranch
      rcases Finset.mem_image.mp hbranch with ⟨pair, pairBad, pairMaps⟩
      have pairPredicate :
          concreteFirstInterval outer pair.1 pair.2 ∈
            concreteBadValues outer pair.1 := by
        exact (Finset.mem_filter.mp pairBad).2
      have globalPredicate :=
        (split_bad_predicate_iff outer hell supportFits pair).mp pairPredicate
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [split, fits, pairMaps] using globalPredicate
    · intro hbranch
      have globalPredicate := (Finset.mem_filter.mp hbranch).2
      let pair := split.symm branch
      have pairPredicate :
          concreteFirstInterval outer pair.1 pair.2 ∈
            concreteBadValues outer pair.1 := by
        apply (split_bad_predicate_iff outer hell supportFits pair).mpr
        simpa [pair, split, fits] using globalPredicate
      apply Finset.mem_image.mpr
      refine ⟨pair, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, pairPredicate⟩
      · simp [pair]
  calc
    (productBadEvent
        (concreteFirstInterval (N := N) (start := start) (ell := ell) outer)
        (concreteBadValues (N := N) (start := start) (ell := ell) outer)).card =
        (splitEvent.image split).card := by
          symm
          exact Finset.card_image_of_injective splitEvent split.injective
    _ = globalEvent.card := by rw [imageEquality]
    _ = (finiteIntervalBadEvent
        (N := N) (start := start) (ell := ell) outer).card := rfl

/-- The concrete tail bound now lives on the one global choice space used by the LLL. -/
theorem finite_interval_bad_mass_lt
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (hell : 2000 < ell) (supportFits : start + 2 * ell ≤ 18 * N) :
    finiteIntervalBadMass (N := N) (start := start) (ell := ell) outer <
      Real.exp (-(ell : ℝ) / 71) := by
  have hellEighteen : 18 ≤ ell := by omega
  have fits := selected_free_range_fits hellEighteen supportFits
  have cardDomain := Fintype.card_congr (choiceSplitEquiv fits)
  have massEquality :
      finiteIntervalBadMass (N := N) (start := start) (ell := ell) outer =
        uniformProductBadMass
          (concreteFirstInterval (N := N) (start := start) (ell := ell) outer)
          (concreteBadValues (N := N) (start := start) (ell := ell) outer) := by
    unfold finiteIntervalBadMass uniformProductBadMass
    rw [← split_bad_event_card_eq outer hellEighteen supportFits, cardDomain]
  rw [massEquality]
  exact concrete_interval_bad_mass_lt outer hell supportFits

end TernarySyncAudit
