import FormalAudit.Basic
import Mathlib

namespace TernarySyncAudit

abbrev Choice := Fin 2

def letters : List Symbol := [0, 1, 2]
def choices : List Choice := [0, 1]

/-- The six displayed length-18 words, duplicated here as primary data. -/
def codeword (letter : Symbol) (choice : Choice) : Word :=
  match letter.val, choice.val with
  | 0, 0 => [2,1,0,2,0,1,2,0,2,1,2,0,1,0,2,0,1,2]
  | 0, 1 => [2,1,0,2,0,1,0,2,1,2,0,2,1,0,2,0,1,2]
  | 1, 0 => [0,2,1,0,1,2,0,1,0,2,0,1,2,1,0,1,2,0]
  | 1, 1 => [0,2,1,0,1,2,1,0,2,0,1,0,2,1,0,1,2,0]
  | 2, 0 => [1,0,2,1,2,0,1,2,1,0,1,2,0,2,1,2,0,1]
  | 2, 1 => [1,0,2,1,2,0,2,1,0,1,2,1,0,2,1,2,0,1]
  | _, _ => []

def allCodewords : List Word :=
  letters.flatMap fun letter => choices.map fun choice => codeword letter choice

def allWords (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | length + 1 =>
      (allWords alphabet length).flatMap fun tail =>
        alphabet.map fun head => head :: tail

def squareAtB (word : List α) (start period : ℕ) [DecidableEq α] : Bool :=
  decide (0 < period) &&
  decide (start + 2 * period ≤ word.length) &&
  decide (
    word.extract start (start + period) =
      word.extract (start + period) (start + 2 * period))

def squareFreeB (word : List α) [DecidableEq α] : Bool :=
  (List.range word.length).all fun start =>
    (List.range (word.length + 1)).all fun period =>
      !(squareAtB word start period)

def decorate : List Symbol → List Choice → Word
  | [], [] => []
  | letter :: outer, choice :: bits =>
      codeword letter choice ++ decorate outer bits
  | _, _ => []

def occurrenceCheckAtLength (length : ℕ) : Bool :=
  (allWords letters length).all fun outer =>
    !(squareFreeB outer) ||
      (allWords choices length).all fun bits =>
        squareFreeB (decorate outer bits)

def occurrenceChecksThroughFive : Bool :=
  (List.range 5).all fun zeroBased =>
    occurrenceCheckAtLength (zeroBased + 1)

def nonboundaryChecks : Bool :=
  letters.all fun leftLetter =>
    letters.all fun rightLetter =>
      decide (leftLetter = rightLetter) ||
        choices.all fun leftChoice =>
          choices.all fun rightChoice =>
            let pair :=
              codeword leftLetter leftChoice ++
                codeword rightLetter rightChoice
            (List.range 17).all fun zeroBased =>
              let offset := zeroBased + 1
              let factor := (pair.drop offset).take 18
              allCodewords.all fun candidate => decide (factor ≠ candidate)

def sevenPrefixes : List Word := allCodewords.map fun word => word.take 7
def sevenSuffixes : List Word := allCodewords.map fun word => word.drop 11

def symbolAt (word : Word) (position : ℕ) : Symbol :=
  word.getD position 0

theorem all_codewords_have_length_eighteen :
    ∀ (letter : Symbol) (choice : Choice),
      (codeword letter choice).length = 18 := by
  decide

theorem six_codewords_are_distinct : allCodewords.Nodup := by
  native_decide

theorem finite_occurrence_checks_pass : occurrenceChecksThroughFive = true := by
  native_decide

theorem nonboundary_checks_pass : nonboundaryChecks = true := by
  native_decide

theorem seven_prefixes_are_distinct : sevenPrefixes.Nodup := by
  native_decide

theorem seven_suffixes_are_distinct : sevenSuffixes.Nodup := by
  native_decide

/-- Equality of the first seven positions identifies a codeword completely. -/
theorem prefix_signature_injective :
    ∀ (leftLetter rightLetter : Symbol) (leftChoice rightChoice : Choice),
      (∀ position : Fin 7,
        symbolAt (codeword leftLetter leftChoice) position.val =
          symbolAt (codeword rightLetter rightChoice) position.val) →
      leftLetter = rightLetter ∧ leftChoice = rightChoice := by
  decide

/-- For a fixed outer symbol, the two occurrence-wise codewords are different. -/
theorem codeword_choice_injective (letter : Symbol) :
    Function.Injective (codeword letter) := by
  intro left right equality
  exact (prefix_signature_injective letter letter left right fun position =>
    congrArg (fun word => symbolAt word position.val) equality).2

/-- Equality of positions 11 through 17 identifies a codeword completely. -/
theorem suffix_signature_injective :
    ∀ (leftLetter rightLetter : Symbol) (leftChoice rightChoice : Choice),
      (∀ position : Fin 7,
        symbolAt (codeword leftLetter leftChoice) (11 + position.val) =
          symbolAt (codeword rightLetter rightChoice) (11 + position.val)) →
      leftLetter = rightLetter ∧ leftChoice = rightChoice := by
  decide

/-- Pointwise form of all 2,448 nonboundary comparisons. -/
theorem nonboundary_has_mismatch :
    ∀ (leftLetter rightLetter candidateLetter : Symbol)
      (leftChoice rightChoice candidateChoice : Choice)
      (offset : Fin 17),
      leftLetter ≠ rightLetter →
      ∃ position : Fin 18,
        symbolAt (codeword candidateLetter candidateChoice) position.val ≠
          symbolAt
            (codeword leftLetter leftChoice ++
              codeword rightLetter rightChoice)
            (offset.val + 1 + position.val) := by
  decide

/-- The length-five part of the finite occurrence-wise check. -/
theorem every_square_free_five_block_image_is_square_free :
    ∀ (a₀ a₁ a₂ a₃ a₄ : Symbol) (r₀ r₁ r₂ r₃ r₄ : Choice),
      squareFreeB [a₀, a₁, a₂, a₃, a₄] = true →
      squareFreeB
        (codeword a₀ r₀ ++ codeword a₁ r₁ ++ codeword a₂ r₂ ++
          codeword a₃ r₃ ++ codeword a₄ r₄) = true := by
  native_decide

def fiveBlockImage
    (a₀ a₁ a₂ a₃ a₄ : Symbol) (r₀ r₁ r₂ r₃ r₄ : Choice) : Word :=
  codeword a₀ r₀ ++ codeword a₁ r₁ ++ codeword a₂ r₂ ++
    codeword a₃ r₃ ++ codeword a₄ r₄

/--
Pointwise, bounded form of the short-window part needed by the all-length
reduction.  The witness is an explicit mismatching position in the two halves.
-/
theorem five_block_short_windows_have_mismatch :
    ∀ (a₀ a₁ a₂ a₃ a₄ : Symbol) (r₀ r₁ r₂ r₃ r₄ : Choice)
      (start : Fin 90) (period : Fin 35),
      squareFreeB [a₀, a₁, a₂, a₃, a₄] = true →
      0 < period.val →
      start.val + 2 * period.val ≤ 90 →
      ∃ offset : Fin period.val,
        symbolAt
            (fiveBlockImage a₀ a₁ a₂ a₃ a₄ r₀ r₁ r₂ r₃ r₄)
            (start.val + offset.val) ≠
          symbolAt
            (fiveBlockImage a₀ a₁ a₂ a₃ a₄ r₀ r₁ r₂ r₃ r₄)
            (start.val + period.val + offset.val) := by
  native_decide

/-- A five-letter word is square-free once its only possible periods are excluded. -/
theorem five_symbols_square_free_of_local_obstructions :
    ∀ (a₀ a₁ a₂ a₃ a₄ : Symbol),
      a₀ ≠ a₁ → a₁ ≠ a₂ → a₂ ≠ a₃ → a₃ ≠ a₄ →
      (a₀ ≠ a₂ ∨ a₁ ≠ a₃) →
      (a₁ ≠ a₃ ∨ a₂ ≠ a₄) →
      squareFreeB [a₀, a₁, a₂, a₃, a₄] = true := by
  decide

end TernarySyncAudit
