import Mathlib
import FormalAudit.DeletionBallAnalytic

namespace TernarySyncAudit

open Finset

/-- The bad outcomes in a finite product experiment after the outside state is exposed. -/
noncomputable def productBadEvent
    {Fixed Free Value : Type*} [Fintype Fixed] [Fintype Free]
    [DecidableEq Value]
    (output : Fixed → Free → Value) (badValues : Fixed → Finset Value) :
    Finset (Fixed × Free) := by
  classical
  exact Finset.univ.filter fun z => output z.1 z.2 ∈ badValues z.1

/-- Uniform mass on a finite product experiment, represented by exact counting. -/
noncomputable def uniformProductBadMass
    {Fixed Free Value : Type*} [Fintype Fixed] [Fintype Free]
    [DecidableEq Value]
    (output : Fixed → Free → Value) (badValues : Fixed → Finset Value) : ℝ :=
  (productBadEvent output badValues).card / Fintype.card (Fixed × Free)

private theorem card_productBadEvent_eq_sum
    {Fixed Free Value : Type*} [Fintype Fixed] [Fintype Free]
    [DecidableEq Value]
    (output : Fixed → Free → Value) (badValues : Fixed → Finset Value) :
    (productBadEvent output badValues).card =
      ∑ fixed : Fixed,
        (Finset.univ.filter fun free : Free =>
          output fixed free ∈ badValues fixed).card := by
  classical
  simp only [productBadEvent, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Fintype.sum_prod_type _

/-- For fixed outside data, injectivity makes the number of bad free choices no larger
than the number of bad output values. -/
theorem card_bad_free_choices_le
    {Free Value : Type*} [Fintype Free] [DecidableEq Value]
    (output : Free → Value) (badValues : Finset Value)
    (outputInjective : Function.Injective output) :
    (Finset.univ.filter fun free : Free => output free ∈ badValues).card ≤
      badValues.card := by
  classical
  let choices := Finset.univ.filter fun free : Free => output free ∈ badValues
  have imageSubset : choices.image output ⊆ badValues := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with ⟨free, hfree, rfl⟩
    exact (Finset.mem_filter.mp hfree).2
  calc
    (Finset.univ.filter fun free : Free => output free ∈ badValues).card =
        (choices.image output).card := by
          symm
          exact Finset.card_image_of_injective choices outputInjective
    _ ≤ badValues.card := Finset.card_le_card imageSubset

/-- Averaging the preceding conditional count over every outside state. -/
theorem productBadEvent_card_le
    {Fixed Free Value : Type*} [Fintype Fixed] [Fintype Free]
    [DecidableEq Value]
    (output : Fixed → Free → Value) (badValues : Fixed → Finset Value)
    (outputInjective : ∀ fixed, Function.Injective (output fixed))
    (B : ℕ) (badCard : ∀ fixed, (badValues fixed).card ≤ B) :
    (productBadEvent output badValues).card ≤ Fintype.card Fixed * B := by
  classical
  rw [card_productBadEvent_eq_sum]
  calc
    (∑ fixed : Fixed,
        (Finset.univ.filter fun free : Free =>
          output fixed free ∈ badValues fixed).card) ≤
        ∑ _fixed : Fixed, B := by
      exact Finset.sum_le_sum fun fixed _ =>
        (card_bad_free_choices_le (output fixed) (badValues fixed)
          (outputInjective fixed)).trans (badCard fixed)
    _ = Fintype.card Fixed * B := by simp

/-- Exact finite conditional-point-mass principle in probability form. -/
theorem uniformProductBadMass_le
    {Fixed Free Value : Type*} [Fintype Fixed] [Fintype Free]
    [Nonempty Fixed] [Nonempty Free] [DecidableEq Value]
    (output : Fixed → Free → Value) (badValues : Fixed → Finset Value)
    (outputInjective : ∀ fixed, Function.Injective (output fixed))
    (B : ℕ) (badCard : ∀ fixed, (badValues fixed).card ≤ B) :
    uniformProductBadMass output badValues ≤ (B : ℝ) / Fintype.card Free := by
  have eventCard := productBadEvent_card_le output badValues outputInjective B badCard
  have fixedPositive : (0 : ℝ) < Fintype.card Fixed := by
    exact_mod_cast Fintype.card_pos
  have freePositive : (0 : ℝ) < Fintype.card Free := by
    exact_mod_cast Fintype.card_pos
  have eventCardReal :
      ((productBadEvent output badValues).card : ℝ) ≤
        Fintype.card Fixed * B := by
    exact_mod_cast eventCard
  simp only [uniformProductBadMass, Fintype.card_prod]
  rw [Nat.cast_mul]
  rw [div_le_div_iff₀ (mul_pos fixedPositive freePositive) freePositive]
  nlinarith

/-- Real-valued volume version, avoiding an unnecessary ceiling of an exponential bound. -/
theorem uniformProductBadMass_le_realVolume
    {Fixed Free Value : Type*} [Fintype Fixed] [Fintype Free]
    [Nonempty Fixed] [Nonempty Free] [DecidableEq Value]
    (output : Fixed → Free → Value) (badValues : Fixed → Finset Value)
    (outputInjective : ∀ fixed, Function.Injective (output fixed))
    (volume : ℝ) (badCard : ∀ fixed, ((badValues fixed).card : ℝ) ≤ volume) :
    uniformProductBadMass output badValues ≤ volume / Fintype.card Free := by
  classical
  have fixedPositive : (0 : ℝ) < Fintype.card Fixed := by
    exact_mod_cast Fintype.card_pos
  have freePositive : (0 : ℝ) < Fintype.card Free := by
    exact_mod_cast Fintype.card_pos
  have eventCardReal :
      ((productBadEvent output badValues).card : ℝ) ≤
        Fintype.card Fixed * volume := by
    rw [card_productBadEvent_eq_sum]
    push_cast
    calc
      (∑ fixed : Fixed,
          ((Finset.univ.filter fun free : Free =>
            output fixed free ∈ badValues fixed).card : ℝ)) ≤
          ∑ _fixed : Fixed, volume := by
        apply Finset.sum_le_sum
        intro fixed hfixed
        have fiberNat := card_bad_free_choices_le
          (output fixed) (badValues fixed) (outputInjective fixed)
        have fiberReal :
            ((Finset.univ.filter fun free : Free =>
              output fixed free ∈ badValues fixed).card : ℝ) ≤
                (badValues fixed).card := by
          exact_mod_cast fiberNat
        exact fiberReal.trans (badCard fixed)
      _ = Fintype.card Fixed * volume := by simp [nsmul_eq_mul]
  simp only [uniformProductBadMass, Fintype.card_prod]
  rw [Nat.cast_mul]
  rw [div_le_div_iff₀ (mul_pos fixedPositive freePositive) freePositive]
  nlinarith

/-- A block of `s` independent binary choices has exactly `2^s` assignments. -/
theorem card_binary_choice_block (s : ℕ) :
    Fintype.card (Fin s → Fin 2) = 2 ^ s := by
  simp

/-- Specialization of conditional min-entropy to `s` independent branch bits. -/
theorem binaryProductBadMass_le
    {Fixed Value : Type*} [Fintype Fixed] [Nonempty Fixed]
    [DecidableEq Value]
    (s : ℕ) (output : Fixed → (Fin s → Fin 2) → Value)
    (badValues : Fixed → Finset Value)
    (outputInjective : ∀ fixed, Function.Injective (output fixed))
    (B : ℕ) (badCard : ∀ fixed, (badValues fixed).card ≤ B) :
    uniformProductBadMass output badValues ≤ (B : ℝ) / (2 : ℝ) ^ s := by
  have bound := uniformProductBadMass_le output badValues outputInjective B badCard
  simpa [card_binary_choice_block] using bound

/-- Binary free-coordinate specialization with a real-valued bad-value volume. -/
theorem binaryProductBadMass_le_realVolume
    {Fixed Value : Type*} [Fintype Fixed] [Nonempty Fixed]
    [DecidableEq Value]
    (s : ℕ) (output : Fixed → (Fin s → Fin 2) → Value)
    (badValues : Fixed → Finset Value)
    (outputInjective : ∀ fixed, Function.Injective (output fixed))
    (volume : ℝ) (badCard : ∀ fixed, ((badValues fixed).card : ℝ) ≤ volume) :
    uniformProductBadMass output badValues ≤ volume / (2 : ℝ) ^ s := by
  have bound := uniformProductBadMass_le_realVolume
    output badValues outputInjective volume badCard
  simpa [card_binary_choice_block] using bound

/-- The numerical decay after combining `s ≥ ell/18 - 2` free bits with the
stronger `exp(ell/100)` deletion-volume estimate proved in Lean. -/
theorem explicit_free_bit_decay
    {ell s : ℕ} (hell : 2000 < ell) (wholeBlocks : ell ≤ 18 * (s + 2)) :
    Real.exp ((ell : ℝ) / 100) / (2 : ℝ) ^ s <
      Real.exp (-(ell : ℝ) / 71) := by
  have logLower : (69 : ℝ) / 100 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have sNonnegative : (0 : ℝ) ≤ s := by positivity
  have logTimesLower : (69 : ℝ) / 100 * s ≤ Real.log 2 * s :=
    mul_le_mul_of_nonneg_right logLower.le sNonnegative
  have wholeBlocksReal : (ell : ℝ) ≤ 18 * (s + 2) := by exact_mod_cast wholeBlocks
  have scaledBlocks :
      (69 : ℝ) / 100 * ((ell : ℝ) / 18 - 2) ≤
        (69 : ℝ) / 100 * s := by
    gcongr
    linarith
  have exponentStrict :
      (ell : ℝ) / 100 - Real.log 2 * s < -(ell : ℝ) / 71 := by
    have hellReal : (2000 : ℝ) < ell := by exact_mod_cast hell
    nlinarith [scaledBlocks.trans logTimesLower]
  have twoPowIdentity :
      (2 : ℝ) ^ s = Real.exp (Real.log 2 * s) := by
    calc
      (2 : ℝ) ^ s = (Real.exp (Real.log 2)) ^ s := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((s : ℝ) * Real.log 2) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (Real.log 2 * s) := by
        congr 1
        ring
  rw [twoPowIdentity, ← Real.exp_sub]
  exact Real.exp_lt_exp.mpr exponentStrict

/-- End-to-end finite averaging plus exponential tail, abstracting only the concrete
codeword injection and the deletion-ball membership implication. -/
theorem binaryProductBadMass_lt_exp_neg_one_over_71
    {Fixed Value : Type*} [Fintype Fixed] [Nonempty Fixed]
    [DecidableEq Value]
    {ell s B : ℕ} (hell : 2000 < ell) (wholeBlocks : ell ≤ 18 * (s + 2))
    (output : Fixed → (Fin s → Fin 2) → Value)
    (badValues : Fixed → Finset Value)
    (outputInjective : ∀ fixed, Function.Injective (output fixed))
    (badCard : ∀ fixed, (badValues fixed).card ≤ B)
    (volume : (B : ℝ) ≤ Real.exp ((ell : ℝ) / 100)) :
    uniformProductBadMass output badValues < Real.exp (-(ell : ℝ) / 71) := by
  have massBound := binaryProductBadMass_le s output badValues outputInjective B badCard
  have denominatorPositive : (0 : ℝ) ≤ (2 : ℝ) ^ s := by positivity
  have volumeBound :
      (B : ℝ) / (2 : ℝ) ^ s ≤
        Real.exp ((ell : ℝ) / 100) / (2 : ℝ) ^ s := by
    exact div_le_div_of_nonneg_right volume denominatorPositive
  exact (massBound.trans volumeBound).trans_lt
    (explicit_free_bit_decay hell wholeBlocks)

/-- Real-volume endpoint used by the concrete deletion ball, with no rounding loss. -/
theorem binaryProductBadMass_lt_exp_neg_one_over_71_realVolume
    {Fixed Value : Type*} [Fintype Fixed] [Nonempty Fixed]
    [DecidableEq Value]
    {ell s : ℕ} (hell : 2000 < ell) (wholeBlocks : ell ≤ 18 * (s + 2))
    (output : Fixed → (Fin s → Fin 2) → Value)
    (badValues : Fixed → Finset Value)
    (outputInjective : ∀ fixed, Function.Injective (output fixed))
    (badCard : ∀ fixed,
      ((badValues fixed).card : ℝ) ≤ Real.exp ((ell : ℝ) / 100)) :
    uniformProductBadMass output badValues < Real.exp (-(ell : ℝ) / 71) := by
  have massBound := binaryProductBadMass_le_realVolume s output badValues
    outputInjective (Real.exp ((ell : ℝ) / 100)) badCard
  exact massBound.trans_lt (explicit_free_bit_decay hell wholeBlocks)

end TernarySyncAudit
