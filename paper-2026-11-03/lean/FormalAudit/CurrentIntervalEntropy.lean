import Mathlib
import FormalAudit.ConcreteIntervalEntropy
import FormalAudit.CurrentDeletionBallAnalytic

namespace TernarySyncAudit

/-! The conditional-entropy calculation used by the current `2001/2002`
transparent theorem.  The combinatorial block injection is reused from the
fully formalized six-codeword Brinkhuis development; only the larger deletion
radius and the new constants are specialized here. -/

/-- The current deletion-ball volume and `s >= ell/18 - 2` free bits imply
the paper's strict `exp(-9 ell / 500)` event bound. -/
theorem current_explicit_free_bit_decay
    {ell s : ℕ} (hell : 1000 < ell) (wholeBlocks : ell ≤ 18 * (s + 2)) :
    Real.exp ((9 : ℝ) * ell / 500) / (2 : ℝ) ^ s <
      Real.exp (-(9 : ℝ) * ell / 500) := by
  have logLower : (69 : ℝ) / 100 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have sNonnegative : (0 : ℝ) ≤ s := by positivity
  have logTimesLower : (69 : ℝ) / 100 * s ≤ Real.log 2 * s :=
    mul_le_mul_of_nonneg_right logLower.le sNonnegative
  have wholeBlocksReal : (ell : ℝ) ≤ 18 * (s + 2) := by
    exact_mod_cast wholeBlocks
  have scaledBlocks :
      (69 : ℝ) / 100 * ((ell : ℝ) / 18 - 2) ≤
        (69 : ℝ) / 100 * s := by
    gcongr
    linarith
  have hellReal : (1000 : ℝ) < ell := by exact_mod_cast hell
  have exponentStrict :
      (9 : ℝ) * ell / 500 - Real.log 2 * s <
        -(9 : ℝ) * ell / 500 := by
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

/-- Current high-LCS values after the outside choices are fixed. -/
noncomputable def currentConcreteBadValues
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (outside : OutsideChoices N (firstFreeBlock start) (freeBlockCount ell)) :
    Finset (FixedWord Symbol ell) :=
  deletionBall (concreteSecondInterval outer outside) (currentSmallDeletions ell)

/-- Fully formal conditional probability bound for one current-paper bad
equal-block event. -/
theorem current_concrete_interval_bad_mass_lt
    {N start ell : ℕ} (outer : ℕ → Symbol)
    (hell : 1000 < ell) (supportFits : start + 2 * ell ≤ 18 * N) :
    uniformProductBadMass
        (concreteFirstInterval (N := N) (start := start) (ell := ell) outer)
        (currentConcreteBadValues (N := N) (start := start) (ell := ell) outer) <
      Real.exp (-(9 : ℝ) * ell / 500) := by
  have hellEighteen : 18 ≤ ell := by omega
  have massBound := binaryProductBadMass_le_realVolume
    (freeBlockCount ell)
    (concreteFirstInterval (N := N) (start := start) (ell := ell) outer)
    (currentConcreteBadValues (N := N) (start := start) (ell := ell) outer)
    (fun outside => concreteFirstInterval_injective outer hellEighteen supportFits outside)
    (Real.exp ((9 : ℝ) * ell / 500))
    (fun outside => current_ternary_deletionBall_card_le_exp_nine_over_500
      hell.le (concreteSecondInterval outer outside))
  exact massBound.trans_lt
    (current_explicit_free_bit_decay hell
      (selected_free_blocks_whole_bound hellEighteen))

end TernarySyncAudit
