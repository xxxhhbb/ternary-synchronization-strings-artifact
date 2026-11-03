import Mathlib
import FormalAudit.LocalLemmaProduct

namespace TernarySyncAudit

open Finset

/-- A finite map whose fibers on `s` have size at most `K` loses at most a factor `K`. -/
theorem card_le_fiber_bound_mul_image_card
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (K : ℕ)
    (fiberBound : ∀ b ∈ s.image f, (s.filter fun a => f a = b).card ≤ K) :
    s.card ≤ K * (s.image f).card := by
  rw [Finset.card_eq_sum_card_fiberwise (t := s.image f)
    (fun a ha => Finset.mem_image_of_mem f ha)]
  calc
    (∑ b ∈ s.image f, (s.filter fun a => f a = b).card)
        ≤ ∑ _b ∈ s.image f, K := by
          exact Finset.sum_le_sum fun b hb => fiberBound b hb
    _ = K * (s.image f).card := by simp [Nat.mul_comm]

/-- Injectivity of the macroblock output preserves the number of good choices. -/
theorem card_image_of_good_choices
    {α β : Type*} [DecidableEq β]
    (goodChoices : Finset α) (output : α → β)
    (outputInjective : Function.Injective output) :
    (goodChoices.image output).card = goodChoices.card :=
  Finset.card_image_of_injective goodChoices outputInjective

/-- Rationally checkable lower bound on `exp 20` used in the paper. -/
theorem exp_twenty_gt_624000 : (624000 : ℝ) < Real.exp 20 := by
  have h := Real.sum_le_exp_of_nonneg (x := (20 : ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- The exact full-output abundance exponent in Appendix D. -/
theorem explicit_full_output_exponent :
    (1 : ℝ) / 27 < Real.log 2 / 18 - 202 * Real.exp (-20) := by
  have logLower : (69 : ℝ) / 100 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have expTail : Real.exp (-20) < (1 : ℝ) / 624000 := by
    rw [Real.exp_neg]
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 624000)
        exp_twenty_gt_624000)
  nlinarith

/-- The final truncation comparison `e^(M/27)/2 ≥ e^(n/28)`. -/
theorem explicit_prefix_exponent
    {n M : ℕ} (hn : 756 ≤ n) (hM : n ≤ M) :
    Real.exp ((n : ℝ) / 28) ≤ Real.exp ((M : ℝ) / 27) / 2 := by
  have logUpper : Real.log 2 < 1 := by
    linarith [Real.log_two_lt_d9]
  have hnReal : (756 : ℝ) ≤ n := by exact_mod_cast hn
  have hMReal : (n : ℝ) ≤ M := by exact_mod_cast hM
  have exponentBound : (n : ℝ) / 28 + Real.log 2 ≤ (M : ℝ) / 27 := by
    calc
      (n : ℝ) / 28 + Real.log 2 ≤ (n : ℝ) / 28 + (n : ℝ) / 756 := by
        gcongr
        nlinarith
      _ = (n : ℝ) / 27 := by ring
      _ ≤ (M : ℝ) / 27 := by gcongr
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  exact Real.exp_monotone exponentBound

/--
The deterministic final step of the explicit abundance proof.  If there are
at least `e^(M/27)` good full outputs and truncation has multiplicity at most
two, then there are at least `e^(n/28)` distinct good prefixes.
-/
theorem explicit_prefix_abundance
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (goodFull : Finset α) (truncate : α → β) {n M : ℕ}
    (hn : 756 ≤ n) (hM : n ≤ M)
    (fullLower : Real.exp ((M : ℝ) / 27) ≤ goodFull.card)
    (prefixMultiplicity :
      ∀ b ∈ goodFull.image truncate,
        (goodFull.filter fun a => truncate a = b).card ≤ 2) :
    Real.exp ((n : ℝ) / 28) ≤ (goodFull.image truncate).card := by
  have fiberCount :=
    card_le_fiber_bound_mul_image_card goodFull truncate 2 prefixMultiplicity
  have fiberCountReal :
      (goodFull.card : ℝ) ≤ 2 * ((goodFull.image truncate).card : ℝ) := by
    exact_mod_cast fiberCount
  have prefixExp := explicit_prefix_exponent hn hM
  nlinarith

/-- The full deterministic counting pipeline after the LLL survival bound. -/
theorem explicit_abundance_pipeline
    {Choice Full Prefix : Type*}
    [DecidableEq Full] [DecidableEq Prefix]
    (goodChoices : Finset Choice) (output : Choice → Full)
    (truncate : Full → Prefix) {n M : ℕ}
    (hn : 756 ≤ n) (hM : n ≤ M)
    (outputInjective : Function.Injective output)
    (choiceLower :
      Real.exp ((Real.log 2 / 18 - 202 * Real.exp (-20)) * M) ≤
        goodChoices.card)
    (prefixMultiplicity :
      ∀ b ∈ (goodChoices.image output).image truncate,
        ((goodChoices.image output).filter fun a => truncate a = b).card ≤ 2) :
    Real.exp ((n : ℝ) / 28) ≤
      ((goodChoices.image output).image truncate).card := by
  have nonnegativeM : (0 : ℝ) ≤ M := by positivity
  have rateLower :
      (M : ℝ) / 27 ≤
        (Real.log 2 / 18 - 202 * Real.exp (-20)) * M := by
    have rate := explicit_full_output_exponent
    nlinarith
  have fullLowerChoices :
      Real.exp ((M : ℝ) / 27) ≤ goodChoices.card := by
    exact (Real.exp_monotone rateLower).trans choiceLower
  have fullCard : (goodChoices.image output).card = goodChoices.card :=
    card_image_of_good_choices goodChoices output outputInjective
  apply explicit_prefix_abundance (goodChoices.image output) truncate hn hM
  · simpa [fullCard] using fullLowerChoices
  · exact prefixMultiplicity

end TernarySyncAudit
