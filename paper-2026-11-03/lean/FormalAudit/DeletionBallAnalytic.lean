import Mathlib
import FormalAudit.DeletionBall

namespace TernarySyncAudit

open Finset

/-- The deletion counts corresponding exactly to `d < n / 2000` over the reals. -/
def explicitSmallDeletions (n : ℕ) : Finset ℕ :=
  (Finset.range (n / 2000 + 1)).filter fun d => 2000 * d < n

theorem mem_explicitSmallDeletions_iff {n d : ℕ} :
    d ∈ explicitSmallDeletions n ↔ 2000 * d < n := by
  constructor
  · intro hd
    exact (Finset.mem_filter.mp hd).2
  · intro hd
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have : d ≤ n / 2000 :=
        (Nat.le_div_iff_mul_le (by norm_num)).2 (by simpa [Nat.mul_comm] using hd.le)
      omega
    · exact hd

/-- Semantic form of the exact high-LCS event used by the paper. -/
theorem mem_explicit_ternary_deletionBall_iff
    {n : ℕ} (x y : FixedWord (Fin 3) n) :
    x ∈ deletionBall y (explicitSmallDeletions n) ↔
      ∃ d, 2000 * d < n ∧ ∃ h : d ≤ n,
        HasCommonSubsequenceAfterDeleting h x y := by
  rw [mem_deletionBall_iff]
  constructor
  · rintro ⟨d, hd, h, common⟩
    exact ⟨d, mem_explicitSmallDeletions_iff.mp hd, h, common⟩
  · rintro ⟨d, hd, h, common⟩
    exact ⟨d, mem_explicitSmallDeletions_iff.mpr hd, h, common⟩

/-- A single binomial coefficient is controlled by one term of the binomial expansion. -/
theorem choose_mul_scaled_pow_le
    (n d : ℕ) (hd : d ≤ n) :
    (n.choose d : ℝ) * ((1 : ℝ) / 2000) ^ d ≤
      (1 + (1 : ℝ) / 2000) ^ n := by
  have hdRange : d ∈ Finset.range (n + 1) := by
    simp [hd]
  have termNonnegative :
      ∀ m ∈ Finset.range (n + 1),
        0 ≤ ((1 : ℝ) / 2000) ^ m * 1 ^ (n - m) * (n.choose m : ℝ) := by
    intro m hm
    positivity
  have oneTerm := Finset.single_le_sum termNonnegative hdRange
  calc
    (n.choose d : ℝ) * ((1 : ℝ) / 2000) ^ d =
        ((1 : ℝ) / 2000) ^ d * 1 ^ (n - d) * (n.choose d : ℝ) := by ring
    _ ≤ ∑ m ∈ Finset.range (n + 1),
        ((1 : ℝ) / 2000) ^ m * 1 ^ (n - m) * (n.choose m : ℝ) := oneTerm
    _ = ((1 : ℝ) / 2000 + 1) ^ n := by
      symm
      exact add_pow ((1 : ℝ) / 2000) 1 n
    _ = (1 + (1 : ℝ) / 2000) ^ n := by ring

/-- The binomial coefficient bound needed below, obtained without Stirling's formula. -/
theorem choose_le_exp_mul_pow_2000
    (n d : ℕ) (hd : d ≤ n) :
    (n.choose d : ℝ) ≤
      Real.exp ((n : ℝ) / 2000) * (2000 : ℝ) ^ d := by
  have scaled := choose_mul_scaled_pow_le n d hd
  have powNonnegative : 0 ≤ (2000 : ℝ) ^ d := by positivity
  have unscaled := mul_le_mul_of_nonneg_right scaled powNonnegative
  have expOneStep : 1 + (1 : ℝ) / 2000 ≤ Real.exp ((1 : ℝ) / 2000) := by
    simpa [add_comm] using Real.add_one_le_exp ((1 : ℝ) / 2000)
  have powBound :
      (1 + (1 : ℝ) / 2000) ^ n ≤
        (Real.exp ((1 : ℝ) / 2000)) ^ n := by
    exact pow_le_pow_left₀ (by norm_num) expOneStep n
  calc
    (n.choose d : ℝ) =
        ((n.choose d : ℝ) * ((1 : ℝ) / 2000) ^ d) * (2000 : ℝ) ^ d := by
      rw [mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (1 + (1 : ℝ) / 2000) ^ n * (2000 : ℝ) ^ d := unscaled
    _ ≤ (Real.exp ((1 : ℝ) / 2000)) ^ n * (2000 : ℝ) ^ d := by
      gcongr
    _ = Real.exp ((n : ℝ) / 2000) * (2000 : ℝ) ^ d := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

/-- A deliberately coarse, proof-producing comparison for the integer base. -/
theorem twelve_million_lt_exp_seventeen :
    (12000000 : ℝ) < Real.exp 17 := by
  have h := Real.sum_le_exp_of_nonneg (x := (17 : ℝ)) (by norm_num) 18
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- Every summand in the explicit ternary deletion ball has one common exponent. -/
theorem explicit_deletion_summand_le
    {n d : ℕ} (hd : 2000 * d < n) :
    (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d ≤
      Real.exp ((19 : ℝ) * n / 2000) := by
  have hdLe : d ≤ n := by omega
  have chooseBound := choose_le_exp_mul_pow_2000 n d hdLe
  have chooseNonnegative : 0 ≤ (n.choose d : ℝ) := by positivity
  have squareBound :
      (n.choose d : ℝ) ^ 2 ≤
        (Real.exp ((n : ℝ) / 2000) * (2000 : ℝ) ^ d) ^ 2 := by
    exact pow_le_pow_left₀ chooseNonnegative chooseBound 2
  have withAlphabet :
      (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d ≤
        (Real.exp ((n : ℝ) / 2000) * (2000 : ℝ) ^ d) ^ 2 *
          (3 : ℝ) ^ d := by
    exact mul_le_mul_of_nonneg_right squareBound (by positivity)
  have basePowBound :
      (12000000 : ℝ) ^ d ≤ Real.exp ((17 : ℝ) * d) := by
    calc
      (12000000 : ℝ) ^ d ≤ (Real.exp 17) ^ d := by
        exact pow_le_pow_left₀ (by norm_num) twelve_million_lt_exp_seventeen.le d
      _ = Real.exp ((17 : ℝ) * d) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hdReal : (2000 : ℝ) * d < n := by exact_mod_cast hd
  have exponentBound :
      (n : ℝ) / 1000 + 17 * d ≤ (19 : ℝ) * n / 2000 := by
    linarith
  have baseIdentity :
      ((2000 : ℝ) ^ d) ^ 2 * (3 : ℝ) ^ d = (12000000 : ℝ) ^ d := by
    rw [pow_two, ← mul_pow, ← mul_pow]
    norm_num
  calc
    (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d ≤
        (Real.exp ((n : ℝ) / 2000) * (2000 : ℝ) ^ d) ^ 2 *
          (3 : ℝ) ^ d := withAlphabet
    _ = Real.exp ((n : ℝ) / 1000) * (12000000 : ℝ) ^ d := by
      rw [mul_pow]
      have expSquare :
          Real.exp ((n : ℝ) / 2000) ^ 2 = Real.exp ((n : ℝ) / 1000) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [expSquare]
      rw [mul_assoc, baseIdentity]
    _ ≤ Real.exp ((n : ℝ) / 1000) * Real.exp ((17 : ℝ) * d) := by
      gcongr
    _ = Real.exp ((n : ℝ) / 1000 + 17 * d) := by
      rw [Real.exp_add]
    _ ≤ Real.exp ((19 : ℝ) * n / 2000) := Real.exp_monotone exponentBound

/-- The number of permitted deletion counts costs at most `exp(n/2000)`. -/
theorem explicitSmallDeletions_card_le_exp
    {n : ℕ} (_hn : 2000 ≤ n) :
    ((explicitSmallDeletions n).card : ℝ) ≤ Real.exp ((n : ℝ) / 2000) := by
  let k := n / 2000
  have cardBound : (explicitSmallDeletions n).card ≤ k + 1 := by
    calc
      (explicitSmallDeletions n).card ≤ (Finset.range (n / 2000 + 1)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = k + 1 := by simp [k]
  have bernoulli : (1 : ℝ) + k ≤ (2 : ℝ) ^ k := by
    simpa [one_add_one_eq_two] using
      (one_add_mul_le_pow (R := ℝ) (a := (1 : ℝ)) (by norm_num) k)
  have twoLeExpOne : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  have powerBound : (2 : ℝ) ^ k ≤ Real.exp (k : ℝ) := by
    calc
      (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k :=
        pow_le_pow_left₀ (by norm_num) twoLeExpOne k
      _ = Real.exp (k : ℝ) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have quotientBound : (k : ℝ) ≤ (n : ℝ) / 2000 := by
    have hNat : k * 2000 ≤ n := by
      dsimp [k]
      exact Nat.div_mul_le_self n 2000
    have hReal : (k : ℝ) * 2000 ≤ n := by exact_mod_cast hNat
    linarith
  calc
    ((explicitSmallDeletions n).card : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast cardBound
    _ = (1 : ℝ) + k := by push_cast; ring
    _ ≤ (2 : ℝ) ^ k := bernoulli
    _ ≤ Real.exp (k : ℝ) := powerBound
    _ ≤ Real.exp ((n : ℝ) / 2000) := Real.exp_monotone quotientBound

/-- A stronger intermediate rate than the paper needs, obtained by the coarse
binomial-expansion proof above. -/
theorem explicit_ternary_deletion_volume_le_exp_hundred
    {n : ℕ} (hn : 2000 ≤ n) :
    (∑ d ∈ explicitSmallDeletions n,
        (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d) ≤
      Real.exp ((n : ℝ) / 100) := by
  have summandBound :
      ∀ d ∈ explicitSmallDeletions n,
        (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d ≤
          Real.exp ((19 : ℝ) * n / 2000) := by
    intro d hd
    exact explicit_deletion_summand_le (mem_explicitSmallDeletions_iff.mp hd)
  have sumBound :
      (∑ d ∈ explicitSmallDeletions n,
          (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d) ≤
        (explicitSmallDeletions n).card *
          Real.exp ((19 : ℝ) * n / 2000) := by
    calc
      (∑ d ∈ explicitSmallDeletions n,
          (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d) ≤
          ∑ _d ∈ explicitSmallDeletions n,
            Real.exp ((19 : ℝ) * n / 2000) := by
              exact Finset.sum_le_sum fun d hd => summandBound d hd
      _ = (explicitSmallDeletions n).card *
          Real.exp ((19 : ℝ) * n / 2000) := by simp
  have cardBound := explicitSmallDeletions_card_le_exp hn
  have nonnegativeExp : 0 ≤ Real.exp ((19 : ℝ) * n / 2000) := Real.exp_nonneg _
  calc
    (∑ d ∈ explicitSmallDeletions n,
        (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d) ≤
        (explicitSmallDeletions n).card *
          Real.exp ((19 : ℝ) * n / 2000) := sumBound
    _ ≤ Real.exp ((n : ℝ) / 2000) *
        Real.exp ((19 : ℝ) * n / 2000) := by
          exact mul_le_mul_of_nonneg_right cardBound nonnegativeExp
    _ = Real.exp ((n : ℝ) / 100) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The complete analytic estimate omitted by the first formalization report. -/
theorem explicit_ternary_deletion_volume_lt
    {n : ℕ} (hn : 2000 ≤ n) :
    (∑ d ∈ explicitSmallDeletions n,
        (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d) <
      Real.exp ((n : ℝ) / 80) := by
  have combined := explicit_ternary_deletion_volume_le_exp_hundred hn
  have exponentStrict : (n : ℝ) / 100 < (n : ℝ) / 80 := by
    have hnPositive : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    nlinarith
  exact combined.trans_lt (Real.exp_lt_exp.mpr exponentStrict)

/-- Cardinal form at the stronger intermediate rate, suitable for the event-tail lemma. -/
theorem explicit_ternary_deletionBall_card_le_exp_hundred
    {n : ℕ} (hn : 2000 ≤ n) (y : FixedWord (Fin 3) n) :
    ((deletionBall y (explicitSmallDeletions n)).card : ℝ) ≤
      Real.exp ((n : ℝ) / 100) := by
  have natBound := deletionBall_card_le y (explicitSmallDeletions n)
  have realBound :
      ((deletionBall y (explicitSmallDeletions n)).card : ℝ) ≤
        ∑ d ∈ explicitSmallDeletions n,
          (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d := by
    exact_mod_cast natBound
  exact realBound.trans (explicit_ternary_deletion_volume_le_exp_hundred hn)

/-- Cardinal form: every ternary high-LCS deletion ball has size below `exp(n/80)`. -/
theorem explicit_ternary_deletionBall_card_lt
    {n : ℕ} (hn : 2000 ≤ n) (y : FixedWord (Fin 3) n) :
    ((deletionBall y (explicitSmallDeletions n)).card : ℝ) <
      Real.exp ((n : ℝ) / 80) := by
  have natBound := deletionBall_card_le y (explicitSmallDeletions n)
  have realBound :
      ((deletionBall y (explicitSmallDeletions n)).card : ℝ) ≤
        ∑ d ∈ explicitSmallDeletions n,
          (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d := by
    exact_mod_cast natBound
  exact realBound.trans_lt (explicit_ternary_deletion_volume_lt hn)

end TernarySyncAudit
