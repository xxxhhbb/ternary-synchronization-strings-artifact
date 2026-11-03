import Mathlib
import FormalAudit.DeletionBall

namespace TernarySyncAudit

/-! Current-paper deletion-ball arithmetic for eta = 1/1000. -/

open Finset

/-- The deletion counts corresponding exactly to `d < n / 1000` over the reals. -/
def currentSmallDeletions (n : ℕ) : Finset ℕ :=
  (Finset.range (n / 1000 + 1)).filter fun d => 1000 * d < n

theorem mem_currentSmallDeletions_iff {n d : ℕ} :
    d ∈ currentSmallDeletions n ↔ 1000 * d < n := by
  constructor
  · intro hd
    exact (Finset.mem_filter.mp hd).2
  · intro hd
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have : d ≤ n / 1000 :=
        (Nat.le_div_iff_mul_le (by norm_num)).2 (by simpa [Nat.mul_comm] using hd.le)
      omega
    · exact hd

/-- Semantic form of the exact high-LCS event used by the paper. -/
theorem mem_current_ternary_deletionBall_iff
    {n : ℕ} (x y : FixedWord (Fin 3) n) :
    x ∈ deletionBall y (currentSmallDeletions n) ↔
      ∃ d, 1000 * d < n ∧ ∃ h : d ≤ n,
        HasCommonSubsequenceAfterDeleting h x y := by
  rw [mem_deletionBall_iff]
  constructor
  · rintro ⟨d, hd, h, common⟩
    exact ⟨d, mem_currentSmallDeletions_iff.mp hd, h, common⟩
  · rintro ⟨d, hd, h, common⟩
    exact ⟨d, mem_currentSmallDeletions_iff.mpr hd, h, common⟩

/-- A single binomial coefficient is controlled by one term of the binomial expansion. -/
theorem current_choose_mul_scaled_pow_le
    (n d : ℕ) (hd : d ≤ n) :
    (n.choose d : ℝ) * ((1 : ℝ) / 1000) ^ d ≤
      (1 + (1 : ℝ) / 1000) ^ n := by
  have hdRange : d ∈ Finset.range (n + 1) := by
    simp [hd]
  have termNonnegative :
      ∀ m ∈ Finset.range (n + 1),
        0 ≤ ((1 : ℝ) / 1000) ^ m * 1 ^ (n - m) * (n.choose m : ℝ) := by
    intro m hm
    positivity
  have oneTerm := Finset.single_le_sum termNonnegative hdRange
  calc
    (n.choose d : ℝ) * ((1 : ℝ) / 1000) ^ d =
        ((1 : ℝ) / 1000) ^ d * 1 ^ (n - d) * (n.choose d : ℝ) := by ring
    _ ≤ ∑ m ∈ Finset.range (n + 1),
        ((1 : ℝ) / 1000) ^ m * 1 ^ (n - m) * (n.choose m : ℝ) := oneTerm
    _ = ((1 : ℝ) / 1000 + 1) ^ n := by
      symm
      exact add_pow ((1 : ℝ) / 1000) 1 n
    _ = (1 + (1 : ℝ) / 1000) ^ n := by ring

/-- The binomial coefficient bound needed below, obtained without Stirling's formula. -/
theorem current_choose_le_exp_mul_pow_1000
    (n d : ℕ) (hd : d ≤ n) :
    (n.choose d : ℝ) ≤
      Real.exp ((n : ℝ) / 1000) * (1000 : ℝ) ^ d := by
  have scaled := current_choose_mul_scaled_pow_le n d hd
  have powNonnegative : 0 ≤ (1000 : ℝ) ^ d := by positivity
  have unscaled := mul_le_mul_of_nonneg_right scaled powNonnegative
  have expOneStep : 1 + (1 : ℝ) / 1000 ≤ Real.exp ((1 : ℝ) / 1000) := by
    simpa [add_comm] using Real.add_one_le_exp ((1 : ℝ) / 1000)
  have powBound :
      (1 + (1 : ℝ) / 1000) ^ n ≤
        (Real.exp ((1 : ℝ) / 1000)) ^ n := by
    exact pow_le_pow_left₀ (by norm_num) expOneStep n
  calc
    (n.choose d : ℝ) =
        ((n.choose d : ℝ) * ((1 : ℝ) / 1000) ^ d) * (1000 : ℝ) ^ d := by
      rw [mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (1 + (1 : ℝ) / 1000) ^ n * (1000 : ℝ) ^ d := unscaled
    _ ≤ (Real.exp ((1 : ℝ) / 1000)) ^ n * (1000 : ℝ) ^ d := by
      gcongr
    _ = Real.exp ((n : ℝ) / 1000) * (1000 : ℝ) ^ d := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

/-- A deliberately coarse, proof-producing comparison for the integer base. -/
theorem three_million_lt_exp_fifteen :
    (3000000 : ℝ) < Real.exp 15 := by
  have h := Real.sum_le_exp_of_nonneg (x := (15 : ℝ)) (by norm_num) 22
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- Every summand in the explicit ternary deletion ball has one common exponent. -/
theorem current_deletion_summand_le
    {n d : ℕ} (hd : 1000 * d < n) :
    (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d ≤
      Real.exp ((17 : ℝ) * n / 1000) := by
  have hdLe : d ≤ n := by omega
  have chooseBound := current_choose_le_exp_mul_pow_1000 n d hdLe
  have chooseNonnegative : 0 ≤ (n.choose d : ℝ) := by positivity
  have squareBound :
      (n.choose d : ℝ) ^ 2 ≤
        (Real.exp ((n : ℝ) / 1000) * (1000 : ℝ) ^ d) ^ 2 := by
    exact pow_le_pow_left₀ chooseNonnegative chooseBound 2
  have withAlphabet :
      (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d ≤
        (Real.exp ((n : ℝ) / 1000) * (1000 : ℝ) ^ d) ^ 2 *
          (3 : ℝ) ^ d := by
    exact mul_le_mul_of_nonneg_right squareBound (by positivity)
  have basePowBound :
      (3000000 : ℝ) ^ d ≤ Real.exp ((15 : ℝ) * d) := by
    calc
      (3000000 : ℝ) ^ d ≤ (Real.exp 15) ^ d := by
        exact pow_le_pow_left₀ (by norm_num) three_million_lt_exp_fifteen.le d
      _ = Real.exp ((15 : ℝ) * d) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hdReal : (1000 : ℝ) * d < n := by exact_mod_cast hd
  have exponentBound :
      (n : ℝ) / 500 + 15 * d ≤ (17 : ℝ) * n / 1000 := by
    linarith
  have baseIdentity :
      ((1000 : ℝ) ^ d) ^ 2 * (3 : ℝ) ^ d = (3000000 : ℝ) ^ d := by
    rw [pow_two, ← mul_pow, ← mul_pow]
    norm_num
  calc
    (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d ≤
        (Real.exp ((n : ℝ) / 1000) * (1000 : ℝ) ^ d) ^ 2 *
          (3 : ℝ) ^ d := withAlphabet
    _ = Real.exp ((n : ℝ) / 500) * (3000000 : ℝ) ^ d := by
      rw [mul_pow]
      have expSquare :
          Real.exp ((n : ℝ) / 1000) ^ 2 = Real.exp ((n : ℝ) / 500) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [expSquare]
      rw [mul_assoc, baseIdentity]
    _ ≤ Real.exp ((n : ℝ) / 500) * Real.exp ((15 : ℝ) * d) := by
      gcongr
    _ = Real.exp ((n : ℝ) / 500 + 15 * d) := by
      rw [Real.exp_add]
    _ ≤ Real.exp ((17 : ℝ) * n / 1000) := Real.exp_monotone exponentBound

/-- The number of permitted deletion counts costs at most `exp(n/1000)`. -/
theorem currentSmallDeletions_card_le_exp
    {n : ℕ} (_hn : 1000 ≤ n) :
    ((currentSmallDeletions n).card : ℝ) ≤ Real.exp ((n : ℝ) / 1000) := by
  let k := n / 1000
  have cardBound : (currentSmallDeletions n).card ≤ k + 1 := by
    calc
      (currentSmallDeletions n).card ≤ (Finset.range (n / 1000 + 1)).card :=
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
  have quotientBound : (k : ℝ) ≤ (n : ℝ) / 1000 := by
    have hNat : k * 1000 ≤ n := by
      dsimp [k]
      exact Nat.div_mul_le_self n 1000
    have hReal : (k : ℝ) * 1000 ≤ n := by exact_mod_cast hNat
    linarith
  calc
    ((currentSmallDeletions n).card : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast cardBound
    _ = (1 : ℝ) + k := by push_cast; ring
    _ ≤ (2 : ℝ) ^ k := bernoulli
    _ ≤ Real.exp (k : ℝ) := powerBound
    _ ≤ Real.exp ((n : ℝ) / 1000) := Real.exp_monotone quotientBound

/-- A stronger intermediate rate than the paper needs, obtained by the coarse
binomial-expansion proof above. -/
theorem current_ternary_deletion_volume_le_exp_nine_over_500
    {n : ℕ} (hn : 1000 ≤ n) :
    (∑ d ∈ currentSmallDeletions n,
        (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d) ≤
      Real.exp ((9 : ℝ) * n / 500) := by
  have summandBound :
      ∀ d ∈ currentSmallDeletions n,
        (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d ≤
          Real.exp ((17 : ℝ) * n / 1000) := by
    intro d hd
    exact current_deletion_summand_le (mem_currentSmallDeletions_iff.mp hd)
  have sumBound :
      (∑ d ∈ currentSmallDeletions n,
          (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d) ≤
        (currentSmallDeletions n).card *
          Real.exp ((17 : ℝ) * n / 1000) := by
    calc
      (∑ d ∈ currentSmallDeletions n,
          (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d) ≤
          ∑ _d ∈ currentSmallDeletions n,
            Real.exp ((17 : ℝ) * n / 1000) := by
              exact Finset.sum_le_sum fun d hd => summandBound d hd
      _ = (currentSmallDeletions n).card *
          Real.exp ((17 : ℝ) * n / 1000) := by simp
  have cardBound := currentSmallDeletions_card_le_exp hn
  have nonnegativeExp : 0 ≤ Real.exp ((17 : ℝ) * n / 1000) := Real.exp_nonneg _
  calc
    (∑ d ∈ currentSmallDeletions n,
        (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d) ≤
        (currentSmallDeletions n).card *
          Real.exp ((17 : ℝ) * n / 1000) := sumBound
    _ ≤ Real.exp ((n : ℝ) / 1000) *
        Real.exp ((17 : ℝ) * n / 1000) := by
          exact mul_le_mul_of_nonneg_right cardBound nonnegativeExp
    _ = Real.exp ((9 : ℝ) * n / 500) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The complete analytic estimate omitted by the first formalization report. -/
theorem current_ternary_deletion_volume_lt
    {n : ℕ} (hn : 1000 ≤ n) :
    (∑ d ∈ currentSmallDeletions n,
        (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d) <
      Real.exp ((19 : ℝ) * n / 1000) := by
  have combined := current_ternary_deletion_volume_le_exp_nine_over_500 hn
  have exponentStrict : (9 : ℝ) * n / 500 < (19 : ℝ) * n / 1000 := by
    have hnPositive : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    nlinarith
  exact combined.trans_lt (Real.exp_lt_exp.mpr exponentStrict)

/-- Cardinal form at the stronger intermediate rate, suitable for the event-tail lemma. -/
theorem current_ternary_deletionBall_card_le_exp_nine_over_500
    {n : ℕ} (hn : 1000 ≤ n) (y : FixedWord (Fin 3) n) :
    ((deletionBall y (currentSmallDeletions n)).card : ℝ) ≤
      Real.exp ((9 : ℝ) * n / 500) := by
  have natBound := deletionBall_card_le y (currentSmallDeletions n)
  have realBound :
      ((deletionBall y (currentSmallDeletions n)).card : ℝ) ≤
        ∑ d ∈ currentSmallDeletions n,
          (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d := by
    exact_mod_cast natBound
  exact realBound.trans (current_ternary_deletion_volume_le_exp_nine_over_500 hn)

/-- Cardinal form: every ternary high-LCS deletion ball has size below `exp(n/80)`. -/
theorem current_ternary_deletionBall_card_lt
    {n : ℕ} (hn : 1000 ≤ n) (y : FixedWord (Fin 3) n) :
    ((deletionBall y (currentSmallDeletions n)).card : ℝ) <
      Real.exp ((19 : ℝ) * n / 1000) := by
  have natBound := deletionBall_card_le y (currentSmallDeletions n)
  have realBound :
      ((deletionBall y (currentSmallDeletions n)).card : ℝ) ≤
        ∑ d ∈ currentSmallDeletions n,
          (n.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d := by
    exact_mod_cast natBound
  exact realBound.trans_lt (current_ternary_deletion_volume_lt hn)

end TernarySyncAudit
