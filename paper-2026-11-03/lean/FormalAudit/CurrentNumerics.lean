import Mathlib
import FormalAudit.LocalLemmaProduct

namespace TernarySyncAudit

/-! Exact real-number checks for the current transparent theorem.  These
lemmas isolate the constants used after the conditional event bound. -/

theorem current_charge_lt_half {ell : ℕ} (hell : 1000 < ell) :
    Real.exp (-(ell : ℝ) / 80) < (1 : ℝ) / 2 := by
  have exponentBound : -(ell : ℝ) / 80 < -(25 : ℝ) / 2 := by
    have hellReal : (1000 : ℝ) < ell := by exact_mod_cast hell
    linarith
  have expBound := Real.exp_strictMono exponentBound
  have expTwelveGtTwo : (2 : ℝ) < Real.exp ((25 : ℝ) / 2) := by
    have h : (12 : ℝ) < Real.exp ((25 : ℝ) / 2) := by
      have := Real.add_one_lt_exp
        (x := (25 : ℝ) / 2) (by norm_num)
      nlinarith
    linarith
  have inverseBound : Real.exp (-(25 : ℝ) / 2) < (1 : ℝ) / 2 := by
    rw [show -(25 : ℝ) / 2 = -((25 : ℝ) / 2) by ring, Real.exp_neg]
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) expTwelveGtTwo)
  exact expBound.trans inverseBound

private noncomputable def currentGeometricRatio : ℝ := (80 : ℝ) / 81

private noncomputable def currentNeighborMajorant (ell k : ℕ) : ℝ :=
  3 * ((ell + 1000 + k : ℕ) : ℝ) * Real.exp (-(25 : ℝ) / 2) *
    currentGeometricRatio ^ k

private theorem currentGeometricRatio_nonnegative :
    0 ≤ currentGeometricRatio := by unfold currentGeometricRatio; norm_num

private theorem currentGeometricRatio_lt_one : currentGeometricRatio < 1 := by
  unfold currentGeometricRatio
  norm_num

private theorem currentGeometricRatio_norm_lt_one :
    ‖currentGeometricRatio‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg currentGeometricRatio_nonnegative]
  exact currentGeometricRatio_lt_one

private theorem currentNeighborMajorant_summable (ell : ℕ) :
    Summable (currentNeighborMajorant ell) := by
  have geom : Summable (fun k : ℕ => currentGeometricRatio ^ k) :=
    summable_geometric_of_norm_lt_one currentGeometricRatio_norm_lt_one
  have moment : Summable (fun k : ℕ => (k : ℝ) * currentGeometricRatio ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      currentGeometricRatio_norm_lt_one).summable
  have split : Summable (fun k : ℕ =>
      (((ell + 1000 : ℕ) : ℝ) * currentGeometricRatio ^ k) +
        (k : ℝ) * currentGeometricRatio ^ k) :=
    (geom.mul_left _).add moment
  refine (split.mul_left (3 * Real.exp (-(25 : ℝ) / 2))).congr ?_
  intro k
  unfold currentNeighborMajorant
  push_cast
  ring

private theorem currentNeighborMajorant_tsum (ell : ℕ) :
    (∑' k : ℕ, currentNeighborMajorant ell k) =
      3 * Real.exp (-(25 : ℝ) / 2) * (81 * (ell + 1000) + 6480) := by
  have geom : Summable (fun k : ℕ => currentGeometricRatio ^ k) :=
    summable_geometric_of_norm_lt_one currentGeometricRatio_norm_lt_one
  have moment : Summable (fun k : ℕ => (k : ℝ) * currentGeometricRatio ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      currentGeometricRatio_norm_lt_one).summable
  have termIdentity (k : ℕ) :
      currentNeighborMajorant ell k =
        3 * Real.exp (-(25 : ℝ) / 2) *
          ((((ell + 1000 : ℕ) : ℝ) * currentGeometricRatio ^ k) +
            (k : ℝ) * currentGeometricRatio ^ k) := by
    unfold currentNeighborMajorant
    push_cast
    ring
  rw [tsum_congr termIdentity, tsum_mul_left]
  rw [(geom.mul_left (((ell + 1000 : ℕ) : ℝ))).tsum_add moment]
  rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one
    currentGeometricRatio_norm_lt_one]
  rw [tsum_geometric_of_lt_one currentGeometricRatio_nonnegative
    currentGeometricRatio_lt_one]
  unfold currentGeometricRatio
  norm_num
  ring

private theorem exp_twenty_five_halves_gt_248832 :
    (248832 : ℝ) < Real.exp ((25 : ℝ) / 2) := by
  have expFiveHalvesGtTwelve :
      (12 : ℝ) < Real.exp ((5 : ℝ) / 2) := by
    have series := Real.sum_le_exp_of_nonneg
      (x := (5 : ℝ) / 2) (by norm_num) 7
    norm_num [Finset.sum_range_succ] at series ⊢
    linarith
  have powStrict : (12 : ℝ) ^ 5 < (Real.exp ((5 : ℝ) / 2)) ^ 5 := by
    exact pow_lt_pow_left₀ expFiveHalvesGtTwelve (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at powStrict
  norm_num at powStrict ⊢
  convert powStrict using 1

private theorem currentNeighborMajorant_tsum_lt
    (ell : ℕ) (hell : 1000 ≤ ell) :
    (∑' k : ℕ, currentNeighborMajorant ell k) < (ell : ℝ) / 490 := by
  rw [currentNeighborMajorant_tsum]
  have expSmall : Real.exp (-(25 : ℝ) / 2) < (1 : ℝ) / 248832 := by
    rw [show -(25 : ℝ) / 2 = -((25 : ℝ) / 2) by ring, Real.exp_neg]
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 248832)
        exp_twenty_five_halves_gt_248832)
  have hellReal : (1000 : ℝ) ≤ ell := by exact_mod_cast hell
  have expPositive : 0 < Real.exp (-(25 : ℝ) / 2) := Real.exp_pos _
  nlinarith

private theorem current_event_charge_le_majorant (ell k : ℕ) :
    3 * ((ell + 1000 + k : ℕ) : ℝ) *
        Real.exp (-((1000 + k : ℕ) : ℝ) / 80) ≤
      currentNeighborMajorant ell k := by
  let q₀ := Real.exp (-(1 : ℝ) / 80)
  have q₀Nonnegative : 0 ≤ q₀ := Real.exp_nonneg _
  have q₀LeRatio : q₀ ≤ currentGeometricRatio := by
    have expLower := Real.add_one_lt_exp
      (x := (1 : ℝ) / 80) (by norm_num)
    have positiveExp : 0 < Real.exp ((1 : ℝ) / 80) := Real.exp_pos _
    have qIdentity : q₀ = (Real.exp ((1 : ℝ) / 80))⁻¹ := by
      unfold q₀
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [qIdentity]
    unfold currentGeometricRatio
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 81)).2
    have h : (Real.exp ((1 : ℝ) / 80))⁻¹ * 81 ≤ 80 := by
      apply (inv_mul_le_iff₀ positiveExp).2
      nlinarith
    simpa [mul_comm] using h
  have ratioLeOne : currentGeometricRatio ≤ 1 := currentGeometricRatio_lt_one.le
  have powFirst : q₀ ^ k ≤ currentGeometricRatio ^ k :=
    pow_le_pow_left₀ q₀Nonnegative q₀LeRatio _
  have exponentialPower :
      Real.exp (-((1000 + k : ℕ) : ℝ) / 80) =
        Real.exp (-(25 : ℝ) / 2) * q₀ ^ k := by
    rw [show -((1000 + k : ℕ) : ℝ) / 80 =
        -(25 : ℝ) / 2 + ((k : ℕ) : ℝ) * (-(1 : ℝ) / 80) by
          push_cast
          ring]
    rw [Real.exp_add, Real.exp_nat_mul]
  rw [exponentialPower]
  unfold currentNeighborMajorant
  have coefficientNonnegative :
      0 ≤ 3 * ((ell + 1000 + k : ℕ) : ℝ) * Real.exp (-(25 : ℝ) / 2) := by
    positivity
  simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_left powFirst coefficientNonnegative)

/-- The exact infinite tail used for the current neighbor-charge estimate. -/
theorem current_neighbor_charge_series_lt (ell : ℕ) (hell : 1000 ≤ ell) :
    (∑' k : ℕ,
      3 * ((ell + 1000 + k : ℕ) : ℝ) *
        Real.exp (-((1000 + k : ℕ) : ℝ) / 80)) <
      (ell : ℝ) / 490 := by
  have summableMajorant := currentNeighborMajorant_summable ell
  have termNonnegative : ∀ k : ℕ,
      0 ≤ 3 * ((ell + 1000 + k : ℕ) : ℝ) *
        Real.exp (-((1000 + k : ℕ) : ℝ) / 80) := by
    intro k
    positivity
  have termComparison : ∀ k : ℕ,
      3 * ((ell + 1000 + k : ℕ) : ℝ) *
          Real.exp (-((1000 + k : ℕ) : ℝ) / 80) ≤
        currentNeighborMajorant ell k :=
    current_event_charge_le_majorant ell
  have summableTerms := Summable.of_nonneg_of_le
    termNonnegative termComparison summableMajorant
  calc
    (∑' k : ℕ,
      3 * ((ell + 1000 + k : ℕ) : ℝ) *
        Real.exp (-((1000 + k : ℕ) : ℝ) / 80)) ≤
        ∑' k : ℕ, currentNeighborMajorant ell k := by
      exact Summable.tsum_le_tsum termComparison summableTerms summableMajorant
    _ < (ell : ℝ) / 490 := currentNeighborMajorant_tsum_lt ell hell

theorem current_lll_margin :
    (1 : ℝ) / 80 + (1 : ℝ) / 245 < (9 : ℝ) / 500 := by
  norm_num

theorem current_equal_to_arbitrary_gap :
    ((1 : ℝ) / 1000) / (2 + (1 : ℝ) / 1000) = (1 : ℝ) / 2001 := by
  norm_num

theorem current_advertised_gap_strict :
    (1 : ℝ) / 2002 < (1 : ℝ) / 2001 := by
  norm_num

theorem current_headline_epsilon_lt_one :
    ((2001 : ℝ) / 2002) < 1 := by norm_num

theorem current_headline_gap_identity :
    1 - ((2001 : ℝ) / 2002) = (1 : ℝ) / 2002 := by norm_num

/-- Abstract closure of the current asymmetric-LLL calculation.  All
combinatorics enters through the event tail and the sum of neighboring
charges; the theorem below checks the remaining product inequality. -/
theorem current_lll_numeric_closure
    {ι : Type*} [DecidableEq ι] (neighbors : Finset ι) (charge : ι → ℝ)
    (ell : ℕ) (mass : ℝ)
    (ellPositive : 0 < ell)
    (massTail : mass < Real.exp (-(9 : ℝ) * ell / 500))
    (chargeNonnegative : ∀ i ∈ neighbors, 0 ≤ charge i)
    (chargeAtMostHalf : ∀ i ∈ neighbors, charge i ≤ (1 : ℝ) / 2)
    (neighborSum : (∑ i ∈ neighbors, charge i) < (ell : ℝ) / 490) :
    mass < Real.exp (-(ell : ℝ) / 80) *
      ∏ i ∈ neighbors, (1 - charge i) := by
  have productLower := exp_neg_two_sum_le_product
    neighbors charge chargeNonnegative chargeAtMostHalf
  have expNeighborStrict :
      Real.exp (-(ell : ℝ) / 245) <
        Real.exp (-2 * ∑ i ∈ neighbors, charge i) := by
    apply Real.exp_strictMono
    nlinarith
  have chargedProductStrict :
      Real.exp (-(ell : ℝ) * ((1 : ℝ) / 80 + (1 : ℝ) / 245)) <
        Real.exp (-(ell : ℝ) / 80) *
          ∏ i ∈ neighbors, (1 - charge i) := by
    calc
      Real.exp (-(ell : ℝ) * ((1 : ℝ) / 80 + (1 : ℝ) / 245)) =
          Real.exp (-(ell : ℝ) / 80) *
            Real.exp (-(ell : ℝ) / 245) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ < Real.exp (-(ell : ℝ) / 80) *
          Real.exp (-2 * ∑ i ∈ neighbors, charge i) := by
        exact mul_lt_mul_of_pos_left expNeighborStrict (Real.exp_pos _)
      _ ≤ Real.exp (-(ell : ℝ) / 80) *
          ∏ i ∈ neighbors, (1 - charge i) := by
        exact mul_le_mul_of_nonneg_left productLower (Real.exp_nonneg _)
  have tailToCharge :
      Real.exp (-(9 : ℝ) * ell / 500) <
        Real.exp (-(ell : ℝ) * ((1 : ℝ) / 80 + (1 : ℝ) / 245)) := by
    apply Real.exp_strictMono
    have hellPositive : (0 : ℝ) < ell := by exact_mod_cast ellPositive
    nlinarith [current_lll_margin]
  exact massTail.trans (tailToCharge.trans chargedProductStrict)

end TernarySyncAudit
