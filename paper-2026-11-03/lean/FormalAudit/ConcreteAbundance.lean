import Mathlib
import FormalAudit.ConcreteLLLExistence
import FormalAudit.Abundance

namespace TernarySyncAudit

open Finset

/-- For one fixed length there are at most `18*N` admissible starts. -/
theorem long_interval_length_fiber_card_le
    (N r : ℕ) :
    ((Finset.univ : Finset (LongIntervalIndex N)).filter
      fun event => event.length = r).card ≤ 18 * N := by
  classical
  let fiber := (Finset.univ : Finset (LongIntervalIndex N)).filter
    fun event => event.length = r
  let startCoordinate : LongIntervalIndex N → ℕ := fun event => event.start
  let target := Finset.range (18 * N)
  have cardBound : fiber.card ≤ target.card := by
    apply Finset.card_le_card_of_injOn startCoordinate
    · intro event eventIn
      change event.start ∈ Finset.range (18 * N)
      apply Finset.mem_range.mpr
      have fits := event.fits
      have positive := event.long
      omega
    · intro left leftIn right rightIn startEq
      have leftLength : left.length = r := (Finset.mem_filter.mp leftIn).2
      have rightLength : right.length = r := (Finset.mem_filter.mp rightIn).2
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        exact startEq
      · apply Fin.ext
        exact leftLength.trans rightLength.symm
  simpa [fiber, target] using cardBound

private noncomputable def unitChargeRatio : ℝ := Real.exp (-(1 : ℝ) / 100)

private theorem unitChargeRatio_norm_lt_one : ‖unitChargeRatio‖ < 1 := by
  rw [Real.norm_eq_abs]
  unfold unitChargeRatio
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_lt_one_iff.mpr (by norm_num)

private theorem shifted_charge_summable (base : ℕ) :
    Summable (fun k : ℕ => Real.exp (-((base + k : ℕ) : ℝ) / 100)) := by
  have geom : Summable (fun k : ℕ => unitChargeRatio ^ k) :=
    summable_geometric_of_norm_lt_one unitChargeRatio_norm_lt_one
  have scaled := geom.mul_left (Real.exp (-(base : ℝ) / 100))
  refine scaled.congr ?_
  intro k
  rw [show -((base + k : ℕ) : ℝ) / 100 =
      -(base : ℝ) / 100 + (k : ℝ) * (-(1 : ℝ) / 100) by
        push_cast
        ring]
  rw [Real.exp_add, Real.exp_nat_mul]
  rfl

/-- The tail beginning at length 2001 is bounded by the already certified
tail beginning at 2000. -/
theorem shifted_explicit_charge_tail_le :
    (∑' k : ℕ, Real.exp (-((2001 + k : ℕ) : ℝ) / 100)) ≤
      101 * Real.exp (-20) := by
  have shifted := shifted_charge_summable 2001
  have base := shifted_charge_summable 2000
  have pointwise : ∀ k : ℕ,
      Real.exp (-((2001 + k : ℕ) : ℝ) / 100) ≤
        Real.exp (-((2000 + k : ℕ) : ℝ) / 100) := by
    intro k
    apply Real.exp_monotone
    push_cast
    linarith
  exact (shifted.tsum_le_tsum pointwise base).trans explicit_charge_tail_lt.le

/-- Total charge of all long interval events is linear in the encoded length. -/
theorem total_long_interval_charge_le (N : ℕ) :
    (∑ event : LongIntervalIndex N, longIntervalCharge event) ≤
      101 * Real.exp (-20) * (18 * N) := by
  classical
  let events := (Finset.univ : Finset (LongIntervalIndex N))
  let lengthOffset : LongIntervalIndex N → ℕ := fun event => event.length - 2001
  have mapsTo : (events : Set (LongIntervalIndex N)).MapsTo lengthOffset
      (Finset.range (18 * N + 1)) := by
    intro event eventIn
    change lengthOffset event ∈ Finset.range (18 * N + 1)
    apply Finset.mem_range.mpr
    have bound : event.length < 18 * N + 1 := event.val.2.isLt
    dsimp [lengthOffset]
    omega
  have fiberwise :
      (∑ event ∈ events, longIntervalCharge event) =
        ∑ k ∈ Finset.range (18 * N + 1),
          ∑ event ∈ events with lengthOffset event = k,
            longIntervalCharge event := by
    symm
    exact Finset.sum_fiberwise_of_maps_to mapsTo longIntervalCharge
  rw [fiberwise]
  have eachFiber (k : ℕ) :
      (∑ event ∈ events with lengthOffset event = k,
          longIntervalCharge event) ≤
        (18 * N : ℕ) * Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by
    let fiber := events.filter fun event => lengthOffset event = k
    have fiberEquality :
        fiber = events.filter fun event => event.length = 2001 + k := by
      ext event
      simp only [fiber, Finset.mem_filter]
      constructor
      · rintro ⟨eventIn, offsetEq⟩
        refine ⟨eventIn, ?_⟩
        have long := event.long
        dsimp [lengthOffset] at offsetEq
        omega
      · rintro ⟨eventIn, lengthEq⟩
        refine ⟨eventIn, ?_⟩
        dsimp [lengthOffset]
        omega
    have lengthIdentity : ∀ event ∈ fiber, event.length = 2001 + k := by
      intro event eventIn
      rw [fiberEquality] at eventIn
      exact (Finset.mem_filter.mp eventIn).2
    have sumIdentity :
        (∑ event ∈ events with lengthOffset event = k,
            longIntervalCharge event) =
          (fiber.card : ℝ) *
            Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by
      change (∑ event ∈ fiber, longIntervalCharge event) = _
      calc
        (∑ event ∈ fiber, longIntervalCharge event) =
            ∑ _event ∈ fiber,
              Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by
          apply Finset.sum_congr rfl
          intro event eventIn
          unfold longIntervalCharge
          rw [lengthIdentity event eventIn]
        _ = (fiber.card : ℝ) *
              Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by simp
    rw [sumIdentity]
    have cardNat : fiber.card ≤ 18 * N := by
      rw [fiberEquality]
      change
        ((Finset.univ : Finset (LongIntervalIndex N)).filter
          fun event => event.length = 2001 + k).card ≤ 18 * N
      exact long_interval_length_fiber_card_le N (2001 + k)
    have cardReal : (fiber.card : ℝ) ≤ (18 * N : ℕ) := by
      exact (Nat.cast_le).2 cardNat
    exact mul_le_mul_of_nonneg_right cardReal (Real.exp_nonneg _)
  calc
    (∑ k ∈ Finset.range (18 * N + 1),
        ∑ event ∈ events with lengthOffset event = k,
          longIntervalCharge event) ≤
        ∑ k ∈ Finset.range (18 * N + 1),
          (18 * N : ℕ) *
            Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by
      exact Finset.sum_le_sum fun k _ => eachFiber k
    _ = (18 * N : ℕ) *
        ∑ k ∈ Finset.range (18 * N + 1),
          Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by
      rw [Finset.mul_sum]
    _ ≤ (18 * N : ℕ) *
        ∑' k : ℕ, Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by
      apply mul_le_mul_of_nonneg_left
      · exact (shifted_charge_summable 2001).sum_le_tsum _
          (fun k _ => Real.exp_nonneg _)
      · positivity
    _ ≤ (18 * N : ℕ) * (101 * Real.exp (-20)) := by
      exact mul_le_mul_of_nonneg_left shifted_explicit_charge_tail_le (by positivity)
    _ = 101 * Real.exp (-20) * (18 * N) := by
      push_cast
      ring

/-- Concrete LLL survival probability, with the full event family and charge
sum instantiated. -/
theorem concrete_good_choice_mass_lower (N : ℕ) (outer : ℕ → Symbol) :
    Real.exp (-202 * Real.exp (-20) * (18 * N)) ≤
      finiteAvoidMass (longIntervalEvent N outer)
        (Finset.univ : Finset (LongIntervalIndex N)) := by
  have productBound := finite_asymmetric_lll_product_bound
    (Finset.univ : Finset (LongIntervalIndex N))
    (longIntervalEvent N outer) (longIntervalNeighbors N) longIntervalCharge
    (fun event => longIntervalCharge_nonnegative event)
    (fun event => (longIntervalCharge_lt_half event).le.trans (by norm_num))
    (fun event S eventNotIn nonneighbors =>
      concrete_long_interval_dependency N outer event S eventNotIn nonneighbors)
    (concrete_long_interval_lll_criterion N outer)
  have productLower := exp_neg_two_sum_le_product
    (Finset.univ : Finset (LongIntervalIndex N)) longIntervalCharge
    (fun event _ => longIntervalCharge_nonnegative event)
    (fun event _ => (longIntervalCharge_lt_half event).le)
  have exponentLower :
      Real.exp (-202 * Real.exp (-20) * (18 * N)) ≤
        Real.exp (-2 * ∑ event : LongIntervalIndex N,
          longIntervalCharge event) := by
    apply Real.exp_monotone
    have total := total_long_interval_charge_le N
    nlinarith
  exact exponentLower.trans (productLower.trans productBound)

/-- Concrete exponential abundance of good binary occurrence-choice vectors. -/
theorem concrete_good_choice_abundance (N : ℕ) (outer : ℕ → Symbol) :
    Real.exp ((Real.log 2 / 18 - 202 * Real.exp (-20)) * (18 * N)) ≤
      (avoidOutcomes (longIntervalEvent N outer)
        (Finset.univ : Finset (LongIntervalIndex N))).card := by
  let good := avoidOutcomes (longIntervalEvent N outer)
    (Finset.univ : Finset (LongIntervalIndex N))
  have massLower := concrete_good_choice_mass_lower N outer
  have countLower := uniform_survival_probability_to_count
    (good := good.card) (total := Fintype.card (Fin N → Choice))
    (lower := Real.exp (-202 * Real.exp (-20) * (18 * N)))
    Fintype.card_pos massLower
  have sampleCard : (Fintype.card (Fin N → Choice) : ℝ) =
      Real.exp (Real.log 2 / 18 * (18 * N)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rw [show Real.log 2 / 18 * (18 * (N : ℝ)) = (N : ℝ) * Real.log 2 by ring]
    rw [Real.exp_nat_mul]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have exponentialProduct :
      Real.exp (-202 * Real.exp (-20) * (18 * N)) *
          Real.exp (Real.log 2 / 18 * (18 * N)) =
        Real.exp ((Real.log 2 / 18 - 202 * Real.exp (-20)) * (18 * N)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change Real.exp ((Real.log 2 / 18 - 202 * Real.exp (-20)) * (18 * N)) ≤
    good.card
  rw [← exponentialProduct, ← sampleCard]
  exact countLower

end TernarySyncAudit
