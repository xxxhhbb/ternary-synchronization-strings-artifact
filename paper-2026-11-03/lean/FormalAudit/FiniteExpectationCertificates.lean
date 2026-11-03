import Mathlib
import FormalAudit.VariableIndependence

namespace TernarySyncAudit

open Finset

/-- Expectation under the uniform distribution on a nonempty finite type. -/
noncomputable def uniformExpectation
    {Ω : Type*} [Fintype Ω] (value : Ω → ℝ) : ℝ :=
  (∑ outcome, value outcome) / Fintype.card Ω

/-- Double-counting identity for a finite family of certificate events. -/
theorem sum_certificate_incidence
    {Ω C : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq C]
    (certificates : Finset C) (event : C → Finset Ω) :
    (∑ outcome : Ω,
      ((certificates.filter fun certificate =>
        outcome ∈ event certificate).card : ℝ)) =
      ∑ certificate ∈ certificates, ((event certificate).card : ℝ) := by
  classical
  calc
    (∑ outcome : Ω,
        ((certificates.filter fun certificate =>
          outcome ∈ event certificate).card : ℝ)) =
        ∑ outcome : Ω, ∑ certificate ∈ certificates,
          if outcome ∈ event certificate then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro outcome outcomeIn
            simp
    _ = ∑ certificate ∈ certificates, ∑ outcome : Ω,
          if outcome ∈ event certificate then (1 : ℝ) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ certificate ∈ certificates, ((event certificate).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro certificate certificateIn
          simp

/-- Generic certificate method for expectations: if every outcome's count is
at most the number of compatible certificates, then its uniform expectation
is at most the sum of certificate-event probabilities. -/
theorem uniformExpectation_le_certificate_mass
    {Ω C : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    [DecidableEq C]
    (certificates : Finset C) (event : C → Finset Ω)
    (count : Ω → ℕ)
    (pointwise : ∀ outcome,
      count outcome ≤
        (certificates.filter fun certificate =>
          outcome ∈ event certificate).card) :
    uniformExpectation (fun outcome => (count outcome : ℝ)) ≤
      ∑ certificate ∈ certificates, uniformFinsetMass (event certificate) := by
  classical
  have summed :
      (∑ outcome : Ω, (count outcome : ℝ)) ≤
        ∑ outcome : Ω,
          ((certificates.filter fun certificate =>
            outcome ∈ event certificate).card : ℝ) := by
    exact Finset.sum_le_sum fun outcome outcomeIn => by
      exact_mod_cast pointwise outcome
  rw [sum_certificate_incidence certificates event] at summed
  unfold uniformExpectation uniformFinsetMass
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right summed (by positivity)

/-- Special case where each certificate event has a supplied mass upper
bound, matching the fixed-witness probability-product argument. -/
theorem uniformExpectation_le_certificate_weights
    {Ω C : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    [DecidableEq C]
    (certificates : Finset C) (event : C → Finset Ω)
    (count : Ω → ℕ) (weight : C → ℝ)
    (pointwise : ∀ outcome,
      count outcome ≤
        (certificates.filter fun certificate =>
          outcome ∈ event certificate).card)
    (eventMassBound : ∀ certificate ∈ certificates,
      uniformFinsetMass (event certificate) ≤ weight certificate) :
    uniformExpectation (fun outcome => (count outcome : ℝ)) ≤
      ∑ certificate ∈ certificates, weight certificate := by
  calc
    uniformExpectation (fun outcome => (count outcome : ℝ)) ≤
        ∑ certificate ∈ certificates,
          uniformFinsetMass (event certificate) :=
      uniformExpectation_le_certificate_mass certificates event count pointwise
    _ ≤ ∑ certificate ∈ certificates, weight certificate :=
      Finset.sum_le_sum eventMassBound

/-- Outcomes on which a natural-valued statistic reaches a threshold. -/
def uniformNatTailEvent
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (count : Ω → ℕ) (threshold : ℕ) : Finset Ω :=
  Finset.univ.filter fun outcome => threshold ≤ count outcome

/-- Exact finite Markov numerator inequality under the uniform distribution. -/
theorem uniformNatTailEvent_mul_threshold_le_expectation
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (count : Ω → ℕ) (threshold : ℕ) :
    uniformFinsetMass (uniformNatTailEvent count threshold) * threshold ≤
      uniformExpectation (fun outcome => (count outcome : ℝ)) := by
  classical
  have numeratorNat :
      threshold * (uniformNatTailEvent count threshold).card ≤
        ∑ outcome : Ω, count outcome := by
    calc
      threshold * (uniformNatTailEvent count threshold).card =
          ∑ outcome : Ω,
            if outcome ∈ uniformNatTailEvent count threshold
            then threshold else 0 := by
              simp [Nat.mul_comm]
      _ ≤ ∑ outcome : Ω, count outcome := by
        apply Finset.sum_le_sum
        intro outcome outcomeIn
        by_cases tail : outcome ∈ uniformNatTailEvent count threshold
        · simp only [tail, if_true]
          exact (Finset.mem_filter.mp tail).2
        · simp [tail]
  have numeratorReal :
      ((uniformNatTailEvent count threshold).card : ℝ) * threshold ≤
        ∑ outcome : Ω, (count outcome : ℝ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using numeratorNat)
  unfold uniformFinsetMass uniformExpectation
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right numeratorReal (by positivity)

/-- Finite uniform Markov tail bound, used to turn the MT expectation bound
into vanishing nontermination probability. -/
theorem uniformNatTailEvent_mass_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (count : Ω → ℕ) {threshold : ℕ} (thresholdPositive : 0 < threshold) :
    uniformFinsetMass (uniformNatTailEvent count threshold) ≤
      uniformExpectation (fun outcome => (count outcome : ℝ)) / threshold := by
  have numerator := uniformNatTailEvent_mul_threshold_le_expectation
    count threshold
  exact (le_div_iff₀ (by exact_mod_cast thresholdPositive)).2 (by
    simpa [mul_comm] using numerator)

end TernarySyncAudit
