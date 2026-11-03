import Mathlib
import FormalAudit.AsymmetricLLL

namespace TernarySyncAudit

open Finset

/-- Exact uniform mass of a subset of a finite nonempty sample space. -/
noncomputable def uniformFinsetMass
    {Ω : Type*} [Fintype Ω] (A : Finset Ω) : ℝ :=
  A.card / Fintype.card Ω

/-- Outcomes avoiding every event indexed by `S`. -/
def avoidOutcomes
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (event : ι → Finset Ω) (S : Finset ι) : Finset Ω :=
  Finset.univ.filter fun outcome => ∀ e ∈ S, outcome ∉ event e

/-- Uniform mass of simultaneous avoidance. -/
noncomputable def finiteAvoidMass
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (event : ι → Finset Ω) (S : Finset ι) : ℝ :=
  uniformFinsetMass (avoidOutcomes event S)

/-- Mass of event `e` while all events in `S` are avoided. -/
noncomputable def finiteBadAvoidMass
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (event : ι → Finset Ω) (e : ι) (S : Finset ι) : ℝ :=
  uniformFinsetMass (event e ∩ avoidOutcomes event S)

/-- Unconditional event mass. -/
noncomputable def finiteEventMass
    {ι Ω : Type*} [Fintype Ω] (event : ι → Finset Ω) (e : ι) : ℝ :=
  uniformFinsetMass (event e)

theorem avoidOutcomes_empty
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (event : ι → Finset Ω) :
    avoidOutcomes event ∅ = Finset.univ := by
  classical
  ext outcome
  simp [avoidOutcomes]

theorem avoidOutcomes_insert
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (event : ι → Finset Ω) (e : ι) (S : Finset ι) :
    avoidOutcomes event (insert e S) = avoidOutcomes event S \ event e := by
  classical
  ext outcome
  simp [avoidOutcomes, and_comm]

theorem avoidOutcomes_antitone
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (event : ι → Finset Ω) {A B : Finset ι} (hAB : A ⊆ B) :
    avoidOutcomes event B ⊆ avoidOutcomes event A := by
  classical
  intro outcome hOutcome
  simp only [avoidOutcomes, Finset.mem_filter] at hOutcome ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  intro e heA
  exact hOutcome.2 e (hAB heA)

theorem uniformFinsetMass_nonnegative
    {Ω : Type*} [Fintype Ω] (A : Finset Ω) :
    0 ≤ uniformFinsetMass A := by
  unfold uniformFinsetMass
  positivity

theorem uniformFinsetMass_mono
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {A B : Finset Ω} (hAB : A ⊆ B) :
    uniformFinsetMass A ≤ uniformFinsetMass B := by
  unfold uniformFinsetMass
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Finset.card_le_card hAB)
    (by positivity)

theorem finiteAvoidMass_empty
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : ι → Finset Ω) :
    finiteAvoidMass event ∅ = 1 := by
  unfold finiteAvoidMass uniformFinsetMass
  rw [avoidOutcomes_empty]
  simp

theorem finiteAvoidMass_nonnegative
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (event : ι → Finset Ω) (S : Finset ι) :
    0 ≤ finiteAvoidMass event S :=
  uniformFinsetMass_nonnegative _

/-- Exact chain-rule decomposition before any conditional division. -/
theorem finiteAvoidMass_decomposition
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : ι → Finset Ω) (e : ι) (S : Finset ι) (_he : e ∉ S) :
    finiteAvoidMass event (insert e S) =
      finiteAvoidMass event S - finiteBadAvoidMass event e S := by
  classical
  have interSubset : event e ∩ avoidOutcomes event S ⊆ avoidOutcomes event S :=
    Finset.inter_subset_right
  have differenceIdentity :
      avoidOutcomes event S \ event e =
        avoidOutcomes event S \ (event e ∩ avoidOutcomes event S) := by
    ext outcome
    simp [and_comm]
  have cardIdentity :
      ((avoidOutcomes event S \ (event e ∩ avoidOutcomes event S)).card : ℝ) =
        (avoidOutcomes event S).card - (event e ∩ avoidOutcomes event S).card := by
    exact Finset.cast_card_sdiff interSubset
  unfold finiteAvoidMass finiteBadAvoidMass uniformFinsetMass
  rw [avoidOutcomes_insert, differenceIdentity, cardIdentity]
  ring

theorem finiteBadAvoidMass_antitone
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : ι → Finset Ω) (e : ι) {A B : Finset ι} (hAB : A ⊆ B) :
    finiteBadAvoidMass event e B ≤ finiteBadAvoidMass event e A := by
  apply uniformFinsetMass_mono
  intro outcome hOutcome
  refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hOutcome).1, ?_⟩
  exact avoidOutcomes_antitone event hAB (Finset.mem_inter.mp hOutcome).2

/-- Finite-space asymmetric LLL: only the genuine dependency equality and numerical
criterion remain as hypotheses.  All event algebra and the conditional induction are proved. -/
theorem finite_asymmetric_lll_product_bound
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (events : Finset ι) (event : ι → Finset Ω)
    (neighbors : ι → Finset ι) (charge : ι → ℝ)
    (chargeNonnegative : ∀ e, 0 ≤ charge e)
    (chargeAtMostOne : ∀ e, charge e ≤ 1)
    (dependency : ∀ e S, e ∉ S → Disjoint S (neighbors e) →
      finiteBadAvoidMass event e S =
        finiteEventMass event e * finiteAvoidMass event S)
    (criterion : ∀ e,
      finiteEventMass event e ≤
        charge e * ∏ f ∈ neighbors e, (1 - charge f)) :
    (∏ e ∈ events, (1 - charge e)) ≤ finiteAvoidMass event events := by
  apply asymmetric_lll_product_bound events neighbors
    (finiteAvoidMass event) (finiteBadAvoidMass event)
    (finiteEventMass event) charge
    (finiteAvoidMass_empty event) chargeNonnegative chargeAtMostOne
    (finiteAvoidMass_nonnegative event)
    (finiteAvoidMass_decomposition event)
  · intro e A B hAB
    exact finiteBadAvoidMass_antitone event e hAB
  · exact dependency
  · exact criterion

/-- Positive avoidance mass gives an actual outcome avoiding every bad event. -/
theorem finite_asymmetric_lll_exists
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (events : Finset ι) (event : ι → Finset Ω)
    (neighbors : ι → Finset ι) (charge : ι → ℝ)
    (chargeNonnegative : ∀ e, 0 ≤ charge e)
    (chargeStrict : ∀ e, charge e < 1)
    (dependency : ∀ e S, e ∉ S → Disjoint S (neighbors e) →
      finiteBadAvoidMass event e S =
        finiteEventMass event e * finiteAvoidMass event S)
    (criterion : ∀ e,
      finiteEventMass event e ≤
        charge e * ∏ f ∈ neighbors e, (1 - charge f)) :
    (avoidOutcomes event events).Nonempty := by
  have productPositive := complementary_charge_product_pos events charge
    (fun e he => chargeNonnegative e) (fun e he => chargeStrict e)
  have massLower := finite_asymmetric_lll_product_bound events event neighbors charge
    chargeNonnegative (fun e => (chargeStrict e).le) dependency criterion
  have massPositive : 0 < finiteAvoidMass event events := productPositive.trans_le massLower
  unfold finiteAvoidMass uniformFinsetMass at massPositive
  have cardPositive : 0 < (avoidOutcomes event events).card := by
    by_contra h
    have cardZero : (avoidOutcomes event events).card = 0 := by omega
    simp [cardZero] at massPositive
  exact Finset.card_pos.mp cardPositive

end TernarySyncAudit
