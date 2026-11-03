import Mathlib
import FormalAudit.LocalLemmaProduct

namespace TernarySyncAudit

open Finset

/--
Finite asymmetric Lovasz Local Lemma, in the algebraic conditional-mass
interface used by Appendix D.  The proof contains the full strong induction:
nonneighbors are removed by the dependency hypothesis, while neighboring
avoidance conditions are reinserted one at a time using smaller conditioning
sets.
-/
theorem asymmetric_lll_conditional_bound
    {ι : Type*} [DecidableEq ι]
    (neighbors : ι → Finset ι)
    (mass : Finset ι → ℝ) (badMass : ι → Finset ι → ℝ)
    (probability charge : ι → ℝ)
    (chargeNonnegative : ∀ e, 0 ≤ charge e)
    (chargeAtMostOne : ∀ e, charge e ≤ 1)
    (massNonnegative : ∀ S, 0 ≤ mass S)
    (decomposition : ∀ e S, e ∉ S →
      mass (insert e S) = mass S - badMass e S)
    (badAntitone : ∀ e A B, A ⊆ B → badMass e B ≤ badMass e A)
    (dependency : ∀ e S, e ∉ S → Disjoint S (neighbors e) →
      badMass e S = probability e * mass S)
    (criterion : ∀ e,
      probability e ≤ charge e * ∏ f ∈ neighbors e, (1 - charge f)) :
    ∀ e S, e ∉ S → badMass e S ≤ charge e * mass S := by
  intro e S eNotS
  induction S using Finset.strongInduction generalizing e with
  | H S inductionHypothesis =>
    let nonneighbors := S \ neighbors e
    let localNeighbors := S ∩ neighbors e
    have nonneighborsSubset : nonneighbors ⊆ S := Finset.sdiff_subset
    have localNeighborsSubset : localNeighbors ⊆ S := Finset.inter_subset_left
    have partition : nonneighbors ∪ localNeighbors = S := by
      exact Finset.sdiff_union_inter S (neighbors e)
    have eNotNonneighbors : e ∉ nonneighbors := by
      exact fun he => eNotS (nonneighborsSubset he)
    have nonneighborsDisjoint : Disjoint nonneighbors (neighbors e) := by
      rw [Finset.disjoint_left]
      intro x hx hneighbor
      exact (Finset.mem_sdiff.mp hx).2 hneighbor
    have independentMass :
        badMass e nonneighbors = probability e * mass nonneighbors :=
      dependency e nonneighbors eNotNonneighbors nonneighborsDisjoint

    have relativeAvoidance :
        ∀ T : Finset ι, T ⊆ localNeighbors →
          mass nonneighbors * ∏ f ∈ T, (1 - charge f) ≤
            mass (nonneighbors ∪ T) := by
      intro T TSubset
      induction T using Finset.induction_on with
      | empty => simp
      | @insert f T fNotT TInduction =>
        have TSubsetLocal : T ⊆ localNeighbors := by
          exact fun x hx => TSubset (Finset.mem_insert_of_mem hx)
        have fLocal : f ∈ localNeighbors := TSubset (Finset.mem_insert_self _ _)
        have previousBound := TInduction TSubsetLocal
        let previous := nonneighbors ∪ T
        have fInS : f ∈ S := localNeighborsSubset fLocal
        have fInNeighborSet : f ∈ neighbors e := (Finset.mem_inter.mp fLocal).2
        have fNotNonneighbors : f ∉ nonneighbors := by
          simp [nonneighbors, fInNeighborSet]
        have fNotPrevious : f ∉ previous := by
          simp [previous, fNotNonneighbors, fNotT]
        have previousSubsetS : previous ⊆ S := by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact nonneighborsSubset hx
          · exact localNeighborsSubset (TSubsetLocal hx)
        have previousProper : previous ⊂ S := by
          rw [Finset.ssubset_iff_of_subset previousSubsetS]
          exact ⟨f, fInS, fNotPrevious⟩
        have smallerConditional :
            badMass f previous ≤ charge f * mass previous :=
          inductionHypothesis previous previousProper f fNotPrevious
        have oneStep :
            (1 - charge f) * mass previous ≤ mass (insert f previous) := by
          rw [decomposition f previous fNotPrevious]
          nlinarith
        have factorNonnegative : 0 ≤ 1 - charge f := by
          linarith [chargeAtMostOne f]
        have lifted :=
          mul_le_mul_of_nonneg_left previousBound factorNonnegative
        calc
          mass nonneighbors * ∏ x ∈ insert f T, (1 - charge x) =
              (1 - charge f) *
                (mass nonneighbors * ∏ x ∈ T, (1 - charge x)) := by
            rw [Finset.prod_insert fNotT]
            ring
          _ ≤ (1 - charge f) * mass previous := lifted
          _ ≤ mass (insert f previous) := oneStep
          _ = mass (nonneighbors ∪ insert f T) := by
            congr 1
            ext x
            simp [previous]

    have relativeFull :
        mass nonneighbors * ∏ f ∈ localNeighbors, (1 - charge f) ≤ mass S := by
      have h := relativeAvoidance localNeighbors Finset.Subset.rfl
      simpa [partition] using h

    have localSubsetNeighbors : localNeighbors ⊆ neighbors e :=
      Finset.inter_subset_right
    have fullProductLeLocal :
        (∏ f ∈ neighbors e, (1 - charge f)) ≤
          ∏ f ∈ localNeighbors, (1 - charge f) := by
      apply Finset.prod_le_prod_of_subset_of_le_one localSubsetNeighbors
      · intro f hf
        linarith [chargeAtMostOne f]
      · intro f hf fNotLocal
        linarith [chargeNonnegative f]
    have probabilityLocal :
        probability e ≤ charge e *
          ∏ f ∈ localNeighbors, (1 - charge f) := by
      exact (criterion e).trans
        (mul_le_mul_of_nonneg_left fullProductLeLocal (chargeNonnegative e))
    have probabilityTimesMass :
        probability e * mass nonneighbors ≤
          charge e *
            (mass nonneighbors *
              ∏ f ∈ localNeighbors, (1 - charge f)) := by
      have scaled := mul_le_mul_of_nonneg_right probabilityLocal
        (massNonnegative nonneighbors)
      nlinarith
    have badReduction : badMass e S ≤ badMass e nonneighbors :=
      badAntitone e nonneighbors S nonneighborsSubset
    calc
      badMass e S ≤ badMass e nonneighbors := badReduction
      _ = probability e * mass nonneighbors := independentMass
      _ ≤ charge e *
          (mass nonneighbors *
            ∏ f ∈ localNeighbors, (1 - charge f)) := probabilityTimesMass
      _ ≤ charge e * mass S :=
        mul_le_mul_of_nonneg_left relativeFull (chargeNonnegative e)

/-- Product-form conclusion of the asymmetric LLL, including positivity when every charge is
strictly below one. -/
theorem asymmetric_lll_product_bound
    {ι : Type*} [DecidableEq ι]
    (events : Finset ι) (neighbors : ι → Finset ι)
    (mass : Finset ι → ℝ) (badMass : ι → Finset ι → ℝ)
    (probability charge : ι → ℝ)
    (emptyMass : mass ∅ = 1)
    (chargeNonnegative : ∀ e, 0 ≤ charge e)
    (chargeAtMostOne : ∀ e, charge e ≤ 1)
    (massNonnegative : ∀ S, 0 ≤ mass S)
    (decomposition : ∀ e S, e ∉ S →
      mass (insert e S) = mass S - badMass e S)
    (badAntitone : ∀ e A B, A ⊆ B → badMass e B ≤ badMass e A)
    (dependency : ∀ e S, e ∉ S → Disjoint S (neighbors e) →
      badMass e S = probability e * mass S)
    (criterion : ∀ e,
      probability e ≤ charge e * ∏ f ∈ neighbors e, (1 - charge f)) :
    (∏ e ∈ events, (1 - charge e)) ≤ mass events := by
  apply conditional_bounds_imply_product mass badMass charge emptyMass chargeAtMostOne
    decomposition
  intro e S eNotS
  exact asymmetric_lll_conditional_bound neighbors mass badMass probability charge
    chargeNonnegative chargeAtMostOne massNonnegative decomposition badAntitone
    dependency criterion e S eNotS

/-- Positive product of complementary charges. -/
theorem complementary_charge_product_pos
    {ι : Type*} [DecidableEq ι] (events : Finset ι) (charge : ι → ℝ)
    (_chargeNonnegative : ∀ e ∈ events, 0 ≤ charge e)
    (chargeStrict : ∀ e ∈ events, charge e < 1) :
    0 < ∏ e ∈ events, (1 - charge e) := by
  exact Finset.prod_pos fun e he => sub_pos.mpr (chargeStrict e he)

end TernarySyncAudit
