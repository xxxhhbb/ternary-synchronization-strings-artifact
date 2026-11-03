import Mathlib
import FormalAudit.VariableIndependence

namespace TernarySyncAudit

open Finset

/-- Uncurrying is an embedding: a family of local assignments determines one
assignment on the sigma type of all local cells. -/
def sigmaUncurryEmbedding
    {I A : Type*} {L : I → Type*} :
    (∀ i, L i → A) ↪ ((Σ i, L i) → A) where
  toFun := Sigma.uncurry
  inj' := by
    intro left right equality
    funext i coordinate
    exact congrFun equality ⟨i, coordinate⟩

/-- The finite set of assignments on pairwise tagged local cell sets for
which every node receives one of its allowed local patterns. -/
def independentPatterns
    {I A : Type*} {L : I → Type*}
    [Fintype I] [DecidableEq I]
    [∀ i, Fintype (L i)] [∀ i, DecidableEq (L i)]
    [Fintype A] [DecidableEq A]
    (allowed : ∀ i, Finset (L i → A)) :
    Finset ((Σ i, L i) → A) :=
  (Fintype.piFinset allowed).map sigmaUncurryEmbedding

theorem mem_independentPatterns_iff
    {I A : Type*} {L : I → Type*}
    [Fintype I] [DecidableEq I]
    [∀ i, Fintype (L i)] [∀ i, DecidableEq (L i)]
    [Fintype A] [DecidableEq A]
    (allowed : ∀ i, Finset (L i → A))
    (assignment : (Σ i, L i) → A) :
    assignment ∈ independentPatterns allowed ↔
      ∀ i, (fun coordinate => assignment ⟨i, coordinate⟩) ∈ allowed i := by
  classical
  constructor
  · intro member
    rw [independentPatterns, Finset.mem_map] at member
    rcases member with ⟨family, familyMember, rfl⟩
    exact Fintype.mem_piFinset.mp familyMember
  · intro localMember
    rw [independentPatterns, Finset.mem_map]
    refine ⟨Sigma.curry assignment, ?_, ?_⟩
    · exact Fintype.mem_piFinset.mpr localMember
    · ext coordinate
      rcases coordinate with ⟨i, coordinate⟩
      rfl

/-- Exact factorization of the number of compatible assignments across
pairwise tagged local cell sets. -/
@[simp] theorem card_independentPatterns
    {I A : Type*} {L : I → Type*}
    [Fintype I] [DecidableEq I]
    [∀ i, Fintype (L i)] [∀ i, DecidableEq (L i)]
    [Fintype A] [DecidableEq A]
    (allowed : ∀ i, Finset (L i → A)) :
    #(independentPatterns allowed) = ∏ i, #(allowed i) := by
  simp [independentPatterns]

private theorem card_sigma_power
    {I A : Type*} {L : I → Type*}
  [Fintype I] [Fintype A] [∀ i, Fintype (L i)] :
    (Fintype.card A : ℝ) ^ Fintype.card (Σ i, L i) =
      ∏ i, (Fintype.card A : ℝ) ^ Fintype.card (L i) := by
  rw [Fintype.card_sigma]
  simpa using (Finset.prod_pow_eq_pow_sum
    (Finset.univ : Finset I) (fun i => Fintype.card (L i))
      (Fintype.card A : ℝ)).symm

/-- Under a uniform product table, constraints on pairwise tagged local cell
sets have probability exactly equal to the product of their local masses. -/
theorem uniformFinsetMass_independentPatterns
    {I A : Type*} {L : I → Type*}
    [Fintype I] [DecidableEq I]
    [∀ i, Fintype (L i)] [∀ i, DecidableEq (L i)]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (allowed : ∀ i, Finset (L i → A)) :
    uniformFinsetMass (independentPatterns allowed) =
      ∏ i, uniformFinsetMass (allowed i) := by
  classical
  unfold uniformFinsetMass
  rw [card_independentPatterns]
  simp only [Fintype.card_fun]
  push_cast
  rw [card_sigma_power]
  rw [Finset.prod_div_distrib]

end TernarySyncAudit
