import Mathlib
import FormalAudit.SynchronizationHeadline

namespace TernarySyncAudit

/-- A finite ternary word is synchronizing if an extension of its positions
to a stream satisfies the condition up to its length.  This existential
formulation is sufficient for counting the concrete generated prefixes. -/
def IsFiniteEpsilonSynchronizationWord
    {n : ℕ} (word : FixedWord Symbol n) (epsilon : ℝ) : Prop :=
  ∃ stream : ℕ → Symbol,
    (∀ position : Fin n, stream position.val = word position) ∧
      IsEpsilonSynchronizationString stream n epsilon

/-- The finite set of all ternary length-`n` words satisfying the conventional
epsilon-synchronization condition. -/
noncomputable def finiteSynchronizationWords
    (n : ℕ) (epsilon : ℝ) : Finset (FixedWord Symbol n) := by
  classical
  exact Finset.univ.filter fun word =>
    IsFiniteEpsilonSynchronizationWord word epsilon

theorem good_prefixes_are_synchronizing
    {n : ℕ} (outer : ℕ → Symbol) (outerSquareFree : OuterSquareFree outer) :
    (avoidOutcomes
        (longIntervalEvent (macroblockCount n) outer)
        (Finset.univ : Finset (LongIntervalIndex (macroblockCount n)))).image
      (finiteEncodedPrefix (N := macroblockCount n) (n := n) outer) ⊆
      finiteSynchronizationWords n ((5999 : ℝ) / 6000) := by
  classical
  intro outputWord outputIn
  rcases Finset.mem_image.mp outputIn with ⟨branch, branchGood, rfl⟩
  have avoids : ∀ event : LongIntervalIndex (macroblockCount n),
      branch ∉ longIntervalEvent (macroblockCount n) outer event := by
    have avoidsEvery : ∀ event ∈
        (Finset.univ : Finset (LongIntervalIndex (macroblockCount n))),
        branch ∉ longIntervalEvent (macroblockCount n) outer event := by
      simpa only [avoidOutcomes, Finset.mem_filter, Finset.mem_univ,
        true_and] using branchGood
    intro event
    exact avoidsEvery event (Finset.mem_univ event)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  refine ⟨codeStream outer (extendFiniteChoices branch), ?_, ?_⟩
  · intro position
    rfl
  · apply synchronization_gap_mono (prefix_fits_macroblocks n)
    exact epsilon_synchronizing_of_avoids
      outer branch outerSquareFree avoids

/-- Fully concrete abundance of actual synchronization strings, rather than
only of good occurrence-choice vectors. -/
theorem concrete_synchronization_string_abundance
    {n : ℕ} (hn : 756 ≤ n)
    (outer : ℕ → Symbol) (outerSquareFree : OuterSquareFree outer) :
    Real.exp ((n : ℝ) / 28) ≤
      (finiteSynchronizationWords n ((5999 : ℝ) / 6000)).card := by
  have cardBound := Finset.card_le_card
    (good_prefixes_are_synchronizing (n := n) outer outerSquareFree)
  have cardBoundReal :
      (((avoidOutcomes
          (longIntervalEvent (macroblockCount n) outer)
          (Finset.univ : Finset (LongIntervalIndex (macroblockCount n)))).image
        (finiteEncodedPrefix (N := macroblockCount n) (n := n) outer)).card : ℝ) ≤
        (finiteSynchronizationWords n ((5999 : ℝ) / 6000)).card := by
    exact_mod_cast cardBound
  exact (concrete_prefix_abundance hn outer).trans cardBoundReal

end TernarySyncAudit
