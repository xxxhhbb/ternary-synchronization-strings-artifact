import Mathlib

namespace TernarySyncAudit

open Finset

/-- Length-`n` words over `α`, represented with explicit finite positions. -/
abbrev FixedWord (α : Type*) (n : ℕ) := Fin n → α

/-- The `d`-subsets of the positions of a length-`n` word. -/
def deletionPatterns (n d : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powersetCard d

theorem card_deletionPatterns (n d : ℕ) :
    (deletionPatterns n d).card = n.choose d := by
  simp [deletionPatterns, Finset.card_powersetCard]

private theorem deleted_card_of_mem
    {n d : ℕ} {s : Finset (Fin n)} (hs : s ∈ deletionPatterns n d) :
    s.card = d := by
  simpa [deletionPatterns] using (Finset.mem_powersetCard.mp hs).2

theorem kept_card
    {n d : ℕ} (_h : d ≤ n) {s : Finset (Fin n)}
    (hs : s ∈ deletionPatterns n d) :
    sᶜ.card = n - d := by
  rw [Finset.card_compl, deleted_card_of_mem hs]
  simp

/--
Two words agree after deleting the positions in `dx` from the first word and
the positions in `dy` from the second.  The remaining positions are compared
in their original order.
-/
def AgreesAfterDeleting
    {α : Type*} {n d : ℕ} (h : d ≤ n)
    (x y : FixedWord α n) (dx dy : Finset (Fin n))
    (hx : dx ∈ deletionPatterns n d) (hy : dy ∈ deletionPatterns n d) : Prop :=
  ∀ k : Fin (n - d),
    x (dxᶜ.orderEmbOfFin (kept_card h hx) k) =
      y (dyᶜ.orderEmbOfFin (kept_card h hy) k)

/-- There is a common subsequence of length `n - d`, witnessed by deletions. -/
def HasCommonSubsequenceAfterDeleting
    {α : Type*} {n d : ℕ} (h : d ≤ n)
    (x y : FixedWord α n) : Prop :=
  ∃ dx, ∃ hx : dx ∈ deletionPatterns n d,
    ∃ dy, ∃ hy : dy ∈ deletionPatterns n d,
      AgreesAfterDeleting h x y dx dy hx hy

/-- All first words realizing one fixed pair of deletion patterns. -/
noncomputable def deletionFiber
    {α : Type*} [Fintype α] [DecidableEq α]
    {n d : ℕ} (h : d ≤ n) (y : FixedWord α n)
    (dx dy : Finset (Fin n))
    (hx : dx ∈ deletionPatterns n d) (hy : dy ∈ deletionPatterns n d) :
    Finset (FixedWord α n) := by
  classical
  exact Finset.univ.filter fun x => AgreesAfterDeleting h x y dx dy hx hy

private theorem deletionFiber_card_le
    {α : Type*} [Fintype α] [DecidableEq α]
    {n d : ℕ} (h : d ≤ n) (y : FixedWord α n)
    (dx dy : Finset (Fin n))
    (hx : dx ∈ deletionPatterns n d) (hy : dy ∈ deletionPatterns n d) :
    (deletionFiber h y dx dy hx hy).card ≤ (Fintype.card α) ^ d := by
  classical
  let restrictDeleted :
      ↥(deletionFiber h y dx dy hx hy) → ↥dx → α :=
    fun x i => x.1 i.1
  have restrictDeleted_injective : Function.Injective restrictDeleted := by
    intro x x' sameRestriction
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ dx
    · have atDeleted := congrFun sameRestriction (⟨i, hi⟩ : dx)
      exact atDeleted
    · have hiComplement : i ∈ dxᶜ := by simp [hi]
      have hiRange : i ∈ Set.range (dxᶜ.orderEmbOfFin (kept_card h hx)) := by
        rw [Finset.range_orderEmbOfFin]
        exact hiComplement
      obtain ⟨k, hk⟩ := hiRange
      have xMatches : AgreesAfterDeleting h x.1 y dx dy hx hy := by
        exact (Finset.mem_filter.mp x.2).2
      have x'Matches : AgreesAfterDeleting h x'.1 y dx dy hx hy := by
        exact (Finset.mem_filter.mp x'.2).2
      rw [← hk, xMatches k, x'Matches k]
  calc
    (deletionFiber h y dx dy hx hy).card =
        Fintype.card ↥(deletionFiber h y dx dy hx hy) := by
          symm
          exact Fintype.card_coe _
    _ ≤ Fintype.card (↥dx → α) :=
      Fintype.card_le_of_injective restrictDeleted restrictDeleted_injective
    _ = (Fintype.card α) ^ d := by
      rw [Fintype.card_fun, Fintype.card_coe, deleted_card_of_mem hx]

/--
The exact deletion ball at distance `d`: the union over the two sets of `d`
deleted positions of all compatible first words.
-/
noncomputable def exactDeletionBall
    {α : Type*} [Fintype α] [DecidableEq α]
    {n d : ℕ} (h : d ≤ n) (y : FixedWord α n) : Finset (FixedWord α n) :=
  (deletionPatterns n d).attach.biUnion fun dx =>
    (deletionPatterns n d).attach.biUnion fun dy =>
      deletionFiber h y dx.1 dy.1 dx.2 dy.2

theorem mem_exactDeletionBall_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    {n d : ℕ} (h : d ≤ n) (x y : FixedWord α n) :
    x ∈ exactDeletionBall h y ↔ HasCommonSubsequenceAfterDeleting h x y := by
  classical
  simp only [exactDeletionBall, Finset.mem_biUnion, deletionFiber,
    Finset.mem_filter, Finset.mem_univ, true_and,
    HasCommonSubsequenceAfterDeleting]
  constructor
  · rintro ⟨dx, hdxAttach, dy, hdyAttach, hmatch⟩
    exact ⟨dx.1, dx.2, dy.1, dy.2, hmatch⟩
  · rintro ⟨dx, hdx, dy, hdy, hmatch⟩
    exact ⟨⟨dx, hdx⟩, Finset.mem_attach _ _,
      ⟨dy, hdy⟩, Finset.mem_attach _ _, hmatch⟩

/-- Deleting zero symbols witnesses a common subsequence exactly when the two
equal-length words are equal. -/
theorem commonSubsequenceAfterDeleting_zero_iff
    {alpha : Type*} {n : ℕ} (x y : FixedWord alpha n) :
    HasCommonSubsequenceAfterDeleting (Nat.zero_le n) x y ↔ x = y := by
  constructor
  · rintro ⟨dx, hdx, dy, hdy, agrees⟩
    have dxCard : dx.card = 0 := by
      simpa [deletionPatterns] using (Finset.mem_powersetCard.mp hdx).2
    have dyCard : dy.card = 0 := by
      simpa [deletionPatterns] using (Finset.mem_powersetCard.mp hdy).2
    have dxEmpty : dx = ∅ := Finset.card_eq_zero.mp dxCard
    have dyEmpty : dy = ∅ := Finset.card_eq_zero.mp dyCard
    subst dx
    subst dy
    funext position
    have positionRange :
        position ∈ Set.range
          ((∅ : Finset (Fin n))ᶜ.orderEmbOfFin
            (kept_card (Nat.zero_le n) hdx)) := by
      rw [Finset.range_orderEmbOfFin]
      simp
    rcases positionRange with ⟨k, leftIndex⟩
    have embeddingEquality :
        ((∅ : Finset (Fin n))ᶜ.orderEmbOfFin
            (kept_card (Nat.zero_le n) hdx)) =
          ((∅ : Finset (Fin n))ᶜ.orderEmbOfFin
            (kept_card (Nat.zero_le n) hdy)) := by
      congr
    have rightIndex :
        ((∅ : Finset (Fin n))ᶜ.orderEmbOfFin
          (kept_card (Nat.zero_le n) hdy)) k = position := by
      rw [← embeddingEquality]
      exact leftIndex
    simpa only [leftIndex, rightIndex] using agrees k
  · intro equality
    subst y
    refine ⟨∅, ?_, ∅, ?_, ?_⟩
    · simp [deletionPatterns]
    · simp [deletionPatterns]
    · intro position
      rfl

/-- The exact high-LCS deletion-ball count used in the paper. -/
theorem exactDeletionBall_card_le
    {α : Type*} [Fintype α] [DecidableEq α]
    {n d : ℕ} (h : d ≤ n) (y : FixedWord α n) :
    (exactDeletionBall h y).card ≤
      (n.choose d) ^ 2 * (Fintype.card α) ^ d := by
  classical
  unfold exactDeletionBall
  calc
    ((deletionPatterns n d).attach.biUnion fun dx =>
        (deletionPatterns n d).attach.biUnion fun dy =>
          deletionFiber h y dx.1 dy.1 dx.2 dy.2).card
        ≤ ∑ dx ∈ (deletionPatterns n d).attach,
            ((deletionPatterns n d).attach.biUnion fun dy =>
              deletionFiber h y dx.1 dy.1 dx.2 dy.2).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _dx ∈ (deletionPatterns n d).attach,
          ∑ _dy ∈ (deletionPatterns n d).attach,
            (Fintype.card α) ^ d := by
      gcongr with dx hdx
      exact (Finset.card_biUnion_le.trans <|
        Finset.sum_le_sum fun dy _ =>
          deletionFiber_card_le h y dx.1 dy.1 dx.2 dy.2)
    _ = (n.choose d) ^ 2 * (Fintype.card α) ^ d := by
      simp [card_deletionPatterns, pow_two, Nat.mul_assoc]

/-- Union of exact deletion balls over a finite set of permitted deletions. -/
noncomputable def deletionBall
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (y : FixedWord α n) (allowed : Finset ℕ) :
    Finset (FixedWord α n) :=
  allowed.biUnion fun d => if h : d ≤ n then exactDeletionBall h y else ∅

/-- Semantic membership in a union of deletion balls. -/
theorem mem_deletionBall_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (x y : FixedWord α n) (allowed : Finset ℕ) :
    x ∈ deletionBall y allowed ↔
      ∃ d ∈ allowed, ∃ h : d ≤ n,
        HasCommonSubsequenceAfterDeleting h x y := by
  classical
  constructor
  · intro hx
    rw [deletionBall, Finset.mem_biUnion] at hx
    rcases hx with ⟨d, hd, hx⟩
    by_cases h : d ≤ n
    · refine ⟨d, hd, h, ?_⟩
      simpa [h, mem_exactDeletionBall_iff] using hx
    · simp [h] at hx
  · rintro ⟨d, hd, h, common⟩
    rw [deletionBall, Finset.mem_biUnion]
    refine ⟨d, hd, ?_⟩
    simpa [h, mem_exactDeletionBall_iff] using common

/-- Summing the exact bound gives the paper's deletion-ball cover. -/
theorem deletionBall_card_le
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (y : FixedWord α n) (allowed : Finset ℕ) :
    (deletionBall y allowed).card ≤
      ∑ d ∈ allowed, (n.choose d) ^ 2 * (Fintype.card α) ^ d := by
  classical
  unfold deletionBall
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro d hd
  split_ifs with h
  · exact exactDeletionBall_card_le h y
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]

end TernarySyncAudit
