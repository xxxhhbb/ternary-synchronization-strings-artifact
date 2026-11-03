import Mathlib
import Mathlib.Data.List.NodupEquivFin
import FormalAudit.EqualBlockHeadline

namespace TernarySyncAudit

/-- List representation of a fixed-length word. -/
def fixedWordList {alpha : Type*} {n : ℕ} (word : FixedWord alpha n) : List alpha :=
  List.ofFn word

@[simp] theorem fixedWordList_length
    {alpha : Type*} {n : ℕ} (word : FixedWord alpha n) :
    (fixedWordList word).length = n := by
  simp [fixedWordList]

/-- Position-embedding characterization specialized to a fixed word. -/
theorem sublist_fixedWordList_iff
    {alpha : Type*} {n : ℕ} (subsequence : List alpha)
    (word : FixedWord alpha n) :
    List.Sublist subsequence (fixedWordList word) ↔
      ∃ embedding : Fin subsequence.length ↪o Fin (fixedWordList word).length,
        ∀ position : Fin subsequence.length,
          subsequence.get position = (fixedWordList word).get (embedding position) := by
  exact List.sublist_iff_exists_fin_orderEmbedding_get_eq

/-- A common-subsequence witness in the standard list formulation. -/
def IsCommonSubsequence
    {alpha : Type*} (subsequence left right : List alpha) : Prop :=
  List.Sublist subsequence left ∧ List.Sublist subsequence right

/-- Exact semantic bridge from the deletion-pattern model used in the event
count to the standard common-subsequence definition. -/
theorem commonSubsequenceAfterDeleting_iff_list
    {alpha : Type*} {n d : ℕ} (hd : d ≤ n)
    (left right : FixedWord alpha n) :
    HasCommonSubsequenceAfterDeleting hd left right ↔
      ∃ subsequence : List alpha,
        subsequence.length = n - d ∧
          IsCommonSubsequence subsequence
            (fixedWordList left) (fixedWordList right) := by
  constructor
  · rintro ⟨deletedLeft, deletedLeftPattern,
      deletedRight, deletedRightPattern, agrees⟩
    let leftEmbedding : Fin (n - d) ↪o Fin n := deletedLeftᶜ.orderEmbOfFin
      (kept_card hd deletedLeftPattern)
    let rightEmbedding : Fin (n - d) ↪o Fin n := deletedRightᶜ.orderEmbOfFin
      (kept_card hd deletedRightPattern)
    let subsequence : List alpha := List.ofFn fun position =>
      left (leftEmbedding position)
    have subsequenceLength : subsequence.length = n - d := by simp [subsequence]
    let domainCast : Fin subsequence.length ≃o Fin (n - d) :=
      Fin.castOrderIso subsequenceLength
    let leftCodomainCast : Fin n ≃o Fin (fixedWordList left).length :=
      Fin.castOrderIso (fixedWordList_length left).symm
    let rightCodomainCast : Fin n ≃o Fin (fixedWordList right).length :=
      Fin.castOrderIso (fixedWordList_length right).symm
    let leftListEmbedding :
        Fin subsequence.length ↪o Fin (fixedWordList left).length :=
      domainCast.toOrderEmbedding.trans
        (leftEmbedding.trans leftCodomainCast.toOrderEmbedding)
    let rightListEmbedding :
        Fin subsequence.length ↪o Fin (fixedWordList right).length :=
      domainCast.toOrderEmbedding.trans
        (rightEmbedding.trans rightCodomainCast.toOrderEmbedding)
    refine ⟨subsequence, subsequenceLength, ⟨?_, ?_⟩⟩
    · apply (sublist_fixedWordList_iff subsequence left).mpr
      refine ⟨leftListEmbedding, ?_⟩
      intro position
      simp [subsequence, leftListEmbedding, domainCast, leftCodomainCast,
        fixedWordList]
      congr 1
    · apply (sublist_fixedWordList_iff subsequence right).mpr
      refine ⟨rightListEmbedding, ?_⟩
      intro position
      simp [subsequence, rightListEmbedding, domainCast, rightCodomainCast,
        fixedWordList]
      exact agrees (domainCast position)
  · rintro ⟨subsequence, lengthEq, leftSublist, rightSublist⟩
    rcases (sublist_fixedWordList_iff subsequence left).mp leftSublist with
      ⟨rawLeftEmbedding, rawLeftValues⟩
    rcases (sublist_fixedWordList_iff subsequence right).mp rightSublist with
      ⟨rawRightEmbedding, rawRightValues⟩
    let leftCodomainCast : Fin (fixedWordList left).length ≃o Fin n :=
      Fin.castOrderIso (fixedWordList_length left)
    let rightCodomainCast : Fin (fixedWordList right).length ≃o Fin n :=
      Fin.castOrderIso (fixedWordList_length right)
    let leftEmbedding : Fin subsequence.length ↪o Fin n :=
      rawLeftEmbedding.trans leftCodomainCast.toOrderEmbedding
    let rightEmbedding : Fin subsequence.length ↪o Fin n :=
      rawRightEmbedding.trans rightCodomainCast.toOrderEmbedding
    have leftValues : ∀ position : Fin subsequence.length,
        subsequence.get position = left (leftEmbedding position) := by
      intro position
      have getIdentity :
          (fixedWordList left).get (rawLeftEmbedding position) =
            left (leftEmbedding position) := by
        simp [leftEmbedding, leftCodomainCast, fixedWordList]
        congr 1
      exact (rawLeftValues position).trans getIdentity
    have rightValues : ∀ position : Fin subsequence.length,
        subsequence.get position = right (rightEmbedding position) := by
      intro position
      have getIdentity :
          (fixedWordList right).get (rawRightEmbedding position) =
            right (rightEmbedding position) := by
        simp [rightEmbedding, rightCodomainCast, fixedWordList]
        congr 1
      exact (rawRightValues position).trans getIdentity
    let domainCast : Fin (n - d) ≃o Fin subsequence.length :=
      Fin.castOrderIso lengthEq.symm
    let leftDeletionEmbedding : Fin (n - d) ↪o Fin n :=
      domainCast.toOrderEmbedding.trans leftEmbedding
    let rightDeletionEmbedding : Fin (n - d) ↪o Fin n :=
      domainCast.toOrderEmbedding.trans rightEmbedding
    let keptLeft : Finset (Fin n) := Finset.univ.image leftDeletionEmbedding
    let keptRight : Finset (Fin n) := Finset.univ.image rightDeletionEmbedding
    let deletedLeft := keptLeftᶜ
    let deletedRight := keptRightᶜ
    have keptLeftCard : keptLeft.card = n - d := by
      dsimp [keptLeft]
      rw [Finset.card_image_of_injective _ leftDeletionEmbedding.injective,
        Finset.card_univ, Fintype.card_fin]
    have keptRightCard : keptRight.card = n - d := by
      dsimp [keptRight]
      rw [Finset.card_image_of_injective _ rightDeletionEmbedding.injective,
        Finset.card_univ, Fintype.card_fin]
    have deletedLeftCard : deletedLeft.card = d := by
      dsimp [deletedLeft]
      rw [Finset.card_compl, keptLeftCard]
      simp only [Fintype.card_fin]
      omega
    have deletedRightCard : deletedRight.card = d := by
      dsimp [deletedRight]
      rw [Finset.card_compl, keptRightCard]
      simp only [Fintype.card_fin]
      omega
    have deletedLeftPattern : deletedLeft ∈ deletionPatterns n d := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.subset_univ _, deletedLeftCard⟩
    have deletedRightPattern : deletedRight ∈ deletionPatterns n d := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.subset_univ _, deletedRightCard⟩
    refine ⟨deletedLeft, deletedLeftPattern,
      deletedRight, deletedRightPattern, ?_⟩
    have leftRange : ∀ position,
        leftDeletionEmbedding position ∈ keptLeft := by
      intro position
      exact Finset.mem_image.mpr ⟨position, Finset.mem_univ _, rfl⟩
    have rightRange : ∀ position,
        rightDeletionEmbedding position ∈ keptRight := by
      intro position
      exact Finset.mem_image.mpr ⟨position, Finset.mem_univ _, rfl⟩
    intro position
    have leftIndex :
        deletedLeftᶜ.orderEmbOfFin
            (kept_card hd deletedLeftPattern) position =
          leftDeletionEmbedding position := by
      have complementEq : deletedLeftᶜ = keptLeft := by
        simp [deletedLeft]
      have canonical :
          leftDeletionEmbedding = deletedLeftᶜ.orderEmbOfFin
            (kept_card hd deletedLeftPattern) := by
        apply Finset.orderEmbOfFin_unique'
        intro embeddedPosition
        rw [complementEq]
        exact leftRange embeddedPosition
      exact congrArg
        (fun embedding : Fin (n - d) ↪o Fin n => embedding position)
        canonical.symm
    have rightIndex :
        deletedRightᶜ.orderEmbOfFin
            (kept_card hd deletedRightPattern) position =
          rightDeletionEmbedding position := by
      have complementEq : deletedRightᶜ = keptRight := by
        simp [deletedRight]
      have canonical :
          rightDeletionEmbedding = deletedRightᶜ.orderEmbOfFin
            (kept_card hd deletedRightPattern) := by
        apply Finset.orderEmbOfFin_unique'
        intro embeddedPosition
        rw [complementEq]
        exact rightRange embeddedPosition
      exact congrArg
        (fun embedding : Fin (n - d) ↪o Fin n => embedding position)
        canonical.symm
    rw [leftIndex, rightIndex]
    have leftValue := leftValues (domainCast position)
    have rightValue := rightValues (domainCast position)
    exact leftValue.symm.trans rightValue

end TernarySyncAudit
