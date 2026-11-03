import Mathlib
import FormalAudit.CompatibleSublog
import FormalAudit.DeepestWitnessScan

namespace TernarySyncAudit

/-- Labels of a deepest-scan entry list, in retained chronological order. -/
def witnessEntryLabels
    {E : Type*} (entries : List (WitnessScanEntry E)) : List E :=
  entries.map WitnessScanEntry.label

/-- Prepending the same event to an original and retained log preserves a
support-count embedding. -/
def SupportCountLogEmbedding.prependBoth
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (head : E)
    {original retained : List E}
    (embedding : SupportCountLogEmbedding support original retained) :
    SupportCountLogEmbedding support
      (head :: original) (head :: retained) := by
  let newPosition : Fin (head :: retained).length →
      Fin (head :: original).length := fun index =>
    if indexZero : index.1 = 0 then ⟨0, by simp⟩
    else Fin.succ (embedding.position
      ⟨index.1 - 1, by
        have indexLt := index.isLt
        simp only [List.length_cons] at indexLt
        omega⟩)
  refine {
    position := newPosition
    label_eq := ?_
    support_count_eq := ?_
  }
  · intro index
    by_cases indexZero : index.1 = 0
    · have indexEq : index = 0 := Fin.ext indexZero
      subst index
      simp [newPosition]
    · let tailIndex : Fin retained.length :=
          ⟨index.1 - 1, by
            have indexLt := index.isLt
            simp only [List.length_cons] at indexLt
            omega⟩
      have indexEq : index = Fin.succ tailIndex := by
        apply Fin.ext
        simp [tailIndex]
        omega
      rw [indexEq]
      simp only [newPosition, Fin.val_succ]
      simp only [Nat.succ_ne_zero, dite_false]
      exact embedding.label_eq tailIndex
  · intro index coordinate inside
    by_cases indexZero : index.1 = 0
    · have indexEq : index = 0 := Fin.ext indexZero
      subst index
      simp [newPosition]
    · let tailIndex : Fin retained.length :=
          ⟨index.1 - 1, by
            have indexLt := index.isLt
            simp only [List.length_cons] at indexLt
            omega⟩
      have indexEq : index = Fin.succ tailIndex := by
        apply Fin.ext
        simp [tailIndex]
        omega
      rw [indexEq] at inside ⊢
      have insideTail : coordinate ∈ support (retained.get tailIndex) := by
        simpa using inside
      have oldEq := embedding.support_count_eq
          tailIndex coordinate insideTail
      change supportOccurrenceCount support coordinate
          ((head :: original).take
            ((embedding.position tailIndex).1 + 1)) =
        supportOccurrenceCount support coordinate
          ((head :: retained).take (tailIndex.1 + 1))
      simp only [List.take_succ_cons, supportOccurrenceCount_cons]
      rw [oldEq]

/-- If a new original head has support disjoint from every retained event,
it may be omitted without changing any retained event's support counters. -/
def SupportCountLogEmbedding.prependOriginalDisjoint
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (head : E)
    {original retained : List E}
    (embedding : SupportCountLogEmbedding support original retained)
    (disjoint : ∀ retainedLabel ∈ retained,
      Disjoint (support head) (support retainedLabel)) :
    SupportCountLogEmbedding support (head :: original) retained where
  position := fun index => Fin.succ (embedding.position index)
  label_eq := by
    intro index
    simpa using embedding.label_eq index
  support_count_eq := by
    intro index coordinate inside
    have labelMember : retained.get index ∈ retained := List.get_mem _ _
    have supportsDisjoint := disjoint (retained.get index) labelMember
    have outsideHead : coordinate ∉ support head := by
      intro insideHead
      exact Finset.disjoint_left.mp supportsDisjoint insideHead inside
    have oldEq := embedding.support_count_eq index coordinate inside
    change supportOccurrenceCount support coordinate
        ((head :: original).take ((embedding.position index).1 + 1)) =
      supportOccurrenceCount support coordinate (retained.take index.1)
    simp only [List.take_succ_cons, supportOccurrenceCount_cons,
      outsideHead, if_false]
    exact oldEq

/-- If a deepest scan discards a new label, its support is disjoint from the
support of every currently retained entry, provided support intersection
implies closed-neighborhood dependence. -/
theorem deepestWitnessStep_none_support_disjoint
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (support : E → Finset V) (neighbors : E → Finset E)
    (overlapDependent : ∀ left right,
      ¬Disjoint (support left) (support right) →
        left ∈ closedNeighbors neighbors right)
    (newLabel : E) (entries : List (WitnessScanEntry E))
    (maximumNone : maxDepthOption
      (dependentEntryDepths neighbors newLabel entries) = none) :
    ∀ entry ∈ entries,
      Disjoint (support newLabel) (support entry.label) := by
  intro entry entryMember
  by_contra overlaps
  have dependent := overlapDependent newLabel entry.label overlaps
  have depthMember := depth_mem_dependentEntryDepths
    neighbors newLabel entries entry entryMember dependent
  have emptyDepths := (maxDepthOption_eq_none_iff _).mp maximumNone
  rw [emptyDepths] at depthMember
  simp at depthMember

/-- One reverse scan step preserves a support-count embedding from the
chronological original prefix to the retained entry labels. -/
def deepestWitnessStep_supportCountEmbedding
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (support : E → Finset V) (neighbors : E → Finset E)
    (overlapDependent : ∀ left right,
      ¬Disjoint (support left) (support right) →
        left ∈ closedNeighbors neighbors right)
    (newLabel : E) (original : List E)
    (entries : List (WitnessScanEntry E))
    (embedding : SupportCountLogEmbedding support original
      (witnessEntryLabels entries)) :
    SupportCountLogEmbedding support (newLabel :: original)
      (witnessEntryLabels
        (deepestWitnessStep neighbors newLabel entries)) := by
  unfold deepestWitnessStep
  split
  · next maximumNone =>
      apply SupportCountLogEmbedding.prependOriginalDisjoint
        support newLabel embedding
      intro retainedLabel retainedMember
      rw [witnessEntryLabels, List.mem_map] at retainedMember
      obtain ⟨entry, entryMember, labelEq⟩ := retainedMember
      subst retainedLabel
      exact deepestWitnessStep_none_support_disjoint
        support neighbors overlapDependent newLabel entries maximumNone
          entry entryMember
  · exact SupportCountLogEmbedding.prependBoth
      support newLabel embedding

/-- Processing an arbitrary reverse-chronological continuation preserves a
support-count embedding. -/
def foldl_deepestWitnessStep_supportCountEmbedding
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (support : E → Finset V) (neighbors : E → Finset E)
    (overlapDependent : ∀ left right,
      ¬Disjoint (support left) (support right) →
        left ∈ closedNeighbors neighbors right)
    (older original : List E) (entries : List (WitnessScanEntry E))
    (embedding : SupportCountLogEmbedding support original
      (witnessEntryLabels entries)) :
    SupportCountLogEmbedding support (older.reverse ++ original)
      (witnessEntryLabels
        (older.foldl (fun current label =>
          deepestWitnessStep neighbors label current) entries)) := by
  induction older generalizing original entries with
  | nil => simpa using embedding
  | cons label rest inductionHypothesis =>
      simp only [List.foldl_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      exact inductionHypothesis (label :: original)
        (deepestWitnessStep neighbors label entries)
        (deepestWitnessStep_supportCountEmbedding
          support neighbors overlapDependent label original entries embedding)

/-- The full deepest retained log of a nonempty reverse scan has exact
support counters inherited from the corresponding chronological prefix. -/
def deepestWitnessScanReversed_supportCountEmbedding
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (support : E → Finset V) (neighbors : E → Finset E)
    (overlapDependent : ∀ left right,
      ¬Disjoint (support left) (support right) →
        left ∈ closedNeighbors neighbors right)
    (root : E) (older : List E) :
    SupportCountLogEmbedding support (older.reverse ++ [root])
      (witnessEntryLabels
        (deepestWitnessScanReversed neighbors (root :: older))) := by
  simp only [deepestWitnessScanReversed]
  let empty : SupportCountLogEmbedding support [] [] := {
    position := fun index => Fin.elim0 index
    label_eq := fun index => Fin.elim0 index
    support_count_eq := fun index => Fin.elim0 index
  }
  have base : SupportCountLogEmbedding support [root] [root] :=
    SupportCountLogEmbedding.prependBoth support root empty
  simpa [witnessEntryLabels] using
    foldl_deepestWitnessStep_supportCountEmbedding
      support neighbors overlapDependent older [root] [⟨root, 0⟩] base

end TernarySyncAudit
