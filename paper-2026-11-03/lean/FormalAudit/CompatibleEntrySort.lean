import Mathlib
import FormalAudit.DeepestRetainedLogEmbedding
import FormalAudit.DeepestWitnessOrder

namespace TernarySyncAudit

/-- Canonical descending-depth order, with the transported finite label order
as a deterministic tie breaker. -/
noncomputable def witnessDepthBefore
    {E : Type*} [Fintype E] [DecidableEq E]
    (left right : WitnessScanEntry E) : Prop :=
  right.depth < left.depth ∨
    (right.depth = left.depth ∧
      (Fintype.equivFin E left.label).1 ≤
        (Fintype.equivFin E right.label).1)

noncomputable instance witnessDepthBefore_decidable
    {E : Type*} [Fintype E] [DecidableEq E]
    (left right : WitnessScanEntry E) :
    Decidable (witnessDepthBefore left right) := by
  unfold witnessDepthBefore
  infer_instance

noncomputable instance witnessDepthBefore_total
    {E : Type*} [Fintype E] [DecidableEq E] :
    Std.Total (@witnessDepthBefore E _ _) where
  total left right := by
    by_cases depthLt : right.depth < left.depth
    · exact Or.inl (Or.inl depthLt)
    by_cases reverseDepthLt : left.depth < right.depth
    · exact Or.inr (Or.inl reverseDepthLt)
    have depthEq : right.depth = left.depth := by omega
    rcases le_total (Fintype.equivFin E left.label).1
        (Fintype.equivFin E right.label).1 with labelLe | labelLe
    · exact Or.inl (Or.inr ⟨depthEq, labelLe⟩)
    · exact Or.inr (Or.inr ⟨depthEq.symm, labelLe⟩)

noncomputable instance witnessDepthBefore_trans
    {E : Type*} [Fintype E] [DecidableEq E] :
    IsTrans (WitnessScanEntry E) (@witnessDepthBefore E _ _) where
  trans left middle right leftMiddle middleRight := by
    rcases leftMiddle with leftMiddle | ⟨middleDepth, leftLabel⟩
    · rcases middleRight with middleRight | ⟨rightDepth, middleLabel⟩
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
    · rcases middleRight with middleRight | ⟨rightDepth, middleLabel⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, le_trans leftLabel middleLabel⟩

noncomputable instance witnessDepthBefore_antisymm
    {E : Type*} [Fintype E] [DecidableEq E] :
    Std.Antisymm (@witnessDepthBefore E _ _) where
  antisymm left right leftRight rightLeft := by
    rcases leftRight with leftRight | ⟨rightDepth, leftLabel⟩
    · rcases rightLeft with rightLeft | ⟨leftDepth, rightLabel⟩ <;> omega
    · rcases rightLeft with rightLeft | ⟨leftDepth, rightLabel⟩
      · omega
      · have labelIndexEq := le_antisymm leftLabel rightLabel
        have labelEq : left.label = right.label := by
          exact (Fintype.equivFin E).injective (Fin.ext labelIndexEq)
        cases left
        cases right
        simp_all

/-- Strictly larger depth always precedes strictly smaller depth in the
canonical order, independently of the label tie breaker. -/
theorem witnessDepthBefore_of_depth_lt
    {E : Type*} [Fintype E] [DecidableEq E]
    {left right : WitnessScanEntry E} (depthLt : right.depth < left.depth) :
    witnessDepthBefore left right := by
  unfold witnessDepthBefore
  exact Or.inl depthLt

/-- Entry-log compatibility means compatibility of its label projection. -/
def witnessEntryLogCompatible
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (eventSet : E → Set (V → A))
    (table : V → ℕ → A) (initial : V → ℕ)
    (entries : List (WitnessScanEntry E)) : Prop :=
  logCompatible support eventSet table initial (witnessEntryLabels entries)

/-- Incrementing two disjoint supports commutes pointwise. -/
theorem incrementSupport_comm_of_disjoint
    {V : Type*} [DecidableEq V] (left right : Finset V)
    (disjoint : Disjoint left right) (count : V → ℕ) :
    incrementSupport right (incrementSupport left count) =
      incrementSupport left (incrementSupport right count) := by
  funext coordinate
  by_cases inLeft : coordinate ∈ left
  · have notRight : coordinate ∉ right := by
      intro inRight
      exact Finset.disjoint_left.mp disjoint inLeft inRight
    simp [incrementSupport, inLeft, notRight]
  · by_cases inRight : coordinate ∈ right
    · simp [incrementSupport, inLeft, inRight]
    · simp [incrementSupport, inLeft, inRight]

/-- Two adjacent disjoint-support events may be exchanged without destroying
log compatibility. -/
theorem logCompatible_swap_disjoint
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate,
      DependsOn (event candidate) (support candidate))
    (table : V → ℕ → A) (initial : V → ℕ)
    (left right : E) (rest : List E)
    (disjoint : Disjoint (support left) (support right))
    (compatible : logCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      table initial (left :: right :: rest)) :
    logCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      table initial (right :: left :: rest) := by
  rw [logCompatible_cons, logCompatible_cons] at compatible ⊢
  let initialAssignment : V → A := fun coordinate =>
    table coordinate (initial coordinate)
  let afterLeftAssignment : V → A := fun coordinate =>
    table coordinate (incrementSupport (support left) initial coordinate)
  let afterRightAssignment : V → A := fun coordinate =>
    table coordinate (incrementSupport (support right) initial coordinate)
  have rightAtInitial : initialAssignment ∈ event right := by
    have agree : ∀ coordinate ∈ support right,
        afterLeftAssignment coordinate = initialAssignment coordinate := by
      intro coordinate inRight
      have outsideLeft : coordinate ∉ support left := by
        intro inLeft
        exact Finset.disjoint_left.mp disjoint inLeft inRight
      simp [afterLeftAssignment, initialAssignment,
        incrementSupport, outsideLeft]
    exact ((eventDepends right)
      afterLeftAssignment initialAssignment agree).mp compatible.2.1
  have leftAfterRight : afterRightAssignment ∈ event left := by
    have agree : ∀ coordinate ∈ support left,
        initialAssignment coordinate = afterRightAssignment coordinate := by
      intro coordinate inLeft
      have outsideRight : coordinate ∉ support right := by
        intro inRight
        exact Finset.disjoint_left.mp disjoint inLeft inRight
      simp [afterRightAssignment, initialAssignment,
        incrementSupport, outsideRight]
    exact ((eventDepends left)
      initialAssignment afterRightAssignment agree).mp compatible.1
  refine ⟨rightAtInitial, leftAfterRight, ?_⟩
  have countEq := incrementSupport_comm_of_disjoint
    (support left) (support right) disjoint initial
  rw [← countEq]
  exact compatible.2.2

/-- Inserting one chronological entry into descending-depth order changes
compatibility only by swaps with support-disjoint entries. -/
theorem orderedInsert_witnessEntryLogCompatible
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate,
      DependsOn (event candidate) (support candidate))
    (table : V → ℕ → A) (initial : V → ℕ)
    (newEntry : WitnessScanEntry E) (entries : List (WitnessScanEntry E))
    (ahead : ∀ oldEntry ∈ entries,
      ¬Disjoint (support newEntry.label) (support oldEntry.label) →
        oldEntry.depth < newEntry.depth)
    (compatible : witnessEntryLogCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      table initial (newEntry :: entries)) :
    witnessEntryLogCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      table initial (entries.orderedInsert witnessDepthBefore newEntry) := by
  induction entries generalizing initial with
  | nil => exact compatible
  | cons head tail inductionHypothesis =>
      rw [List.orderedInsert_cons]
      by_cases alreadyBefore : witnessDepthBefore newEntry head
      · simpa [alreadyBefore] using compatible
      · have supportsDisjoint :
            Disjoint (support newEntry.label) (support head.label) := by
          by_contra overlaps
          have strict := ahead head (by simp) overlaps
          exact alreadyBefore (witnessDepthBefore_of_depth_lt strict)
        have swapped := logCompatible_swap_disjoint
          support event eventDepends table initial
          newEntry.label head.label (witnessEntryLabels tail)
          supportsDisjoint compatible
        simp only [alreadyBefore, if_false]
        unfold witnessEntryLogCompatible
        simp only [witnessEntryLabels, List.map_cons]
        rw [logCompatible_cons, logCompatible_cons] at swapped
        rw [logCompatible_cons]
        refine ⟨swapped.1, ?_⟩
        apply inductionHypothesis
        · intro oldEntry oldMember overlaps
          exact ahead oldEntry (by simp [oldMember]) overlaps
        · exact swapped.2

/-- Sorting a chronologically depth-consistent retained entry log into the
canonical descending-depth order preserves compatibility. -/
theorem insertionSort_witnessEntryLogCompatible
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate,
      DependsOn (event candidate) (support candidate))
    (table : V → ℕ → A) (initial : V → ℕ)
    (entries : List (WitnessScanEntry E))
    (ordered : SupportsFollowDepth support entries)
    (compatible : witnessEntryLogCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      table initial entries) :
    witnessEntryLogCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      table initial (entries.insertionSort witnessDepthBefore) := by
  induction entries generalizing initial with
  | nil => exact compatible
  | cons head tail inductionHypothesis =>
      rw [SupportsFollowDepth, List.pairwise_cons] at ordered
      rw [witnessEntryLogCompatible, witnessEntryLabels,
        List.map_cons, logCompatible_cons] at compatible
      have sortedTailCompatible := inductionHypothesis
        (incrementSupport (support head.label) initial)
        ordered.2 compatible.2
      have headWithSortedTail : witnessEntryLogCompatible support
          (fun candidate => (event candidate : Set (V → A)))
          table initial (head :: tail.insertionSort witnessDepthBefore) := by
        rw [witnessEntryLogCompatible, witnessEntryLabels,
          List.map_cons, logCompatible_cons]
        exact ⟨compatible.1, sortedTailCompatible⟩
      apply orderedInsert_witnessEntryLogCompatible
        support event eventDepends table initial head
          (tail.insertionSort witnessDepthBefore)
      · intro oldEntry oldMember overlaps
        have oldInTail : oldEntry ∈ tail :=
          (List.perm_insertionSort witnessDepthBefore tail).mem_iff.mp oldMember
        exact ordered.1 oldEntry oldInTail overlaps
      · exact headWithSortedTail

end TernarySyncAudit
