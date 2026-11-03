import Mathlib
import FormalAudit.WitnessTreeWeight

namespace TernarySyncAudit

/-- Later log positions whose labels may be parents of one occurrence in the
standard backwards witness-forest construction. -/
def laterNeighborOccurrences
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E)
    (index : Fin log.length) : Finset (Fin log.length) :=
  Finset.univ.filter fun candidate =>
    index.1 < candidate.1 ∧
      log.get index ∈ closedNeighbors neighbors (log.get candidate)

/-- The closest later dependent occurrence, if one exists.  Repeatedly
following this parent map gives an auxiliary chronological dependency forest.
The standard MT tree additionally chooses a deepest dependent node; that
stronger construction is formalized separately. -/
noncomputable def closestWitnessParent
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E)
    (index : Fin log.length) : Option (Fin log.length) := by
  classical
  let candidates := laterNeighborOccurrences neighbors log index
  exact if nonempty : candidates.Nonempty then
    some (candidates.min' nonempty)
  else none

/-- A returned closest parent is a genuine member of the later-neighbor set. -/
theorem closestWitnessParent_mem
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E)
    (index parent : Fin log.length)
    (parentEq : closestWitnessParent neighbors log index = some parent) :
    parent ∈ laterNeighborOccurrences neighbors log index := by
  classical
  unfold closestWitnessParent at parentEq
  let candidates := laterNeighborOccurrences neighbors log index
  by_cases nonempty : candidates.Nonempty
  · have chosen : candidates.min' nonempty = parent := by
      simpa [closestWitnessParent, candidates, nonempty] using parentEq
    rw [← chosen]
    exact Finset.min'_mem candidates nonempty
  · simp [candidates, nonempty] at parentEq

/-- Every witness-parent edge moves strictly forward in chronological order. -/
theorem closestWitnessParent_later
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E)
    (index parent : Fin log.length)
    (parentEq : closestWitnessParent neighbors log index = some parent) :
    index.1 < parent.1 := by
  have member := closestWitnessParent_mem neighbors log index parent parentEq
  exact (Finset.mem_filter.mp member).2.1

/-- Every witness-parent edge has an allowed child label. -/
theorem closestWitnessParent_neighbor
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E)
    (index parent : Fin log.length)
    (parentEq : closestWitnessParent neighbors log index = some parent) :
    log.get index ∈ closedNeighbors neighbors (log.get parent) := by
  have member := closestWitnessParent_mem neighbors log index parent parentEq
  exact (Finset.mem_filter.mp member).2.2

/-- The chosen parent is no later than every other eligible parent. -/
theorem closestWitnessParent_minimal
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E)
    (index parent candidate : Fin log.length)
    (parentEq : closestWitnessParent neighbors log index = some parent)
    (candidateMember :
      candidate ∈ laterNeighborOccurrences neighbors log index) :
    parent.1 ≤ candidate.1 := by
  classical
  unfold closestWitnessParent at parentEq
  let candidates := laterNeighborOccurrences neighbors log index
  have nonempty : candidates.Nonempty := ⟨candidate, candidateMember⟩
  have chosen : candidates.min' nonempty = parent := by
    simpa [closestWitnessParent, candidates, nonempty] using parentEq
  rw [← chosen]
  exact Finset.min'_le candidates candidate candidateMember

/-- Properness of the closest-parent forest: distinct children of one parent
cannot carry the same event label.  The key point is that the earlier copy
would see the later equal-labelled copy as an eligible closer parent. -/
theorem closestWitnessParent_children_label_injective
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E)
    (parent left right : Fin log.length)
    (leftParent : closestWitnessParent neighbors log left = some parent)
    (rightParent : closestWitnessParent neighbors log right = some parent)
    (sameLabel : log.get left = log.get right) :
    left = right := by
  apply Fin.ext
  by_contra different
  rcases lt_or_gt_of_ne different with order | order
  · have rightEligible :
        right ∈ laterNeighborOccurrences neighbors log left := by
      simp only [laterNeighborOccurrences, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · exact order
      · rw [sameLabel]
        exact Finset.mem_insert_self _ _
    have parentNoLater := closestWitnessParent_minimal
      neighbors log left parent right leftParent rightEligible
    have rightBeforeParent := closestWitnessParent_later
      neighbors log right parent rightParent
    omega
  · have leftEligible :
        left ∈ laterNeighborOccurrences neighbors log right := by
      simp only [laterNeighborOccurrences, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · exact order
      · rw [← sameLabel]
        exact Finset.mem_insert_self _ _
    have parentNoLater := closestWitnessParent_minimal
      neighbors log right parent left rightParent leftEligible
    have leftBeforeParent := closestWitnessParent_later
      neighbors log left parent leftParent
    omega

/-- A finite chronological parent map together with exactly the local
properties required of a proper witness forest. -/
structure ProperWitnessForest
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E) where
  parent : Fin log.length → Option (Fin log.length)
  parent_later : ∀ index parentIndex,
    parent index = some parentIndex → index.1 < parentIndex.1
  parent_neighbor : ∀ index parentIndex,
    parent index = some parentIndex →
      log.get index ∈ closedNeighbors neighbors (log.get parentIndex)
  children_label_injective : ∀ parentIndex left right,
    parent left = some parentIndex → parent right = some parentIndex →
      log.get left = log.get right → left = right

/-- The closest-later-parent construction is a certified proper auxiliary
forest for every finite event log. -/
noncomputable def closestProperWitnessForest
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E) :
    ProperWitnessForest neighbors log where
  parent := closestWitnessParent neighbors log
  parent_later := closestWitnessParent_later neighbors log
  parent_neighbor := closestWitnessParent_neighbor neighbors log
  children_label_injective :=
    closestWitnessParent_children_label_injective neighbors log

/-- The last occurrence in a nonempty chronological log is a root of the
closest-parent witness forest. -/
theorem closestWitnessParent_last
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (first : E) (rest : List E) :
    closestWitnessParent neighbors (first :: rest) (Fin.last rest.length) = none := by
  classical
  have emptyCandidates : laterNeighborOccurrences neighbors (first :: rest)
      (Fin.last rest.length) = ∅ := by
    ext candidate
    simp only [laterNeighborOccurrences, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro eligible
      have candidateBound : candidate.1 < rest.length + 1 := by
        simpa using candidate.2
      have later : rest.length < candidate.1 := by
        simpa using eligible.1
      omega
    · intro emptyMember
      simp at emptyMember
  simp [closestWitnessParent, emptyCandidates]

/-- Follow a closest-parent chain for an exact number of edges. -/
noncomputable def followWitnessParent
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E) :
    ℕ → Fin log.length → Option (Fin log.length)
  | 0, index => some index
  | steps + 1, index =>
      match closestWitnessParent neighbors log index with
      | none => none
      | some parent => followWitnessParent neighbors log steps parent

/-- A parent chain of `steps` edges advances the chronological index by at
least `steps`. -/
theorem followWitnessParent_progress
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E) :
    ∀ steps (start endpoint : Fin log.length),
      followWitnessParent neighbors log steps start = some endpoint →
        start.1 + steps ≤ endpoint.1 := by
  intro steps
  induction steps with
  | zero =>
      intro start endpoint chain
      simp [followWitnessParent] at chain
      subst endpoint
      omega
  | succ steps inductionHypothesis =>
      intro start endpoint chain
      unfold followWitnessParent at chain
      cases parentEq : closestWitnessParent neighbors log start with
      | none => simp [parentEq] at chain
      | some parent =>
          simp only [parentEq] at chain
          have parentProgress := inductionHypothesis parent endpoint chain
          have firstEdge := closestWitnessParent_later
            neighbors log start parent parentEq
          omega

/-- Consequently no parent chain inside a log can have as many edges as the
log has occurrences. -/
theorem followWitnessParent_steps_lt_length
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E)
    (steps : ℕ) (start endpoint : Fin log.length)
    (chain : followWitnessParent neighbors log steps start = some endpoint) :
    steps < log.length := by
  have progress := followWitnessParent_progress
    neighbors log steps start endpoint chain
  have endpointBound := endpoint.2
  omega

end TernarySyncAudit
