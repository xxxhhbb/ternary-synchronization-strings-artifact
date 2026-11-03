import Mathlib
import FormalAudit.WitnessTreeWeight

namespace TernarySyncAudit

/-- One node retained by the backwards deepest-dependent witness scan. -/
structure WitnessScanEntry (E : Type*) where
  label : E
  depth : ℕ
deriving DecidableEq

/-- Maximum of a finite list of natural numbers, with `none` exactly for the
empty list. -/
def maxDepthOption : List ℕ → Option ℕ
  | [] => none
  | depth :: rest =>
      match maxDepthOption rest with
      | none => some depth
      | some maximum => some (max depth maximum)

@[simp] theorem maxDepthOption_eq_none_iff (depths : List ℕ) :
    maxDepthOption depths = none ↔ depths = [] := by
  induction depths with
  | nil => simp [maxDepthOption]
  | cons depth rest inductionHypothesis =>
      simp only [maxDepthOption]
      cases restMaximum : maxDepthOption rest <;> simp

/-- Every member of a list is at most the maximum returned by
`maxDepthOption`. -/
theorem mem_le_maxDepthOption
    (depths : List ℕ) (depth maximum : ℕ)
    (member : depth ∈ depths)
    (maximumEq : maxDepthOption depths = some maximum) :
    depth ≤ maximum := by
  induction depths generalizing maximum with
  | nil => simp at member
  | cons head rest inductionHypothesis =>
      simp only [maxDepthOption] at maximumEq
      cases restMaximum : maxDepthOption rest with
      | none =>
          simp only [restMaximum, Option.some.injEq] at maximumEq
          have restEmpty := (maxDepthOption_eq_none_iff rest).mp restMaximum
          subst rest
          simp at member
          subst depth
          omega
      | some restMax =>
          simp only [restMaximum, Option.some.injEq] at maximumEq
          subst maximum
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact Nat.le_max_left _ _
          · exact (inductionHypothesis restMax member restMaximum).trans
              (Nat.le_max_right _ _)

/-- A returned maximum is attained by some list member. -/
theorem maxDepthOption_mem
    (depths : List ℕ) (maximum : ℕ)
    (maximumEq : maxDepthOption depths = some maximum) :
    maximum ∈ depths := by
  induction depths generalizing maximum with
  | nil => simp [maxDepthOption] at maximumEq
  | cons head rest inductionHypothesis =>
      simp only [maxDepthOption] at maximumEq
      cases restMaximum : maxDepthOption rest with
      | none =>
          simp only [restMaximum, Option.some.injEq] at maximumEq
          subst maximum
          simp
      | some restMax =>
          simp only [restMaximum, Option.some.injEq] at maximumEq
          subst maximum
          have restMember := inductionHypothesis restMax restMaximum
          by_cases order : head ≤ restMax
          · rw [Nat.max_eq_right order]
            exact List.mem_cons_of_mem head restMember
          · rw [Nat.max_eq_left (by omega)]
            exact List.mem_cons_self

/-- Depths of already retained entries whose labels overlap a new event
label according to the closed dependency neighborhood. -/
def dependentEntryDepths
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (entries : List (WitnessScanEntry E)) : List ℕ :=
  entries.filterMap fun entry =>
    if newLabel ∈ closedNeighbors neighbors entry.label then
      some entry.depth
    else none

/-- Any retained dependent entry contributes its depth to the candidate list. -/
theorem depth_mem_dependentEntryDepths
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (entries : List (WitnessScanEntry E))
    (entry : WitnessScanEntry E) (entryMember : entry ∈ entries)
    (dependent : newLabel ∈ closedNeighbors neighbors entry.label) :
    entry.depth ∈ dependentEntryDepths neighbors newLabel entries := by
  unfold dependentEntryDepths
  rw [List.mem_filterMap]
  refine ⟨entry, entryMember, ?_⟩
  simp [dependent]

/-- One step of the standard backwards witness scan.  An earlier event is
discarded if it overlaps no retained node; otherwise it is inserted one level
below the deepest retained node that it overlaps. -/
def deepestWitnessStep
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (entries : List (WitnessScanEntry E)) : List (WitnessScanEntry E) :=
  match maxDepthOption (dependentEntryDepths neighbors newLabel entries) with
  | none => entries
  | some maximum => ⟨newLabel, maximum + 1⟩ :: entries

/-- When a step inserts a node at depth `maximum+1`, that depth is strictly
larger than the depth of every retained node dependent with it. -/
theorem deepestWitnessStep_depth_gt
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (entries : List (WitnessScanEntry E)) (maximum : ℕ)
    (maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel entries) = some maximum)
    (entry : WitnessScanEntry E) (entryMember : entry ∈ entries)
    (dependent : newLabel ∈ closedNeighbors neighbors entry.label) :
    entry.depth < maximum + 1 := by
  have depthMember := depth_mem_dependentEntryDepths
    neighbors newLabel entries entry entryMember dependent
  have depthBound := mem_le_maxDepthOption
    (dependentEntryDepths neighbors newLabel entries)
      entry.depth maximum depthMember maximumEq
  omega

/-- The maximum used by an insertion is attained by an actual retained
dependent node, so the new node has a valid parent at the preceding depth. -/
theorem deepestWitnessStep_parent_exists
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (entries : List (WitnessScanEntry E)) (maximum : ℕ)
    (maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel entries) = some maximum) :
    ∃ parent ∈ entries,
      newLabel ∈ closedNeighbors neighbors parent.label ∧
        parent.depth = maximum := by
  have maximumMember := maxDepthOption_mem
    (dependentEntryDepths neighbors newLabel entries) maximum maximumEq
  unfold dependentEntryDepths at maximumMember
  rw [List.mem_filterMap] at maximumMember
  rcases maximumMember with ⟨parent, parentMember, selected⟩
  by_cases dependent : newLabel ∈ closedNeighbors neighbors parent.label
  · simp [dependent] at selected
    subst maximum
    exact ⟨parent, parentMember, dependent, rfl⟩
  · simp [dependent] at selected

theorem deepestWitnessStep_eq_cons
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (entries : List (WitnessScanEntry E)) (maximum : ℕ)
    (maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel entries) = some maximum) :
    deepestWitnessStep neighbors newLabel entries =
      ⟨newLabel, maximum + 1⟩ :: entries := by
  simp [deepestWitnessStep, maximumEq]

/-- Equal labels always overlap because the dependency neighborhood is
closed; hence an earlier copy is inserted strictly deeper than every retained
copy of that label. -/
theorem deepestWitnessStep_same_label_deeper
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (entries : List (WitnessScanEntry E))
    (entry : WitnessScanEntry E) (entryMember : entry ∈ entries)
    (sameLabel : entry.label = newLabel) :
    ∃ maximum,
      deepestWitnessStep neighbors newLabel entries =
        ⟨newLabel, maximum + 1⟩ :: entries ∧
      entry.depth < maximum + 1 := by
  have dependent : newLabel ∈ closedNeighbors neighbors entry.label := by
    rw [sameLabel]
    exact Finset.mem_insert_self _ _
  have depthMember := depth_mem_dependentEntryDepths
    neighbors newLabel entries entry entryMember dependent
  cases maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel entries) with
  | none =>
      have empty := (maxDepthOption_eq_none_iff _).mp maximumEq
      rw [empty] at depthMember
      simp at depthMember
  | some maximum =>
      refine ⟨maximum,
        deepestWitnessStep_eq_cons neighbors newLabel entries maximum maximumEq,
        deepestWitnessStep_depth_gt neighbors newLabel entries maximum maximumEq
          entry entryMember dependent⟩

/-- Run the deepest-dependent scan on a reverse-chronological list.  The
first entry is the chosen root at depth zero. -/
def deepestWitnessScanReversed
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) : List E → List (WitnessScanEntry E)
  | [] => []
  | root :: older =>
      older.foldl (fun entries label =>
        deepestWitnessStep neighbors label entries) [⟨root, 0⟩]

/-- The witness scan of a chronological log scans its reverse, so the last
event becomes the root. -/
def deepestWitnessScan
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (log : List E) :
    List (WitnessScanEntry E) :=
  deepestWitnessScanReversed neighbors log.reverse

/-- Number of retained scan nodes with one prescribed label. -/
def witnessScanLabelCount
    {E : Type*} [DecidableEq E]
    (target : E) (entries : List (WitnessScanEntry E)) : ℕ :=
  (entries.filter fun entry => decide (entry.label = target)).length

/-- A witness step never removes an already retained entry. -/
theorem deepestWitnessStep_preserves_mem
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (entries : List (WitnessScanEntry E)) (entry : WitnessScanEntry E)
    (member : entry ∈ entries) :
    entry ∈ deepestWitnessStep neighbors newLabel entries := by
  unfold deepestWitnessStep
  cases maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel entries) with
  | none => exact member
  | some maximum => exact List.mem_cons_of_mem _ member

/-- The deepest scan never duplicates an existing labelled-depth node. -/
theorem deepestWitnessStep_preserves_nodup
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (newLabel : E)
    (entries : List (WitnessScanEntry E))
    (entriesNodup : entries.Nodup) :
    (deepestWitnessStep neighbors newLabel entries).Nodup := by
  unfold deepestWitnessStep
  cases maximumEq : maxDepthOption
      (dependentEntryDepths neighbors newLabel entries) with
  | none => exact entriesNodup
  | some maximum =>
      rw [List.nodup_cons]
      constructor
      · intro newEntryMember
        let newEntry : WitnessScanEntry E := ⟨newLabel, maximum + 1⟩
        have dependent : newLabel ∈
            closedNeighbors neighbors newEntry.label := by
          exact Finset.mem_insert_self _ _
        have impossible := deepestWitnessStep_depth_gt
          neighbors newLabel entries maximum maximumEq
            newEntry newEntryMember dependent
        dsimp [newEntry] at impossible
        omega
      · exact entriesNodup

/-- If a target label is already retained, one step changes its retained
count exactly when the new event has that same label. -/
theorem deepestWitnessStep_labelCount
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (target newLabel : E)
    (entries : List (WitnessScanEntry E))
    (targetPresent : ∃ entry ∈ entries, entry.label = target) :
    witnessScanLabelCount target
        (deepestWitnessStep neighbors newLabel entries) =
      witnessScanLabelCount target entries +
        if newLabel = target then 1 else 0 := by
  by_cases same : newLabel = target
  · rcases targetPresent with ⟨entry, entryMember, entryLabel⟩
    have insertion := deepestWitnessStep_same_label_deeper
      neighbors newLabel entries entry entryMember (entryLabel.trans same.symm)
    rcases insertion with ⟨maximum, stepEq, depthInequality⟩
    rw [stepEq]
    simp [witnessScanLabelCount, same]
  · unfold deepestWitnessStep
    cases maximumEq : maxDepthOption
        (dependentEntryDepths neighbors newLabel entries) with
    | none => simp [witnessScanLabelCount, same]
    | some maximum => simp [witnessScanLabelCount, same]

/-- Presence of a retained target label is invariant under later scan steps. -/
theorem deepestWitnessStep_preserves_label
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (target newLabel : E)
    (entries : List (WitnessScanEntry E))
    (targetPresent : ∃ entry ∈ entries, entry.label = target) :
    ∃ entry ∈ deepestWitnessStep neighbors newLabel entries,
      entry.label = target := by
  rcases targetPresent with ⟨entry, member, label⟩
  exact ⟨entry,
    deepestWitnessStep_preserves_mem neighbors newLabel entries entry member,
    label⟩

/-- Number of occurrences of one label in an ordinary label list. -/
def labelOccurrenceCount
    {E : Type*} [DecidableEq E] (target : E) (labels : List E) : ℕ :=
  (labels.filter fun label => decide (label = target)).length

/-- Exact root-label accounting through an arbitrary continuation of the
reverse scan. -/
theorem foldl_deepestWitnessStep_labelCount
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (target : E) (older : List E)
    (entries : List (WitnessScanEntry E))
    (targetPresent : ∃ entry ∈ entries, entry.label = target) :
    witnessScanLabelCount target
        (older.foldl (fun state label =>
          deepestWitnessStep neighbors label state) entries) =
      witnessScanLabelCount target entries +
        labelOccurrenceCount target older := by
  induction older generalizing entries with
  | nil => simp [labelOccurrenceCount]
  | cons label rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis
        (deepestWitnessStep neighbors label entries)
        (deepestWitnessStep_preserves_label
          neighbors target label entries targetPresent)]
      rw [deepestWitnessStep_labelCount
        neighbors target label entries targetPresent]
      by_cases same : label = target
      · simp [labelOccurrenceCount, same]
        omega
      · simp [labelOccurrenceCount, same]

/-- Every copy of the chosen root label is retained by the deepest witness
scan, and no other event creates such a node. -/
theorem deepestWitnessScanReversed_root_count
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (root : E) (older : List E) :
    witnessScanLabelCount root
        (deepestWitnessScanReversed neighbors (root :: older)) =
      labelOccurrenceCount root (root :: older) := by
  simp only [deepestWitnessScanReversed]
  rw [foldl_deepestWitnessStep_labelCount]
  · simp [witnessScanLabelCount, labelOccurrenceCount, Nat.add_comm]
  · exact ⟨⟨root, 0⟩, by simp, rfl⟩

/-- Every reverse scan produces a duplicate-free list of labelled-depth
nodes. -/
theorem deepestWitnessScanReversed_nodup
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (reversed : List E) :
    (deepestWitnessScanReversed neighbors reversed).Nodup := by
  cases reversed with
  | nil => simp [deepestWitnessScanReversed]
  | cons root older =>
      simp only [deepestWitnessScanReversed]
      have foldNodup : ∀ (remaining : List E)
          (entries : List (WitnessScanEntry E)), entries.Nodup →
          (remaining.foldl (fun state label =>
            deepestWitnessStep neighbors label state) entries).Nodup := by
        intro remaining
        induction remaining with
        | nil => intro entries nodup; exact nodup
        | cons label rest inductionHypothesis =>
            intro entries nodup
            simp only [List.foldl_cons]
            exact inductionHypothesis
              (deepestWitnessStep neighbors label entries)
              (deepestWitnessStep_preserves_nodup
                neighbors label entries nodup)
      exact foldNodup older [⟨root, 0⟩] (by simp)

end TernarySyncAudit
