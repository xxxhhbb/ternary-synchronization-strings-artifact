import Mathlib
import FormalAudit.ParentedWitnessScan
import FormalAudit.MTEventExpectation

namespace TernarySyncAudit

/-- One occurrence of a prescribed event label in a chronological log. -/
abbrev EventOccurrence
    {E : Type*} [DecidableEq E] (event : E) (log : List E) :=
  {index : Fin log.length // log.get index = event}

/-- One-based occurrence rank inside the prefix ending at this occurrence. -/
def eventOccurrenceRank
    {E : Type*} [DecidableEq E]
    (event : E) (log : List E) (occurrence : EventOccurrence event log) : ℕ :=
  logEventCount event (log.take (occurrence.1.1 + 1))

/-- Taking a longer prefix cannot decrease the number of occurrences of a
fixed label. -/
theorem logEventCount_take_mono
    {E : Type*} [DecidableEq E]
    (event : E) (log : List E) (left right : ℕ)
    (lengthLe : left ≤ right) :
    logEventCount event (log.take left) ≤
      logEventCount event (log.take right) := by
  induction log generalizing left right with
  | nil => simp
  | cons head rest inductionHypothesis =>
      cases left with
      | zero => simp
      | succ left =>
          cases right with
          | zero => omega
          | succ right =>
              simp only [List.take_succ_cons, logEventCount_cons]
              have tailLe := inductionHypothesis left right (by omega)
              omega

/-- Occurrence rank is strictly increasing with chronological position among
occurrences of the same label. -/
theorem eventOccurrenceRank_strictMono
    {E : Type*} [DecidableEq E]
    (event : E) (log : List E)
    (left right : EventOccurrence event log)
    (positionLt : left.1.1 < right.1.1) :
    eventOccurrenceRank event log left <
      eventOccurrenceRank event log right := by
  have prefixLe := logEventCount_take_mono event log
    (left.1.1 + 1) right.1.1 (by omega)
  have rightPrefixEq : log.take (right.1.1 + 1) =
      log.take right.1.1 ++ [event] := by
    calc
      log.take (right.1.1 + 1) =
          log.take right.1.1 ++ [log.get right.1] := by
            simp
      _ = log.take right.1.1 ++ [event] := by rw [right.2]
  unfold eventOccurrenceRank
  have rightCount :
      logEventCount event (log.take (right.1.1 + 1)) =
        logEventCount event (log.take right.1.1) + 1 := by
    simp [rightPrefixEq, logEventCount]
  rw [rightCount]
  omega

@[simp] theorem labelOccurrenceCount_reverse
    {E : Type*} [DecidableEq E] (event : E) (labels : List E) :
    labelOccurrenceCount event labels.reverse =
      labelOccurrenceCount event labels := by
  simp [labelOccurrenceCount]

/-- The parented deepest witness certificate rooted at one log occurrence. -/
noncomputable def occurrenceWitnessNodes
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (event : E) (log : List E)
    (occurrence : EventOccurrence event log) :
    List (ParentedWitnessNode E) :=
  deepestParentedWitnessScanReversed neighbors
    (event :: (log.take occurrence.1.1).reverse)

/-- The number of retained nodes carrying the root label is exactly the
one-based rank of the occurrence that generated the certificate. -/
theorem occurrenceWitnessNodes_root_count
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (event : E) (log : List E)
    (occurrence : EventOccurrence event log) :
    witnessScanLabelCount event
        (parentedEntries
          (occurrenceWitnessNodes neighbors event log occurrence)) =
      eventOccurrenceRank event log occurrence := by
  rw [occurrenceWitnessNodes,
    parentedEntries_deepestParentedWitnessScanReversed,
    deepestWitnessScanReversed_root_count]
  unfold eventOccurrenceRank
  have prefixEq : log.take (occurrence.1.1 + 1) =
      log.take occurrence.1.1 ++ [event] := by
    calc
      log.take (occurrence.1.1 + 1) =
          log.take occurrence.1.1 ++ [log.get occurrence.1] := by
            simp
      _ = log.take occurrence.1.1 ++ [event] := by rw [occurrence.2]
  rw [prefixEq]
  simp [labelOccurrenceCount, logEventCount, Nat.add_comm]

/-- Distinct occurrences of one event produce distinct parented witness
certificates. -/
theorem occurrenceWitnessNodes_injective
    {E : Type*} [DecidableEq E]
    (neighbors : E → Finset E) (event : E) (log : List E) :
    Function.Injective
      (occurrenceWitnessNodes neighbors event log) := by
  intro left right certificateEq
  apply Subtype.ext
  apply Fin.ext
  by_contra indexNe
  rcases lt_or_gt_of_ne indexNe with positionLt | positionLt
  · have rankLt := eventOccurrenceRank_strictMono
      event log left right positionLt
    have countEq := congrArg (fun nodes =>
      witnessScanLabelCount event (parentedEntries nodes)) certificateEq
    rw [occurrenceWitnessNodes_root_count] at countEq
    rw [occurrenceWitnessNodes_root_count] at countEq
    omega
  · have rankLt := eventOccurrenceRank_strictMono
      event log right left positionLt
    have countEq := congrArg (fun nodes =>
      witnessScanLabelCount event (parentedEntries nodes)) certificateEq
    rw [occurrenceWitnessNodes_root_count] at countEq
    rw [occurrenceWitnessNodes_root_count] at countEq
    omega

end TernarySyncAudit
