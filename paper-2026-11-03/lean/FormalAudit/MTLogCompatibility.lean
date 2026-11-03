import Mathlib
import FormalAudit.MoserTardosProcess

namespace TernarySyncAudit

/-- A chronological event list is compatible with a resampling table from a
given counter vector when, at every list entry, the current table assignment
violates that event and the counters are then advanced on its support. -/
def logCompatible
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (eventSet : E → Set (V → A))
    (table : V → ℕ → A) : (V → ℕ) → List E → Prop
  | _, [] => True
  | count, event :: rest =>
      (fun coordinate => table coordinate (count coordinate)) ∈ eventSet event ∧
        logCompatible support eventSet table
          (incrementSupport (support event) count) rest

@[simp] theorem logCompatible_nil
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (eventSet : E → Set (V → A))
    (table : V → ℕ → A) (count : V → ℕ) :
    logCompatible support eventSet table count [] := by
  simp [logCompatible]

@[simp] theorem logCompatible_cons
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (eventSet : E → Set (V → A))
    (table : V → ℕ → A) (count : V → ℕ) (event : E) (rest : List E) :
    logCompatible support eventSet table count (event :: rest) ↔
      (fun coordinate => table coordinate (count coordinate)) ∈ eventSet event ∧
        logCompatible support eventSet table
          (incrementSupport (support event) count) rest := by
  rfl

/-- Once halted, every bounded continuation stays fixed and emits the empty
log. -/
theorem mtRun_halted
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (steps : ℕ) (state : MTState V)
    (halted : state.halted = true) :
    mtRun support pick table steps state = (state, []) := by
  induction steps generalizing state with
  | zero => simp [mtRun]
  | succ steps inductionHypothesis =>
      rw [mtRun]
      rw [mtTransition_halted support pick table state halted]
      simp only
      rw [inductionHypothesis state halted]
      simp

/-- A transition emitting no event leaves the process halted. -/
theorem mtTransition_none_halted
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (state next : MTState V)
    (transition : mtTransition support pick table state = (next, none)) :
    next.halted = true := by
  unfold mtTransition at transition
  by_cases halted : state.halted = true
  · have stateEquality := congrArg Prod.fst transition
    simpa [halted] using congrArg MTState.halted stateEquality.symm
  · have notHalted : state.halted = false := by
      cases h : state.halted <;> simp_all
    simp only [notHalted, Bool.false_eq_true, ↓reduceIte] at transition
    split at transition
    · have nextEquality := congrArg Prod.fst transition
      simpa using congrArg MTState.halted nextEquality.symm
    · simp at transition

/-- The complete bounded MT execution log is compatible with the random
table.  This is the semantic half of the resampling-table argument, before
compressing logs into witness trees. -/
theorem mtRun_logCompatible
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (eventSet : E → Set (V → A))
    (pick : (V → A) → Option E)
    (pickSound : ∀ assignment event,
      pick assignment = some event → assignment ∈ eventSet event)
    (table : V → ℕ → A) (steps : ℕ) (state : MTState V) :
    logCompatible support eventSet table state.count
      (mtRun support pick table steps state).2 := by
  induction steps generalizing state with
  | zero => simp [mtRun]
  | succ steps inductionHypothesis =>
      cases transitionEq : mtTransition support pick table state with
      | mk next selected =>
          cases selected with
          | none =>
              have nextHalted := mtTransition_none_halted
                support pick table state next transitionEq
              rw [mtRun]
              simp only [transitionEq, Option.toList_none, List.nil_append]
              rw [mtRun_halted support pick table steps next nextHalted]
              simp
          | some event =>
              have bad := mtTransition_selected_is_bad
                support eventSet pick pickSound table state next event transitionEq
              have update := mtTransition_selected_state
                support pick table state next event transitionEq
              rw [mtRun]
              simp only [transitionEq, Option.toList_some, List.singleton_append]
              rw [logCompatible_cons]
              constructor
              · change (fun coordinate =>
                    table coordinate (state.count coordinate)) ∈ eventSet event at bad
                exact bad
              · rw [← update.1]
                exact inductionHypothesis next

/-- Starting from an active state, a bounded run that is still active after
all transitions must have resampled once at every transition. -/
theorem mtRun_active_log_length_eq_steps
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (steps : ℕ) (state : MTState V)
    (initialActive : state.halted = false)
    (finalActive :
      (mtRun support pick table steps state).1.halted = false) :
    (mtRun support pick table steps state).2.length = steps := by
  induction steps generalizing state with
  | zero => simp [mtRun]
  | succ steps inductionHypothesis =>
      cases transitionEq : mtTransition support pick table state with
      | mk next selected =>
          cases selected with
          | none =>
              have nextHalted := mtTransition_none_halted
                support pick table state next transitionEq
              have restHalted := mtRun_halted
                support pick table steps next nextHalted
              rw [mtRun] at finalActive
              simp only [transitionEq] at finalActive
              rw [restHalted] at finalActive
              rw [nextHalted] at finalActive
              simp at finalActive
          | some event =>
              have nextActive :=
                (mtTransition_selected_state
                  support pick table state next event transitionEq).2
              have restActive :
                  (mtRun support pick table steps next).1.halted = false := by
                rw [mtRun] at finalActive
                simpa [transitionEq] using finalActive
              have restLength := inductionHypothesis next nextActive restActive
              rw [mtRun]
              simp [transitionEq, restLength]

/-- Equivalently, an active run with fewer resamplings than its transition
budget has already halted. -/
theorem mtRun_short_log_implies_halted
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (steps : ℕ) (state : MTState V)
    (initialActive : state.halted = false)
    (shortLog : (mtRun support pick table steps state).2.length < steps) :
    (mtRun support pick table steps state).1.halted = true := by
  cases finalState : (mtRun support pick table steps state).1.halted with
  | false =>
      have fullLength := mtRun_active_log_length_eq_steps
        support pick table steps state initialActive finalState
      omega
  | true => rfl

/-- Counter evolution along an abstract compatible log is the same support
occurrence count used by the operational MT process. -/
theorem incrementSupport_fold_eq
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (initial : V → ℕ) (log : List E)
    (coordinate : V) :
    (log.foldl (fun count event => incrementSupport (support event) count)
      initial) coordinate =
      initial coordinate + supportOccurrenceCount support coordinate log := by
  induction log generalizing initial with
  | nil => simp
  | cons event rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      rw [supportOccurrenceCount_cons]
      by_cases inside : coordinate ∈ support event
      · simp [incrementSupport, inside]
        omega
      · simp [incrementSupport, inside]

/-- Pointwise form of log compatibility: the assignment seen at a list
position uses the initial row plus exactly the number of earlier occurrences
touching each coordinate. -/
theorem logCompatible_get
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (eventSet : E → Set (V → A))
    (table : V → ℕ → A) (initial : V → ℕ) (log : List E)
    (compatible : logCompatible support eventSet table initial log)
    (index : Fin log.length) :
    (fun coordinate => table coordinate
      (initial coordinate + supportOccurrenceCount support coordinate
        (log.take index.1))) ∈ eventSet (log.get index) := by
  induction log generalizing initial with
  | nil => exact Fin.elim0 index
  | cons event rest inductionHypothesis =>
      rw [logCompatible_cons] at compatible
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · simpa [supportOccurrenceCount] using compatible.1
      · have restBad := inductionHypothesis
          (initial := incrementSupport (support event) initial)
          compatible.2 tailIndex
        change (fun coordinate => table coordinate
          (initial coordinate + supportOccurrenceCount support coordinate
            ((event :: rest).take (tailIndex.1 + 1)))) ∈
              eventSet ((event :: rest).get (Fin.succ tailIndex))
        change (fun coordinate => table coordinate
          (incrementSupport (support event) initial coordinate +
            supportOccurrenceCount support coordinate
              (rest.take tailIndex.1))) ∈
                eventSet (rest.get tailIndex) at restBad
        have assignmentEquality :
            (fun coordinate => table coordinate
              (initial coordinate + supportOccurrenceCount support coordinate
                ((event :: rest).take (tailIndex.1 + 1)))) =
              (fun coordinate => table coordinate
                (incrementSupport (support event) initial coordinate +
                  supportOccurrenceCount support coordinate
                    (rest.take tailIndex.1))) := by
          funext coordinate
          apply congrArg (table coordinate)
          have takeConsEquality :
              (event :: rest).take (tailIndex.1 + 1) =
                event :: rest.take tailIndex.1 := by
            rfl
          rw [takeConsEquality]
          by_cases inside : coordinate ∈ support event
          · simp [incrementSupport, inside]
            omega
          · simp [incrementSupport, inside]
        rw [assignmentEquality]
        simpa using restBad

end TernarySyncAudit
