import Mathlib

namespace TernarySyncAudit

/-- Per-variable read counters and a permanent halt flag for a resampling-table
execution. -/
structure MTState (V : Type*) where
  count : V → ℕ
  halted : Bool

/-- Current assignment obtained by reading each variable at its own counter. -/
def tableAssignment
    {V A : Type*} (table : V → ℕ → A) (state : MTState V) : V → A :=
  fun coordinate => table coordinate (state.count coordinate)

/-- Increment exactly the variables in one event support. -/
def incrementSupport
    {V : Type*} [DecidableEq V] (support : Finset V) (count : V → ℕ) :
    V → ℕ := fun coordinate =>
  if coordinate ∈ support then count coordinate + 1 else count coordinate

@[simp] theorem incrementSupport_inside
    {V : Type*} [DecidableEq V] (support : Finset V) (count : V → ℕ)
    {coordinate : V} (inside : coordinate ∈ support) :
    incrementSupport support count coordinate = count coordinate + 1 := by
  simp [incrementSupport, inside]

@[simp] theorem incrementSupport_outside
    {V : Type*} [DecidableEq V] (support : Finset V) (count : V → ℕ)
    {coordinate : V} (outside : coordinate ∉ support) :
    incrementSupport support count coordinate = count coordinate := by
  simp [incrementSupport, outside]

/-- One deterministic transition driven by an infinite independent-sample
table.  The returned option is the event resampled at this transition. -/
def mtTransition
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (state : MTState V) :
    MTState V × Option E :=
  if state.halted then
    (state, none)
  else
    match pick (tableAssignment table state) with
    | none => (⟨state.count, true⟩, none)
    | some event =>
        (⟨incrementSupport (support event) state.count, false⟩, some event)

/-- Run at most `steps` transitions and retain the chronological resampling
log. -/
def mtRun
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) : ℕ → MTState V → MTState V × List E
  | 0, state => (state, [])
  | steps + 1, state =>
      let transition := mtTransition support pick table state
      let rest := mtRun support pick table steps transition.1
      (rest.1, transition.2.toList ++ rest.2)

/-- A halted state is absorbing and emits no further log entries. -/
theorem mtTransition_halted
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (state : MTState V)
    (halted : state.halted = true) :
    mtTransition support pick table state = (state, none) := by
  simp [mtTransition, halted]

/-- Every transition either emits no event or exactly the event returned by
the picker on the pre-transition assignment. -/
theorem mtTransition_selected
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (state next : MTState V) (event : E)
    (transition : mtTransition support pick table state = (next, some event)) :
    state.halted = false ∧
      pick (tableAssignment table state) = some event := by
  unfold mtTransition at transition
  by_cases halted : state.halted = true
  · simp [halted] at transition
  · have notHalted : state.halted = false := by
      cases h : state.halted <;> simp_all
    simp only [notHalted, Bool.false_eq_true, ↓reduceIte] at transition
    split at transition
    · simp at transition
    · simp only [Prod.mk.injEq, Option.some.injEq] at transition
      rcases transition with ⟨rfl, rfl⟩
      exact ⟨notHalted, by assumption⟩

/-- A selected event increments precisely its support and leaves the process
active. -/
theorem mtTransition_selected_state
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (state next : MTState V) (event : E)
    (transition : mtTransition support pick table state = (next, some event)) :
    next.count = incrementSupport (support event) state.count ∧
      next.halted = false := by
  unfold mtTransition at transition
  by_cases halted : state.halted = true
  · simp [halted] at transition
  · have notHalted : state.halted = false := by
      cases h : state.halted <;> simp_all
    simp only [notHalted, Bool.false_eq_true, ↓reduceIte] at transition
    split at transition
    · simp at transition
    · simp only [Prod.mk.injEq, Option.some.injEq] at transition
      rcases transition with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

/-- A transition emitting no event never changes a read counter. -/
theorem mtTransition_none_count
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (state next : MTState V)
    (transition : mtTransition support pick table state = (next, none)) :
    next.count = state.count := by
  unfold mtTransition at transition
  by_cases halted : state.halted = true
  · have countEquality := congrArg (fun pair => pair.1.count) transition
    simpa [halted] using countEquality.symm
  · have notHalted : state.halted = false := by
      cases h : state.halted <;> simp_all
    simp only [notHalted, Bool.false_eq_true, ↓reduceIte] at transition
    split at transition
    · have countEquality := congrArg (fun pair => pair.1.count) transition
      simpa using countEquality.symm
    · simp at transition

/-- If the picker is sound, every logged event is genuinely violated by the
assignment immediately before it is resampled. -/
theorem mtTransition_selected_is_bad
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (eventSet : E → Set (V → A))
    (pick : (V → A) → Option E)
    (pickSound : ∀ assignment event,
      pick assignment = some event → assignment ∈ eventSet event)
    (table : V → ℕ → A) (state next : MTState V) (event : E)
    (transition : mtTransition support pick table state = (next, some event)) :
    tableAssignment table state ∈ eventSet event := by
  exact pickSound _ _ (mtTransition_selected support pick table state next event
    transition).2

/-- The number of emitted resamplings never exceeds the transition budget. -/
theorem mtRun_log_length_le
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (steps : ℕ) (state : MTState V) :
    (mtRun support pick table steps state).2.length ≤ steps := by
  induction steps generalizing state with
  | zero => simp [mtRun]
  | succ steps inductionHypothesis =>
      cases transitionEq : mtTransition support pick table state with
      | mk next selected =>
          have restBound := inductionHypothesis next
          cases selected with
          | none =>
              simp only [mtRun, transitionEq, Option.toList_none,
                List.nil_append]
              exact restBound.trans (Nat.le_succ steps)
          | some event =>
              simp only [mtRun, transitionEq, Option.toList_some,
                List.singleton_append, List.length_cons]
              exact Nat.succ_le_succ restBound

/-- Number of entries of a log whose supports contain one variable. -/
def supportOccurrenceCount
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (coordinate : V) (log : List E) : ℕ :=
  (log.filter fun event => decide (coordinate ∈ support event)).length

@[simp] theorem supportOccurrenceCount_nil
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (coordinate : V) :
    supportOccurrenceCount support coordinate [] = 0 := by
  simp [supportOccurrenceCount]

@[simp] theorem supportOccurrenceCount_cons
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (coordinate : V) (event : E) (log : List E) :
    supportOccurrenceCount support coordinate (event :: log) =
      supportOccurrenceCount support coordinate log +
        if coordinate ∈ support event then 1 else 0 := by
  by_cases inside : coordinate ∈ support event <;>
    simp [supportOccurrenceCount, inside, Nat.add_comm]

theorem supportOccurrenceCount_le_length
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (coordinate : V) (log : List E) :
    supportOccurrenceCount support coordinate log ≤ log.length := by
  unfold supportOccurrenceCount
  exact List.length_filter_le _ _

/-- Exact counter accounting: the final counter is the initial counter plus
the number of logged resamplings touching that variable. -/
theorem mtRun_count_eq
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (steps : ℕ) (state : MTState V)
    (coordinate : V) :
    (mtRun support pick table steps state).1.count coordinate =
      state.count coordinate +
        supportOccurrenceCount support coordinate
          (mtRun support pick table steps state).2 := by
  induction steps generalizing state with
  | zero => simp [mtRun]
  | succ steps inductionHypothesis =>
      cases transitionEq : mtTransition support pick table state with
      | mk next selected =>
          have restCount := inductionHypothesis next
          cases selected with
          | none =>
              simp only [mtRun, transitionEq, Option.toList_none,
                List.nil_append]
              rw [restCount,
                mtTransition_none_count support pick table state next transitionEq]
          | some event =>
              simp only [mtRun, transitionEq, Option.toList_some,
                List.singleton_append,
                supportOccurrenceCount_cons]
              rw [restCount]
              have update := mtTransition_selected_state
                support pick table state next event transitionEq
              rw [update.1]
              by_cases inside : coordinate ∈ support event
              · simp [incrementSupport, inside]
                omega
              · simp [incrementSupport, inside]

/-- No variable consumes more than one fresh table cell per transition. -/
theorem mtRun_count_le
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (steps : ℕ) (state : MTState V)
    (coordinate : V) :
    (mtRun support pick table steps state).1.count coordinate ≤
      state.count coordinate + steps := by
  rw [mtRun_count_eq]
  have occurrenceBound := supportOccurrenceCount_le_length support coordinate
    (mtRun support pick table steps state).2
  have logBound := mtRun_log_length_le support pick table steps state
  omega

end TernarySyncAudit
