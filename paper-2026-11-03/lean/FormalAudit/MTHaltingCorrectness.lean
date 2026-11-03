import Mathlib
import FormalAudit.MTLogCompatibility
import FormalAudit.ConcreteMTProcess

namespace TernarySyncAudit

/-- If an active transition emits no event, the picker found no violated
event and the counter vector is unchanged. -/
theorem mtTransition_active_none
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (state next : MTState V)
    (active : state.halted = false)
    (transition : mtTransition support pick table state = (next, none)) :
    pick (tableAssignment table state) = none ∧
      next.count = state.count ∧ next.halted = true := by
  unfold mtTransition at transition
  simp only [active, Bool.false_eq_true, ↓reduceIte] at transition
  cases pickerEq : pick (tableAssignment table state) with
  | none =>
      have nextEq : next = ⟨state.count, true⟩ := by
        have stateEq := congrArg Prod.fst transition
        simpa [pickerEq] using stateEq.symm
      subst next
      exact ⟨rfl, rfl, rfl⟩
  | some event => simp [pickerEq] at transition

/-- A bounded run that starts active and ends halted has a final assignment
on which the picker returns no event. -/
theorem mtRun_halted_pick_none
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (pick : (V → A) → Option E)
    (table : V → ℕ → A) (steps : ℕ) (state : MTState V)
    (initialActive : state.halted = false)
    (finalHalted :
      (mtRun support pick table steps state).1.halted = true) :
    pick (tableAssignment table
      (mtRun support pick table steps state).1) = none := by
  induction steps generalizing state with
  | zero =>
      simp only [mtRun] at finalHalted ⊢
      simp_all
  | succ remaining inductionHypothesis =>
      cases transitionEq : mtTransition support pick table state with
      | mk next selected =>
          cases selected with
          | none =>
              have transitionFacts := mtTransition_active_none
                support pick table state next initialActive transitionEq
              have restHalted := mtRun_halted support pick table
                remaining next transitionFacts.2.2
              rw [mtRun]
              simp only [transitionEq]
              rw [restHalted]
              have assignmentEq : tableAssignment table next =
                  tableAssignment table state := by
                funext coordinate
                simp [tableAssignment, transitionFacts.2.1]
              rw [assignmentEq]
              exact transitionFacts.1
          | some event =>
              have nextActive := (mtTransition_selected_state
                support pick table state next event transitionEq).2
              have restHalted :
                  (mtRun support pick table remaining next).1.halted = true := by
                rw [mtRun] at finalHalted
                simpa [transitionEq] using finalHalted
              rw [mtRun]
              simp only [transitionEq]
              exact inductionHypothesis next nextActive restHalted

/-- In the concrete synchronization-string instance, halting means that the
final branch vector avoids every long-interval bad event. -/
theorem concreteMTRun_halted_avoids
    (N : ℕ) (outer : ℕ → Symbol)
    (table : Fin N → ℕ → Choice) (steps : ℕ)
    (halted : (concreteMTRun N outer table steps).1.halted = true) :
    tableAssignment table (concreteMTRun N outer table steps).1 ∈
      avoidOutcomes (longIntervalEvent N outer)
        (Finset.univ : Finset (LongIntervalIndex N)) := by
  rw [← firstViolatedLongInterval_none_iff_avoids]
  exact mtRun_halted_pick_none
    (longIntervalSupport N) (firstViolatedLongInterval N outer)
      table steps (initialMTState N) rfl halted

end TernarySyncAudit
