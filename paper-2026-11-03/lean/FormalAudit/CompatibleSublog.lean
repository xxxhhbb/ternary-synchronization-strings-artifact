import Mathlib
import FormalAudit.MTLogCompatibility
import FormalAudit.VariableIndependence

namespace TernarySyncAudit

/-- Pointwise badness at every occurrence, with the exact prefix counters,
is sufficient for semantic log compatibility. -/
theorem logCompatible_of_get
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (eventSet : E → Set (V → A))
    (table : V → ℕ → A) (initial : V → ℕ) (log : List E)
    (pointwise : ∀ index : Fin log.length,
      (fun coordinate => table coordinate
        (initial coordinate + supportOccurrenceCount support coordinate
          (log.take index.1))) ∈ eventSet (log.get index)) :
    logCompatible support eventSet table initial log := by
  induction log generalizing initial with
  | nil => simp
  | cons head rest inductionHypothesis =>
      rw [logCompatible_cons]
      constructor
      · simpa [supportOccurrenceCount] using pointwise ⟨0, by simp⟩
      · apply inductionHypothesis
        intro index
        have bad := pointwise (Fin.succ index)
        change (fun coordinate => table coordinate
          (incrementSupport (support head) initial coordinate +
            supportOccurrenceCount support coordinate
              (rest.take index.1))) ∈ eventSet (rest.get index)
        have assignmentEquality :
            (fun coordinate => table coordinate
              (incrementSupport (support head) initial coordinate +
                supportOccurrenceCount support coordinate
                  (rest.take index.1))) =
            (fun coordinate => table coordinate
              (initial coordinate + supportOccurrenceCount support coordinate
                ((head :: rest).take (index.1 + 1)))) := by
          funext coordinate
          apply congrArg (table coordinate)
          have takeCons :
              (head :: rest).take (index.1 + 1) =
                head :: rest.take index.1 := rfl
          rw [takeCons]
          by_cases inside : coordinate ∈ support head
          · simp [incrementSupport, inside]
            omega
          · simp [incrementSupport, inside]
        rw [assignmentEquality]
        simpa using bad

/-- An occurrence-wise embedding of a retained chronological sublog into an
original log, together with the exact counter equality on every retained
event support. -/
structure SupportCountLogEmbedding
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (original retained : List E) where
  position : Fin retained.length → Fin original.length
  label_eq : ∀ index,
    original.get (position index) = retained.get index
  support_count_eq : ∀ index coordinate,
    coordinate ∈ support (retained.get index) →
      supportOccurrenceCount support coordinate
          (original.take (position index).1) =
        supportOccurrenceCount support coordinate
          (retained.take index.1)

/-- Any retained sublog whose event-support counters agree occurrence by
occurrence inherits compatibility from the original log. -/
theorem SupportCountLogEmbedding.compatible
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate,
      DependsOn (event candidate) (support candidate))
    (table : V → ℕ → A) (initial : V → ℕ)
    (original retained : List E)
    (embedding : SupportCountLogEmbedding support original retained)
    (originalCompatible : logCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      table initial original) :
    logCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      table initial retained := by
  apply logCompatible_of_get
  intro index
  let originalAssignment : V → A := fun coordinate =>
    table coordinate
      (initial coordinate + supportOccurrenceCount support coordinate
        (original.take (embedding.position index).1))
  let retainedAssignment : V → A := fun coordinate =>
    table coordinate
      (initial coordinate + supportOccurrenceCount support coordinate
        (retained.take index.1))
  have originalBad : originalAssignment ∈
      event (original.get (embedding.position index)) := by
    exact logCompatible_get support
      (fun candidate => (event candidate : Set (V → A)))
      table initial original originalCompatible (embedding.position index)
  rw [embedding.label_eq index] at originalBad
  have agree : ∀ coordinate ∈ support (retained.get index),
      originalAssignment coordinate = retainedAssignment coordinate := by
    intro coordinate inside
    simp only [originalAssignment, retainedAssignment]
    rw [embedding.support_count_eq index coordinate inside]
  exact ((eventDepends (retained.get index))
    originalAssignment retainedAssignment agree).mp originalBad

end TernarySyncAudit
