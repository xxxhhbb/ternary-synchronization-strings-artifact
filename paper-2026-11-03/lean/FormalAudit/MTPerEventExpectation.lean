import Mathlib
import FormalAudit.FixedHeightOccurrenceShape
import FormalAudit.FiniteExpectationCertificates

namespace TernarySyncAudit

/-- The subtype of occurrences of one label has cardinality equal to the
filter-based occurrence counter used by the MT development. -/
theorem eventOccurrence_card
    {E : Type*} [DecidableEq E] (event : E) (log : List E) :
    Fintype.card (EventOccurrence event log) = logEventCount event log := by
  classical
  rw [Fintype.card_subtype]
  have countEq : logEventCount event log = log.count event := by
    induction log with
    | nil => simp
    | cons head tail inductionHypothesis =>
        rw [logEventCount_cons, List.count_cons, inductionHypothesis]
        by_cases equality : head = event
        · subst head
          simp
        · simp [equality]
  have vectorCount := Fin.card_filter_univ_eq_vector_get_eq_count event
    (⟨log, rfl⟩ : List.Vector E log.length)
  rw [countEq]
  simpa [List.Vector.get_eq_get_toList] using vectorCount

/-- Generic finite-table, fixed-height per-event Moser--Tardos expectation
bound.  Every hypothesis is operational or an explicit asymmetric-LLL
inequality; no probabilistic independence is left implicit. -/
theorem uniformLogEventExpectation_le_charge_ratio
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate,
      DependsOn (event candidate) (support candidate))
    (neighbors : E → Finset E)
    (overlapDependent : ∀ left right,
      ¬Disjoint (support left) (support right) →
        left ∈ closedNeighbors neighbors right)
    (charge : E → ℝ)
    (chargeNonnegative : ∀ candidate, 0 ≤ charge candidate)
    (chargeLtOne : ∀ candidate, charge candidate < 1)
    (selfNotNeighbor : ∀ candidate, candidate ∉ neighbors candidate)
    (criterion : ∀ candidate,
      uniformFinsetMass (event candidate) ≤
        charge candidate *
          ∏ child ∈ neighbors candidate, (1 - charge child))
    (rows height : ℕ) (default : A)
    (log : ((V × Fin rows) → A) → List E)
    (logLength : ∀ table, (log table).length ≤ height)
    (logRows : ∀ table, (log table).length ≤ rows)
    (compatible : ∀ table, logCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      (extendBoundedTable rows default table) (fun _ => 0) (log table))
    (root : E) :
    uniformExpectation (fun table =>
      (logEventCount root (log table) : ℝ)) ≤
        charge root / (1 - charge root) := by
  classical
  let certificates := properWitnessShapes neighbors (height + 1) root
  let certificateEvent := fun shape :
      ProperWitnessShape neighbors (height + 1) root =>
    chronologicalProperWitnessShapeCompatibilityEvent support event neighbors
      rows (height + 1) root shape
  have pointwise : ∀ table,
      logEventCount root (log table) ≤
        (certificates.filter fun shape =>
          table ∈ certificateEvent shape).card := by
    intro table
    let Occurrence := EventOccurrence root (log table)
    let CompatibleShape := {shape :
        ProperWitnessShape neighbors (height + 1) root //
      shape ∈ certificates ∧ table ∈ certificateEvent shape}
    let encode : Occurrence → CompatibleShape := fun occurrence =>
      ⟨occurrenceWitnessShapeAt neighbors height root (log table) occurrence,
        mem_properWitnessShapes neighbors (height + 1) root _,
        occurrence_table_mem_chronologicalShapeEventAt
          support event eventDepends neighbors overlapDependent
          rows height default table (log table) (logLength table)
          (logRows table) (compatible table) root occurrence⟩
    have encodeInjective : Function.Injective encode := by
      intro left right equality
      apply occurrenceWitnessShapeAt_injective neighbors height root (log table)
        (logLength table)
      exact congrArg Subtype.val equality
    have cardLe : Fintype.card Occurrence ≤ Fintype.card CompatibleShape :=
      Fintype.card_le_of_injective encode encodeInjective
    have occurrenceCard : Fintype.card Occurrence =
        logEventCount root (log table) := eventOccurrence_card root (log table)
    have shapeCard : Fintype.card CompatibleShape =
        (certificates.filter fun shape =>
          table ∈ certificateEvent shape).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext shape
      simp [certificates, certificateEvent]
    rw [occurrenceCard, shapeCard] at cardLe
    exact cardLe
  have eventMassBound : ∀ shape ∈ certificates,
      uniformFinsetMass (certificateEvent shape) ≤
        properWitnessShapeMass
          (fun candidate => uniformFinsetMass (event candidate))
          neighbors (height + 1) root shape := by
    intro shape shapeMember
    by_cases lengthBound :
        (chronologicalProperWitnessShapeLog neighbors (height + 1) root
          shape).length ≤ rows
    · rw [chronologicalProperWitnessShapeCompatibilityEvent_mass
          support event eventDepends neighbors rows (height + 1) root shape
            lengthBound]
    · have emptyEvent : certificateEvent shape = ∅ := by
        simp [certificateEvent,
          chronologicalProperWitnessShapeCompatibilityEvent, lengthBound]
      rw [emptyEvent]
      simp only [uniformFinsetMass, Finset.card_empty, Nat.cast_zero,
        zero_div]
      exact properWitnessShapeMass_nonnegative
        (fun candidate => uniformFinsetMass (event candidate)) neighbors
        (fun candidate => uniformFinsetMass_nonnegative _)
        (height + 1) root shape
  calc
    uniformExpectation (fun table =>
        (logEventCount root (log table) : ℝ)) ≤
      ∑ shape ∈ certificates,
        properWitnessShapeMass
          (fun candidate => uniformFinsetMass (event candidate))
          neighbors (height + 1) root shape :=
      uniformExpectation_le_certificate_weights certificates certificateEvent
        (fun table => logEventCount root (log table))
        (fun shape => properWitnessShapeMass
          (fun candidate => uniformFinsetMass (event candidate))
          neighbors (height + 1) root shape)
        pointwise eventMassBound
    _ ≤ charge root / (1 - charge root) :=
      sum_properWitnessShapeMass_le_charge_ratio
        (fun candidate => uniformFinsetMass (event candidate))
        charge neighbors
        (fun candidate => uniformFinsetMass_nonnegative _)
        chargeNonnegative chargeLtOne selfNotNeighbor criterion
        (height + 1) root

end TernarySyncAudit
