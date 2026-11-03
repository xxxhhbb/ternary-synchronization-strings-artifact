import Mathlib
import FormalAudit.BoundedLogProbability
import FormalAudit.ProperWitnessShapeLog

namespace TernarySyncAudit

/-- A bounded-table compatibility event for one proper witness shape.  Shapes
whose deterministic linearization does not fit in the table are assigned the
empty event. -/
noncomputable def properWitnessShapeCompatibilityEvent
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (neighbors : E → Finset E) (rows height : ℕ) (root : E)
    (shape : ProperWitnessShape neighbors height root) :
    Finset ((V × Fin rows) → A) := by
  classical
  let log := properWitnessShapeLog neighbors height root shape
  exact if lengthBound : log.length ≤ rows then
    boundedLogCompatibilityEvent support event log rows lengthBound
  else ∅

/-- If the shape fits in the table, its compatibility-event mass is exactly
the recursive product of its node event masses. -/
theorem properWitnessShapeCompatibilityEvent_mass
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate,
      DependsOn (event candidate) (support candidate))
    (neighbors : E → Finset E) (rows height : ℕ) (root : E)
    (shape : ProperWitnessShape neighbors height root)
    (lengthBound :
      (properWitnessShapeLog neighbors height root shape).length ≤ rows) :
    uniformFinsetMass
        (properWitnessShapeCompatibilityEvent support event neighbors
          rows height root shape) =
      properWitnessShapeMass
        (fun candidate => uniformFinsetMass (event candidate))
        neighbors height root shape := by
  classical
  rw [properWitnessShapeCompatibilityEvent]
  simp only [lengthBound, dite_true]
  rw [boundedLogCompatibilityEvent_mass support event eventDepends]
  exact properWitnessShapeLog_fin_mass
    (fun candidate => uniformFinsetMass (event candidate))
      neighbors height root shape

/-- Recursive proper-shape mass is nonnegative when every node mass is. -/
theorem properWitnessShapeMass_nonnegative
    {E : Type*} [DecidableEq E]
    (eventMass : E → ℝ) (neighbors : E → Finset E)
    (massNonnegative : ∀ candidate, 0 ≤ eventMass candidate) :
    ∀ height root (shape : ProperWitnessShape neighbors height root),
      0 ≤ properWitnessShapeMass eventMass neighbors height root shape := by
  intro height
  induction height with
  | zero =>
      intro root shape
      exact PEmpty.elim shape
  | succ height inductionHypothesis =>
      intro root children
      simp only [properWitnessShapeMass]
      apply mul_nonneg (massNonnegative root)
      apply Finset.prod_nonneg
      intro child childMember
      cases childEq : children child with
      | none => simp
      | some subtree =>
          simpa [childEq] using
            inductionHypothesis child.1 subtree

/-- Finite union bound stated directly for uniform finite probability. -/
theorem uniformFinsetMass_biUnion_le_sum
    {Ω C : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    [DecidableEq C]
    (certificates : Finset C) (certificateEvent : C → Finset Ω) :
    uniformFinsetMass (certificates.biUnion certificateEvent) ≤
      ∑ certificate ∈ certificates,
        uniformFinsetMass (certificateEvent certificate) := by
  classical
  unfold uniformFinsetMass
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_biUnion_le
  · positivity

/-- Union of the bounded-table compatibility events over every explicitly
enumerated proper shape of fixed height and root. -/
noncomputable def properWitnessShapeCompatibilityUnion
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (neighbors : E → Finset E) (rows height : ℕ) (root : E) :
    Finset ((V × Fin rows) → A) :=
  (properWitnessShapes neighbors height root).biUnion fun shape =>
    properWitnessShapeCompatibilityEvent support event neighbors
      rows height root shape

/-- The complete finite union of compatible proper shapes is bounded by the
sum of their recursive masses. -/
theorem properWitnessShapeCompatibilityUnion_mass_le_sum
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate,
      DependsOn (event candidate) (support candidate))
    (neighbors : E → Finset E) (rows height : ℕ) (root : E) :
    uniformFinsetMass
        (properWitnessShapeCompatibilityUnion support event neighbors
          rows height root) ≤
      ∑ shape ∈ properWitnessShapes neighbors height root,
        properWitnessShapeMass
          (fun candidate => uniformFinsetMass (event candidate))
          neighbors height root shape := by
  classical
  rw [properWitnessShapeCompatibilityUnion]
  calc
    uniformFinsetMass
        ((properWitnessShapes neighbors height root).biUnion fun shape =>
          properWitnessShapeCompatibilityEvent support event neighbors
            rows height root shape) ≤
      ∑ shape ∈ properWitnessShapes neighbors height root,
        uniformFinsetMass
          (properWitnessShapeCompatibilityEvent support event neighbors
            rows height root shape) :=
      uniformFinsetMass_biUnion_le_sum _ _
    _ ≤ ∑ shape ∈ properWitnessShapes neighbors height root,
        properWitnessShapeMass
          (fun candidate => uniformFinsetMass (event candidate))
          neighbors height root shape := by
      apply Finset.sum_le_sum
      intro shape shapeMember
      by_cases lengthBound :
          (properWitnessShapeLog neighbors height root shape).length ≤ rows
      · rw [properWitnessShapeCompatibilityEvent_mass
            support event eventDepends neighbors rows height root shape
              lengthBound]
      · have emptyEvent :
            properWitnessShapeCompatibilityEvent support event neighbors
              rows height root shape = ∅ := by
            simp [properWitnessShapeCompatibilityEvent, lengthBound]
        rw [emptyEvent]
        simp only [uniformFinsetMass, Finset.card_empty, Nat.cast_zero,
          zero_div]
        exact properWitnessShapeMass_nonnegative
          (fun candidate => uniformFinsetMass (event candidate)) neighbors
          (fun candidate => uniformFinsetMass_nonnegative _) height root shape

/-- Under the asymmetric LLL criterion, the entire compatible-shape union has
mass at most the standard charge ratio. -/
theorem properWitnessShapeCompatibilityUnion_mass_le_charge_ratio
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate,
      DependsOn (event candidate) (support candidate))
    (charge : E → ℝ) (neighbors : E → Finset E)
    (chargeNonnegative : ∀ candidate, 0 ≤ charge candidate)
    (chargeLtOne : ∀ candidate, charge candidate < 1)
    (selfNotNeighbor : ∀ candidate, candidate ∉ neighbors candidate)
    (criterion : ∀ candidate,
      uniformFinsetMass (event candidate) ≤
        charge candidate *
          ∏ child ∈ neighbors candidate, (1 - charge child))
    (rows height : ℕ) (root : E) :
    uniformFinsetMass
        (properWitnessShapeCompatibilityUnion support event neighbors
          rows height root) ≤
      charge root / (1 - charge root) := by
  calc
    uniformFinsetMass
        (properWitnessShapeCompatibilityUnion support event neighbors
          rows height root) ≤
      ∑ shape ∈ properWitnessShapes neighbors height root,
        properWitnessShapeMass
          (fun candidate => uniformFinsetMass (event candidate))
          neighbors height root shape :=
      properWitnessShapeCompatibilityUnion_mass_le_sum
        support event eventDepends neighbors rows height root
    _ ≤ charge root / (1 - charge root) :=
      sum_properWitnessShapeMass_le_charge_ratio
        (fun candidate => uniformFinsetMass (event candidate))
        charge neighbors
        (fun candidate => uniformFinsetMass_nonnegative _)
        chargeNonnegative chargeLtOne selfNotNeighbor criterion height root

end TernarySyncAudit
