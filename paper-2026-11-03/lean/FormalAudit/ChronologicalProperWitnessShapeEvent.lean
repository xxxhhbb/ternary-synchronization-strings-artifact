import Mathlib
import FormalAudit.ProperWitnessShapeEvent
import FormalAudit.ChronologicalProperWitnessShape

namespace TernarySyncAudit

/-- Finite-table compatibility event for the canonical chronological log of
one proper witness shape. -/
noncomputable def chronologicalProperWitnessShapeCompatibilityEvent
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (neighbors : E → Finset E) (rows height : ℕ) (root : E)
    (shape : ProperWitnessShape neighbors height root) :
    Finset ((V × Fin rows) → A) := by
  classical
  let log := chronologicalProperWitnessShapeLog
    neighbors height root shape
  exact if lengthBound : log.length ≤ rows then
    boundedLogCompatibilityEvent support event log rows lengthBound
  else ∅

/-- Exact mass of a chronological shape event when its log fits. -/
theorem chronologicalProperWitnessShapeCompatibilityEvent_mass
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate,
      DependsOn (event candidate) (support candidate))
    (neighbors : E → Finset E) (rows height : ℕ) (root : E)
    (shape : ProperWitnessShape neighbors height root)
    (lengthBound :
      (chronologicalProperWitnessShapeLog
        neighbors height root shape).length ≤ rows) :
    uniformFinsetMass
        (chronologicalProperWitnessShapeCompatibilityEvent support event
          neighbors rows height root shape) =
      properWitnessShapeMass
        (fun candidate => uniformFinsetMass (event candidate))
        neighbors height root shape := by
  classical
  rw [chronologicalProperWitnessShapeCompatibilityEvent]
  simp only [lengthBound, dite_true]
  rw [boundedLogCompatibilityEvent_mass support event eventDepends]
  exact chronologicalProperWitnessShapeLog_fin_mass
    (fun candidate => uniformFinsetMass (event candidate))
      neighbors height root shape

/-- Union of all chronological proper-shape compatibility events of fixed
height and root. -/
noncomputable def chronologicalProperWitnessShapeCompatibilityUnion
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (neighbors : E → Finset E) (rows height : ℕ) (root : E) :
    Finset ((V × Fin rows) → A) :=
  (properWitnessShapes neighbors height root).biUnion fun shape =>
    chronologicalProperWitnessShapeCompatibilityEvent support event neighbors
      rows height root shape

/-- The chronological compatibility union is bounded by the total recursive
shape mass. -/
theorem chronologicalProperWitnessShapeCompatibilityUnion_mass_le_sum
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate,
      DependsOn (event candidate) (support candidate))
    (neighbors : E → Finset E) (rows height : ℕ) (root : E) :
    uniformFinsetMass
        (chronologicalProperWitnessShapeCompatibilityUnion support event
          neighbors rows height root) ≤
      ∑ shape ∈ properWitnessShapes neighbors height root,
        properWitnessShapeMass
          (fun candidate => uniformFinsetMass (event candidate))
          neighbors height root shape := by
  classical
  rw [chronologicalProperWitnessShapeCompatibilityUnion]
  calc
    uniformFinsetMass
        ((properWitnessShapes neighbors height root).biUnion fun shape =>
          chronologicalProperWitnessShapeCompatibilityEvent support event
            neighbors rows height root shape) ≤
      ∑ shape ∈ properWitnessShapes neighbors height root,
        uniformFinsetMass
          (chronologicalProperWitnessShapeCompatibilityEvent support event
            neighbors rows height root shape) :=
      uniformFinsetMass_biUnion_le_sum _ _
    _ ≤ ∑ shape ∈ properWitnessShapes neighbors height root,
        properWitnessShapeMass
          (fun candidate => uniformFinsetMass (event candidate))
          neighbors height root shape := by
      apply Finset.sum_le_sum
      intro shape shapeMember
      by_cases lengthBound :
          (chronologicalProperWitnessShapeLog
            neighbors height root shape).length ≤ rows
      · rw [chronologicalProperWitnessShapeCompatibilityEvent_mass
            support event eventDepends neighbors rows height root shape
              lengthBound]
      · have emptyEvent :
            chronologicalProperWitnessShapeCompatibilityEvent support event
              neighbors rows height root shape = ∅ := by
            simp [chronologicalProperWitnessShapeCompatibilityEvent,
              lengthBound]
        rw [emptyEvent]
        simp only [uniformFinsetMass, Finset.card_empty, Nat.cast_zero,
          zero_div]
        exact properWitnessShapeMass_nonnegative
          (fun candidate => uniformFinsetMass (event candidate)) neighbors
          (fun candidate => uniformFinsetMass_nonnegative _) height root shape

/-- Under the asymmetric LLL criterion, the entire chronological proper-shape
union has mass at most the standard Moser--Tardos charge ratio. -/
theorem chronologicalProperWitnessShapeCompatibilityUnion_mass_le_charge_ratio
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
        (chronologicalProperWitnessShapeCompatibilityUnion support event
          neighbors rows height root) ≤
      charge root / (1 - charge root) := by
  calc
    uniformFinsetMass
        (chronologicalProperWitnessShapeCompatibilityUnion support event
          neighbors rows height root) ≤
      ∑ shape ∈ properWitnessShapes neighbors height root,
        properWitnessShapeMass
          (fun candidate => uniformFinsetMass (event candidate))
          neighbors height root shape :=
      chronologicalProperWitnessShapeCompatibilityUnion_mass_le_sum
        support event eventDepends neighbors rows height root
    _ ≤ charge root / (1 - charge root) :=
      sum_properWitnessShapeMass_le_charge_ratio
        (fun candidate => uniformFinsetMass (event candidate))
        charge neighbors
        (fun candidate => uniformFinsetMass_nonnegative _)
        chargeNonnegative chargeLtOne selfNotNeighbor criterion height root

end TernarySyncAudit
