import Mathlib
import FormalAudit.ProperWitnessShape

namespace TernarySyncAudit

/-- A deterministic chronological linearization of a proper witness shape:
all recursively earlier child subtrees precede their parent.  The arbitrary
finite child-slot order only permutes mutually unordered branches. -/
noncomputable def properWitnessShapeLog
    {E : Type*} [Fintype E] [DecidableEq E]
    (neighbors : E → Finset E) :
    ∀ height event,
      ProperWitnessShape neighbors height event → List E
  | 0, _, shape => nomatch shape
  | height + 1, event, children =>
      (Finset.univ.toList.map (fun child =>
        match children child with
        | none => []
        | some subtree =>
            properWitnessShapeLog neighbors height child.1 subtree)).flatten ++
        [event]

/-- Product over `Fin log.length` is the ordinary product of the mapped
list. -/
theorem fin_product_get_eq_list_product
    {E : Type*} (mass : E → ℝ) (log : List E) :
    (∏ index : Fin log.length, mass (log.get index)) =
      (log.map mass).prod := by
  rw [← List.prod_ofFn]
  congr 1
  simp

/-- The product of node masses in the deterministic linearization is exactly
the recursively defined proper-shape mass. -/
theorem properWitnessShapeLog_mass
    {E : Type*} [Fintype E] [DecidableEq E]
    (eventMass : E → ℝ) (neighbors : E → Finset E) :
    ∀ height event (shape : ProperWitnessShape neighbors height event),
      ((properWitnessShapeLog neighbors height event shape).map
        eventMass).prod =
      properWitnessShapeMass eventMass neighbors height event shape := by
  intro height
  induction height with
  | zero =>
      intro event shape
      exact PEmpty.elim shape
  | succ height inductionHypothesis =>
      intro event children
      classical
      simp only [properWitnessShapeLog, List.map_append, List.map_singleton,
        List.prod_append, List.prod_singleton, properWitnessShapeMass]
      rw [mul_comm]
      congr 1
      rw [List.map_flatten, List.prod_flatten]
      simp only [List.map_map]
      rw [Finset.prod_map_toList]
      apply Finset.prod_congr rfl
      intro child childMember
      cases childEq : children child with
      | none => simp [childEq]
      | some subtree =>
          simp [childEq, inductionHypothesis child.1 subtree]

/-- Consequently the exact canonical fixed-log mass product attached to a
shape equals its witness-tree mass. -/
theorem properWitnessShapeLog_fin_mass
    {E : Type*} [Fintype E] [DecidableEq E]
    (eventMass : E → ℝ) (neighbors : E → Finset E)
    (height : ℕ) (event : E)
    (shape : ProperWitnessShape neighbors height event) :
    (∏ index : Fin
        (properWitnessShapeLog neighbors height event shape).length,
      eventMass
        ((properWitnessShapeLog neighbors height event shape).get index)) =
      properWitnessShapeMass eventMass neighbors height event shape := by
  rw [fin_product_get_eq_list_product]
  exact properWitnessShapeLog_mass
    eventMass neighbors height event shape

end TernarySyncAudit
