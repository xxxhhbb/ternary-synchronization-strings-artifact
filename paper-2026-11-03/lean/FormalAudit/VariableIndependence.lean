import Mathlib
import FormalAudit.FiniteLLLModel

namespace TernarySyncAudit

open Finset

/-- A finite event is determined by the coordinates in `support`. -/
def DependsOn
    {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (event : Finset (V → A)) (support : Finset V) : Prop :=
  ∀ x y, (∀ v ∈ support, x v = y v) → (x ∈ event ↔ y ∈ event)

/-- A finite event is determined by coordinates outside `support`. -/
def DependsOutside
    {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (event : Finset (V → A)) (support : Finset V) : Prop :=
  ∀ x y, (∀ v, v ∉ support → x v = y v) → (x ∈ event ↔ y ∈ event)

abbrev InsideCoordinate {V : Type*} [DecidableEq V] (support : Finset V) :=
  {v : V // v ∈ support}

abbrev OutsideCoordinate {V : Type*} [DecidableEq V] (support : Finset V) :=
  {v : V // v ∉ support}

/-- Assemble assignments on a support and its complement. -/
def assembleCoordinates
    {V A : Type*} [DecidableEq V] (support : Finset V)
    (inside : InsideCoordinate support → A)
    (outside : OutsideCoordinate support → A) : V → A := fun v =>
  if h : v ∈ support then inside ⟨v, h⟩ else outside ⟨v, h⟩

/-- The coordinate split is a genuine equivalence, including empty support or complement. -/
def coordinateSplitEquiv
    {V A : Type*} [DecidableEq V] (support : Finset V) :
    ((InsideCoordinate support → A) × (OutsideCoordinate support → A)) ≃ (V → A) where
  toFun pair := assembleCoordinates support pair.1 pair.2
  invFun assignment := (fun v => assignment v.1, fun v => assignment v.1)
  left_inv pair := by
    rcases pair with ⟨inside, outside⟩
    apply Prod.ext <;> funext v
    · simp [assembleCoordinates, v.2]
    · simp [assembleCoordinates, v.2]
  right_inv assignment := by
    funext v
    by_cases hv : v ∈ support
    · simp [assembleCoordinates, hv]
    · simp [assembleCoordinates, hv]

/-- Uniform mass is invariant under an equivalence of finite sample spaces. -/
theorem uniformFinsetMass_preimage_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (equiv : α ≃ β) (event : Finset β) :
    uniformFinsetMass (Finset.univ.filter fun x : α => equiv x ∈ event) =
      uniformFinsetMass event := by
  let preimage := Finset.univ.filter fun x : α => equiv x ∈ event
  have imageEquality : preimage.image equiv = event := by
    ext y
    constructor
    · rintro hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.mp hx).2
    · intro hy
      apply Finset.mem_image.mpr
      refine ⟨equiv.symm y, ?_, by simp⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa⟩
  have cardEquality : preimage.card = event.card := by
    rw [← imageEquality]
    symm
    exact Finset.card_image_of_injective preimage equiv.injective
  have domainCard : Fintype.card α = Fintype.card β := Fintype.card_congr equiv
  unfold uniformFinsetMass
  rw [show (Finset.univ.filter fun x : α => equiv x ∈ event) = preimage from rfl,
    cardEquality, domainCard]

/-- Events depending on separate factors of a finite product are independent. -/
theorem uniform_product_independence
    {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (left right : Finset (I × O))
    (leftInvariant : ∀ i o₁ o₂, ((i, o₁) ∈ left ↔ (i, o₂) ∈ left))
    (rightInvariant : ∀ o i₁ i₂, ((i₁, o) ∈ right ↔ (i₂, o) ∈ right)) :
    uniformFinsetMass (left ∩ right) =
      uniformFinsetMass left * uniformFinsetMass right := by
  classical
  let defaultI : I := Classical.choice inferInstance
  let defaultO : O := Classical.choice inferInstance
  let leftSlice : Finset I := Finset.univ.filter fun i => (i, defaultO) ∈ left
  let rightSlice : Finset O := Finset.univ.filter fun o => (defaultI, o) ∈ right
  have leftEquality : left = leftSlice ×ˢ (Finset.univ : Finset O) := by
    ext pair
    simp only [leftSlice, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa using leftInvariant pair.1 pair.2 defaultO
  have rightEquality : right = (Finset.univ : Finset I) ×ˢ rightSlice := by
    ext pair
    simp only [rightSlice, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa using rightInvariant pair.2 pair.1 defaultI
  have intersectionEquality :
      (leftSlice ×ˢ (Finset.univ : Finset O)) ∩
          ((Finset.univ : Finset I) ×ˢ rightSlice) =
        leftSlice ×ˢ rightSlice := by
    ext pair
    simp
  rw [leftEquality, rightEquality, intersectionEquality]
  unfold uniformFinsetMass
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_prod]
  have iPositive : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have oPositive : (0 : ℝ) < Fintype.card O := by exact_mod_cast Fintype.card_pos
  push_cast
  let a : ℝ := leftSlice.card
  let b : ℝ := rightSlice.card
  let i : ℝ := Fintype.card I
  let o : ℝ := Fintype.card O
  change a * b / (i * o) = (a * o / (i * o)) * (i * b / (i * o))
  have iNe : i ≠ 0 := by dsimp [i]; positivity
  have oNe : o ≠ 0 := by dsimp [o]; positivity
  field_simp [iNe, oNe]

/-- A support event is independent of an event determined by complementary coordinates. -/
theorem uniform_independence_of_inside_outside
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (left right : Finset (V → A)) (support : Finset V)
    (leftDepends : DependsOn left support)
    (rightDepends : DependsOutside right support) :
    uniformFinsetMass (left ∩ right) =
      uniformFinsetMass left * uniformFinsetMass right := by
  classical
  let split := coordinateSplitEquiv (A := A) support
  let leftPre := Finset.univ.filter fun z => split z ∈ left
  let rightPre := Finset.univ.filter fun z => split z ∈ right
  have leftInvariant : ∀ i o₁ o₂, ((i, o₁) ∈ leftPre ↔ (i, o₂) ∈ leftPre) := by
    intro inside outside₁ outside₂
    simp only [leftPre, Finset.mem_filter, Finset.mem_univ, true_and]
    apply leftDepends
    intro v hv
    simp [split, coordinateSplitEquiv, assembleCoordinates, hv]
  have rightInvariant : ∀ o i₁ i₂, ((i₁, o) ∈ rightPre ↔ (i₂, o) ∈ rightPre) := by
    intro outside inside₁ inside₂
    simp only [rightPre, Finset.mem_filter, Finset.mem_univ, true_and]
    apply rightDepends
    intro v hv
    simp [split, coordinateSplitEquiv, assembleCoordinates, hv]
  have preIntersection : leftPre ∩ rightPre =
      Finset.univ.filter fun z => split z ∈ left ∩ right := by
    ext z
    simp [leftPre, rightPre]
  have preIndependent := uniform_product_independence
    leftPre rightPre leftInvariant rightInvariant
  rw [preIntersection,
    uniformFinsetMass_preimage_equiv split (left ∩ right),
    uniformFinsetMass_preimage_equiv split left,
    uniformFinsetMass_preimage_equiv split right] at preIndependent
  exact preIndependent

/-- Avoiding events with disjoint variable supports depends only on coordinates outside
the target support. -/
theorem avoidance_depends_outside
    {ι V A : Type*} [DecidableEq ι]
    [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (event : ι → Finset (V → A)) (support : ι → Finset V)
    (eventDepends : ∀ e, DependsOn (event e) (support e))
    (target : ι) (S : Finset ι)
    (supportDisjoint : ∀ f ∈ S, Disjoint (support target) (support f)) :
    DependsOutside (avoidOutcomes event S) (support target) := by
  intro left right equalOutside
  simp only [avoidOutcomes, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro leftAvoids f hf rightEvent
    apply leftAvoids f hf
    apply (eventDepends f left right ?_).mpr rightEvent
    intro v hvSupport
    apply equalOutside v
    intro hvTarget
    exact Finset.disjoint_left.mp (supportDisjoint f hf) hvTarget hvSupport
  · intro rightAvoids f hf leftEvent
    apply rightAvoids f hf
    apply (eventDepends f left right ?_).mp leftEvent
    intro v hvSupport
    apply equalOutside v
    intro hvTarget
    exact Finset.disjoint_left.mp (supportDisjoint f hf) hvTarget hvSupport

/-- Variable-model dependency equality needed by the finite LLL theorem. -/
theorem variable_dependency_equality
    {ι V A : Type*} [DecidableEq ι]
    [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A] [Nonempty A]
    (event : ι → Finset (V → A)) (support : ι → Finset V)
    (eventDepends : ∀ e, DependsOn (event e) (support e))
    (target : ι) (S : Finset ι)
    (supportDisjoint : ∀ f ∈ S, Disjoint (support target) (support f)) :
    finiteBadAvoidMass event target S =
      finiteEventMass event target * finiteAvoidMass event S := by
  unfold finiteBadAvoidMass finiteEventMass finiteAvoidMass
  exact uniform_independence_of_inside_outside
    (event target) (avoidOutcomes event S) (support target)
    (eventDepends target)
    (avoidance_depends_outside event support eventDepends target S supportDisjoint)

end TernarySyncAudit
