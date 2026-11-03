import Mathlib
import FormalAudit.ConcreteLLLNumerics

namespace TernarySyncAudit

open Finset

/-- Intersecting macroblock supports force the two character intervals to be
within 18 characters of genuinely overlapping. -/
theorem intersecting_support_start_bounds
    {N : ℕ} (left right : LongIntervalIndex N)
    (intersects : ¬Disjoint (longIntervalSupport N left) (longIntervalSupport N right)) :
    right.start < left.start + 2 * left.length + 18 ∧
      left.start < right.start + 2 * right.length + 18 := by
  rcases Finset.not_disjoint_iff.mp intersects with ⟨block, blockLeft, blockRight⟩
  have leftFacts := (Finset.mem_filter.mp blockLeft).2
  have rightFacts := (Finset.mem_filter.mp blockRight).2
  constructor <;> omega

/-- At any fixed second length `r`, the start position injects all neighbors
into an interval of length `2*ell+2*r+35`. -/
theorem neighbor_length_fiber_card_le
    {N : ℕ} (event : LongIntervalIndex N) (r : ℕ) :
    ((longIntervalNeighbors N event).filter fun other => other.length = r).card ≤
      2 * event.length + 2 * r + 35 := by
  classical
  let fiber := (longIntervalNeighbors N event).filter fun other => other.length = r
  let coordinate : LongIntervalIndex N → ℕ := fun other =>
    other.start + 2 * r + 17 - event.start
  let target := Finset.range (2 * event.length + 2 * r + 35)
  have cardBound : fiber.card ≤ target.card := by
    apply Finset.card_le_card_of_injOn coordinate
    · intro other otherIn
      have neighborIn : other ∈ longIntervalNeighbors N event :=
        (Finset.mem_filter.mp otherIn).1
      have lengthEq : other.length = r := (Finset.mem_filter.mp otherIn).2
      have intersects :
          ¬Disjoint (longIntervalSupport N event) (longIntervalSupport N other) :=
        (Finset.mem_filter.mp neighborIn).2.2
      have bounds := intersecting_support_start_bounds event other intersects
      rw [lengthEq] at bounds
      have lower : event.start ≤ other.start + 2 * r + 17 := by omega
      have coordinateEquation :
          coordinate other + event.start = other.start + 2 * r + 17 := by
        dsimp [coordinate]
        exact Nat.sub_add_cancel lower
      change coordinate other ∈
        Finset.range (2 * event.length + 2 * r + 35)
      apply Finset.mem_range.mpr
      omega
    · intro left leftIn right rightIn coordinateEq
      have leftNeighbor : left ∈ longIntervalNeighbors N event :=
        (Finset.mem_filter.mp leftIn).1
      have rightNeighbor : right ∈ longIntervalNeighbors N event :=
        (Finset.mem_filter.mp rightIn).1
      have leftLength : left.length = r := (Finset.mem_filter.mp leftIn).2
      have rightLength : right.length = r := (Finset.mem_filter.mp rightIn).2
      have leftBounds := intersecting_support_start_bounds event left
        (Finset.mem_filter.mp leftNeighbor).2.2
      have rightBounds := intersecting_support_start_bounds event right
        (Finset.mem_filter.mp rightNeighbor).2.2
      have startEq : left.start = right.start := by
        dsimp [coordinate] at coordinateEq
        omega
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        exact startEq
      · apply Fin.ext
        exact leftLength.trans rightLength.symm
  simpa [fiber, target] using cardBound

/-- The paper's simpler per-length estimate follows with ample slack. -/
theorem neighbor_length_fiber_card_le_three
    {N : ℕ} (event : LongIntervalIndex N) (r : ℕ) :
    ((longIntervalNeighbors N event).filter fun other => other.length = r).card ≤
      3 * (event.length + r) := by
  have base := neighbor_length_fiber_card_le event r
  have lengthLarge : 35 ≤ event.length + r := by
    have := event.long
    omega
  omega

private noncomputable def geometricRatio : ℝ := (100 : ℝ) / 101

private noncomputable def neighborMajorant (ell k : ℕ) : ℝ :=
  3 * ((ell + 2001 + k : ℕ) : ℝ) * Real.exp (-20) * geometricRatio ^ k

private theorem geometricRatio_nonnegative : 0 ≤ geometricRatio := by
  unfold geometricRatio
  norm_num

private theorem geometricRatio_lt_one : geometricRatio < 1 := by
  unfold geometricRatio
  norm_num

private theorem geometricRatio_norm_lt_one : ‖geometricRatio‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg geometricRatio_nonnegative]
  exact geometricRatio_lt_one

private theorem neighborMajorant_summable (ell : ℕ) :
    Summable (neighborMajorant ell) := by
  have geom : Summable (fun k : ℕ => geometricRatio ^ k) :=
    summable_geometric_of_norm_lt_one geometricRatio_norm_lt_one
  have moment : Summable (fun k : ℕ => (k : ℝ) * geometricRatio ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one geometricRatio_norm_lt_one).summable
  have split : Summable (fun k : ℕ =>
      (((ell + 2001 : ℕ) : ℝ) * geometricRatio ^ k) +
        (k : ℝ) * geometricRatio ^ k) :=
    (geom.mul_left _).add moment
  refine (split.mul_left (3 * Real.exp (-20))).congr ?_
  intro k
  unfold neighborMajorant
  push_cast
  ring

/-- Exact evaluation of the rational geometric majorant. -/
private theorem neighborMajorant_tsum (ell : ℕ) :
    (∑' k : ℕ, neighborMajorant ell k) =
      3 * Real.exp (-20) * (101 * (ell + 2001) + 10100) := by
  have geom : Summable (fun k : ℕ => geometricRatio ^ k) :=
    summable_geometric_of_norm_lt_one geometricRatio_norm_lt_one
  have moment : Summable (fun k : ℕ => (k : ℝ) * geometricRatio ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one geometricRatio_norm_lt_one).summable
  have termIdentity (k : ℕ) :
      neighborMajorant ell k =
        3 * Real.exp (-20) *
          ((((ell + 2001 : ℕ) : ℝ) * geometricRatio ^ k) +
            (k : ℝ) * geometricRatio ^ k) := by
    unfold neighborMajorant
    push_cast
    ring
  rw [tsum_congr termIdentity, tsum_mul_left]
  rw [(geom.mul_left (((ell + 2001 : ℕ) : ℝ))).tsum_add moment]
  rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one
    geometricRatio_norm_lt_one]
  rw [tsum_geometric_of_lt_one geometricRatio_nonnegative geometricRatio_lt_one]
  unfold geometricRatio
  norm_num
  ring

/-- The majorant is vastly smaller than the `ell/1000` budget used in the LLL. -/
private theorem neighborMajorant_tsum_lt (ell : ℕ) (hell : 2000 < ell) :
    (∑' k : ℕ, neighborMajorant ell k) < (ell : ℝ) / 1000 := by
  rw [neighborMajorant_tsum]
  have expSmall : Real.exp (-20) < (1 : ℝ) / 624000 := by
    rw [Real.exp_neg]
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 624000)
        exp_twenty_gt_624000)
  have ellReal : (2000 : ℝ) < ell := by exact_mod_cast hell
  have expPositive : 0 < Real.exp (-20) := Real.exp_pos _
  nlinarith

/-- Each true event charge is bounded by the corresponding rational-geometric
majorant after writing its length as `2001+k`. -/
private theorem event_charge_le_majorant
    {N : ℕ} (event : LongIntervalIndex N) (k : ℕ) :
    3 * ((event.length + 2001 + k : ℕ) : ℝ) *
        Real.exp (-((2001 + k : ℕ) : ℝ) / 100) ≤
      neighborMajorant event.length k := by
  let q₀ := Real.exp (-(1 : ℝ) / 100)
  have q₀Nonnegative : 0 ≤ q₀ := Real.exp_nonneg _
  have q₀LeRatio : q₀ ≤ geometricRatio := explicit_charge_base_lt.le
  have ratioLeOne : geometricRatio ≤ 1 := geometricRatio_lt_one.le
  have powFirst : q₀ ^ (k + 1) ≤ geometricRatio ^ (k + 1) := by
    exact pow_le_pow_left₀ q₀Nonnegative q₀LeRatio _
  have powSecond : geometricRatio ^ (k + 1) ≤ geometricRatio ^ k := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg geometricRatio_nonnegative k)
      ratioLeOne
  have exponentialPower :
      Real.exp (-((2001 + k : ℕ) : ℝ) / 100) =
        Real.exp (-20) * q₀ ^ (k + 1) := by
    rw [show -((2001 + k : ℕ) : ℝ) / 100 =
        -20 + ((k + 1 : ℕ) : ℝ) * (-(1 : ℝ) / 100) by
          push_cast
          ring]
    rw [Real.exp_add, Real.exp_nat_mul]
  rw [exponentialPower]
  unfold neighborMajorant
  have coefficientNonnegative :
      0 ≤ 3 * ((event.length + 2001 + k : ℕ) : ℝ) * Real.exp (-20) := by
    positivity
  simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_left (powFirst.trans powSecond) coefficientNonnegative)

/-- Fully formal concrete neighbor-charge estimate, including the start-position
count, all endpoint slack, the length fibers, and the infinite geometric tail. -/
theorem concrete_neighbor_charge_sum_lt
    {N : ℕ} (event : LongIntervalIndex N) :
    (∑ other ∈ longIntervalNeighbors N event, longIntervalCharge other) <
      (event.length : ℝ) / 1000 := by
  classical
  let neighbors := longIntervalNeighbors N event
  let lengthOffset : LongIntervalIndex N → ℕ := fun other => other.length - 2001
  have mapsTo : (neighbors : Set (LongIntervalIndex N)).MapsTo lengthOffset
      (Finset.range (18 * N + 1)) := by
    intro other otherIn
    change lengthOffset other ∈ Finset.range (18 * N + 1)
    simp only [Finset.mem_range]
    have lengthBound : other.length < 18 * N + 1 := other.val.2.isLt
    dsimp [lengthOffset]
    omega
  have fiberwise :
      (∑ other ∈ neighbors, longIntervalCharge other) =
        ∑ k ∈ Finset.range (18 * N + 1),
          ∑ other ∈ neighbors with lengthOffset other = k,
            longIntervalCharge other := by
    symm
    exact Finset.sum_fiberwise_of_maps_to mapsTo longIntervalCharge
  rw [fiberwise]
  have eachFiber (k : ℕ) :
      (∑ other ∈ neighbors with lengthOffset other = k,
          longIntervalCharge other) ≤
        3 * ((event.length + 2001 + k : ℕ) : ℝ) *
          Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by
    let fiber := neighbors.filter fun other => lengthOffset other = k
    have fiberEquality :
        fiber = neighbors.filter fun other => other.length = 2001 + k := by
      ext other
      simp only [fiber, Finset.mem_filter]
      constructor
      · rintro ⟨neighborIn, offsetEq⟩
        refine ⟨neighborIn, ?_⟩
        have long := other.long
        dsimp [lengthOffset] at offsetEq
        omega
      · rintro ⟨neighborIn, lengthEq⟩
        refine ⟨neighborIn, ?_⟩
        dsimp [lengthOffset]
        omega
    have lengthIdentity : ∀ other ∈ fiber, other.length = 2001 + k := by
      intro other otherIn
      have offsetEq := (Finset.mem_filter.mp otherIn).2
      have long := other.long
      dsimp [lengthOffset] at offsetEq
      omega
    have sumIdentity :
        (∑ other ∈ neighbors with lengthOffset other = k,
            longIntervalCharge other) =
          (fiber.card : ℝ) *
            Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by
      change (∑ other ∈ fiber, longIntervalCharge other) = _
      calc
        (∑ other ∈ fiber, longIntervalCharge other) =
            ∑ _other ∈ fiber,
              Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by
          apply Finset.sum_congr rfl
          intro other otherIn
          unfold longIntervalCharge
          rw [lengthIdentity other otherIn]
        _ = (fiber.card : ℝ) *
              Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by
          simp
    rw [sumIdentity]
    have cardBoundNat := neighbor_length_fiber_card_le_three event (2001 + k)
    have fiberCardBoundNat :
        fiber.card ≤ 3 * (event.length + (2001 + k)) := by
      rw [fiberEquality]
      change
        ((longIntervalNeighbors N event).filter
          fun other => other.length = 2001 + k).card ≤
            3 * (event.length + (2001 + k))
      exact cardBoundNat
    have cardBoundCast :
        (fiber.card : ℝ) ≤ ((3 * (event.length + (2001 + k)) : ℕ) : ℝ) := by
      exact (Nat.cast_le).2 fiberCardBoundNat
    have castIdentity :
        ((3 * (event.length + (2001 + k)) : ℕ) : ℝ) =
          3 * ((event.length + 2001 + k : ℕ) : ℝ) := by
      push_cast
      ring
    rw [castIdentity] at cardBoundCast
    exact mul_le_mul_of_nonneg_right cardBoundCast (Real.exp_nonneg _)
  calc
    (∑ k ∈ Finset.range (18 * N + 1),
        ∑ other ∈ neighbors with lengthOffset other = k,
          longIntervalCharge other) ≤
        ∑ k ∈ Finset.range (18 * N + 1),
          3 * ((event.length + 2001 + k : ℕ) : ℝ) *
            Real.exp (-((2001 + k : ℕ) : ℝ) / 100) := by
      exact Finset.sum_le_sum fun k _ => eachFiber k
    _ ≤ ∑ k ∈ Finset.range (18 * N + 1), neighborMajorant event.length k := by
      exact Finset.sum_le_sum fun k _ => event_charge_le_majorant event k
    _ ≤ ∑' k : ℕ, neighborMajorant event.length k := by
      exact (neighborMajorant_summable event.length).sum_le_tsum _
        (fun k _ => by unfold neighborMajorant geometricRatio; positivity)
    _ < (event.length : ℝ) / 1000 :=
      neighborMajorant_tsum_lt event.length event.long

end TernarySyncAudit
