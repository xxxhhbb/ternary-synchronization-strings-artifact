import Mathlib

namespace TernarySyncAudit

/-- The two seven-symbol signature cases cover every nonzero block offset. -/
theorem offset_signature_cover {offset : ℕ}
    (positive : 1 ≤ offset) (inside : offset ≤ 17) :
    offset ≤ 11 ∨ 7 ≤ offset := by
  omega

/-- A half-period larger than 34 is at least 35 over the natural numbers. -/
theorem period_after_short_case {period : ℕ} (large : ¬period ≤ 34) :
    35 ≤ period := by
  omega

/-- Divisibility by 18 and a lower bound of 35 force at least two blocks. -/
theorem aligned_period_has_two_blocks {period quotient : ℕ}
    (period_eq : period = 18 * quotient) (large : 35 ≤ period) :
    2 ≤ quotient := by
  omega

/-- Every interval of length at least 35 contains an aligned length-18 block. -/
theorem exists_aligned_eighteen_window {start period : ℕ}
    (large : 35 ≤ period) :
    ∃ aligned,
      aligned % 18 = 0 ∧
      start ≤ aligned ∧
      aligned + 18 ≤ start + period := by
  let remainder := start % 18
  let quotient := start / 18
  have remainder_lt : remainder < 18 := by
    exact Nat.mod_lt _ (by omega)
  have decomposition : remainder + 18 * quotient = start := by
    exact Nat.mod_add_div start 18
  by_cases aligned_case : remainder = 0
  · refine ⟨start, ?_, by omega, by omega⟩
    simpa [remainder] using aligned_case
  · refine ⟨18 * (quotient + 1), by simp, ?_, ?_⟩ <;> omega

end TernarySyncAudit
