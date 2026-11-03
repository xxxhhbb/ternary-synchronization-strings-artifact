import Mathlib.Data.List.Basic

namespace TernarySyncAudit

abbrev Symbol := Fin 3
abbrev Word := List Symbol

/-- A word has a nonempty contiguous square factor. -/
def HasSquare (word : List α) : Prop :=
  ∃ pre block post, block ≠ [] ∧
    word = pre ++ block ++ block ++ post

/-- Square-freeness in the exact factor sense used in Appendix A. -/
def SquareFree (word : List α) : Prop := ¬HasSquare word

theorem squareFree_iff_no_factor (word : List α) :
    SquareFree word ↔
      ¬∃ pre block post, block ≠ [] ∧
        word = pre ++ block ++ block ++ post := by
  rfl

end TernarySyncAudit
