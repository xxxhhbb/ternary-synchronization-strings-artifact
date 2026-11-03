import Mathlib
import FormalAudit.FixedLogProbability
import FormalAudit.EmbeddingRestrictionProbability

namespace TernarySyncAudit

/-- Every occurrence cell of a log of length at most `rows` lies in the
finite table `V × Fin rows`. -/
def boundedOccurrenceCellEmbedding
    {V E : Type*} [DecidableEq V]
    (support : E → Finset V) (log : List E) (rows : ℕ)
    (lengthBound : log.length ≤ rows) :
    (Σ index : Fin log.length,
      InsideCoordinate (support (log.get index))) ↪ V × Fin rows where
  toFun occurrence :=
    (occurrence.2.1,
      ⟨supportOccurrenceCount support occurrence.2.1
          (log.take occurrence.1.1), by
        have occurrenceBound := supportOccurrenceCount_le_length
          support occurrence.2.1 (log.take occurrence.1.1)
        have takeBound : (log.take occurrence.1.1).length ≤ occurrence.1.1 := by
          simp
        omega⟩)
  inj' := by
    intro left right equality
    have coordinateEquality : left.2.1 = right.2.1 :=
      congrArg Prod.fst equality
    have rowEquality :
        supportOccurrenceCount support left.2.1 (log.take left.1.1) =
          supportOccurrenceCount support right.2.1 (log.take right.1.1) :=
      congrArg (fun pair => pair.2.1) equality
    apply occurrenceCell_injective support (fun _ => 0) log
    apply Prod.ext
    · exact coordinateEquality
    · simpa [occurrenceCell] using rowEquality

/-- A finite table extended arbitrarily beyond its declared row bound. -/
def extendBoundedTable
    {V A : Type*} (rows : ℕ) (default : A)
    (table : V × Fin rows → A) : V → ℕ → A :=
  fun coordinate row =>
    if inside : row < rows then table (coordinate, ⟨row, inside⟩) else default

@[simp] theorem extendBoundedTable_inside
    {V A : Type*} (rows : ℕ) (default : A)
    (table : V × Fin rows → A) (coordinate : V) (row : Fin rows) :
    extendBoundedTable rows default table coordinate row.1 =
      table (coordinate, row) := by
  simp [extendBoundedTable]

/-- The finite-table event obtained by pulling the canonical fixed-log event
back along the injective occurrence-cell map. -/
noncomputable def boundedLogCompatibilityEvent
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (support : E → Finset V) (event : E → Finset (V → A))
    (log : List E) (rows : ℕ) (lengthBound : log.length ≤ rows) :
    Finset ((V × Fin rows) → A) :=
  restrictionPatternEvent
    (boundedOccurrenceCellEmbedding support log rows lengthBound)
    (canonicalLogCompatibility support event log)

/-- Exact fixed-log probability in a genuinely finite resampling table. -/
theorem boundedLogCompatibilityEvent_mass
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate, DependsOn (event candidate) (support candidate))
    (log : List E) (rows : ℕ) (lengthBound : log.length ≤ rows) :
    uniformFinsetMass
        (boundedLogCompatibilityEvent support event log rows lengthBound) =
      ∏ index : Fin log.length,
        uniformFinsetMass (event (log.get index)) := by
  classical
  rw [boundedLogCompatibilityEvent,
    uniformFinsetMass_restrictionPatternEvent,
    canonicalLogCompatibility_mass support event eventDepends log]

/-- A semantically compatible finite-table execution belongs to the exact
finite fixed-log event whose mass is the event-probability product. -/
theorem bounded_logCompatible_mem
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate, DependsOn (event candidate) (support candidate))
    (log : List E) (rows : ℕ) (lengthBound : log.length ≤ rows)
    (default : A) (table : V × Fin rows → A)
    (compatible : logCompatible support
      (fun candidate => (event candidate : Set (V → A)))
      (extendBoundedTable rows default table) (fun _ => 0) log) :
    table ∈ boundedLogCompatibilityEvent
      support event log rows lengthBound := by
  classical
  have canonicalMember := logCompatible_logCellAssignment_mem
    support event eventDepends (extendBoundedTable rows default table)
      (fun _ => 0) log compatible
  unfold boundedLogCompatibilityEvent restrictionPatternEvent
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have restrictionEquality :
      (fun occurrence => table
        (boundedOccurrenceCellEmbedding support log rows lengthBound occurrence)) =
      logCellAssignment support (extendBoundedTable rows default table)
        (fun _ => 0) log := by
    funext occurrence
    have rowBound :
        supportOccurrenceCount support occurrence.2.1
            (log.take occurrence.1.1) < rows := by
      have occurrenceBound := supportOccurrenceCount_le_length
        support occurrence.2.1 (log.take occurrence.1.1)
      have takeBound : (log.take occurrence.1.1).length ≤ occurrence.1.1 := by
        simp
      omega
    simp [boundedOccurrenceCellEmbedding, logCellAssignment,
      extendBoundedTable, rowBound]
  rw [restrictionEquality]
  exact canonicalMember

end TernarySyncAudit
