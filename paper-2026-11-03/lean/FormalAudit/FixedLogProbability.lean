import Mathlib
import FormalAudit.MTLogCompatibility
import FormalAudit.OccurrenceCells
import FormalAudit.SupportPatternProbability
import FormalAudit.IndependentPatternProduct

namespace TernarySyncAudit

/-- The local pattern family required by one occurrence of a proposed
resampling log. -/
noncomputable def logAllowedPatterns
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (support : E → Finset V) (event : E → Finset (V → A))
    (log : List E) (index : Fin log.length) :
    Finset (InsideCoordinate (support (log.get index)) → A) :=
  supportPatterns (event (log.get index)) (support (log.get index))

/-- Canonical compatibility event on the disjoint, occurrence-tagged cells
of a fixed chronological log. -/
noncomputable def canonicalLogCompatibility
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (support : E → Finset V) (event : E → Finset (V → A))
    (log : List E) :
    Finset ((Σ index : Fin log.length,
      InsideCoordinate (support (log.get index))) → A) :=
  independentPatterns (logAllowedPatterns support event log)

/-- The canonical tagged-cell probability for a fixed log is exactly the
product of the original event probabilities. -/
theorem canonicalLogCompatibility_mass
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate, DependsOn (event candidate) (support candidate))
    (log : List E) :
    uniformFinsetMass (canonicalLogCompatibility support event log) =
      ∏ index : Fin log.length,
        uniformFinsetMass (event (log.get index)) := by
  classical
  rw [canonicalLogCompatibility,
    uniformFinsetMass_independentPatterns]
  apply Finset.prod_congr rfl
  intro index indexIn
  simpa [logAllowedPatterns] using
    (uniformFinsetMass_eq_supportPatterns
      (event (log.get index)) (support (log.get index))
        (eventDepends (log.get index))).symm

/-- Restriction of an actual resampling table to the distinct cells consumed
by the occurrences of a fixed log. -/
def logCellAssignment
    {V A E : Type*} [DecidableEq V]
    (support : E → Finset V) (table : V → ℕ → A)
    (initial : V → ℕ) (log : List E) :
    (Σ index : Fin log.length,
      InsideCoordinate (support (log.get index))) → A :=
  fun occurrence =>
    table occurrence.2.1
      (initial occurrence.2.1 +
        supportOccurrenceCount support occurrence.2.1
          (log.take occurrence.1.1))

/-- Every semantically compatible fixed log yields a member of its canonical
tagged-cell compatibility event.  Together with occurrence-cell injectivity,
this is the fixed-log probability lemma. -/
theorem logCompatible_logCellAssignment_mem
    {V A E : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (support : E → Finset V) (event : E → Finset (V → A))
    (eventDepends : ∀ candidate, DependsOn (event candidate) (support candidate))
    (table : V → ℕ → A) (initial : V → ℕ) (log : List E)
    (compatible : logCompatible support
      (fun candidate => (event candidate : Set (V → A))) table initial log) :
    logCellAssignment support table initial log ∈
      canonicalLogCompatibility support event log := by
  classical
  rw [canonicalLogCompatibility, mem_independentPatterns_iff]
  intro index
  let current : V → A := fun coordinate =>
    table coordinate
      (initial coordinate + supportOccurrenceCount support coordinate
        (log.take index.1))
  have currentBad : current ∈ event (log.get index) := by
    exact logCompatible_get support
      (fun candidate => (event candidate : Set (V → A)))
      table initial log compatible index
  let outside : OutsideCoordinate (support (log.get index)) → A :=
    fun coordinate => current coordinate.1
  have assembledBad :
      assembleCoordinates (support (log.get index))
          (fun coordinate => current coordinate.1) outside ∈
        event (log.get index) := by
    have assignmentEquality :
        assembleCoordinates (support (log.get index))
            (fun coordinate => current coordinate.1) outside = current := by
      funext coordinate
      simp only [assembleCoordinates]
      split <;> rfl
    rwa [assignmentEquality]
  have patternMember :=
    (assemble_mem_iff_supportPatterns
      (event (log.get index)) (support (log.get index))
      (eventDepends (log.get index))
      (fun coordinate => current coordinate.1) outside).mp assembledBad
  simpa [logAllowedPatterns, logCellAssignment, current] using patternMember

end TernarySyncAudit
