import MatedCRT.FirstPass.S5c.InclusionCode

/-!
# FIRST PASS, Lemma 5.3 (three-inputs §2.4, continuous-profile form): compact inclusion events without cluster openness

The closure-test coding of `InclusionCode.lean` needs the approximating sets to be open almost surely. The three-inputs
§2.4 coding avoids the openness of the cluster itself by working with positivity sets `{x | 0 < g ω x}` of continuous
profiles `g ω` (the profiles `H_{R,s}` of §2.4 are such approximations). For a continuous profile the positivity set is
open for every outcome, so `nullMeasurableSet_inclCompact` applies with no a.s. openness input. The point events
`{ω | d ∈ {x | 0 < g ω x}}` are `{ω | 0 < g ω d}`; their null measurability is the hypothesis `hpt` (for the least
supersolution profiles it is the AE point measurability of B1bThreshold.lean).

Terminology: Armitage-Gardiner (positivity sets of continuous superharmonic profiles), Duplantier-Sheffield and
Berestycki-Powell (the cluster family `Λ_t = interior (closure (positivity set))`, `SatisfiesObstacleCharacterization`).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology

/-- Compact inclusion in the interior of the closure of a continuous-profile positivity set is null measurable, for a
countable dense set `D` of test points whose point events are null measurable (three-inputs §2.4, no openness input). -/
theorem nullMeasurableSet_inclCompact_profile {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Set ℂ} (hDc : D.Countable) (hD : Dense D) (g : Ω → ℂ → ℝ) (hcont : ∀ ω, Continuous (g ω))
    (hpt : ∀ d ∈ D, NullMeasurableSet {ω | 0 < g ω d} P)
    {C : Set ℂ} (hC : IsCompact C) :
    NullMeasurableSet {ω | C ⊆ interior (closure {x : ℂ | 0 < g ω x})} P :=
  nullMeasurableSet_inclCompact hDc hD
    (S := fun ω => {x : ℂ | 0 < g ω x})
    (ae_of_all _ fun ω => isOpen_lt continuous_const (hcont ω))
    (fun d hd => hpt d hd) hC

end MatedCRT.S5c
