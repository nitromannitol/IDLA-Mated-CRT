import Mathlib
import MatedCRT.Defs.Setting

/-!
# Local transfer of the harmonic-ball fields (fp-S2g, q1)

Step H6 of `notes/fp-gaps/CHATGPT-q1-open-steps.md` Section 3: the harmonic-ball properties of a family `Λ_t` inside a
disc `B` depend only on the restriction of the measure to `B`. Concretely, if `μ` and `ν` have the same restriction to
`B` and every `Λ_t` (`0 < t < T`) has closure in `B`, then

* `Λ_t` is a harmonic ball for `μ` centred at `z` iff it is one for `ν` (the mass `μ(Λ_t) = ν(Λ_t)` and the mean value
  property `f(z) μ(Λ_t) = ∫_{Λ_t} f dμ` of `HarmonicBalls.HasMeanValueProperty` only see `μ` on `Λ_t ⊆ B`);
* the fields (a)-(b) of `SatisfiesHarmonicBallConditionsOn` transfer: the mass and boundary-mass conditions are the only
  fields that mention the measure, and the boundary `frontier Λ_t ⊆ closure Λ_t ⊆ B`.

The obstacle characterization `SatisfiesObstacleCharacterizationOn` is NOT transferred here: it quantifies over all discs
`B_ρ` and needs the potential-theoretic step H7. The full family transfer therefore keeps that clause as a hypothesis.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls

/-- Two measures with the same restriction to `B` agree on every subset of `B`. -/
theorem measure_eq_of_restrict_eq {μ ν : Measure ℂ} {B S : Set ℂ} (hSB : S ⊆ B)
    (h : μ.restrict B = ν.restrict B) : μ S = ν S := by
  have hS : μ.restrict S = ν.restrict S := by
    rw [← Measure.restrict_restrict_of_subset hSB, h, Measure.restrict_restrict_of_subset hSB]
  rw [← Measure.restrict_apply_univ (μ := μ) (s := S), ← Measure.restrict_apply_univ (μ := ν) (s := S), hS]

/-- Two measures with the same restriction to `B` have the same restriction to every subset of `B`. -/
theorem restrict_eq_of_restrict_eq {μ ν : Measure ℂ} {B S : Set ℂ} (hSB : S ⊆ B)
    (h : μ.restrict B = ν.restrict B) : μ.restrict S = ν.restrict S := by
  rw [← Measure.restrict_restrict_of_subset hSB, h, Measure.restrict_restrict_of_subset hSB]

/-- The mean value property of a harmonic ball depends only on the restriction of the measure to the ball. -/
theorem hasMeanValueProperty_congr_of_restrict {μ ν : Measure ℂ} {B Λ : Set ℂ} {z : ℂ} {f : ℂ → ℝ}
    (hΛB : Λ ⊆ B) (h : μ.restrict B = ν.restrict B) :
    HasMeanValueProperty μ Λ z f ↔ HasMeanValueProperty ν Λ z f := by
  have hR : μ.restrict Λ = ν.restrict Λ := restrict_eq_of_restrict_eq hΛB h
  have hm : μ Λ = ν Λ := measure_eq_of_restrict_eq hΛB h
  have hmr : μ.real Λ = ν.real Λ := by
    unfold Measure.real
    rw [hm]
  unfold HasMeanValueProperty IntegrableOn
  rw [hR, hmr]

/-- Being a harmonic ball for `μ` centred at `z` depends only on the restriction of `μ` to a disc containing the closure
of the ball. -/
theorem isHarmonicBall_congr_of_restrict {μ ν : Measure ℂ} {B Λ : Set ℂ} {z : ℂ}
    (hΛB : closure Λ ⊆ B) (h : μ.restrict B = ν.restrict B) (hμ : IsHarmonicBall μ Λ z) :
    IsHarmonicBall ν Λ z := by
  unfold IsHarmonicBall at hμ ⊢
  obtain ⟨hopen, hz, hpos, hfin, hmvp⟩ := hμ
  have hΛ : Λ ⊆ B := subset_closure.trans hΛB
  refine ⟨hopen, hz, ?_, ?_, fun f hf => (hasMeanValueProperty_congr_of_restrict hΛ h).mp (hmvp f hf)⟩
  · rw [← measure_eq_of_restrict_eq hΛ h]
    exact hpos
  · rw [← measure_eq_of_restrict_eq hΛ h]
    exact hfin

/-- The fields (a)-(b) of `SatisfiesHarmonicBallConditionsOn` transfer from `μ` to `ν` when the closures of the balls lie in
`B` and `μ`, `ν` agree on `B`. -/
theorem satisfiesHarmonicBallConditionsOn_congr_of_restrict {μ ν : Measure ℂ} {Λ : ℝ → Set ℂ} {z : ℂ} {T : ℝ}
    {B : Set ℂ} (hB : ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ B) (h : μ.restrict B = ν.restrict B)
    (hf : SatisfiesHarmonicBallConditionsOn μ Λ z T) : SatisfiesHarmonicBallConditionsOn ν Λ z T :=
  { hf with
    measure_eq := fun t ht => by
      rw [← measure_eq_of_restrict_eq (subset_closure.trans (hB t ht)) h]
      exact hf.measure_eq t ht
    measure_frontier := fun t ht => by
      rw [← measure_eq_of_restrict_eq ((frontier_subset_closure).trans (hB t ht)) h]
      exact hf.measure_frontier t ht }

/-- The harmonic-ball fields of a cone family (the first two conjuncts of `IsConeHarmonicBallFamilyOn`) transfer from `μ`
to `ν` with the same restriction to `B`. The obstacle clause is not included (see the module comment). -/
theorem coneHarmonicBallFamilyFields_congr_of_restrict {μ ν : Measure ℂ} {Λ : ℝ → Set ℂ} {T : ℝ} {B : Set ℂ}
    (hB : ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ B) (h : μ.restrict B = ν.restrict B)
    (hf : IsConeHarmonicBallFamilyOn μ Λ T) :
    (∀ t ∈ Ioo 0 T, IsHarmonicBall ν (Λ t) 0) ∧ SatisfiesHarmonicBallConditionsOn ν Λ 0 T :=
  ⟨fun t ht => isHarmonicBall_congr_of_restrict (hB t ht) h (hf.1 t ht),
    satisfiesHarmonicBallConditionsOn_congr_of_restrict hB h hf.2.1⟩

end MatedCRT
