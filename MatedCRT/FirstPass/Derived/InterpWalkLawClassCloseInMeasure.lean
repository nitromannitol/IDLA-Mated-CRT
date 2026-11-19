import MatedCRT.FirstPass.Derived.InterpWalkLawClassCloseAtPoint
import MatedCRT.FirstPass.Derived.BrownianClassLawContinuity
import MatedCRT.FirstPass.Derived.UniformStartGoodFinExit
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import MatedCRT.FirstPass.Derived.MaxCellDiamTendsto
import MatedCRT.FirstPass.S6j.LitUniformStartInvariance

/-!
# The stopped class law of the interpolated walk is close to the Brownian one, in probability

Berestycki–Gwynne (2020), proof of Lemma 7.4.  For the interpolated quenched walk law at a fixed point `z`, the
Lévy–Prokhorov distance between the law of the path class stopped at the first exit from `ball 0 R` and the
corresponding class law of planar Brownian motion from `z` is at most `κ` outside an event whose probability tends
to `0` along every sequence `ε_n → 0`.  The event is contained in the union of

* the complement of the uniform-start good event with tolerance `κ / 3` (`GMS21UniformStartInput`, [GMS21,
  Theorem 3.4]),
* the event that the cells meeting the ball of radius `ρ + 1` have diameter larger than `d` (`hdiam_of_isValid`),
* a null set (interpolation defined, finite exits, `η' = η`).

The deterministic estimate on the complement is `levyProkhorovDist_interpWalkLaw_stoppedExitCurve_le`; the
continuity of the Brownian class law in the starting point is
`exists_levyProkhorovDist_planarBrownianMotion_stoppedExitCurve_lt`.  Probabilities are outer measures, so no
measurability is needed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open _root_.HarmonicBalls
open scoped NNReal ENNReal
open MatedCRT.StopAtExitLevyProkhorov MatedCRT.FirstPass.Derived

namespace MatedCRT.InterpClassClose

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The stopped class law of the interpolated walk at `z` is close to the Brownian one, in probability**
(Berestycki–Gwynne (2020), Lemma 7.4): for `‖z‖ < ρ < R`, every `κ > 0` and every sequence `ε_n → 0` with
`m_{ε_n} > 0` eventually, the probability that the Lévy–Prokhorov distance of the stopped class laws exceeds
`κ` tends to `0`. -/
theorem tendsto_measure_levyProkhorovDist_interpWalkLaw_stoppedExitCurve_gt
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hN4 : GMS21UniformStartInput 𝒮)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hmε : ∀ᶠ n in atTop, 0 < S.mε (ε n))
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) {z : ℂ} (hz : ‖z‖ < ρ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n => S.P {ω | κ < levyProkhorovDist
      (((interpWalkLaw S η' (ε n) ω z : ProbabilityMeasure (ContinuousPath ℂ)) :
        Measure (ContinuousPath ℂ)).map (stoppedExitCurve (ball (0 : ℂ) R)))
      ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R)))}) atTop (𝓝 0) := by
  classical
  have hPprob := hS.isProbabilityMeasure
  obtain ⟨δ, hδ, hBM⟩ := MatedCRT.BrownianClassLawContinuity.exists_levyProkhorovDist_planarBrownianMotion_stoppedExitCurve_lt
    (R := R) (z := z) (by rw [mem_ball, dist_zero_right]; linarith) (κ := κ / 3) (by positivity)
  set d : ℝ := min (δ / 2) ((ρ - ‖z‖) / 2) with hd
  have hd0 : 0 < d := lt_min (by positivity) (by linarith)
  have hdδ : d ≤ δ / 2 := min_le_left _ _
  have hdρ : d ≤ (ρ - ‖z‖) / 2 := min_le_right _ _
  rw [ENNReal.tendsto_nhds_zero]
  intro θ' hθ'
  rcases eq_or_ne θ' ⊤ with htop | hfin'
  · exact Eventually.of_forall fun n => htop ▸ le_top
  set θ : ℝ := θ'.toReal / 2 with hθdef
  have hθ : 0 < θ := by
    have := ENNReal.toReal_pos hθ'.ne' hfin'
    positivity
  have hθθ : ENNReal.ofReal θ + ENNReal.ofReal θ = θ' := by
    rw [← ENNReal.ofReal_add hθ.le hθ.le, show θ + θ = θ'.toReal by rw [hθdef]; ring,
      ENNReal.ofReal_toReal hfin']
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := hN4 γ hγ hγ2 Ω S hS R ρ hρ hρR (κ / 3) (by positivity) θ hθ
  have hdiam := hdiam_of_isValid hS hae hε ρ d hd0
  have hev1 : ∀ᶠ n in atTop, S.P {ω | ENNReal.ofReal d < maxCellDiam (ε n) (⇑(η' ω)) ρ} ≤
      ENNReal.ofReal θ := (ENNReal.tendsto_nhds_zero.1 hdiam) _ (ENNReal.ofReal_pos.2 hθ)
  have hev2 : ∀ᶠ n in atTop, ε n < min ε₀ (min (δ / 2) ((ρ - ‖z‖) / 2)) :=
    (hε.eventually (gt_mem_nhds (lt_min hε₀pos (lt_min (by positivity) (by linarith)))))
  filter_upwards [hev1, hev2, hmε] with n h1 h2 h3
  have hεε₀ : ε n < ε₀ := lt_of_lt_of_le h2 (min_le_left _ _)
  have hεδ : ε n < δ / 2 := lt_of_lt_of_le h2 ((min_le_right _ _).trans (min_le_left _ _))
  have hεz : ε n < (ρ - ‖z‖) / 2 := lt_of_lt_of_le h2 ((min_le_right _ _).trans (min_le_right _ _))
  have hG : S.P (UniformStartGood.goodG S (ε n) R ρ (κ / 3))ᶜ ≤ ENNReal.ofReal θ :=
    hε₀ (ε n) (hε0 n) hεε₀
  have hsub : {ω | κ < levyProkhorovDist
      (((interpWalkLaw S η' (ε n) ω z : ProbabilityMeasure (ContinuousPath ℂ)) :
        Measure (ContinuousPath ℂ)).map (stoppedExitCurve (ball (0 : ℂ) R)))
      ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R)))} ≤ᵐ[S.P]
      ((UniformStartGood.goodG S (ε n) R ρ (κ / 3))ᶜ ∪
        {ω | ENNReal.ofReal d < maxCellDiam (ε n) (⇑(η' ω)) ρ} : Set Ω) := by
    filter_upwards [hae, hS.ae_interpWeight_good hae (hε0 n), UniformStartGood.ae_mem_finExit hγ hγ2 hS (hε0 n) R ρ]
      with ω hω hlp hfinE hbad
    by_contra hnot
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not, not_lt] at hnot
    obtain ⟨hGω, hmesh⟩ := hnot
    have hle := levyProkhorovDist_interpWalkLaw_stoppedExitCurve_le S η' (R := R) (ρ := ρ) (κ := κ / 3)
      (κ₂ := κ / 3) (d := d) (ε := ε n) (hε0 n).le (by positivity) hd0.le h3 hω hlp.1 hlp.2 hfinE hGω hmesh
      (z := z) (by linarith) (fun w hw => (hBM w (by linarith)).le)
    have : κ < κ / 3 + κ / 3 := lt_of_lt_of_le hbad hle
    linarith
  calc S.P _ ≤ S.P ((UniformStartGood.goodG S (ε n) R ρ (κ / 3))ᶜ ∪
        {ω | ENNReal.ofReal d < maxCellDiam (ε n) (⇑(η' ω)) ρ}) := measure_mono_ae hsub
    _ ≤ S.P (UniformStartGood.goodG S (ε n) R ρ (κ / 3))ᶜ +
        S.P {ω | ENNReal.ofReal d < maxCellDiam (ε n) (⇑(η' ω)) ρ} := measure_union_le _ _
    _ ≤ ENNReal.ofReal θ + ENNReal.ofReal θ := add_le_add hG h1
    _ = θ' := hθθ

end MatedCRT.InterpClassClose
