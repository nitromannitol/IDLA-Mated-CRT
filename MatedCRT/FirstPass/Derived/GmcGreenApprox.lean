import MatedCRT.Proofs.Sec3.KilledOccupation.GmcGreenMeasure
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.InteriorSubsequence

/-!
# Green-weighted regularized GMC integrals converge to the Green-weighted chaos measure

Let `ψ` be a family of circle averages whose cut-off approximations `gmcApproxCut γ ρ ρ₂ k ψ`
(density `χ(x) ε_k^{γ²/2} e^{γ ψ̃(ε_k, x)}`, `ε_k = 2^{-k}`) converge vaguely to the cut-off GMC limit
`gmcLimit γ ρ ρ₂ ψ` and are eventually finite on compact sets. Let `D = B_r(z) ⊆ closedBall 0 ρ` (where the cut-off
`χ` is `1`) and `y ∈ D`. For a continuous `g ≥ 0` with compact support in `D` vanishing near the pole `y`, the test
function `G_D(y, ·) g` is continuous with compact support, so along every sequence of scales `n k → ∞`
`2 ∫_D G_D(y, x) w_{n k}(x) g(x) dx → ∫ g d(gmcGreenMeasure γ ρ ρ₂ z y r ψ)`,
where `w_k(x) = ε_k^{γ²/2} e^{γ ψ̃(ε_k, x)}` is the weight of the regularized occupation clock and
`gmcGreenMeasure = 2 · 1_D G_D(y, ·) · gmcLimit`. The left side is the right side of the regularized occupation
identity `lintegral_regClock_occupation_eq_green` (`MatedCRT/FirstPass/Derived/RegClockOccupation.lean`); this is the
chaos side of the Revuz-measure argument for the Liouville clock (Garban-Rhodes-Vargas, Thm 2.7(1)).

## Main results
* `integrable_of_continuous_of_hasCompactSupport_of_lt_top`: a continuous compactly supported function is integrable
  for a measure finite on its support.
* `continuous_greenFunction_ball_mul`: `x ↦ G_D(y, x) g(x)` is continuous when `g` is continuous and vanishes near `y`.
* `tendsto_two_mul_setLIntegral_green_regWeight`: the convergence above.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- A continuous compactly supported function is integrable for a measure that is finite on its support. -/
lemma integrable_of_continuous_of_hasCompactSupport_of_lt_top {μ : Measure ℂ} {f : ℂ → ℝ}
    (hfc : Continuous f) (hfK : HasCompactSupport f) (hμ : μ (tsupport f) < ∞) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hfK.exists_bound_of_continuous hfc
  have : IsFiniteMeasure (μ.restrict (tsupport f)) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hon : IntegrableOn f (tsupport f) μ :=
    Integrable.of_bound hfc.aestronglyMeasurable C (Eventually.of_forall hC)
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).1 hon

/-- The Green function of `D = B_r(z)` with pole `y ∈ D`, times a continuous `g` vanishing near `y`, is continuous. -/
lemma continuous_greenFunction_ball_mul {z y : ℂ} {r : ℝ} (hy : y ∈ ball z r) {g : ℂ → ℝ} (hgc : Continuous g)
    (hgy : y ∉ tsupport g) : Continuous fun x => greenFunction (ball z r) y x * g x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = y
  · rw [hx]
    have h0 : (fun x => greenFunction (ball z r) y x * g x) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hgy] with w hw
      simp [hw]
    exact continuousAt_const.congr h0.symm
  · exact ((MatedCRT.GreenEnvironment.continuousOn_greenFunction_ball_compl hy).continuousAt
      (isOpen_compl_singleton.mem_nhds hx)).mul hgc.continuousAt

/-- **Chaos side of the regularized occupation identity.** If the cut-off approximations of `ψ` converge vaguely
to `gmcLimit γ ρ ρ₂ ψ` and are eventually finite on compact sets, `D = B_r(z) ⊆ closedBall 0 ρ`, `y ∈ D`, and `g ≥ 0`
is continuous with compact support in `D` and vanishes near `y`, then along every `n k → ∞`,
`2 ∫_D G_D(y, x) w_{n k}(x) g(x) dx → ∫ g d(gmcGreenMeasure γ ρ ρ₂ z y r ψ)`. -/
theorem tendsto_two_mul_setLIntegral_green_regWeight {γ ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) {z y : ℂ} {r : ℝ}
    (hD : ball z r ⊆ closedBall 0 ρ) (hy : y ∈ ball z r) {ψ : UnitDiskCircleIndex → ℝ}
    (hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop, gmcApproxCut γ ρ ρ₂ k ψ K < ∞)
    (hlim : QuantumZipper.IsVagueLimitOn univ (fun k => gmcApproxCut γ ρ ρ₂ k ψ) (gmcLimit γ ρ ρ₂ ψ))
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    {g : ℂ → ℝ} (hgc : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hgK : HasCompactSupport g)
    (hgD : tsupport g ⊆ ball z r) (hgy : y ∉ tsupport g) :
    Tendsto (fun k => 2 * ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) *
        (ENNReal.ofReal (dyadicScale (n k) ^ (γ ^ 2 / 2) *
          Real.exp (γ * circleAverageRep ψ (dyadicScale (n k)) x)) * ENNReal.ofReal (g x)))
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (g x) ∂gmcGreenMeasure γ ρ ρ₂ z y r ψ)) := by
  set f : ℂ → ℝ := fun x => greenFunction (ball z r) y x * g x with hf_def
  have hfc : Continuous f := continuous_greenFunction_ball_mul hy hgc hgy
  have hfK : HasCompactSupport f := hgK.mono fun x hx =>
    Function.mem_support.2 fun hgx => (Function.mem_support.1 hx) (by simp only [hf_def, hgx, mul_zero])
  have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg (greenFunction_nonneg isBounded_ball y x) (hg0 x)
  have hgout : ∀ x, x ∉ ball z r → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hgD h)
  have hofReal : ∀ x, ENNReal.ofReal (f x) =
      ENNReal.ofReal (greenFunction (ball z r) y x) * ENNReal.ofReal (g x) :=
    fun x => ENNReal.ofReal_mul' (hg0 x)
  have hK : IsCompact (tsupport f) := hfK
  -- Vague convergence along `n`, written with lower Lebesgue integrals.
  have hconv := (ENNReal.continuous_ofReal.tendsto _).comp ((hlim.2.2 f hfc hfK (subset_univ _)).comp hn)
  have hlimI : ENNReal.ofReal (∫ x, f x ∂gmcLimit γ ρ ρ₂ ψ) = ∫⁻ x, ENNReal.ofReal (f x) ∂gmcLimit γ ρ ρ₂ ψ :=
    ofReal_integral_eq_lintegral_ofReal
      (integrable_of_continuous_of_hasCompactSupport_of_lt_top hfc hfK (hlim.2.1 _ hK (subset_univ _)))
      (Eventually.of_forall fun x => hf0 x)
  have happ : ∀ᶠ k in atTop, (ENNReal.ofReal ∘ fun k => ∫ x, f x ∂gmcApproxCut γ ρ ρ₂ (n k) ψ) k =
      ∫⁻ x, ENNReal.ofReal (f x) ∂gmcApproxCut γ ρ ρ₂ (n k) ψ := by
    filter_upwards [hn.eventually (hfin _ hK)] with k hk
    exact ofReal_integral_eq_lintegral_ofReal
      (integrable_of_continuous_of_hasCompactSupport_of_lt_top hfc hfK hk) (Eventually.of_forall fun x => hf0 x)
  have hT : Tendsto (fun k => ∫⁻ x, ENNReal.ofReal (f x) ∂gmcApproxCut γ ρ ρ₂ (n k) ψ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂gmcLimit γ ρ ρ₂ ψ)) := by
    rw [← hlimI]
    exact hconv.congr' happ
  -- The approximations: on `D` the cut-off is `1`, and `g` vanishes off `D`.
  have hcut : ∀ k, Measurable fun x => ENNReal.ofReal (gmcCutDensity γ ρ ρ₂ k ψ x) := fun k => by
    have h : Measurable (Function.uncurry (gmcCutDensity γ ρ ρ₂ k) ∘ fun x : ℂ => (ψ, x)) :=
      (measurable_uncurry_gmcCutDensity γ ρ ρ₂ k).comp measurable_prodMk_left
    exact h.ennreal_ofReal
  have hleft : ∀ k, ∫⁻ x, ENNReal.ofReal (f x) ∂gmcApproxCut γ ρ ρ₂ k ψ =
      ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) *
        (ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ (dyadicScale k) x)) *
          ENNReal.ofReal (g x)) := by
    intro k
    rw [gmcApproxCut, lintegral_withDensity_eq_lintegral_mul _ (hcut k) hfc.measurable.ennreal_ofReal,
      ← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ ball z r
    · rw [indicator_of_mem hx, Pi.mul_apply, gmcCutDensity,
        gmcCutoff_eq_one hρρ₂ (mem_closedBall_zero_iff.1 (hD hx)), one_mul, hofReal]
      ring
    · rw [indicator_of_notMem hx, Pi.mul_apply]
      simp [hf_def, hgout x hx]
  have hright : ∫⁻ x, ENNReal.ofReal (g x) ∂gmcGreenMeasure γ ρ ρ₂ z y r ψ =
      2 * ∫⁻ x, ENNReal.ofReal (f x) ∂gmcLimit γ ρ ρ₂ ψ := by
    rw [gmcGreenMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_greenOccupationDensity z y r)
      hgc.measurable.ennreal_ofReal, ← lintegral_const_mul _ hfc.measurable.ennreal_ofReal]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ ball z r
    · rw [Pi.mul_apply, greenOccupationDensity_of_mem hx, hofReal]
      ring
    · rw [Pi.mul_apply, greenOccupationDensity_of_notMem hx]
      simp [hf_def, hgout x hx]
  rw [hright]
  exact (ENNReal.Tendsto.const_mul hT (Or.inr (by norm_num))).congr fun k => by rw [hleft (n k)]

end MatedCRT.KilledOccupation
