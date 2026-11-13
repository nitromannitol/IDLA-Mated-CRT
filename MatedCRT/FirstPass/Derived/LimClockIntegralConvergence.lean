import MatedCRT.FirstPass.Derived.LimClockUniform
import LatticeProb.Prob.StieltjesIntegralConvergence

/-!
# Integrals against the regularized clocks converge to integrals against the limit clock

Fix a family `ψ` of circle averages, a path `b`, an exit time `σ` and scales `ε_k`. Write
`μ_k = regClockMeasure γ (ε k) ψ σ b` for the measure `ε_k^{γ²/2} e^{γ ψ̃(ε_k, b_u)} du` on `[0, σ(b)]`, whose
distribution function is the regularized clock `Ψ_k = regClockFun γ (ε k) ψ σ b`, and `ν = limClockKernel γ ε σ (ψ, b)`
for the Stieltjes measure of the limit clock. If the integrands of the regularized clocks are bounded along `b` up to
`σ(b)` and the quenched gaps between consecutive scales are eventually at most `(1/2)^k`, then `Ψ_k` converges
uniformly to the distribution function of `ν` (`exists_limClockKernel_Iic_eq_uniform_limit_of_bdd`), and the
Helly-Bray theorem on a compact interval (`LatticeProb.Prob.tendsto_setIntegral_Icc_of_tendsto_measureReal_Iic`)
gives `∫_{[0, σ(b)]} h dμ_k → ∫_{[0, σ(b)]} h dν` for every `h` continuous on `[0, σ(b)]`; in particular
`∫_0^{σ(b)} g(b_u) dΨ_k(u) → ∫_0^{σ(b)} g(b_u) dΦ(u)` for `g` continuous on `ℂ`. This is the passage from the
regularized clocks to the Liouville clock in the identification of the occupation measure of Liouville Brownian
motion (Garban-Rhodes-Vargas, Liouville Brownian motion, Theorem 2.7; Berestycki, Diffusion in planar Liouville
quantum gravity, Sections 2-3).

* `regClockMeasure`, `regClockMeasure_Iic`, `isFiniteMeasure_regClockMeasure`: the measure `dΨ_k` on `ℝ≥0`.
* `isFiniteMeasure_limClockKernel_of_bdd`: the Stieltjes measure of the limit clock is finite.
* `tendsto_setIntegral_regClockMeasure_of_bdd`, `tendsto_setLIntegral_regClockMeasure_of_bdd`: convergence of the
  integrals (Bochner form, and lower Lebesgue form for nonnegative integrands).
* `tendsto_setIntegral_comp_regClockMeasure_of_bdd`: the case `h = g ∘ b` with `g` continuous on `ℂ`.
-/

open MeasureTheory Set Filter Topology MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The measure `ε^{γ²/2} e^{γ ψ̃(ε, b_u)} du` on `[0, σ(b)]` (Lebesgue measure on `ℝ≥0`), whose distribution
function is the regularized clock `regClockFun γ ε ψ σ b`. -/
noncomputable def regClockMeasure (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (b : ContinuousPath ℂ) : Measure ℝ≥0 :=
  (lebNN.restrict (Icc 0 (σ b))).withDensity fun u =>
    ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u)))

section RegClockMeasure

variable (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ)

/-- The regularized clock is the distribution function of `regClockMeasure`. -/
theorem regClockMeasure_Iic (t : ℝ≥0) : regClockMeasure γ ε ψ σ b (Iic t) = regClockFun γ ε ψ σ b t :=
  (regClockFun_eq_withDensity_Iic γ ε ψ σ b t).symm

/-- The total mass of `regClockMeasure` is the regularized clock at the exit time. -/
theorem regClockMeasure_univ : regClockMeasure γ ε ψ σ b univ = regClockFun γ ε ψ σ b (σ b) := by
  unfold regClockMeasure regClockFun
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, min_self]

/-- If the regularized clock is finite at the exit time, `regClockMeasure` is a finite measure. -/
theorem isFiniteMeasure_regClockMeasure (hfin : regClockFun γ ε ψ σ b (σ b) ≠ ∞) :
    IsFiniteMeasure (regClockMeasure γ ε ψ σ b) :=
  ⟨by rw [regClockMeasure_univ]; exact lt_top_iff_ne_top.2 hfin⟩

end RegClockMeasure

/-- **The Stieltjes measure of the limit clock is finite** when the integrands of the regularized clocks are bounded
along the path up to the exit time and the quenched gaps are eventually at most `(1/2)^k`: its distribution function
is bounded by its value at the exit time. -/
theorem isFiniteMeasure_limClockKernel_of_bdd (γ : ℝ) (ε : ℕ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ)
    (hbd : ∀ k, ∃ M : ℝ≥0, ∀ u ≤ σ b,
      ENNReal.ofReal ((ε k) ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ (ε k) (b u))) ≤ M)
    (hgap : ∀ᶠ k in atTop, clockGapFun γ σ (ε k) (ε (k + 1)) (ψ, b) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) :
    IsFiniteMeasure (limClockKernel γ ε σ (ψ, b)) := by
  obtain ⟨G, -, hGmono, hG0, hGmin, -, htrunc, -⟩ :=
    exists_limClockKernel_Iic_eq_uniform_limit_of_bdd γ ε σ ψ b hbd hgap
  have hGnn : ∀ t, 0 ≤ G t := fun t => hG0 ▸ hGmono zero_le
  unfold limClockKernel
  refine (limClockStieltjes γ ε σ (ψ, b)).isFiniteMeasure_of_forall_abs_le (C := G (σ b)) fun t => ?_
  show |limClockTrunc γ ε σ (ψ, b) t| ≤ G (σ b)
  rw [htrunc, abs_of_nonneg (hGnn t), ← hGmin t]
  exact hGmono (min_le_right _ _)

/-- **H3: integrals against the regularized clocks converge to the integral against the limit clock.** If the
integrands of the regularized clocks are bounded along `b` up to `σ(b)` and the quenched gaps between consecutive
scales are eventually at most `(1/2)^k`, then for every `h` continuous on `[0, σ(b)]`,
`∫_{[0, σ(b)]} h dΨ_k → ∫_{[0, σ(b)]} h dΦ`, where `Φ` is the limit clock. -/
theorem tendsto_setIntegral_regClockMeasure_of_bdd (γ : ℝ) (ε : ℕ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ)
    (hbd : ∀ k, ∃ M : ℝ≥0, ∀ u ≤ σ b,
      ENNReal.ofReal ((ε k) ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ (ε k) (b u))) ≤ M)
    (hgap : ∀ᶠ k in atTop, clockGapFun γ σ (ε k) (ε (k + 1)) (ψ, b) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    {h : ℝ≥0 → ℝ} (hh : ContinuousOn h (Icc 0 (σ b))) :
    Tendsto (fun k => ∫ u in Icc 0 (σ b), h u ∂regClockMeasure γ (ε k) ψ σ b) atTop
      (𝓝 (∫ u in Icc 0 (σ b), h u ∂limClockKernel γ ε σ (ψ, b))) := by
  have := isFiniteMeasure_limClockKernel_of_bdd γ ε σ ψ b hbd hgap
  obtain ⟨G, -, hGmono, hG0, -, hU, -, hker⟩ :=
    exists_limClockKernel_Iic_eq_uniform_limit_of_bdd γ ε σ ψ b hbd hgap
  have hGnn : ∀ t, 0 ≤ G t := fun t => hG0 ▸ hGmono zero_le
  choose M hM using hbd
  have : ∀ k, IsFiniteMeasure (regClockMeasure γ (ε k) ψ σ b) := fun k =>
    isFiniteMeasure_regClockMeasure γ (ε k) ψ σ b
      (regClockFun_ne_top_and_continuous_of_le γ (ε k) ψ σ b (M k) (hM k)).1
  refine LatticeProb.Prob.tendsto_setIntegral_Icc_of_tendsto_measureReal_Iic (fun t _ => ?_) hh
  have h1 : ∀ k, (regClockMeasure γ (ε k) ψ σ b).real (Iic t) = (regClockFun γ (ε k) ψ σ b t).toReal :=
    fun k => by rw [Measure.real, regClockMeasure_Iic]
  have h2 : (limClockKernel γ ε σ (ψ, b)).real (Iic t) = G t := by
    rw [Measure.real, hker t, ENNReal.toReal_ofReal (hGnn t)]
  simp only [h1, h2]
  exact hU.tendsto_at t

/-- **H3, lower Lebesgue integral form.** Under the hypotheses of `tendsto_setIntegral_regClockMeasure_of_bdd`, for
every `h` continuous and nonnegative on `[0, σ(b)]`, `∫⁻_{[0, σ(b)]} h dΨ_k → ∫⁻_{[0, σ(b)]} h dΦ`. -/
theorem tendsto_setLIntegral_regClockMeasure_of_bdd (γ : ℝ) (ε : ℕ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ)
    (hbd : ∀ k, ∃ M : ℝ≥0, ∀ u ≤ σ b,
      ENNReal.ofReal ((ε k) ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ (ε k) (b u))) ≤ M)
    (hgap : ∀ᶠ k in atTop, clockGapFun γ σ (ε k) (ε (k + 1)) (ψ, b) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    {h : ℝ≥0 → ℝ} (hh : ContinuousOn h (Icc 0 (σ b))) (hh0 : ∀ u ∈ Icc 0 (σ b), 0 ≤ h u) :
    Tendsto (fun k => ∫⁻ u in Icc 0 (σ b), ENNReal.ofReal (h u) ∂regClockMeasure γ (ε k) ψ σ b) atTop
      (𝓝 (∫⁻ u in Icc 0 (σ b), ENNReal.ofReal (h u) ∂limClockKernel γ ε σ (ψ, b))) := by
  have hI : ∀ (m : Measure ℝ≥0) [IsFiniteMeasure m],
      ∫⁻ u in Icc 0 (σ b), ENNReal.ofReal (h u) ∂m = ENNReal.ofReal (∫ u in Icc 0 (σ b), h u ∂m) := by
    intro m _
    exact (ofReal_integral_eq_lintegral_ofReal (hh.integrableOn_compact isCompact_Icc)
      (ae_restrict_of_forall_mem measurableSet_Icc hh0)).symm
  have := isFiniteMeasure_limClockKernel_of_bdd γ ε σ ψ b hbd hgap
  have hfin : ∀ k, IsFiniteMeasure (regClockMeasure γ (ε k) ψ σ b) := by
    choose M hM using hbd
    exact fun k => isFiniteMeasure_regClockMeasure γ (ε k) ψ σ b
      (regClockFun_ne_top_and_continuous_of_le γ (ε k) ψ σ b (M k) (hM k)).1
  rw [hI]
  refine (ENNReal.tendsto_ofReal (tendsto_setIntegral_regClockMeasure_of_bdd γ ε σ ψ b hbd hgap hh)).congr
    fun k => ?_
  have := hfin k
  exact (hI _).symm

/-- **H3 along the path.** Under the hypotheses of `tendsto_setIntegral_regClockMeasure_of_bdd`, for every `g`
continuous on `ℂ`, `∫_0^{σ(b)} g(b_u) dΨ_k(u) → ∫_0^{σ(b)} g(b_u) dΦ(u)`. -/
theorem tendsto_setIntegral_comp_regClockMeasure_of_bdd (γ : ℝ) (ε : ℕ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ)
    (hbd : ∀ k, ∃ M : ℝ≥0, ∀ u ≤ σ b,
      ENNReal.ofReal ((ε k) ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ (ε k) (b u))) ≤ M)
    (hgap : ∀ᶠ k in atTop, clockGapFun γ σ (ε k) (ε (k + 1)) (ψ, b) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    {g : ℂ → ℝ} (hg : Continuous g) :
    Tendsto (fun k => ∫ u in Icc 0 (σ b), g (b u) ∂regClockMeasure γ (ε k) ψ σ b) atTop
      (𝓝 (∫ u in Icc 0 (σ b), g (b u) ∂limClockKernel γ ε σ (ψ, b))) :=
  tendsto_setIntegral_regClockMeasure_of_bdd γ ε σ ψ b hbd hgap (hg.comp b.continuous).continuousOn

end MatedCRT.KilledOccupation
