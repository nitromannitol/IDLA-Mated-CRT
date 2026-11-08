import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxPathLimit

/-!
# Lemma 3.4 (item 4): convergence of the expectations of the approximate path functionals

Paper argument (`docs/campaign/GAPS-SEC3.md` item 4: "bounded convergence in probability gives convergence of its expectations").
Under the in-probability convergence of the approximate clocks uniformly on compact time intervals (the form of `IsLQGClock`), the
expectations `∫ F (approximate path at scale k) dμ` converge to `∫ F (Liouville path) dμ` for every bounded Lipschitz functional `F`.
Proof: every subsequence has a further subsequence along which the functionals converge almost surely (Borel–Cantelli,
`exists_strictMono_ae_forall_eventually_close`, cutoff inverse convergence `cutoffPath_tendsto_localUniformDist`, Lipschitz bound);
dominated convergence (`|F| ≤ 1`) gives the convergence of the expectations along it, and `tendsto_of_subseq_tendsto` concludes.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal

/-- **Convergence of the expectations of the approximate path functionals.** -/
theorem tendsto_integral_boundedLipschitz_approxPath {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F)
    {γ : ℝ} {H : ℝ → ℂ → ℝ} (hH : ∀ k : ℕ, Continuous (H (dyadicScale k)))
    {G : ContinuousPath ℂ → ℝ≥0 → ℝ} (μ : Measure (ContinuousPath ℂ)) [IsFiniteMeasure μ]
    (hconv : ∀ (T : ℝ≥0) (η : ℝ), 0 < η → Tendsto (fun k : ℕ =>
      μ {b | ∃ t ≤ T, η ≤ |lqgClockApprox γ H (dyadicScale k) b t - G b t|}) atTop (𝓝 0))
    (hTC : ∀ᵐ b ∂μ, IsTimeChangeClock (G b)) (m : ℝ≥0) :
    Tendsto (fun k : ℕ => ∫ b, F (fun t : ℝ≥0 =>
        b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ H (dyadicScale k) b s) (k : ℝ≥0) (m * t))) ∂μ)
      atTop (𝓝 (∫ b, F (fun t : ℝ≥0 => b (clockInverse (G b) (m * t))) ∂μ)) := by
  have hLip := hF
  obtain ⟨hb1, L, hL⟩ := hLip
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hconv' : ∀ (T : ℝ≥0) (η : ℝ), 0 < η → Tendsto (fun j : ℕ =>
      μ {b | ∃ t ≤ T, η ≤ |lqgClockApprox γ H (dyadicScale (ns j)) b t - G b t|}) atTop (𝓝 0) :=
    fun T η hη => (hconv T η hη).comp hns
  obtain ⟨φ, hφ, hae⟩ := exists_strictMono_ae_forall_eventually_close μ
    (fun j b t => lqgClockApprox γ H (dyadicScale (ns j)) b t) G hconv'
  have hns' : Tendsto (fun j : ℕ => ns (φ j)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hc : ∀ T : ℝ≥0, ∀ᶠ j : ℕ in atTop, T ≤ ((ns (φ j) : ℕ) : ℝ≥0) := by
    intro T
    filter_upwards [hns'.eventually_ge_atTop ⌈T⌉₊] with j hj
    exact (Nat.le_ceil T).trans (Nat.cast_le.2 hj)
  refine ⟨φ, ?_⟩
  show Tendsto (fun j : ℕ => ∫ b, F (fun t : ℝ≥0 =>
      b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ H (dyadicScale (ns (φ j))) b s) ((ns (φ j) : ℕ) : ℝ≥0) (m * t))) ∂μ)
    atTop (𝓝 (∫ b, F (fun t : ℝ≥0 => b (clockInverse (G b) (m * t))) ∂μ))
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro j
    exact (measurable_boundedLipschitz_approxPath hF (dyadicScale_pos (ns (φ j))) (hH (ns (φ j)))
      ((ns (φ j) : ℕ) : ℝ≥0) m).aestronglyMeasurable
  · exact integrable_const 1
  · intro j
    refine ae_of_all _ fun b => ?_
    rw [Real.norm_eq_abs]
    exact hb1 _
  · filter_upwards [hae, hTC] with b hb hTCb
    have hcut := cutoffPath_tendsto_localUniformDist hTCb
      (F := fun j t => lqgClockApprox γ H (dyadicScale (ns (φ j))) b t)
      (fun j => strictMono_lqgClockApprox (dyadicScale_pos (ns (φ j))) (hH (ns (φ j))) b)
      (fun j => ((ns (φ j) : ℕ) : ℝ≥0)) hc (fun T η hη => hb T η hη) b m
    have hd := hcut.const_mul L
    rw [mul_zero] at hd
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hd
    rw [Real.dist_eq]
    exact hL _ _

end MatedCRT
