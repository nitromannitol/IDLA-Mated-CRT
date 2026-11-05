import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.DeterminingTests
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.OccupationConvergence
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.DenseTestConvergence

/-! # Identification of a subsequential limit by test integrals

Deterministic core of the proof of Lemma 3.3 (paper, lines 1200-1229): if `g_n → ū` uniformly on
compact subsets of an open set `D`, the measures `ν_n` converge vaguely to `6 μ`, and the integrals
`∫ f g_n dν_n` converge to `c ∫_B G f dμ` for a countable family of localizing tests supported in
`D`, then `ū = (c/6) G` on `D`. -/

namespace MatedCRT.GreenEnvironment

open Set Metric Topology MeasureTheory Filter

/-- The product of a continuous function with a function continuous on an open set containing the
support of the first is continuous. -/
theorem continuous_mul_of_continuousOn_tsupport {f g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hf : Continuous f) (hg : ContinuousOn g U) (hfU : tsupport f ⊆ U) :
    Continuous fun x => f x * g x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact hf.continuousAt.mul (hg.continuousAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport f := fun h => hx (hfU h)
    have hev : (fun x => f x * g x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with w hw
      simp only [hw, Pi.zero_apply, zero_mul]
    exact continuousAt_const.congr hev.symm

/-- **Identification of the limit.** -/
theorem eqOn_of_uniform_limit_and_tests
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {D B : Set ℂ} (hDo : IsOpen D) (hDB : D ⊆ B)
    (G : ℂ → ℝ) (hG : ContinuousOn G D) (c : ℝ) (ubar : ℂ → ℝ) (hubar : ContinuousOn ubar D)
    (g : ℕ → ℂ → ℝ) (ν : ℕ → Measure ℂ)
    (hfin : ∀ K, IsCompact K → ∀ᶠ n in atTop, ν n K < ⊤)
    (hvague : ∀ h : ℂ → ℝ, Continuous h → HasCompactSupport h →
      Tendsto (fun n => ∫ x, h x ∂ν n) atTop (𝓝 (6 * ∫ x, h x ∂μ)))
    (hunif : ∀ O, IsCompact O → O ⊆ D → TendstoUniformlyOn g ubar atTop O)
    (f : ℕ → ℂ → ℝ) (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i))
    (hfn : ∀ i x, 0 ≤ f i x)
    (hlocal : ∀ V : Set ℂ, IsOpen V → V.Nonempty → ∃ i, tsupport (f i) ⊆ V ∧ ∃ x, 0 < f i x)
    (hgint : ∀ i, tsupport (f i) ⊆ D → ∀ᶠ n in atTop,
      Integrable (fun x => f i x * g n x) (ν n))
    (htest : ∀ i, tsupport (f i) ⊆ D → Tendsto (fun n => ∫ x, f i x * g n x ∂ν n) atTop
      (𝓝 (c * ∫ x in B, G x * f i x ∂μ))) :
    EqOn ubar (fun x => c / 6 * G x) D := by
  apply eqOn_of_localizing_tests (μ := μ) hDo hubar (continuousOn_const.mul hG) f hf hfc hfn hlocal
  intro i hi
  have hT : IsCompact (tsupport (f i)) := hfc i
  have hhc : Continuous fun x => f i x * ubar x :=
    continuous_mul_of_continuousOn_tsupport hDo (hf i) hubar hi
  have hhs : HasCompactSupport fun x => f i x * ubar x := (hfc i).mul_right
  have hGc : Continuous fun x => f i x * G x :=
    continuous_mul_of_continuousOn_tsupport hDo (hf i) hG hi
  have hGs : HasCompactSupport fun x => f i x * G x := (hfc i).mul_right
  have hac : Continuous fun x => |f i x| := (hf i).abs
  have has : HasCompactSupport fun x => |f i x| := (hfc i).comp_left abs_zero
  have hlim1 : Tendsto (fun n => ∫ x, f i x * g n x ∂ν n) atTop
      (𝓝 (6 * ∫ x, f i x * ubar x ∂μ)) := by
    refine tendsto_of_eventually_abs_sub_le (hvague _ hhc hhs) (hvague _ hac has) ?_
    intro δ hδ
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hunif _ hT hi) δ hδ, hgint i hi,
      hfin _ hT] with n hn hint hfinT
    have hTi : ∀ {h : ℂ → ℝ}, Continuous h → HasCompactSupport h → tsupport h ⊆ tsupport (f i) →
        Integrable h (ν n) := fun hc hs hsub =>
      VagueWholePlane.IsTestC.integrable ⟨hc, hs⟩ (lt_of_le_of_lt (measure_mono hsub) hfinT)
    have hhi : Integrable (fun x => f i x * ubar x) (ν n) :=
      hTi hhc hhs (tsupport_mul_subset_left)
    have hai : Integrable (fun x => |f i x|) (ν n) :=
      hTi hac has (tsupport_comp_subset abs_zero _)
    rw [← integral_sub hint hhi, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans
      (integral_mono (hint.sub hhi).abs (hai.const_mul δ) fun x => ?_)
    show |f i x * g n x - f i x * ubar x| ≤ δ * |f i x|
    by_cases hx : x ∈ tsupport (f i)
    · have h1 := hn x hx
      rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] at h1
      rw [← mul_sub, abs_mul, mul_comm δ]
      exact mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
    · have hfx : f i x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hfx]
      simp
  have heq := tendsto_nhds_unique hlim1 (htest i hi)
  have hBint : ∫ x in B, G x * f i x ∂μ = ∫ x, f i x * G x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    · intro x hx
      have hfx : f i x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hx (hDB (hi h))
      rw [hfx, mul_zero]
  have hint1 : Integrable (fun x => f i x * ubar x) μ := hhc.integrable_of_hasCompactSupport hhs
  have hint2 : Integrable (fun x => f i x * G x) μ := hGc.integrable_of_hasCompactSupport hGs
  have hsplit : (fun x => f i x * (ubar x - c / 6 * G x)) =
      fun x => f i x * ubar x - c / 6 * (f i x * G x) := by
    funext x
    ring
  show ∫ x, f i x * (ubar x - c / 6 * G x) ∂μ = 0
  rw [hsplit, integral_sub hint1 (hint2.const_mul _), integral_const_mul]
  rw [hBint] at heq
  linarith

end MatedCRT.GreenEnvironment
