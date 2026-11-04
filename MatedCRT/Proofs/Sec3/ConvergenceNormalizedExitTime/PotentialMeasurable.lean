import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PointwiseConvergence

/-! Measurability of continuum Green integrals. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls
open scoped ENNReal

/-- A truncated Green integral has an almost-everywhere measurable version
when its deterministic truncation circle is null. -/
theorem greenIntegral_aemeasurable_fixed_truncation
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r δ : ℝ} {z y : ℂ} (hr : 0 < r) (hδ : 0 < δ)
    (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hsmall : δ + dist y z < r)
    (hcircle : ∀ᵐ ω ∂S.P, S.μ ω (sphere y δ) = 0) :
    AEMeasurable (fun ω => ∫ x in ball z r \ ball y δ,
      S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω) S.P := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepos : ∀ n, 0 < e n := by intro n; dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hepos⟩
  obtain ⟨ns, _, hns⟩ := greenSum_ae_subsequence_fixed_truncation 𝒮 h33 hγ hγ2 hρ hρ1
    S hS hr hδ hball hy hsmall hcircle e he
  apply aemeasurable_of_tendsto_metrizable_ae atTop _ hns
  intro n
  obtain ⟨X, hX, hXa⟩ := hS.exists_measurable_truncatedGreenSum (hepos (ns n)) z y r δ
  exact hX.aemeasurable.congr hXa

/-- Real convergence in probability gives convergence in measure. -/
theorem tendstoInMeasure_of_real_tendstoInProbability
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : ℝ → Ω → ℝ) (U : Ω → ℝ)
    (h : TendstoInProbability P F U) : TendstoInMeasure P F (𝓝[>] 0) U := by
  apply tendstoInMeasure_of_ne_top
  intro t ht httop
  let d : ℝ := t.toReal / 2
  have hd : 0 < d := half_pos (ENNReal.toReal_pos ht.ne' httop)
  have hdt : ENNReal.ofReal d < t := by
    calc
      ENNReal.ofReal d < ENNReal.ofReal t.toReal :=
        (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos ht.ne' httop)).2
          (by dsimp [d]; linarith [ENNReal.toReal_pos ht.ne' httop])
      _ = t := ENNReal.ofReal_toReal httop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h d hd)
    (fun _ => zero_le)
  intro δ
  apply measure_mono
  intro ω hω
  by_contra hn
  have hb : edist (F δ ω) (U ω) ≤ ENNReal.ofReal d := by
    have hab : |F δ ω - U ω| ≤ d := le_of_not_gt hn
    simpa [edist_dist, Real.dist_eq] using ENNReal.ofReal_le_ofReal hab
  exact (not_le_of_gt (lt_of_le_of_lt hb hdt)) hω

/-- The full normalized exit potential at a fixed interior point is
almost-everywhere measurable. -/
theorem normalizedExitGreenPotential_aemeasurable
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) : AEMeasurable (fun ω => normalizedExitGreenPotential S r z ω y) S.P := by
  let V : ℝ → Ω → ℝ := fun δ ω => ∫ x in ball z r \ ball y δ,
    S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω
  let U : Ω → ℝ := fun ω => ∫ x in ball z r,
    S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω
  have hyz : dist y z < r := hy
  have hex : ∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 / ((n : ℝ) + 1) ∧
      δ + dist y z < r ∧ ∀ᵐ ω ∂S.P, S.μ ω (sphere y δ) = 0 := by
    intro n
    have hR : 0 < min (1 / ((n : ℝ) + 1)) (r - dist y z) :=
      lt_min (by positivity) (by linarith)
    obtain ⟨δ, hδ, hδR, hnull⟩ := hS.exists_ae_null_sphere y hR
    refine ⟨δ, hδ, hδR.trans_le (min_le_left _ _), ?_, hnull⟩
    have h := hδR.trans_le (min_le_right (1 / ((n : ℝ) + 1)) (r - dist y z))
    linarith
  choose δ hδ hδn hδr hnull using hex
  have hδlim : Tendsto δ atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hδ n).le)
      (fun n => (hδn n).le), Eventually.of_forall hδ⟩
  have hV : ∀ n, AEMeasurable (V (δ n)) S.P := by
    intro n
    exact greenIntegral_aemeasurable_fixed_truncation 𝒮 h33 hγ hγ2 hρ hρ1 S hS
      hr (hδ n) hball hy (hδr n) (hnull n)
  have hprob : TendstoInProbability S.P V U :=
    greenIntegral_truncation_tendstoInProbability 𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hball hy
  have hmeasure := (tendstoInMeasure_of_real_tendstoInProbability S.P V U hprob).comp hδlim
  obtain ⟨ns, _, hns⟩ := hmeasure.exists_seq_tendsto_ae
  have hU : AEMeasurable U S.P := aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => hV (ns n)) hns
  simpa only [U, normalizedExitGreenPotential, integral_const_mul] using hU

end MatedCRT
