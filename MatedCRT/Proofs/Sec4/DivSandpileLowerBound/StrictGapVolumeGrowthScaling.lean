import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapVolumeGrowthRepresentative

/-! Volume growth is stable under positive finite changes of mass. -/

namespace MatedCRT

open Set MeasureTheory Metric Filter Topology _root_.HarmonicBalls

/-- Multiplying a volume-growth measure by a positive finite scalar preserves
volume growth, possibly with different exponents. -/
theorem volumeGrowth_smul_ofReal {μ : Measure ℂ} {R βm βp a : ℝ}
    (hV : VolumeGrowth μ R βm βp) (ha : 0 < a) :
    VolumeGrowth (ENNReal.ofReal a • μ) R (βm + 1) (βp / 2) := by
  obtain ⟨hβm, hβp, r₀, hr₀, hmass⟩ := hV
  have hp : 0 < βp / 2 := by positivity
  have hsmall : ∀ᶠ r : ℝ in 𝓝 0, r ^ (βp / 2) < a⁻¹ := by
    have hc := (Real.continuousAt_rpow_const 0 (βp / 2) (Or.inr hp.le)).tendsto
    have hmem : Iio a⁻¹ ∈ 𝓝 ((0 : ℝ) ^ (βp / 2)) := by
      rw [Real.zero_rpow (ne_of_gt hp)]
      exact Iio_mem_nhds (inv_pos.mpr ha)
    exact hc.eventually hmem
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨by linarith, hp, min r₀ (min a δ), by positivity, ?_⟩
  intro r hr hrr z hz
  have hrr₀ : r < r₀ := lt_of_lt_of_le hrr (min_le_left _ _)
  have hra : r < a := lt_of_lt_of_le hrr ((min_le_right _ _).trans (min_le_left _ _))
  have hrδ : r < δ := lt_of_lt_of_le hrr ((min_le_right _ _).trans (min_le_right _ _))
  have hpwr : r ^ (βp / 2) < a⁻¹ := hδsmall (by simpa [Real.dist_eq, abs_of_pos hr] using hrδ)
  have hl := (hmass r hr hrr₀ z hz).1
  have hu := (hmass r hr hrr₀ z hz).2
  have hlow : r ^ (βm + 1) ≤ a * r ^ βm := by
    rw [Real.rpow_add hr, Real.rpow_one]
    nlinarith [Real.rpow_nonneg hr.le βm]
  have hupp : a * r ^ βp ≤ r ^ (βp / 2) := by
    have heq : βp = βp / 2 + βp / 2 := by ring
    conv_lhs => rw [heq, Real.rpow_add hr]
    have hprod : a * r ^ (βp / 2) ≤ 1 := by
      rw [inv_eq_one_div] at hpwr
      have := (lt_div_iff₀ ha).mp hpwr
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hr.le (βp / 2))
    nlinarith
  simp only [Measure.smul_apply, smul_eq_mul]
  constructor
  · calc
      ENNReal.ofReal (r ^ (βm + 1)) ≤ ENNReal.ofReal (a * r ^ βm) := ENNReal.ofReal_le_ofReal hlow
      _ = ENNReal.ofReal a * ENNReal.ofReal (r ^ βm) := ENNReal.ofReal_mul ha.le
      _ ≤ ENNReal.ofReal a * μ (ball z r) := by gcongr
  · calc
      ENNReal.ofReal a * μ (ball z r) ≤ ENNReal.ofReal a * ENNReal.ofReal (r ^ βp) := by gcongr
      _ = ENNReal.ofReal (a * r ^ βp) := (ENNReal.ofReal_mul ha.le).symm
      _ ≤ ENNReal.ofReal (r ^ (βp / 2)) := ENNReal.ofReal_le_ofReal hupp

/-- The scaled-volume-growth condition in the fixed-time reduction follows
from the unscaled one. -/
theorem ae_no_regularization_defect_of_restricted_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμm : AEMeasurable μ P) {R t γ : ℝ} {z : ℂ}
    (hR : 0 < R) (ht : 0 < t) (hγ : γ ≠ 0) (hz : z ∈ ball 0 R)
    (hregular : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (μ ω) ∧
      VolumeGrowth (μ ω) R βm βp ∧
      ∀ s : ℝ, 0 < s → closure (cluster (μ ω) R z s) ⊆ ball 0 R →
        μ ω (frontier (cluster (μ ω) R z s)) = 0)
    (hlaw : ∀ c : ℝ,
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) •
        (μ ω).restrict (ball 0 R)) P ≪
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) •
        (μ ω).restrict (ball 0 R)) P) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) R z t) ⊆ ball 0 R →
      interior (closure (cluster (μ ω) R z t)) = cluster (μ ω) R z t := by
  apply ae_no_regularization_defect_of_scaled_volumeGrowth P μ hμm hR ht hγ hz hregular _ hlaw
  filter_upwards [hregular] with ω hω
  obtain ⟨βm, βp, hlocal, hV, _⟩ := hω
  intro c
  let _ : IsLocallyFiniteMeasure (μ ω) := hlocal
  let _ : IsFiniteMeasureOnCompacts (ENNReal.ofReal (Real.exp (γ * c)) • μ ω) :=
    IsFiniteMeasureOnCompacts.smul (μ ω) ENNReal.ofReal_ne_top
  exact ⟨inferInstance, βm + 1, βp / 2, volumeGrowth_smul_ofReal hV (Real.exp_pos _)⟩

end MatedCRT
