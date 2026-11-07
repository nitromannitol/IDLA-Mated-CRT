import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSDiskMargin

/-! # Eventual quenched rate on the comparison-disk good event -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- For fixed exponents and a fixed Hölder exponent, the GMS tail estimate
holds eventually and uniformly for disks inside the smaller comparison disk,
on each environment satisfying the displayed cell and annulus estimates. -/
theorem MatedCRTEnv.IsValid.ae_eventually_sameWalkExitDiscrepancy_le_of_gms
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 < p) (hp1 : p < 1)
    {a b ρ ρ' q : ℝ} {χ : ℝ≥0}
    (hρ : 0 < ρ) (hρρ' : ρ < ρ') (ha : 0 < a)
    (hχ : 0 < χ) (hq : 0 < q) (hqbound : q / (χ : ℝ) < min a b) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂S.P, ∀ᶠ ε : ℝ in 𝓝[>] 0,
      IsLocallyFiniteMult (S.mult ε ω) →
      (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) → 0 < S.mε ε →
      Continuous (S.η ω) → Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) →
      (∀ j k, S.mult ε ω j k ≠ 0 →
        (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) →
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ').Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a) →
      (∀ z ∈ ball (0 : ℂ) ρ', ∀ s : ℝ, ε ^ b ≤ s → s ≤ ρ' →
        ball z (2 * s) ⊆ ball 0 ρ' → ∀ j ∈ cellVertices ε (S.η ω) (ball z s),
        ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
          {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
            walkDisconnectsBeforeHit (S.mult ε ω)
              (cellVertices ε (S.η ω) (sphere z (2 * s))) y path}) →
      ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
      ∀ (ψ : ℂ → ℝ) (H : ℝ≥0), HolderOnWith H χ ψ (closedBall z r) →
      ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
        srwLaw (S.mult ε ω) v
          {path | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω path} ≤
        ENNReal.ofReal (((2 : ℝ) ^ ν * (202 : ℝ) ^ ν) *
          ε ^ ((min a b - q / (χ : ℝ)) * ν)) := by
  have hχ' : 0 < (χ : ℝ) := by exact_mod_cast hχ
  have hc : 0 < q / (χ : ℝ) := div_pos hq hχ'
  have hmargin := eventually_gms_disk_margin hρ hρρ' ha hc
  have hscale := eventually_gms_mesoscopic_scale (lt_of_lt_of_le hqbound (min_le_left a b))
    (lt_of_lt_of_le hqbound (min_le_right a b))
  obtain ⟨ν, hν, hbound⟩ := hS.ae_sameWalkExitDiscrepancy_le_of_uniform_gms hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hbound] with ω hbound
  filter_upwards [hmargin, hscale, self_mem_nhdsWithin,
    (nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)))] with ε hmargin hscale hε hε1
  intro hlf hcons hm hη hproper hadj hsize hgood r z hr hball ψ H hψ v hv
  exact hbound ε a b ρ' q z r ψ H χ v hε hε1.le hr hχ hψ hscale hlf hcons hm hη
    hproper hv hadj (hmargin z r hr hball) hsize hgood

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_eventually_sameWalkExitDiscrepancy_le_of_gms
