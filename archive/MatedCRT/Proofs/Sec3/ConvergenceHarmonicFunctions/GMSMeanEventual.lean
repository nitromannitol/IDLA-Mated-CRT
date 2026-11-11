import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSMeanRates
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSFixedScale
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkDiscrepancyZero

/-! A fixed mean-rate constant for the GMS comparison. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The mean-rate bound holds on one deterministic neighborhood of zero,
for almost every environment simultaneously and for all geometric data. -/
theorem MatedCRTEnv.IsValid.uniform_mesh_ae_sameWalkExitDiscrepancy_mean_of_gms
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ (ρ ρ' a b r : ℝ) (χ : ℝ≥0),
      0 < ρ → ρ < ρ' → 0 < a → 0 < b → 0 < r → 0 < χ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ U : Set ℝ, U ∈ 𝓝[>] 0 ∧ ∀ᵐ ω ∂S.P, ∀ ε ∈ U,
        ∀ (z : ℂ) (ψ : ℂ → ℝ) (H : ℝ≥0) (v : ℤ),
        ball z r ⊆ ball 0 ρ → HolderOnWith H χ ψ (closedBall z r) →
        IsLocallyFiniteMult (S.mult ε ω) →
        (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) → 0 < S.mε ε →
        Continuous (S.η ω) → Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) →
        v ∈ interiorCellVertices ε (S.η ω) (ball z r) →
        (∀ j k, S.mult ε ω j k ≠ 0 →
          (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) →
        (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ').Nonempty →
          diam (cell ε (S.η ω) i) ≤ ε ^ a) →
        (∀ z ∈ ball (0 : ℂ) ρ', ∀ t : ℝ, ε ^ b ≤ t → t ≤ ρ' →
          ball z (2 * t) ⊆ ball 0 ρ' → ∀ j ∈ cellVertices ε (S.η ω) (ball z t),
          ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
            {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (t / 2)),
              walkDisconnectsBeforeHit (S.mult ε ω)
                (cellVertices ε (S.η ω) (sphere z (2 * t))) y path}) →
        (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
          C * (H : ℝ) *
            (if (χ : ℝ) < ν then ε ^ (min a b * χ)
             else if (χ : ℝ) = ν then ε ^ (min a b * ν) * (1 + |Real.log ε|)
             else ε ^ (min a b * ν)) := by
  obtain ⟨ν, hν, hmean⟩ := hS.ae_sameWalkExitDiscrepancy_mean_rates_of_gms hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  intro ρ ρ' a b r χ hρ hρρ' ha hb hr hχ
  obtain ⟨T, hT, hTr, hevent⟩ := exists_fixed_gms_comparison_scale hρ hρρ' ha hb hr
  let K := (r / T) ^ ν
  let D1 := (202 : ℝ) ^ (χ : ℝ) * (1 + (χ : ℝ) * K / (ν - χ))
  let D2 := (202 : ℝ) ^ ν * (1 + ν * K * (|Real.log r| + |min a b|))
  let D3 := (202 : ℝ) ^ (χ : ℝ) + (χ : ℝ) * K * (202 : ℝ) ^ ν *
    r ^ ((χ : ℝ) - ν) / ((χ : ℝ) - ν)
  let M := max 0 (max D1 (max D2 D3))
  let C := (2 : ℝ) ^ (χ : ℝ) * M
  have hM : 0 ≤ M := le_max_left _ _
  have hD1 : D1 ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hD2 : D2 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hD3 : D3 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hM
  refine ⟨C, hC, _, hevent, ?_⟩
  filter_upwards [hmean] with ω hmean
  intro ε hε z ψ H v hball hψ hlf hcons hm hη hproper hv hadj hsize hann
  obtain ⟨hε0, hε1, hcut, hmargin⟩ := hε
  by_cases hH : H = 0
  · subst H
    have hz := srwLaw_sameWalkExitDiscrepancy_integral_eq_zero_of_holder_zero S hr z ψ hψ hε0 ω v
      hlf hcons hm hη hproper hv
    simp [hz]
  have hHpos : 0 < H := pos_iff_ne_zero.mpr hH
  have hrates := hmean ε a b ρ' z r ψ H χ v T hHpos hχ hTr hε0 hε1
    (le_min ha.le hb.le) hr hψ hcut hlf hcons hm hη hproper hv hadj (hmargin z hball) hsize hann
  have hfactor : ∀ D s : ℝ, D ≤ M → 0 ≤ s →
      ((H : ℝ) * (2 : ℝ) ^ (χ : ℝ)) * D * s ≤ C * (H : ℝ) * s := by
    intro D s hD hs
    calc
      ((H : ℝ) * (2 : ℝ) ^ (χ : ℝ)) * D * s =
          ((2 : ℝ) ^ (χ : ℝ) * (H : ℝ) * s) * D := by ring
      _ ≤ ((2 : ℝ) ^ (χ : ℝ) * (H : ℝ) * s) * M :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      _ = C * (H : ℝ) * s := by dsimp [C]; ring
  by_cases hlt : (χ : ℝ) < ν
  · simp only [ite_eq_left hlt]
    exact (hrates.1 hlt).trans (hfactor D1 _ hD1 (Real.rpow_nonneg hε0.le _))
  · by_cases heq : (χ : ℝ) = ν
    · simp only [ite_eq_right hlt, ite_eq_left heq]
      have hbnd := hfactor D2 (ε ^ (min a b * ν) * (1 + |Real.log ε|)) hD2 (by positivity)
      exact (hrates.2.1 heq).trans (by convert hbnd using 1; ring)
    · simp only [ite_eq_right hlt, ite_eq_right heq]
      have hgt : ν < (χ : ℝ) := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      exact (hrates.2.2 hgt).trans (hfactor D3 _ hD3 (Real.rpow_nonneg hε0.le _))

/-- Under the displayed geometric hypotheses, one constant controls all three
mean-discrepancy regimes for sufficiently small mesh. It is uniform in the
center, boundary datum, Hölder constant, and starting vertex. -/
theorem MatedCRTEnv.IsValid.eventually_ae_sameWalkExitDiscrepancy_mean_of_gms
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ (ρ ρ' a b r : ℝ) (χ : ℝ≥0),
      0 < ρ → ρ < ρ' → 0 < a → 0 < b → 0 < r → 0 < χ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂S.P, ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ∀ (z : ℂ) (ψ : ℂ → ℝ) (H : ℝ≥0) (v : ℤ),
        ball z r ⊆ ball 0 ρ → HolderOnWith H χ ψ (closedBall z r) →
        IsLocallyFiniteMult (S.mult ε ω) →
        (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) → 0 < S.mε ε →
        Continuous (S.η ω) → Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) →
        v ∈ interiorCellVertices ε (S.η ω) (ball z r) →
        (∀ j k, S.mult ε ω j k ≠ 0 →
          (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) →
        (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ').Nonempty →
          diam (cell ε (S.η ω) i) ≤ ε ^ a) →
        (∀ z ∈ ball (0 : ℂ) ρ', ∀ t : ℝ, ε ^ b ≤ t → t ≤ ρ' →
          ball z (2 * t) ⊆ ball 0 ρ' → ∀ j ∈ cellVertices ε (S.η ω) (ball z t),
          ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
            {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (t / 2)),
              walkDisconnectsBeforeHit (S.mult ε ω)
                (cellVertices ε (S.η ω) (sphere z (2 * t))) y path}) →
        (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
          C * (H : ℝ) *
            (if (χ : ℝ) < ν then ε ^ (min a b * χ)
             else if (χ : ℝ) = ν then ε ^ (min a b * ν) * (1 + |Real.log ε|)
             else ε ^ (min a b * ν)) := by
  obtain ⟨ν, hν, hbound⟩ := hS.uniform_mesh_ae_sameWalkExitDiscrepancy_mean_of_gms hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  intro ρ ρ' a b r χ hρ hρρ' ha hb hr hχ
  obtain ⟨C, hC, U, hU, hbound⟩ := hbound ρ ρ' a b r χ hρ hρρ' ha hb hr hχ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with ω hω
  filter_upwards [hU] with ε hε
  exact hω ε hε

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.eventually_ae_sameWalkExitDiscrepancy_mean_of_gms

#print axioms MatedCRT.MatedCRTEnv.IsValid.uniform_mesh_ae_sameWalkExitDiscrepancy_mean_of_gms
