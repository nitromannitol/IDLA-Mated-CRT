import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSUniformRate
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnealedTailRate

/-! Annealed same-walk rate from the GMS quenched estimate. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The GMS quenched estimate gives the annealed same-walk bound for any
random starting vertex, provided the displayed geometric and annulus
conditions hold almost everywhere outside an exceptional environment set. -/
theorem MatedCRTEnv.IsValid.annealed_sameWalkExitDiscrepancy_le_of_uniform_gms
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ (ε a b ρ q : ℝ) (z : ℂ)
      (r : ℝ) (ψ : ℂ → ℝ) (H χ : ℝ≥0) (v : Ω → ℤ) (B : Set Ω) (A : ℝ),
      0 < ε → ε ≤ 1 → 0 < r → 0 < χ → 0 ≤ A →
      HolderOnWith H χ ψ (closedBall z r) →
      4 * (100 * ε ^ a + ε ^ b) ≤ ε ^ (q / (χ : ℝ)) / 2 →
      r + 3 * ε ^ a + dist z 0 + ε ^ a + 2 * (ε ^ (q / (χ : ℝ)) / 2) < ρ →
      S.P B ≤ ENNReal.ofReal A →
      (∀ᵐ ω ∂S.P, ω ∉ B →
        IsLocallyFiniteMult (S.mult ε ω) ∧
        (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) ∧ 0 < S.mε ε ∧
        Continuous (S.η ω) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
        v ω ∈ interiorCellVertices ε (S.η ω) (ball z r) ∧
        (∀ j k, S.mult ε ω j k ≠ 0 →
          (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) ∧
        (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
          diam (cell ε (S.η ω) i) ≤ ε ^ a) ∧
        (∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ b ≤ s → s ≤ ρ →
          ball z (2 * s) ⊆ ball 0 ρ → ∀ j ∈ cellVertices ε (S.η ω) (ball z s),
          ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
            {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
              walkDisconnectsBeforeHit (S.mult ε ω)
                (cellVertices ε (S.η ω) (sphere z (2 * s))) y path})) →
      sectionwiseOuterProb S.P (fun ω => srwLaw (S.mult ε ω) (v ω))
        {p | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2} ≤
      ENNReal.ofReal (A + (((2 : ℝ) ^ ν * (202 : ℝ) ^ ν) *
        ε ^ ((min a b - q / (χ : ℝ)) * ν))) := by
  obtain ⟨ν, hν, hbound⟩ := hS.ae_sameWalkExitDiscrepancy_le_of_uniform_gms hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  intro ε a b ρ q z r ψ H χ v B A hε hε1 hr hχ hA hψ hscale hmargin hB hgood
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply sectionwiseOuterProb_le_of_ae_quenched_and_environment S.P
    (fun ω => srwLaw (S.mult ε ω) (v ω)) (fun _ => le_of_eq measure_univ) _ B hA
    (by positivity) hB
  filter_upwards [hbound, hgood] with ω hbound hgood
  intro hω
  obtain ⟨hlf, hcons, hm, hη, hproper, hv, hadj, hsize, hann⟩ := hgood hω
  exact hbound ε a b ρ q z r ψ H χ (v ω) hε hε1 hr hχ hψ hscale hlf hcons hm hη
    hproper hv hadj hmargin hsize hann

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.annealed_sameWalkExitDiscrepancy_le_of_uniform_gms
