import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationEnergyIsometry
import MatedCRT.Proposed.Berestycki2017

/-! # GMC based on Brownian occupation -/

namespace MatedCRT

universe u

open MeasureTheory Filter Topology HarmonicBalls
open scoped ENNReal

/-- Berestycki's GMC convergence theorem applies conditionally on almost every
Brownian path, simultaneously for all finite horizons up to exit. -/
theorem planarBrownianMotion_ae_occupation_gmc
    (hGMC : BerestyckiGMCConvergenceStmt.{u})
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Set (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ)
    (h : SignedMeasure (EuclideanSpace ℝ (Fin 2)) → Ω → ℝ)
    (θ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure θ]
    (γ : ℝ) (z : ℂ)
    (hD : IsOpen D) (hconn : IsPreconnected D) (hnonempty : D.Nonempty)
    (hbounded : Bornology.IsBounded D)
    (hg : ContinuousOn (fun p => g p.1 p.2) (closure D ×ˢ closure D))
    (hfield : IsLogCorrelatedField P D g h) (hθ : IsGMCRegularizer 2 θ)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ b ∂(planarBrownianMotion z), ∀ T : ℝ,
      ENNReal.ofReal T ≤ b.exitTime (Complex.orthonormalBasisOneI.repr ⁻¹' D) →
      let σ := pathOccupationMeasure (fun t => Complex.orthonormalBasisOneI.repr (b t.toNNReal)) T
      ∃ (μ : Ω → Measure D) (H : ℝ → Ω → EuclideanSpace ℝ (Fin 2) → ℝ),
        IsLogFieldRegularizationVersion P 2 D h θ H ∧
        TendstoWeaklyInProbability P
          (fun ε ω => gmcApprox P (σ.comap Subtype.val) γ
            (fun (ω' : Ω) (x : D) => H ε ω' x.1) ω) μ ∧
        ∀ S : Set D, MeasurableSet S →
          Integrable (fun ω => (μ ω).real S) P ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), Integrable
            (fun ω => (gmcApprox P (σ.comap Subtype.val) γ
              (fun (ω' : Ω) (x : D) => H ε ω' x.1) ω).real S) P) ∧
          Tendsto (fun ε => ∫ ω, |(gmcApprox P (σ.comap Subtype.val) γ
            (fun (ω' : Ω) (x : D) => H ε ω' x.1) ω).real S - (μ ω).real S| ∂P)
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [planarBrownianMotion_ae_euclidean_occupation_before_exit z] with b hb T hT
  let σ := pathOccupationMeasure (fun t => Complex.orthonormalBasisOneI.repr (b t.toNNReal)) T
  have hocc := hb D hD.measurableSet T hT
  have hsupport : σ (closure D)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr subset_closure) hocc.2
  have hγ' : γ < Real.sqrt (2 * (2 : ℝ)) := by norm_num; exact hγ2
  obtain ⟨μ, hμ⟩ := hGMC 2 Ω P D g h σ 2 γ hD hconn hnonempty hbounded hg
    hfield hsupport (by norm_num) (by norm_num) hocc.1 hγ hγ'
  obtain ⟨H, hH, hweak, hmass⟩ := hμ θ hθ
  refine ⟨μ, H, hH, hweak, ?_⟩
  intro S hS
  exact ⟨(hmass S hS).1, (hmass S hS).2.1, (hmass S hS).2.2.2⟩

end MatedCRT
