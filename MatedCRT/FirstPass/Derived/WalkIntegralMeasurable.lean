import MatedCRT.FirstPass.Derived.WalkFunctionalIntegral
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellMeasurable

/-!
# Measurability of the quenched walk integral from the vertex of a point

For a bounded Lipschitz path functional `F` and `z : ℂ`, the quenched walk integral
`ω ↦ ∫ F(interpolatedWalk ε (η ω) (m^ε) x) d srwLaw (S.mult ε ω) (vertexOf ε (η ω) z)` (Berestycki–Gwynne (2020),
Thm. 1.2) is almost surely equal to a measurable function of `ω` which is bounded by `1`.  The measurable version uses
the measurable version of the vertex `a^ε_z` (`exists_measurable_vertexOf`) and the measurability of the quenched path
laws `walkPathLaw` in `ω`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- **A measurable version of the quenched walk integral, bounded by `1`.** -/
theorem exists_measurable_walkIntegral {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℝ} (hε : 0 < ε) {F : (ℝ≥0 → ℂ) → ℝ}
    (hF : IsBoundedLipschitzPathFunctional F) (z : ℂ) :
    ∃ R : Ω → ℝ, Measurable R ∧ (∀ ω, |R ω| ≤ 1) ∧
      ∀ᵐ ω ∂S.P, R ω = ∫ x, F (interpolatedWalk ε (S.η ω) (S.mε ε) x) ∂srwLaw (S.mult ε ω)
        (vertexOf ε (S.η ω) z) := by
  obtain ⟨V, hV, hVe⟩ := hS.exists_measurable_vertexOf hε
  set v : Ω → ℤ → ℂ := fun ω => vertexPoint ε (⇑(η' ω)) with hvdef
  have hv : Measurable v := measurable_vertexPoint_curve hη' ε
  have hg : Measurable (fun p : Ω × ℤ => walkPathLaw S v (S.mε_nonneg ε) ε p.2 p.1) :=
    measurable_from_prod_countable_left fun k => measurable_walkPathLaw hS hv (S.mε_nonneg ε) ε k
  refine ⟨fun ω => ∫ q, blPathFunctionalBCF hF q
    ∂(walkPathLaw S v (S.mε_nonneg ε) ε (V (ω, z)) ω : Measure (ContinuousPath ℂ)), ?_, ?_, ?_⟩
  · exact (measurable_integral_probabilityMeasure_of_boundedContinuous (blPathFunctionalBCF hF)).comp
      (hg.comp (measurable_id.prodMk (hV.comp (measurable_id.prodMk measurable_const))))
  · intro ω
    have h := norm_integral_le_of_norm_le_const
      (μ := (walkPathLaw S v (S.mε_nonneg ε) ε (V (ω, z)) ω : Measure (ContinuousPath ℂ)))
      (f := fun q => blPathFunctionalBCF hF q) (C := 1)
      (ae_of_all _ fun q => by
        rw [Real.norm_eq_abs, blPathFunctionalBCF_apply]
        exact hF.1 _)
    simpa [Real.norm_eq_abs] using h
  · filter_upwards [hae, hVe] with ω hω hVω
    rw [hVω z]
    exact (integral_interpolatedWalk_eq_integral_walkPathLaw hF S ε ω (S.η ω) v
      (by simp only [hvdef]; rw [hω]) _).symm

end MatedCRT.FirstPass.Derived
