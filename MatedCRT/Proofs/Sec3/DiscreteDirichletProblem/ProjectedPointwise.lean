import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedGreenSum
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.CorrectedContinuum
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedBoundaryProbability

/-! Pointwise convergence for the projected Dirichlet problem. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Green occupation and corrected harmonic convergence imply pointwise
convergence for projected Dirichlet data. -/
theorem projectedDirichletPointwiseStep_of_corrected_harmonic
    (𝒮 : SpaceFillingSLEModel) (hfinite : FiniteDomainDirichletRepresentation)
    (h36 : CorrectedHarmonicConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (hm : MepsScalingInput 𝒮) :
    ProjectedDirichletPointwiseStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ F hdata y hy
  obtain ⟨hψb, hψh, hφ, hF⟩ := hdata
  let φ' := fun x => φ (ballRetraction z r x)
  obtain ⟨C, χ, hχ, -, hH⟩ := holder_ballRetraction hr (le_of_lt hr) z hφ
  have hφc : ContinuousOn φ' (closedBall z r) := hH.continuousOn hχ
  obtain ⟨u, -, -, -, hu, -⟩ := h36 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball φ' hφc
  obtain ⟨hu_eq, hu_lim⟩ := hu y hy
  have hidem : ∀ x, ballRetraction z r (ballRetraction z r x) = ballRetraction z r x :=
    fun x => ballRetraction_of_mem z hr (ballRetraction_mem z hr x)
  have hharm : TendstoInProbability S.P (fun ε ω => projectedDiscreteHarmonicExtension S r z φ ε ω y)
      (fun _ => u y) := by
    simpa only [projectedDiscreteHarmonicExtension, φ', hidem] using hu_lim
  have hgreen := h34 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy
    (fun _ => ψ) (fun _ => measurable_const) (fun _ => hψb) (fun _ => hψh)
  obtain ⟨K, hK, hscale⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hscale⟩ := hscale Ω S hS
  intro δ hδ
  have hlim := (hharm (δ / 2) (by linarith)).add (hgreen (δ / 2) (by linarith))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hlim)
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hε₀)] with ε hε hεsmall
  have hM : S.mε ε ≠ 0 := ne_of_gt ((mul_pos (inv_pos.mpr (by linarith : 0 < K))
    (inv_pos.mpr hε)).trans_le (hscale ε hε hεsmall).1)
  calc
    _ ≤ S.P ({ω | δ / 2 < |projectedDiscreteHarmonicExtension S r z φ ε ω y - u y|} ∪
      {ω | δ / 2 < |(S.mε ε)⁻¹ * (∑' b : cellVertices ε (S.η ω) (ball z r),
        greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (vertexOf ε (S.η ω) y) b * ψ (vertexPoint ε (S.η ω) b)) -
          S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * ψ x ∂S.μ ω|}) := by
      apply measure_mono_ae
      filter_upwards [hS.ae_projected_dirichlet_green_decomposition hγ hγ2 hfinite ε hε hM hr hy ψ φ (F ε) (hF ε hε), hu_eq] with ω hrepr hcont hbad
      simp only [mem_ofPred_eq, mem_union]
      by_contra hn
      simp only [not_or, not_lt] at hn
      have hlimit : dirichletLimit S r z ψ φ' ω y = u y -
          S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * ψ x ∂S.μ ω := by
        simp only [dirichletLimit, hy, ↓reduceIte, hcont]
      rw [hrepr, hlimit] at hbad
      have htri := abs_add_le (projectedDiscreteHarmonicExtension S r z φ ε ω y - u y)
        (-((S.mε ε)⁻¹ * (∑' b : cellVertices ε (S.η ω) (ball z r),
          greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (vertexOf ε (S.η ω) y) b * ψ (vertexPoint ε (S.η ω) b)) -
          S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * ψ x ∂S.μ ω))
      have heq : projectedDiscreteHarmonicExtension S r z φ ε ω y -
          (S.mε ε)⁻¹ * (∑' b : cellVertices ε (S.η ω) (ball z r),
            greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
              (vertexOf ε (S.η ω) y) b * ψ (vertexPoint ε (S.η ω) b)) -
          (u y - S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * ψ x ∂S.μ ω) =
          (projectedDiscreteHarmonicExtension S r z φ ε ω y - u y) -
          ((S.mε ε)⁻¹ * (∑' b : cellVertices ε (S.η ω) (ball z r),
            greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
              (vertexOf ε (S.η ω) y) b * ψ (vertexPoint ε (S.η ω) b)) -
            S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * ψ x ∂S.μ ω) := by ring
      rw [heq] at hbad
      simp only [← sub_eq_add_neg, abs_neg] at htri
      linarith
    _ ≤ _ := measure_union_le _ _

end MatedCRT

#print axioms MatedCRT.projectedDirichletPointwiseStep_of_corrected_harmonic
