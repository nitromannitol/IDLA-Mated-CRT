import MatedCRT.FirstPass.Derived.AreaCellVertexInequalityInner
import MatedCRT.FirstPass.Derived.UniformStartGoodPackage

/-!
# Almost-sure eventual uniform start from the cellwise Lévy-Prokhorov bound on the inner ball

`ae_eventually_mem_goodG_of_cellwise_inner` and `exists_eps_uniformStart_bound_of_cellwise_inner` are the statements
`ae_eventually_mem_goodG_of_cellwise` and `exists_eps_uniformStart_bound_of_cellwise` of `UniformStartGoodPackage`
with the cellwise Lévy-Prokhorov comparison required only at the cells whose representative lies in the closed ball of
radius `(ρ + R) / 2 < R` (instead of the whole ball of radius `R`).  The deterministic engine is
`AreaCellVertexInequality.eventually_forall_vertex_walk_allSet_le_inner`: the cell of a vertex of norm at most `ρ` has
diameter at most `(R - ρ) / 2`, so its representative has norm at most `(ρ + R) / 2`.  The comparison on the inner
ball is the form in which the Brownian uniform-in-the-start estimates (a disc of radius strictly smaller than `R`)
apply.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess Filter ReflectedGMS.GMS
open scoped ENNReal NNReal Topology

namespace MatedCRT

namespace UniformStartGood

open LatticeProb LatticeProb.ReparamDistanceIsometry LatticeProb.CurveSpaceComparison

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Almost-sure eventual uniform start from the cellwise Lévy-Prokhorov bound on the inner ball.** As
`ae_eventually_mem_goodG_of_cellwise`, with the comparison required only at the cells whose representative has
norm at most `(ρ + R) / 2`. -/
theorem ae_eventually_mem_goodG_of_cellwise_inner {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {R ρ : ℝ} (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ)
    {e : ℕ → ℝ} (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0))
    (U : Set (LatticeProb.Euc 2))
    (hU : U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' ball (0 : ℂ) R)
    (μB : Measure (LatticeProb.BrownianPath 2)) (hμB : LatticeProb.IsStandardBrownianLaw μB)
    (hLP : ∀ᵐ ω ∂S.P, ∀ h : IsAreaParametrized (S.μ ω) (S.η ω), ∀ᶠ n in atTop,
      ∀ v : (areaCellConfig h (he n) (S.mult (e n) ω)).cells,
        ‖Complex.orthonormalBasisOneI.repr.symm
          (areaCellRepresentative h (he n) (S.mult (e n) ω) v)‖ ≤ (ρ + R) / 2 →
          levyProkhorovEDist
            ((srwLaw (S.mult (e n) ω) ((euclideanCellEquiv h (he n)).symm v)).map
              (fun w : ℕ → ℤ => isometryEquiv 2
                (normalizedPrefixCurve
                  (complexToEuclideanPath (((1 : ℝ≥0) : ℝ) •
                    interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one w))
                  (pathExitTime (ball (0 : ℂ) R)
                    ⇑(((1 : ℝ≥0) : ℝ) • interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one w)).toNNReal)))
            (BouRabeeGwynne.stoppedBrownianLaw U (areaCellRepresentative h (he n) (S.mult (e n) ω) v) μB) <
              ENNReal.ofReal ((κ / 2) / 3)) :
    ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ goodG S (e n) R ρ (κ / 2) := by
  filter_upwards [hLP, Uniform68Env.ae_envInputs hγ hγ2 hS, hS.ae_tendsto_cocompact,
    hS.isAreaParametrized] with ω hLPω hE hp hap
  obtain ⟨hc, -, hadj⟩ := hE
  refine AreaCellVertexInequality.eventually_forall_vertex_walk_allSet_le_inner hap hp he he0
    (fun n => S.mult (e n) ω) (fun n k => S.mult_succ_ne_zero (he n).le ω k) hρR (half_pos hκ) rfl
    zero_lt_one rfl
    (fun n x => ae_pathExitTime_interpolatedWalk_ne_top (he n) hc hp
      (Uniform68Env.envAt S (he n) ω hc hp hadj).1 (Uniform68Env.envAt S (he n) ω hc hp hadj).2.1 R x)
    U hU μB hμB (fun _ => Set.univ) (fun n v _ w hw => absurd (Set.mem_univ w) hw)
    (fun n v => areaCellRepresentative hap (he n) (S.mult (e n) ω) v.1)
    (fun n v => areaCellRepresentative_mem hap (he n) (S.mult (e n) ω) v.1) ?_
  filter_upwards [hLPω hap] with n hn v hv
  exact hn v.1 hv

/-- **Uniform-start bound from the cellwise Lévy-Prokhorov bound on the inner ball.** As
`exists_eps_uniformStart_bound_of_cellwise`, with the comparison required only at the cells whose representative has
norm at most `(ρ + R) / 2`. -/
theorem exists_eps_uniformStart_bound_of_cellwise_inner {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {R ρ : ℝ} (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ)
    (U : Set (LatticeProb.Euc 2))
    (hU : U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' ball (0 : ℂ) R)
    (μB : Measure (LatticeProb.BrownianPath 2)) (hμB : LatticeProb.IsStandardBrownianLaw μB)
    (hLP : ∀ (e : ℕ → ℝ) (he : ∀ n, 0 < e n), Tendsto e atTop (𝓝 0) →
      ∀ᵐ ω ∂S.P, ∀ h : IsAreaParametrized (S.μ ω) (S.η ω), ∀ᶠ n in atTop,
      ∀ v : (areaCellConfig h (he n) (S.mult (e n) ω)).cells,
        ‖Complex.orthonormalBasisOneI.repr.symm
          (areaCellRepresentative h (he n) (S.mult (e n) ω) v)‖ ≤ (ρ + R) / 2 →
          levyProkhorovEDist
            ((srwLaw (S.mult (e n) ω) ((euclideanCellEquiv h (he n)).symm v)).map
              (fun w : ℕ → ℤ => isometryEquiv 2
                (normalizedPrefixCurve
                  (complexToEuclideanPath (((1 : ℝ≥0) : ℝ) •
                    interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one w))
                  (pathExitTime (ball (0 : ℂ) R)
                    ⇑(((1 : ℝ≥0) : ℝ) • interpPathCM (vertexPoint (e n) (S.η ω)) zero_le_one w)).toNNReal)))
            (BouRabeeGwynne.stoppedBrownianLaw U (areaCellRepresentative h (he n) (S.mult (e n) ω) v) μB) <
              ENNReal.ofReal ((κ / 2) / 3))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.P (goodG S ε R ρ κ)ᶜ ≤ ENNReal.ofReal θ :=
  exists_eps_uniformStart_bound_derived hγ hγ2 hS hκ
    (fun e he he0 => ae_eventually_mem_goodG_of_cellwise_inner hγ hγ2 hS hρR hκ he he0 U hU μB hμB
      (hLP e he he0)) hθ

end UniformStartGood

end MatedCRT
