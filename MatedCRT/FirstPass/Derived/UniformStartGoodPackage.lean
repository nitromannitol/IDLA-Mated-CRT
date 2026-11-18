import MatedCRT.FirstPass.Derived.AreaCellVertexInequality
import MatedCRT.FirstPass.Derived.UniformStartGoodDerived

/-!
# Almost-sure eventual uniform start from the cellwise Lévy-Prokhorov bound

`exists_eps_uniformStart_bound_derived` leaves one hypothesis, the almost-sure eventual uniform-start statement `hpkg`
at tolerance `κ / 2` along every positive null sequence.  Here `hpkg` is obtained from the deterministic engine
`AreaCellVertexInequality.eventually_forall_vertex_walk_allSet_le`: the area parametrization and the properness of the
curve, the consecutive adjacency, the local finiteness and the exit of the interpolated walk are supplied by the
mating-of-trees coupling, the finite cell set of the engine is taken to be all cells (the cells with representative in
`ball 0 R` are finite in number, so nothing is lost), and the point of a cell is its representative.

What stays a hypothesis is the cellwise comparison: almost surely, for the area parametrization of the curve, for all
large `n` and every cell `v` of the mated-CRT map at mesh `e n` whose representative lies in `ball 0 R`, the
Lévy-Prokhorov distance between the law of the embedded stopped walk from `v` and the stopped Brownian law started at
the representative is `< κ / 6`.  A comparison in the budget form `≤ 4 α d + r + τ` with `d ≤ κ / 96`, `r = κ / 48`,
`τ ≤ r` implies this bound.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess Filter ReflectedGMS.GMS
open scoped ENNReal NNReal Topology

namespace MatedCRT

namespace UniformStartGood

open LatticeProb LatticeProb.ReparamDistanceIsometry LatticeProb.CurveSpaceComparison

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Almost-sure eventual uniform start from the cellwise Lévy-Prokhorov bound.** For `0 < γ < 2`, a valid
environment, `ρ < R`, `κ > 0` and a positive null sequence `e`: if almost surely, for the area parametrization of the
curve, eventually in `n` the stopped embedded walk from every cell with representative in `U` (the ball of radius `R`)
is within Lévy-Prokhorov distance `κ / 6` of the stopped Brownian law started at the representative, then almost
surely the uniform-start event `goodG S (e n) R ρ (κ / 2)` holds for all large `n`. -/
theorem ae_eventually_mem_goodG_of_cellwise {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {R ρ : ℝ} (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ)
    {e : ℕ → ℝ} (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0))
    (U : Set (LatticeProb.Euc 2))
    (hU : U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' ball (0 : ℂ) R)
    (μB : Measure (LatticeProb.BrownianPath 2)) (hμB : LatticeProb.IsStandardBrownianLaw μB)
    (hLP : ∀ᵐ ω ∂S.P, ∀ h : IsAreaParametrized (S.μ ω) (S.η ω), ∀ᶠ n in atTop,
      ∀ v : (areaCellConfig h (he n) (S.mult (e n) ω)).cells,
        areaCellRepresentative h (he n) (S.mult (e n) ω) v ∈ U →
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
  refine AreaCellVertexInequality.eventually_forall_vertex_walk_allSet_le hap hp he he0
    (fun n => S.mult (e n) ω) (fun n k => S.mult_succ_ne_zero (he n).le ω k) hρR (half_pos hκ) rfl
    zero_lt_one rfl
    (fun n x => ae_pathExitTime_interpolatedWalk_ne_top (he n) hc hp
      (Uniform68Env.envAt S (he n) ω hc hp hadj).1 (Uniform68Env.envAt S (he n) ω hc hp hadj).2.1 R x)
    U hU μB hμB (fun _ => Set.univ) (fun n v _ w hw => absurd (Set.mem_univ w) hw)
    (fun n v => areaCellRepresentative hap (he n) (S.mult (e n) ω) v.1)
    (fun n v => areaCellRepresentative_mem hap (he n) (S.mult (e n) ω) v.1) ?_
  filter_upwards [hLPω hap] with n hn v hv
  exact hn v.1 hv

/-- **Uniform-start bound from the cellwise Lévy-Prokhorov bound.** For `0 < γ < 2`, a valid environment, `ρ < R`,
`κ, θ > 0`: if for every positive null sequence the cellwise bound of `ae_eventually_mem_goodG_of_cellwise` holds almost
surely, then there is `ε₀ > 0` such that for every `ε < ε₀` the uniform-start event at tolerance `κ` has complement of
probability at most `θ`. -/
theorem exists_eps_uniformStart_bound_of_cellwise {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {R ρ : ℝ} (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ)
    (U : Set (LatticeProb.Euc 2))
    (hU : U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' ball (0 : ℂ) R)
    (μB : Measure (LatticeProb.BrownianPath 2)) (hμB : LatticeProb.IsStandardBrownianLaw μB)
    (hLP : ∀ (e : ℕ → ℝ) (he : ∀ n, 0 < e n), Tendsto e atTop (𝓝 0) →
      ∀ᵐ ω ∂S.P, ∀ h : IsAreaParametrized (S.μ ω) (S.η ω), ∀ᶠ n in atTop,
      ∀ v : (areaCellConfig h (he n) (S.mult (e n) ω)).cells,
        areaCellRepresentative h (he n) (S.mult (e n) ω) v ∈ U →
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
    (fun e he he0 => ae_eventually_mem_goodG_of_cellwise hγ hγ2 hS hρR hκ he he0 U hU μB hμB
      (hLP e he he0)) hθ

end UniformStartGood

end MatedCRT
