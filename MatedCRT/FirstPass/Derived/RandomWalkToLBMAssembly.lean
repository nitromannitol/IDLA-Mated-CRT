import MatedCRT.FirstPass.Derived.WalkInterpIntegralInMeasure
import MatedCRT.FirstPass.Derived.WalkIntegralMeasurable
import MatedCRT.FirstPass.Derived.TendstoInProbabilityOfSubseqLaw
import LatticeProb.Prob.LawFieldEvalConvergence
import LatticeProb.Prob.ProbabilityMeasureBorel

/-!
# Convergence in probability of the quenched walk integral: assembly

Berestycki-Gwynne (arXiv:2003.10320, proof of Theorem 1.2, lines 3630-3665) deduce convergence in
probability of the quenched random walk to the LBM kernel from three ingredients, assembled here for a
fixed bounded Lipschitz path functional `F` and a fixed point `z`:

1. **identification** (`hident`): along every sequence `ε_n → 0⁺` there is a subsequence along which
   the pair (environment data `X`, interpolated walk law `P̃^{ε_n}`) converges in law to
   `(X, Λ X)` for a measurable random law `Λ X` of the data;
2. **equicontinuity in law** (`hEqLaw`) and the comparison of the quenched walk integral with the
   integral against the interpolated law at `z` (`tendsto_prob_abs_walkIntegral_sub_interpIntegral`),
   through the modulus of the bounded Lipschitz functional for the Lévy-Prokhorov distance (`hcomp`);
3. the sub-subsequence criterion `tendstoInProbability_of_subseq_tendsto_law`.

## Main result

* `tendstoInProbability_walkIntegral_of_identification`: under `hident`, `hEqLaw` and `hcomp`, the
  quenched walk integral from the vertex of `z` converges in probability, as `ε → 0⁺`, to any
  random variable `Y` that is almost surely `∫ F d(Λ X z)`.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The quenched walk integral converges in probability to the integral against the limit law.**
Let `X : Ω → D` be measurable data in a pseudo-metrizable Borel space and
`Λ : D → C(ℂ, Prob(ContinuousPath ℂ))` measurable. Assume that along every sequence `ε_n → 0⁺` there is
a subsequence along which `(X, P̃^{ε_{n_k}})` converges in law to `(X, Λ X)` (`hident`), the vertex
laws are equicontinuous in law along every such sequence (`hEqLaw`), and the bounded Lipschitz
functional `F` has a modulus of continuity for the Lévy-Prokhorov distance on path laws (`hcomp`).
If `Y = ∫ F d(Λ X z)` almost surely, then
`∫ F(W^ε) d srwLaw(vertex of z) → Y` in probability as `ε → 0⁺`. -/
theorem tendstoInProbability_walkIntegral_of_identification {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    (hEqLaw : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
        S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (e n) R δ ω} ≤ ENNReal.ofReal a)
    {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F)
    (hcomp : ∀ η : ℝ, 0 < η → ∃ a : ℝ, 0 < a ∧
      ∀ μ ν : ProbabilityMeasure (ContinuousPath ℂ), pathLevyProkhorovEDist μ ν < ENNReal.ofReal a →
        |∫ q, blPathFunctionalBCF hF q ∂(μ : Measure (ContinuousPath ℂ)) -
          ∫ q, blPathFunctionalBCF hF q ∂(ν : Measure (ContinuousPath ℂ))| ≤ η)
    (z : ℂ) {D : Type*} [TopologicalSpace D] [TopologicalSpace.PseudoMetrizableSpace D]
    [MeasurableSpace D] [BorelSpace D] {X : Ω → D} (hX : Measurable X)
    {Λ : D → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛ : Measurable Λ) {Y : Ω → ℝ}
    (hY : ∀ᵐ ω ∂S.P, Y ω = ∫ q, blPathFunctionalBCF hF q ∂(Λ (X ω) z : Measure (ContinuousPath ℂ)))
    (hident : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ f : (D × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
          Tendsto (fun k => ∫ ω, f (X ω, interpWalkLaw S η' (e (φ k)) ω) ∂S.P) atTop
            (𝓝 (∫ ω, f (X ω, Λ (X ω)) ∂S.P))) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, F (interpolatedWalk ε (S.η ω) (S.mε ε) x)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z)) Y := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  -- measurable versions of the quenched walk integrals
  have hex : ∀ ε : ℝ, ∃ R : Ω → ℝ, Measurable R ∧ (∀ ω, |R ω| ≤ 1) ∧
      (0 < ε → ∀ᵐ ω ∂S.P, R ω = ∫ x, F (interpolatedWalk ε (S.η ω) (S.mε ε) x)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z)) := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨R, h1, h2, h3⟩ := exists_measurable_walkIntegral hS hη' hae hε hF z
      exact ⟨R, h1, h2, fun _ => h3⟩
    · exact ⟨fun _ => 0, measurable_const, fun _ => by simp, fun h => absurd h hε⟩
  choose Rt hRtm hRtb hRte using hex
  -- the limit observable
  set u : D → ℝ := fun d => ∫ q, blPathFunctionalBCF hF q ∂(Λ d z : Measure (ContinuousPath ℂ))
    with hudef
  have hu : Measurable u :=
    (measurable_integral_probabilityMeasure_of_boundedContinuous (blPathFunctionalBCF hF)).comp
      ((continuous_eval_const z).measurable.comp hΛ)
  have hubd : ∀ d, |u d| ≤ 1 := by
    intro d
    have h := norm_integral_le_of_norm_le_const (μ := (Λ d z : Measure (ContinuousPath ℂ)))
      (f := fun q => blPathFunctionalBCF hF q) (C := 1)
      (Filter.Eventually.of_forall fun q => by
        rw [blPathFunctionalBCF_apply, Real.norm_eq_abs]
        exact hF.1 _)
    simpa [hudef] using h
  have hY' : Y =ᵐ[S.P] fun ω => u (X ω) := hY
  -- convergence in probability of the measurable versions
  have hA : TendstoInProbability S.P Rt Y := by
    refine tendstoInProbability_of_subseq_tendsto_law S.P hX (fun ε _ => hRtm ε) hu zero_le_one
      (fun ε _ ω => hRtb ε ω) hubd hY' ?_
    intro e hepos he0
    obtain ⟨φ, hφ, hid⟩ := hident e hepos he0
    refine ⟨φ, hφ, ?_⟩
    have hεφ0 : ∀ k, 0 < e (φ k) := fun k => hepos _
    have hεφ : Tendsto (fun k => e (φ k)) atTop (𝓝 0) := he0.comp hφ.tendsto_atTop
    have hg : Measurable fun ω => (X ω, Λ (X ω)) := hX.prodMk (hΛ.comp hX)
    have hRF : TendstoInMeasure S.P (fun k ω => Rt (e (φ k)) ω -
        ∫ x, blPathFunctionalBCF hF x ∂(interpWalkLaw S η' (e (φ k)) ω z : Measure (ContinuousPath ℂ)))
        atTop 0 := by
      rw [tendstoInMeasure_iff_norm]
      intro c hc
      have hP1d := tendsto_prob_abs_walkIntegral_sub_interpIntegral hS hae hεφ0 hεφ
        (hEqLaw (fun k => e (φ k)) hεφ0 hεφ) hF hcomp z (half_pos hc)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP1d (fun _ => zero_le)
        (fun k => measure_mono_ae ?_)
      filter_upwards [hRte (e (φ k)) (hεφ0 k)] with ω hω hmem
      simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hmem ⊢
      rw [← hω]
      linarith
    have hlaw : ∀ f : (D × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
        Tendsto (fun k => ∫ ω, f (X ω, interpWalkLaw S η' (e (φ k)) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂(S.P.map fun ω => (X ω, Λ (X ω))))) := by
      intro f
      rw [integral_map hg.aemeasurable f.continuous.aestronglyMeasurable]
      exact hid f
    have key := LatticeProb.tendsto_integral_eval_of_tendsto_law_of_tendstoInMeasure_sub
      (P := S.P) hX.aemeasurable
      (fun k => aemeasurable_interpWalkLaw hS hη' hae (hεφ0 k))
      (R := fun k => Rt (e (φ k))) (fun k => (hRtm _).aemeasurable)
      (ν := S.P.map fun ω => (X ω, Λ (X ω))) z (blPathFunctionalBCF hF) hlaw hRF
    intro f
    have hk := key f
    have hGc : Continuous fun c : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) =>
        ∫ x, blPathFunctionalBCF hF x ∂(c z : Measure (ContinuousPath ℂ)) :=
      (continuous_integral_probabilityMeasure (blPathFunctionalBCF hF)).comp
        (continuous_eval_const z)
    have hcont : Continuous fun p : D × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) =>
        f (p.1, ∫ x, blPathFunctionalBCF hF x ∂(p.2 z : Measure (ContinuousPath ℂ))) :=
      f.continuous.comp (continuous_fst.prodMk (hGc.comp continuous_snd))
    have hmap : ∫ p : D × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)),
        f (p.1, ∫ x, blPathFunctionalBCF hF x ∂(p.2 z : Measure (ContinuousPath ℂ)))
          ∂(S.P.map fun ω => (X ω, Λ (X ω))) = ∫ ω, f (X ω, u (X ω)) ∂S.P :=
      integral_map hg.aemeasurable hcont.aestronglyMeasurable
    rw [hmap] at hk
    exact hk
  -- transfer to the quenched walk integrals
  intro δ hδ
  refine (hA δ hδ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  refine measure_congr ?_
  filter_upwards [hRte ε hε'] with ω hω
  rw [hω]

end MatedCRT.FirstPass.Derived
