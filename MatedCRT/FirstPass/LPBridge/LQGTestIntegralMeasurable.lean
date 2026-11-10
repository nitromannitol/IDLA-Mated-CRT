import MatedCRT.FirstPass.Frozen.S1c
import MatedCRT.LPStaging.Prob.VagueLimitMeasurable
import HarmonicBalls.Proofs.Sec5.LQGApproxDecoder

/-!
# Bridge: field-level measurability of the LQG measure against test functions

`FrozenLQGTestIntegralMeasurable` (`FirstPass/Frozen/S1c.lean`) asserts that for a γ-quantum cone field
`(P, hC, hcirc, μ)` (`IsConeField`) and a continuous compactly supported `φ`, the map `ω ↦ ∫ φ dμ_ω` is a.e. measurable.
The proof combines two facts:

* the dyadic approximations `ω ↦ ε^{γ²/2} e^{γ h_ε(·)} dz` (`lqgApprox`) are a.e. measurable as `Measure ℂ`-valued
  maps, because `IsQuantumCone` gives measurability in `ω` of each circle average `h_r(z)` (`r > 0`) and a.s. joint
  continuity on `(0, ∞) × ℂ`, and `exists_measurable_lqgApprox_decoder` makes `lqgApprox` a measurable function of
  the continuous density;
* the vague limit `IsLQGLimit` of these approximations along the dyadic scales `ε = 2^{-k}` (Duplantier-Sheffield 2011,
  Prop. 1.1; Kallenberg, *Random Measures*, 2017), which is the hypothesis of the general vague-limit lemma
  `LatticeProb.aemeasurable_integral_of_vague_limit`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set HarmonicBalls LatticeProb

/-- Measurability of the dyadic approximation `ω ↦ lqgApprox γ (hε ω) r` of the γ-LQG measure, as a `Measure ℂ`-valued
map on `Ω`, for a random family of circle averages `hε ω r z` that is measurable in `ω` for each `r > 0` and a.s.
continuous on `(0, ∞) × ℂ`. The proof is the one of `aemeasurable_lqgMeasure_of_circleAverages`
(`Proofs/Sec4/Prop42Closure/WholePlaneLQGMeasurable.lean`), at a single radius. -/
theorem aemeasurable_lqgApprox_circleAverages {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hε : Ω → ℝ → ℂ → ℝ}
    (hmeas : ∀ (r : ℝ) (z : ℂ), 0 < r → Measurable fun ω => hε ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hε ω p.1 p.2) (Ioi 0 ×ˢ univ))
    {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => lqgApprox γ (hε ω) r) P := by
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_lqgApprox_decoder γ r
  have hp : Measurable (fun ω (z : ℂ) => hε ω r z) :=
    Measurable.of_eval fun z => hmeas r z hr
  refine (hF.comp hp).aemeasurable.congr ?_
  filter_upwards [hcont] with ω hω
  have hc : Continuous (fun z => hε ω r z) :=
    hω.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨hr, mem_univ z⟩)
  simpa only [Function.comp_apply, lqgApprox] using hFeq (fun z => hε ω r z) hc

/-- The frozen field-level measurability of the LQG measure against test functions: for `0 < γ < 2`, every γ-quantum
cone field `(P, hC, hcirc, μ)` and every continuous compactly supported `φ`, the map `ω ↦ ∫ φ dμ_ω` is a.e. measurable.
The dyadic approximations are a.e. measurable (`aemeasurable_lqgApprox_circleAverages`, from `IsQuantumCone`), and
`IsLQGMeasure` says that `μ ω` is their vague limit along `ε = 2^{-k}` for a.e. `ω` (`IsLQGLimit.tendsto_integral`);
the general lemma `LatticeProb.aemeasurable_integral_of_vague_limit` then gives the claim. -/
theorem frozenLQGTestIntegralMeasurable_holds : FrozenLQGTestIntegralMeasurable := by
  unfold FrozenLQGTestIntegralMeasurable
  intro γ _hγ0 _hγ2 Ω _ P hC hcirc μ hcone φ hφ hφc
  obtain ⟨_, hQ, hL⟩ := hcone
  have hL' : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hL
  exact aemeasurable_integral_of_vague_limit P (fun n ω => lqgApprox γ (hcirc ω) (dyadicScale n)) μ
    (fun n => aemeasurable_lqgApprox_circleAverages hQ.measurable_circle hQ.ae_continuousOn_circle
      (dyadicScale_pos n))
    (hL'.mono fun ω hω f hf hfc => hω.tendsto_integral f hf hfc) φ hφ hφc

end MatedCRT
