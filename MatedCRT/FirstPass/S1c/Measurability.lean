import MatedCRT.FirstPass.S1c.Threshold
import MatedCRT.FirstPass.Frozen.S1c

/-!
# Null-measurability of the threshold event (Lemma 1)

For a random locally finite measure `μ_ω` on `ℂ` and a point `p ≠ 0` of the closed disc, the event
`{ω | -uG(0,p) < v_{B_R;0}(u)(p)(μ_ω)}` is a countable union, over rationals `q`, of the sets
`{c < q} ∩ {ω | moment(μ_ω) ∉ A_q}` a.s., where `A_q` is the analytic moment set of `supersolutionPairs` and
`moment(μ)_k = ∫ φs k dμ`. Hence it is `P`-null-measurable by the frozen Lusin theorem applied to the law of the
moment vector, which is measurable by the frozen field-level measurability of `ω ↦ ∫ φ dμ_ω`
(`FrozenUniversalMeasurabilityOfAnalytic`, `FrozenLQGTestIntegralMeasurable`). Only these two frozen inputs enter.
-/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory HarmonicBalls

/-- The threshold event `{ω | -uG(0,p) < v(u)(p)(μ_ω)}` is `P`-null-measurable, for a probability space `(Ω, P)`
and a random measure `μ` whose masses of the closed disc are finite almost surely. -/
theorem nullMeasurableSet_threshold {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) {μ : Ω → Measure ℂ} {R u : ℝ} (hR : 0 ≤ R) (hu : 0 < u)
    (hμ : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x)
    {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) R) (hp0 : p ≠ 0) :
    NullMeasurableSet
      {ω | -u * greenFunction (ball (0 : ℂ) R) 0 p < leastSupersolution (μ ω) R 0 u p} P := by
  let Y : Ω → (ℕ → ℝ) := fun ω k => ∫ x, φs k x ∂(μ ω)
  have hY : AEMeasurable Y P :=
    aemeasurable_pi_iff.2 fun k => hmeas (φs k)
      (contDiff_two_of_isTestFunction (hφs k).1).continuous (hφs k).1.2.1
  -- a measurable representative of the moment vector, equal to `Y` almost surely
  let g : Ω → (ℕ → ℝ) := hY.mk Y
  have hg : Measurable g := hY.measurable_mk
  have hYg : Y =ᵐ[P] g := hY.ae_eq_mk
  have hA : ∀ q : ℚ, AnalyticSet (Prod.fst '' supersolutionPairs hR φs u
      (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ)) :=
    fun q => analyticSet_supersolutionMoments hR (fun k => (hφs k).1) u _ ⟨p, hp⟩ (q : ℝ)
  have hNM : ∀ q : ℚ, NullMeasurableSet (Y ⁻¹' (Prod.fst '' supersolutionPairs hR φs u
      (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ))) P := fun q =>
    ((hF1 (ℕ → ℝ) (P.map g) (by infer_instance) _ (hA q)).preimage ⟨hg, fun _ h => h⟩).congr
      (by
        rw [Filter.eventuallyEqSet_iff]
        filter_upwards [hYg] with ω hω
        simp only [mem_preimage, hω])
  have hset : {ω | -u * greenFunction (ball (0 : ℂ) R) 0 p < leastSupersolution (μ ω) R 0 u p} =ᵐ[P]
      ⋃ q : ℚ, ({ω | -u * greenFunction (ball (0 : ℂ) R) 0 p < (q : ℝ)} ∩
        (Y ⁻¹' (Prod.fst '' supersolutionPairs hR φs u (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ)))ᶜ) := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hμ] with ω hω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_compl_iff, mem_preimage]
    exact threshold_iff_moments hR hω hu φs hφs hdense hG hp hp0
  exact (NullMeasurableSet.iUnion fun q =>
    ((MeasurableSet.const _).nullMeasurableSet.inter (hNM q).compl)).congr hset.symm

end MatedCRT
