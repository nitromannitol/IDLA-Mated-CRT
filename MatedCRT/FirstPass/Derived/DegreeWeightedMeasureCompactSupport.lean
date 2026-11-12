import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureContinuous
import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureScalingTransfer
import MatedCRT.Proofs.Infra.LocallyFinite

/-!
# Lemma 2.10: the degree-weighted measure for continuous compactly supported test functions

BG20, Corollary A.6 (Lemma 2.10 of the paper, `DegreeMeasureConvergenceStmt`):

* `tendstoInProbability_degreeWeightedMeasure_of_continuous_of_lipschitz`: on a valid environment, if
  `∫ g dμ^ε_h → 6 ∫ g dμ_h` in probability for every bounded Lipschitz `g` vanishing off some ball, then the same
  holds for every continuous compactly supported `f`. The function `f` is uniformly approximated by Lipschitz functions
  (`exists_lipschitz_approx_of_continuous`), the error is controlled by a bump function, and integrability for `μ^ε_h`
  comes from the almost sure properness of `η`: finitely many cells meet a bounded set
  (`cellVertices_finite_of_isCompact`).
* `degreeMeasureConvergenceStmt_of_lemmaA5`: Lemma 2.10 from the cell size estimate (Lemma 2.8), the scale invariance
  of the `γ`-quantum cone (`QuantumConeScalingInput`, `ConeEnvironmentScalingStep`) and the degree-weighted counting
  bound of BG20 Lemma A.5 on the balls `B_r`, `r < 1`, for every valid environment.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls
open scoped ENNReal

namespace MatedCRT

/-- **From Lipschitz to continuous compactly supported test functions** (BG20, end of the proof of Corollary A.6).
On a valid environment, if `∫ g dμ^ε_h → 6 ∫ g dμ_h` in probability for every continuous, bounded, Lipschitz `g`
vanishing off some ball, then `∫ f dμ^ε_h → 6 ∫ f dμ_h` in probability for every continuous compactly supported `f`. -/
theorem tendstoInProbability_degreeWeightedMeasure_of_continuous_of_lipschitz
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hLip : ∀ (g : ℂ → ℝ) (K L R₀ : ℝ), Continuous g → (∀ x, |g x| ≤ K) →
      (∀ x y, |g x - g y| ≤ L * ‖x - y‖) → (∀ x ∉ ball (0 : ℂ) R₀, g x = 0) →
      TendstoInProbability S.P
        (fun ε ω => ∫ x, g x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
        (fun ω => 6 * ∫ x, g x ∂S.μ ω))
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, f x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
      (fun ω => 6 * ∫ x, f x ∂S.μ ω) := by
  have := hS.isProbabilityMeasure
  obtain ⟨ρ, hρ⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 hfc.isCompact.isBounded
  have hfρ : ∀ x ∉ ball (0 : ℂ) ρ, f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hρ h)
  set ρ₀ : ℝ := max ρ 0 with hρ₀
  have hρ₀0 : 0 ≤ ρ₀ := le_max_right _ _
  set r : ℝ := ρ₀ + 2 with hr
  -- the bump `φ`: `1` on `B_{ρ₀ + 1}`, `0` off `B_r`
  let φ : ContDiffBump (0 : ℂ) := ⟨ρ₀ + 1, r, by linarith, by rw [hr]; linarith⟩
  have hrIn : φ.rIn = ρ₀ + 1 := rfl
  have hrOut : φ.rOut = r := rfl
  have hgc : Continuous fun x => φ x := φ.continuous
  have hg0 : ∀ x ∉ ball (0 : ℂ) r, φ x = 0 := fun x hx =>
    φ.zero_of_le_dist (by rw [hrOut, dist_zero_right]; simpa [mem_ball_zero_iff, not_lt] using hx)
  have hg1 : ∀ x ∈ ball (0 : ℂ) (ρ₀ + 1), φ x = 1 := fun x hx =>
    φ.one_of_mem_closedBall (by rw [hrIn]; exact ball_subset_closedBall hx)
  obtain ⟨Lg, hLg⟩ := exists_abs_sub_le_of_contDiffBump φ
  have hgK : ∀ x, |φ x| ≤ 1 := fun x => by rw [abs_of_nonneg φ.nonneg]; exact φ.le_one
  have hG := hLip _ 1 Lg r hgc hgK hLg hg0
  have hZ : AEMeasurable (fun ω => 6 * ∫ x, φ x ∂S.μ ω) S.P :=
    (frozenLQGTestIntegralMeasurable_holds γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ
      ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩ _ hgc
      φ.hasCompactSupport).const_mul 6
  -- the almost sure event: `η` area-parametrized (hence continuous) and proper, `μ_h` locally finite
  have hW : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) ∧
      Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧ IsLocallyFiniteMeasure (S.μ ω) := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hS.isLQGMeasure] with ω h1 h2 h3
    exact ⟨h1, h2, h3.isLocallyFiniteMeasure⟩
  have hW0 := mem_ae_iff.1 hW
  refine tendstoInProbability_of_approx hZ hG fun θ hθ => ?_
  obtain ⟨f', hf'c, ⟨K', hK'⟩, ⟨L', hL'⟩, hf'0, hff'⟩ :=
    exists_lipschitz_approx_of_continuous hf one_pos hθ hfρ
  have hf'cs : HasCompactSupport f' := HasCompactSupport.intro
    (isCompact_closedBall (0 : ℂ) (ρ₀ + 1)) fun x hx => hf'0 x fun h => hx (ball_subset_closedBall h)
  have hpt : ∀ x, |f x - f' x| ≤ θ * φ x := fun x => by
    by_cases hx : x ∈ ball (0 : ℂ) (ρ₀ + 1)
    · rw [hg1 x hx, mul_one]; exact hff' x
    · have h1 : f x = 0 := hfρ x fun h => hx (ball_subset_ball (by linarith [le_max_left ρ 0]) h)
      rw [h1, hf'0 x hx, sub_zero, abs_zero]
      exact mul_nonneg hθ.le φ.nonneg
  refine ⟨_, _, fun _ => {ω | IsAreaParametrized (S.μ ω) (S.η ω) ∧
      Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧ IsLocallyFiniteMeasure (S.μ ω)},
    hLip f' K' L' (ρ₀ + 1) hf'c hK' hL' hf'0, tendsto_const_nhds.congr fun _ => hW0.symm, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε0
  rintro ω ⟨hpar, hp, hlf⟩
  have hε : (0 : ℝ) < ε := hε0
  have hfin := cellVertices_finite_of_isCompact hpar.1 hp hε (isCompact_closedBall (0 : ℂ) r)
  have hint : ∀ u : ℂ → ℝ, Continuous u → (∀ x ∉ ball (0 : ℂ) r, u x = 0) →
      Integrable u (degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω)) := by
    intro u hu hu0
    refine integrable_degreeWeightedMeasure hu hpar.1 hfin.toFinset (fun k hk x hx => ?_)
      (fun k _ => hpar.integrableOn_cell hε hu k)
    by_contra hux
    have hxr : x ∈ ball (0 : ℂ) r := by
      by_contra h; exact hux (hu0 x h)
    exact hk (hfin.mem_toFinset.2 ⟨x, hx, ball_subset_closedBall hxr⟩)
  have hsub : ∀ x ∉ ball (0 : ℂ) r, x ∉ ball (0 : ℂ) (ρ₀ + 1) := fun x hx h =>
    hx (ball_subset_ball (by rw [hr]; linarith) h)
  have hρr : ρ ≤ r := by rw [hr]; linarith [le_max_left ρ 0]
  constructor
  · exact abs_integral_sub_le_mul_abs_integral
      (hint f hf fun x hx => hfρ x fun h => hx (ball_subset_ball hρr h))
      (hint f' hf'c fun x hx => hf'0 x (hsub x hx)) (hint _ hgc hg0) hθ.le hpt
  · have h := abs_integral_sub_le_mul_abs_integral (ν := S.μ ω)
      (hf.integrable_of_hasCompactSupport hfc) (hf'c.integrable_of_hasCompactSupport hf'cs)
      (hgc.integrable_of_hasCompactSupport φ.hasCompactSupport) hθ.le hpt
    rw [← mul_sub, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    calc 6 * |∫ x, f x ∂S.μ ω - ∫ x, f' x ∂S.μ ω| ≤ 6 * (θ * |∫ x, φ x ∂S.μ ω|) := by gcongr
      _ = θ * (6 * |∫ x, φ x ∂S.μ ω|) := by ring

/-- **Lemma 2.10 from Lemma A.5** (lemma:mu_h_degree-convergence; BG20 Corollary A.6). Given the cell size estimate
(Lemma 2.8), the scale invariance of the `γ`-quantum cone (`QuantumConeScalingInput` and the environment form
`ConeEnvironmentScalingStep`), and, for each `γ ∈ (0, 2)`, exponents `α, b > 0` such that on every valid environment
the degree-weighted counting bound of BG20 Lemma A.5 holds on every ball `B_r`, `r < 1`, with polynomially high
probability, the degree-weighted measure satisfies `μ^ε_h → 6 μ_h` in probability for the vague topology. -/
theorem degreeMeasureConvergenceStmt_of_lemmaA5 {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) (hscale : QuantumConeScalingInput)
    (hEnv : ConeEnvironmentScalingStep 𝒮)
    (hA5 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α b : ℝ, 0 < α ∧ 0 < b ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ r : ℝ, 0 < r → r < 1 → PolyHighProb S.P fun ε => {ω | ∀ g : ℂ → ℝ,
        (∀ x, 0 ≤ g x ∧ |g x| ≤ ε ^ (-b)) → (∀ x y, |g x - g y| ≤ ε ^ (-b) * ‖x - y‖) →
        ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) (ball 0 r), w k ∈ cell ε (S.η ω) k ∩ closure (ball 0 r)) →
        6 * ε⁻¹ * ∫ x in ball 0 r \ thickening (ε ^ α) (frontier (ball 0 r)), g x ∂S.μ ω - ε ^ (-1 + α) ≤
            ∑' k : cellVertices ε (S.η ω) (ball 0 r), (matedDeg (S.mult ε ω) k : ℝ) * g (w k) ∧
          ∑' k : cellVertices ε (S.η ω) (ball 0 r), (matedDeg (S.mult ε ω) k : ℝ) * g (w k) ≤
            6 * ε⁻¹ * ∫ x in thickening (ε ^ α) (ball 0 r), g x ∂S.μ ω + ε ^ (-1 + α)}) :
    DegreeMeasureConvergenceStmt 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS f hf hfc
  obtain ⟨α, b, hα, hb, hA⟩ := hA5 γ hγ hγ2
  refine tendstoInProbability_degreeWeightedMeasure_of_continuous_of_lipschitz hγ hγ2 hS
    (fun g K L R₀ hg hgK hgL hgR => ?_) hf hfc
  exact tendstoInProbability_degreeWeightedMeasure_of_scaling hγ hγ2 hscale hEnv hS
    (fun S' hS' g' K' L' hg' hgK' hgL' hg0' =>
      tendstoInProbability_degreeWeightedMeasure_of_ball_random hcell hγ hγ2 hS' hα hb
        (hA Ω S' hS') hg' (by norm_num) hgK' hgL' hg0') hg hgK hgL hgR

end MatedCRT
