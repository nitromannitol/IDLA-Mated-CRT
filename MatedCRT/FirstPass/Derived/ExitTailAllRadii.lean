import MatedCRT.FirstPass.Derived.ExitTailUniformStart
import MatedCRT.FirstPass.Derived.ConeScaledWalkData
import MatedCRT.FirstPass.Derived.ConeRadiusTails
import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureScaling
import MatedCRT.Steps.Sec1.Convergence

/-!
# The exit time of the embedded walk from `B_r` is `O(ε⁻¹)` at every radius, uniformly in the start

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Section 6.4 (scale invariance of the `γ`-quantum cone), applied to the exit tail
`exitTail_half_uniformStart` from `B_{1/2}`.

For the rescaled environment `S'` with `η' = R_b⁻¹ η(b ·)` at mesh `ε / b` the vertices of `S` in `B(0, r)` are
vertices of `S'` in `B(0, r / R_b)`, the walks have the same law, and `R_b > 2 r` gives `B(0, r / R_b) ⊆ B(0, 1/2)`.
The exit time from `B(0, r)` of `S` is at most the exit time from `B(0, 1/2)` of `S'`.  The bad event
`R_b ≤ 2 r` has probability at most `θ` for large `b`; the constant of the rescaled estimate at mesh `ε / b` is
`K`, hence `K b` at mesh `ε`.

* `exitTail_allRadii`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter HarmonicBalls
open scoped ENNReal Topology

namespace MatedCRT
namespace ExitTailAllRadii

/-- A vertex of `η` in `B(0, r)` is a vertex of the rescaled curve in `B(0, 1/2)` when `2 r ≤ R`. -/
theorem vertexPoint_mem_half {ε b R r : ℝ} (hb : 0 < b) (hR : 0 < R) (hrR : 2 * r ≤ R)
    (η η' : ℝ → ℂ) (hη : ∀ s, η' s = (R : ℂ)⁻¹ * η (b * s)) {k : ℤ}
    (hk : vertexPoint ε η k ∈ ball (0 : ℂ) r) :
    vertexPoint (ε / b) η' k ∈ ball (0 : ℂ) (1 / 2) := by
  have hvp : vertexPoint ε η k = (R : ℂ) * vertexPoint (ε / b) η' k :=
    ConeScaledWalkData.vertexPoint_eq_mul_rescale hb (Complex.ofReal_ne_zero.2 hR.ne') η η' hη k
  rw [mem_ball_zero_iff, hvp, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le] at hk
  rw [mem_ball_zero_iff]
  nlinarith [norm_nonneg (vertexPoint (ε / b) η' k)]

/-- The exit time of the embedded walk from `B(0, r)` is at most the exit time of the rescaled walk from
`B(0, 1/2)` when `2 r ≤ R`. -/
theorem embeddedExitTime_le_scaled {ε b R r : ℝ} (hb : 0 < b) (hR : 0 < R) (hrR : 2 * r ≤ R)
    (η η' : ℝ → ℂ) (hη : ∀ s, η' s = (R : ℂ)⁻¹ * η (b * s)) (x : ℕ → ℤ) :
    embeddedExitTime ε η (ball (0 : ℂ) r) x ≤ embeddedExitTime (ε / b) η' (ball (0 : ℂ) (1 / 2)) x :=
  GreenTest68.vExitTime_le_of_subset
    (fun _ hk => vertexPoint_mem_half hb hR hrR η η' hη hk) x

end ExitTailAllRadii

/-- **Exit tail from `B_r`, uniform in the start** (Berestycki-Gwynne, Section 6.4 with Proposition 5.1 and
Lemma 2.17): for every radius `r > 0` and `θ > 0`, in a valid environment there are `K, ε₀ > 0` such that for
`ε < ε₀`, with probability at least `1 - 2 θ`, from every vertex `k` with `η(ε k) ∈ B_r` the embedded walk
exits `B_r` before step `K ε⁻¹` except with quenched probability at most `θ`. -/
theorem exitTail_allRadii {𝒮 : SpaceFillingSLEModel} (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (h214 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {θ : ℝ} (hθ : 0 < θ) {r : ℝ} (hr : 0 < r) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) :
    ∃ K : ℝ, 0 < K ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      S.P {ω | ∃ k : ℤ, vertexPoint ε (S.η ω) k ∈ ball (0 : ℂ) r ∧
        ENNReal.ofReal θ < srwLaw (S.mult ε ω) k
          {x | ENNReal.ofReal (K * ε⁻¹) <
            (embeddedExitTime ε (S.η ω) (ball 0 r) x : ℝ≥0∞)}}
        ≤ ENNReal.ofReal (2 * θ) := by
  obtain ⟨K, hK, hKS⟩ := exitTail_half_uniformStart h214 h217 hγ hγ2 hθ
  have hPS : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨N, hN⟩ := FirstPass.Derived.exists_measure_coneScaleRadius_le_le hγ hγ2 hS.isQuantumCone (2 * r)
    (θ := ENNReal.ofReal θ) (ENNReal.ofReal_pos.2 hθ)
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = (N : ℝ) + 1 := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; positivity
  have hE1 : S.P {ω | coneScaleRadius γ (S.hcirc ω) b ≤ 2 * r} ≤ ENNReal.ofReal θ := by
    rw [hbdef]; exact hN N le_rfl
  obtain ⟨S', hS', hP, hηs, hbm, -⟩ := hEnvS γ hγ hγ2 Ω S hS b hb
  obtain ⟨ε₀', hε₀', h'⟩ := hKS Ω S' hS'
  refine ⟨K * b, by positivity, b * ε₀', by positivity, fun ε hε hεlt => ?_⟩
  have hε' : ε / b < ε₀' := by rw [div_lt_iff₀ hb]; linarith
  have hbad := h' (ε / b) (div_pos hε hb) hε'
  rw [hP] at hbad
  have hKe : K * b * ε⁻¹ = K * (ε / b)⁻¹ := by
    rw [inv_div, div_eq_mul_inv]; ring
  have hle : {ω | ∃ k : ℤ, vertexPoint ε (S.η ω) k ∈ ball (0 : ℂ) r ∧
        ENNReal.ofReal θ < srwLaw (S.mult ε ω) k
          {x | ENNReal.ofReal (K * b * ε⁻¹) <
            (embeddedExitTime ε (S.η ω) (ball 0 r) x : ℝ≥0∞)}} ≤ᵐ[S.P]
      ({ω | coneScaleRadius γ (S.hcirc ω) b ≤ 2 * r} ∪
        {ω | ∃ k : ℤ, vertexPoint (ε / b) (S'.η ω) k ∈ ball (0 : ℂ) (1 / 2) ∧
          ENNReal.ofReal θ < srwLaw (S'.mult (ε / b) ω) k
            {x | ENNReal.ofReal (K * (ε / b)⁻¹) <
              (embeddedExitTime (ε / b) (S'.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞)}}) := by
    filter_upwards [hηs, hbm] with ω h1 h2 hω
    by_cases hR : coneScaleRadius γ (S.hcirc ω) b ≤ 2 * r
    · exact Or.inl hR
    · right
      replace hR := not_le.1 hR
      have hR0 : 0 < coneScaleRadius γ (S.hcirc ω) b := by linarith
      obtain ⟨k, hk1, hk2⟩ := hω
      refine ⟨k, ExitTailAllRadii.vertexPoint_mem_half hb hR0 hR.le (S.η ω) (S'.η ω) h1 hk1, ?_⟩
      refine lt_of_lt_of_le hk2 ?_
      rw [MatedCRTEnv.mult_rescale S S' hb ω h2 ε]
      refine measure_mono fun x hx => ?_
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [← hKe]
      exact lt_of_lt_of_le hx (ENat.toENNReal_le.2
        (ExitTailAllRadii.embeddedExitTime_le_scaled hb hR0 hR.le (S.η ω) (S'.η ω) h1 x))
  calc S.P _ ≤ _ := measure_mono_ae hle
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal θ + ENNReal.ofReal θ := add_le_add hE1 hbad
    _ = ENNReal.ofReal (2 * θ) := by
        rw [← ENNReal.ofReal_add hθ.le hθ.le]; congr 1; ring

end MatedCRT
