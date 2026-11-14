import MatedCRT.FirstPass.Derived.NoStickingEvent
import MatedCRT.FirstPass.Derived.ConeScaledWalkData
import MatedCRT.FirstPass.Derived.ConeRadiusTails
import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureScaling
import MatedCRT.Steps.Sec1.Convergence

/-!
# The window event of the quenched walk at every radius, from the cone scaling

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Section 6.4 (proof of Proposition 6.1 from Proposition 6.2 by the scale invariance of the
`γ`-quantum cone), at the level of the failure event of the window estimate of Proposition 6.14.

`NoStickingEvent.limLimSmall_noSticking` controls, for a radius `ρ < 1`, the windows of `2 ⌊ε⁻¹ δ^q⌋` steps of
the walk before it leaves the cells meeting `B(0, ρ)`.  For the rescaled environment `S'` with `η' = R_b⁻¹ η(b ·)`
at mesh `ε / b` the cells meeting `B(0, ρ / R_b)` are the cells of `S` meeting `B(0, ρ)`, the walks have the same
law, and the distances are multiplied by `R_b⁻¹`.  If `R_b > 2 ρ` then `B(0, ρ / R_b) ⊆ B(0, 1/2)`, so the
estimate of the environment `S'` at radius `1/2` and scale `δ / (2 ρ)` controls the estimate of `S` at radius
`ρ` and scale `δ`, with the exponent `q` replaced by `q / 2` (the number of steps `b ε⁻¹ (δ/(2ρ))^q` of the
window of `S'` is at most `ε⁻¹ δ^{q/2}` for small `δ`).  The bad event `R_b ≤ 2 ρ` has probability at most `θ`
for large `b`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace NoStickingAllRadii

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology NNReal

/-- The set of walks that, before leaving the cells meeting `B(0, ρ)`, have a window of `2 ⌊ε⁻¹ δ^q⌋` steps
in which the embedded walk does not travel the distance `δ`. -/
def windowBad (ε : ℝ) (η : ℝ → ℂ) (ρ δ q : ℝ) : Set (ℕ → ℤ) :=
  {X | ¬ ∀ j : ℕ, ((j + ⌊ε⁻¹ * δ ^ q⌋₊ : ℕ) : ℕ∞) ≤
        vExitTime (cellVertices ε η (ball (0 : ℂ) ρ)) X →
      ∃ i₁ i₂ : ℕ, j ≤ i₁ ∧ i₁ ≤ i₂ ∧ i₂ < j + 2 * ⌊ε⁻¹ * δ ^ q⌋₊ ∧
        δ ≤ ‖vertexPoint ε η (X i₂) - vertexPoint ε η (X i₁)‖}

/-- The cells meeting `B(0, ρ)` of `η` are among the cells of the rescaled curve meeting `B(0, 1/2)` when
`2 ρ ≤ R`. -/
theorem cellVertices_subset_half {ε b R ρ : ℝ} (hb : 0 < b) (hR : 0 < R) (hρR : 2 * ρ ≤ R)
    (η η' : ℝ → ℂ) (hη : ∀ s, η' s = (R : ℂ)⁻¹ * η (b * s)) :
    cellVertices ε η (ball (0 : ℂ) ρ) ⊆ cellVertices (ε / b) η' (ball (0 : ℂ) (1 / 2)) := by
  have h := ConeScaledWalkData.cellVertices_rescale_ball (ε := ε) hb hR η η' hη (ρ / R)
  have e : R * (ρ / R) = ρ := by field_simp
  rw [e] at h
  rw [← h]
  rintro k ⟨x, hx1, hx2⟩
  refine ⟨x, hx1, ?_⟩
  exact ball_subset_ball (by rw [div_le_iff₀ hR]; linarith) hx2

/-- **Deterministic comparison of the window events**: a walk that is bad at radius `ρ` and scale `δ` with
exponent `q'` in `S` is bad at radius `1/2` and scale `δ / (2 ρ)` with exponent `q` in the environment rescaled by
`R ≥ 2 ρ`, provided the window of the latter is not longer. -/
theorem windowBad_subset_scaled {ε b R ρ δ q q' : ℝ} (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hρR : 2 * ρ ≤ R) (η η' : ℝ → ℂ) (hη : ∀ s, η' s = (R : ℂ)⁻¹ * η (b * s))
    (hn : ⌊(ε / b)⁻¹ * (δ / (2 * ρ)) ^ q⌋₊ ≤ ⌊ε⁻¹ * δ ^ q'⌋₊) :
    windowBad ε η ρ δ q' ⊆ windowBad (ε / b) η' (1 / 2) (δ / (2 * ρ)) q := by
  intro X hX hgood
  apply hX
  intro j hj
  have hsub := cellVertices_subset_half (ε := ε) hb hR hρR η η' hη
  have hexit : vExitTime (cellVertices ε η (ball (0 : ℂ) ρ)) X ≤
      vExitTime (cellVertices (ε / b) η' (ball (0 : ℂ) (1 / 2))) X :=
    GreenTest68.vExitTime_le_of_subset hsub X
  have hj1 : ((j + ⌊(ε / b)⁻¹ * (δ / (2 * ρ)) ^ q⌋₊ : ℕ) : ℕ∞) ≤
      vExitTime (cellVertices (ε / b) η' (ball (0 : ℂ) (1 / 2))) X := by
    refine le_trans ?_ (hj.trans hexit)
    exact_mod_cast Nat.add_le_add_left hn j
  obtain ⟨i₁, i₂, h1, h2, h3, h4⟩ := hgood j hj1
  refine ⟨i₁, i₂, h1, h2, by omega, ?_⟩
  have hvp : ∀ k, vertexPoint ε η k = (R : ℂ) * vertexPoint (ε / b) η' k := fun k =>
    ConeScaledWalkData.vertexPoint_eq_mul_rescale hb (Complex.ofReal_ne_zero.2 hR.ne') η η' hη k
  rw [hvp, hvp, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have h2ρ : 0 < 2 * ρ := by positivity
  calc δ = (2 * ρ) * (δ / (2 * ρ)) := by field_simp
    _ ≤ R * (δ / (2 * ρ)) := by
        gcongr
    _ ≤ R * ‖vertexPoint (ε / b) η' (X i₂) - vertexPoint (ε / b) η' (X i₁)‖ := by
        gcongr

/-- For `b > 0`, the window of the rescaled environment is not longer than the window of `S` with exponent
`q / 2` for small `δ`. -/
theorem exists_scale_floor_le {b ρ q : ℝ} (hb : 0 < b) (hρ : 0 < ρ) (hq : 0 < q) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ ε : ℝ, 0 < ε →
      ⌊(ε / b)⁻¹ * (δ / (2 * ρ)) ^ q⌋₊ ≤ ⌊ε⁻¹ * δ ^ (q / 2)⌋₊ := by
  have h2ρ : 0 < 2 * ρ := by positivity
  have hc : 0 < (2 * ρ) ^ q / b := div_pos (Real.rpow_pos_of_pos h2ρ q) hb
  refine ⟨((2 * ρ) ^ q / b) ^ (2 / q), Real.rpow_pos_of_pos hc _, fun δ hδ hδlt ε hε => ?_⟩
  apply Nat.floor_le_floor
  have hle : δ ^ (q / 2) ≤ (2 * ρ) ^ q / b := by
    have h1 : δ ^ (q / 2) ≤ (((2 * ρ) ^ q / b) ^ (2 / q)) ^ (q / 2) :=
      Real.rpow_le_rpow hδ.le hδlt.le (by positivity)
    rwa [← Real.rpow_mul hc.le, show 2 / q * (q / 2) = 1 by field_simp, Real.rpow_one] at h1
  have hpos : 0 < (2 * ρ) ^ q := Real.rpow_pos_of_pos h2ρ q
  have hd : b * δ ^ (q / 2) ≤ (2 * ρ) ^ q := by
    rw [le_div_iff₀ hb] at hle
    linarith [mul_comm b (δ ^ (q / 2))]
  have hδq : δ ^ q = δ ^ (q / 2) * δ ^ (q / 2) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hδh : 0 ≤ δ ^ (q / 2) := (Real.rpow_pos_of_pos hδ _).le
  rw [Real.div_rpow hδ.le h2ρ.le, hδq, inv_div]
  calc b / ε * (δ ^ (q / 2) * δ ^ (q / 2) / (2 * ρ) ^ q)
      = ε⁻¹ * δ ^ (q / 2) * (b * δ ^ (q / 2) / (2 * ρ) ^ q) := by field_simp
    _ ≤ ε⁻¹ * δ ^ (q / 2) * 1 := by
        gcongr
        rw [div_le_one hpos]
        exact hd
    _ = ε⁻¹ * δ ^ (q / 2) := mul_one _

/-- **The window event at every radius from the window event at radius `1/2`** (Berestycki-Gwynne, Section 6.4,
at the level of the failure event of Proposition 6.14).  For every `ρ > 0`: if the failure event of the window
estimate at radius `1/2`, with exponent `q` and the superpolynomial bound `ψ`, is negligible in every valid
environment (`NoStickingEvent.limLimSmall_noSticking` at `ρ = 1/2`), then the failure event at radius `ρ`, with
exponent `q / 2` and the superpolynomial bound `δ ↦ ψ (δ / (2 ρ))`, is negligible in every valid environment. -/
theorem limLimSmall_windowBad_allRadii {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {q : ℝ} (hq : 0 < q) {ψ : ℝ → ℝ}
    (hψ : (∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ δ) ∧
      ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ δ) (𝓝[>] 0) (𝓝 0))
    (hLL : ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2)),
        srwLaw (S.mult ε ω) x (windowBad ε (S.η ω) (1 / 2) δ q) ≤ ENNReal.ofReal (ψ δ)}))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ψ' : ℝ → ℝ, ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ' δ) ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ' δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ),
          srwLaw (S.mult ε ω) x (windowBad ε (S.η ω) ρ δ (q / 2)) ≤ ENNReal.ofReal (ψ' δ)}) := by
  have h2ρ : 0 < 2 * ρ := by positivity
  refine ⟨fun δ => ψ (δ / (2 * ρ)), ⟨fun δ hδ => hψ.1 _ (by positivity), fun p hp => ?_⟩, ?_⟩
  · have hc : Tendsto (fun δ : ℝ => δ / (2 * ρ)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun δ : ℝ => δ / (2 * ρ)) (𝓝 0) (𝓝 (0 / (2 * ρ))) :=
          (continuous_id.div_const _).tendsto 0
        rw [zero_div] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact div_pos hδ h2ρ
    have h := ((hψ.2 p hp).comp hc).const_mul ((2 * ρ) ^ (-p))
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hne : (2 * ρ) ^ (-p) ≠ 0 := (Real.rpow_pos_of_pos h2ρ _).ne'
    simp only [Function.comp]
    rw [Real.div_rpow (le_of_lt hδ) h2ρ.le]
    field_simp
  intro Ω _ S hS θ hθ
  have hPS : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨N, hN⟩ := FirstPass.Derived.exists_measure_coneScaleRadius_le_le hγ hγ2 hS.isQuantumCone (2 * ρ)
    (θ := ENNReal.ofReal (θ / 2)) (ENNReal.ofReal_pos.2 (by positivity))
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = (N : ℝ) + 1 := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; positivity
  have hE1 : S.P {ω | coneScaleRadius γ (S.hcirc ω) b ≤ 2 * ρ} ≤ ENNReal.ofReal (θ / 2) := by
    rw [hbdef]; exact hN N le_rfl
  obtain ⟨S', hS', hP, hηs, hbm, -⟩ := hEnvS γ hγ hγ2 Ω S hS b hb
  obtain ⟨δ₀', hδ₀', h'⟩ := hLL Ω S' hS' (θ / 2) (by positivity)
  obtain ⟨δ₁, hδ₁, hfl⟩ := exists_scale_floor_le hb hρ hq
  refine ⟨min (2 * ρ * δ₀') δ₁, lt_min (by positivity) hδ₁, fun δ hδ hδlt => ?_⟩
  have hδ1 : δ < 2 * ρ * δ₀' := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδ2 : δ < δ₁ := lt_of_lt_of_le hδlt (min_le_right _ _)
  obtain ⟨ε₀', hε₀', h''⟩ := h' (δ / (2 * ρ)) (by positivity)
    (by rw [div_lt_iff₀ h2ρ]; linarith)
  refine ⟨b * ε₀', by positivity, fun ε hε hεlt => ?_⟩
  have hε' : ε / b < ε₀' := by rw [div_lt_iff₀ hb]; linarith
  have hbad := h'' (ε / b) (div_pos hε hb) hε'
  rw [hP] at hbad
  have hle : {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ),
        srwLaw (S.mult ε ω) x (windowBad ε (S.η ω) ρ δ (q / 2)) ≤ ENNReal.ofReal (ψ (δ / (2 * ρ)))} ≤ᵐ[S.P]
      ({ω | coneScaleRadius γ (S.hcirc ω) b ≤ 2 * ρ} ∪
        {ω | ¬ ∀ x ∈ cellVertices (ε / b) (S'.η ω) (ball (0 : ℂ) (1 / 2)),
          srwLaw (S'.mult (ε / b) ω) x (windowBad (ε / b) (S'.η ω) (1 / 2) (δ / (2 * ρ)) q) ≤
            ENNReal.ofReal (ψ (δ / (2 * ρ)))}) := by
    filter_upwards [hηs, hbm] with ω h1 h2 hω
    by_cases hR : coneScaleRadius γ (S.hcirc ω) b ≤ 2 * ρ
    · exact Or.inl hR
    · right
      replace hR := not_le.1 hR
      have hR0 : 0 < coneScaleRadius γ (S.hcirc ω) b := by linarith
      intro hall
      apply hω
      intro x hx
      have hx' : x ∈ cellVertices (ε / b) (S'.η ω) (ball (0 : ℂ) (1 / 2)) :=
        cellVertices_subset_half hb hR0 hR.le (S.η ω) (S'.η ω) h1 hx
      calc srwLaw (S.mult ε ω) x (windowBad ε (S.η ω) ρ δ (q / 2))
          ≤ srwLaw (S'.mult (ε / b) ω) x
              (windowBad (ε / b) (S'.η ω) (1 / 2) (δ / (2 * ρ)) q) := by
            rw [MatedCRTEnv.mult_rescale S S' hb ω h2 ε]
            exact measure_mono (windowBad_subset_scaled hb hR0 hρ hδ hR.le (S.η ω) (S'.η ω) h1
              (hfl δ hδ hδ2 ε hε))
        _ ≤ ENNReal.ofReal (ψ (δ / (2 * ρ))) := hall x hx'
  calc S.P _ ≤ _ := measure_mono_ae hle
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) := add_le_add hE1 hbad
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

end NoStickingAllRadii
end MatedCRT
