import MatedCRT.FirstPass.Derived.ConeEventTransfer
import MatedCRT.FirstPass.Derived.ConeBallRatio

/-!
# The concentric ball-mass ratio bound for the quantum cone, uniform over cone fields

Berestycki and Gwynne (arXiv:2003.10320v2), Lemma A.2 (p. 66), concentric form: for `0 < c < 1`, `ζ > 0` and
`R < 1` there are `p > 0`, `C` and `r₀ > 0`, depending only on `γ`, `R`, `c` and `ζ`, such that for every
γ-quantum cone field and every `δ ∈ (0, r₀)`, with probability at least `1 - C δ^p` every `z ∈ B_R(0)` satisfies
`δ^{γ²/2 + ζ} μ_h(B_δ(z)) ≤ μ_h(B_{cδ}(z))`.

The event quantifies over uncountably many centres. With `κ = c/4` and a countable dense set `D ⊆ ℂ` it contains the
Borel event "every `z₀ ∈ D ∩ B_{R+κδ}(0)` satisfies `δ^{γ²/2+ζ} μ_h(B_{(1+κ)δ}(z₀)) ≤ μ_h(B_{(c-κ)δ}(z₀))`", which
contains the event of `polyHighProb_coneBallRatio` at radius `(1+κ)δ` and ratio `(c-κ)/(1+κ)`. The uniformity then
comes from `exists_uniform_polyBound_of_sandwich`.
-/

open MeasureTheory Set Metric Filter HarmonicBalls LatticeProb
open LatticeProb.LQG.LQGMeasureNonatomicMass
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **BG20 Lemma A.2 (concentric form) with constants uniform over cone fields.** For `0 < c < 1`, `ζ > 0` and
`R < 1` there are `p > 0`, `C` and `r₀ > 0` such that for every γ-quantum cone field and `δ ∈ (0, r₀)`, the event
"`δ^{γ²/2+ζ} μ_h(B_δ(z)) ≤ μ_h(B_{cδ}(z))` for every `z ∈ B_R(0)`" fails with probability at most `C δ^p`. -/
theorem exists_uniform_coneBallRatio {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R c ζ : ℝ} (hR : R < 1)
    (hc0 : 0 < c) (hc1 : c < 1) (hζ : 0 < ζ) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsConeField γ P hC hcirc μ → ∀ δ : ℝ, 0 < δ → δ < r₀ →
        P {ω | ∀ z ∈ ball (0 : ℂ) R, ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * μ ω (ball z δ) ≤
          μ ω (ball z (c * δ))}ᶜ ≤ ENNReal.ofReal (C * δ ^ p) := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  have he0 : 0 ≤ γ ^ 2 / 2 + ζ := by positivity
  set κ : ℝ := c / 4 with hκ
  have hκ0 : 0 < κ := by positivity
  set c' : ℝ := (c - κ) / (1 + κ) with hc'
  have hc'0 : 0 < c' := div_pos (by linarith) (by linarith)
  have hc'1 : c' < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hc'κ : ∀ δ : ℝ, c' * ((1 + κ) * δ) = (c - κ) * δ := fun δ => by
    rw [hc']; field_simp
  refine exists_uniform_polyBound_of_sandwich (γ := γ)
    (Es := fun δ => {ν | ∀ z ∈ ball (0 : ℂ) (1 - (1 + κ) * δ),
      ENNReal.ofReal (((1 + κ) * δ) ^ (γ ^ 2 / 2 + ζ)) * ν (ball z ((1 + κ) * δ)) ≤
        ν (ball z (c' * ((1 + κ) * δ)))})
    (Bm := fun δ => ⋂ z₀ ∈ D ∩ ball (0 : ℂ) (R + κ * δ), {ν : Measure ℂ |
      ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * ν (ball z₀ ((1 + κ) * δ)) ≤ ν (ball z₀ ((c - κ) * δ))})
    (Ew := fun δ => {ν | ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * ν (ball z δ) ≤ ν (ball z (c * δ))})
    (fun δ => MeasurableSet.biInter (hDc.mono inter_subset_left) fun z₀ _ =>
      measurableSet_le ((Measure.measurable_coe measurableSet_ball).const_mul _)
        (Measure.measurable_coe measurableSet_ball))
    (r₁ := (1 - R) / (1 + 2 * κ)) (div_pos (by linarith) (by linarith)) (fun δ hδ hδr => ?_) ?_
  · have hδR : R + κ * δ ≤ 1 - (1 + κ) * δ := by
      rw [lt_div_iff₀ (by linarith)] at hδr
      have : δ * (1 + 2 * κ) = δ + 2 * (κ * δ) := by ring
      have : (1 + κ) * δ = δ + κ * δ := by ring
      linarith
    have h1κ : (1 + κ) * δ = δ + κ * δ := by ring
    have hcκ : (c - κ) * δ = c * δ - κ * δ := by ring
    refine ⟨fun ν hν => ?_, fun ν hν => ?_⟩
    · refine mem_iInter₂.2 fun z₀ hz₀ => ?_
      have h := hν z₀ (ball_subset_ball hδR hz₀.2)
      rw [hc'κ] at h
      refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) h
      exact Real.rpow_le_rpow hδ.le (le_mul_of_one_le_left hδ.le (by linarith)) he0
    · intro z hz
      obtain ⟨z₀, hz₀D, hzz₀⟩ := hD.exists_dist_lt z (mul_pos hκ0 hδ)
      have hz₀ : z₀ ∈ D ∩ ball (0 : ℂ) (R + κ * δ) := by
        refine ⟨hz₀D, ?_⟩
        have htri := dist_triangle z₀ z 0
        rw [mem_ball] at hz ⊢
        rw [dist_comm z₀ z] at htri
        linarith
      have h := mem_iInter₂.1 hν z₀ hz₀
      calc ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * ν (ball z δ)
          ≤ ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * ν (ball z₀ ((1 + κ) * δ)) :=
            mul_le_mul' le_rfl (measure_mono (ball_subset_ball' (by linarith)))
        _ ≤ ν (ball z₀ ((c - κ) * δ)) := h
        _ ≤ ν (ball z (c * δ)) :=
            measure_mono (ball_subset_ball' (by rw [dist_comm]; linarith))
  · intro Ω _ P hC hcirc μ hcone
    exact polyHighProb_comp_mul (polyHighProb_coneBallRatio hγ hγ2 hcone hc'0 hc'1 hζ)
      (by linarith : (0 : ℝ) < 1 + κ)

end MatedCRT.FirstPass.Derived
