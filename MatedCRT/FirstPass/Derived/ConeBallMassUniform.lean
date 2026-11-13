import MatedCRT.FirstPass.Derived.ConeEventTransfer
import MatedCRT.FirstPass.Derived.HBBallMassHolds

/-!
# Two-sided ball-mass bounds for the quantum cone, uniform over cone fields

Berestycki and Gwynne (arXiv:2003.10320v2), Lemma A.1: for `0 < ζ < 1` and `R < 1` there are `p > 0`, `C` and
`r₀ > 0`, depending only on `γ`, `R` and `ζ`, such that for every γ-quantum cone field and every `δ ∈ (0, r₀)`,
with probability at least `1 - C δ^p` every `z ∈ B_R(0)` satisfies
`δ^{(2+γ)²/2 + ζ} ≤ μ_h(B_δ(z)) ≤ δ^{(2-γ)²/2 - ζ}`.

With a countable dense set `D ⊆ ℂ`, the event contains the Borel event "every `z₀ ∈ D ∩ B_{R+δ/2}(0)` satisfies
`δ^{(2+γ)²/2+ζ} ≤ μ_h(B_{δ/2}(z₀))` and `μ_h(B_{3δ/2}(z₀)) ≤ δ^{(2-γ)²/2-ζ}`", which for small `δ` contains the
events of Lemma A.1 with `ζ/2` at the radii `δ/2` and `3δ/2`. The uniformity then comes from
`exists_uniform_polyBound_of_sandwich`.
-/

open MeasureTheory Set Metric Filter HarmonicBalls LatticeProb
open LatticeProb.LQG.LQGMeasureNonatomicMass
open scoped ENNReal Topology

namespace MatedCRT.FirstPass.Derived

/-- **BG20 Lemma A.1 with constants uniform over cone fields.** For `0 < ζ < 1` and `R < 1` there are `p > 0`,
`C` and `r₀ > 0` such that for every γ-quantum cone field and `δ ∈ (0, r₀)`, the event
"`δ^{(2+γ)²/2+ζ} ≤ μ_h(B_δ(z)) ≤ δ^{(2-γ)²/2-ζ}` for every `z ∈ B_R(0)`" fails with probability at most
`C δ^p`. -/
theorem exists_uniform_coneBallMass {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R ζ : ℝ} (hR : R < 1)
    (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsConeField γ P hC hcirc μ → ∀ δ : ℝ, 0 < δ → δ < r₀ →
        P {ω | ∀ z ∈ ball (0 : ℂ) R, ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + ζ)) ≤ μ ω (ball z δ) ∧
          μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ ((2 - γ) ^ 2 / 2 - ζ))}ᶜ ≤ ENNReal.ofReal (C * δ ^ p) := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hA1 : BerestyckiGwynneConeBallMassStmt := frozenBerestyckiGwynneConeBallMass_holds
  have hK : (0 : ℝ) < (3 / 2) ^ ((2 - γ) ^ 2 / 2 - ζ / 2) := by positivity
  have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ ((2 + γ) ^ 2 / 2 + ζ) ≤
      (1 / 2) ^ ((2 + γ) ^ 2 / 2 + ζ / 2) * δ ^ ((2 + γ) ^ 2 / 2 + ζ / 2) :=
    LQG.LQGMeasureNonatomicMass.eventually_rpow_le_mul (by positivity) (by linarith)
  have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ ((2 - γ) ^ 2 / 2 - ζ / 2) ≤
      ((3 / 2) ^ ((2 - γ) ^ 2 / 2 - ζ / 2))⁻¹ * δ ^ ((2 - γ) ^ 2 / 2 - ζ) :=
    LQG.LQGMeasureNonatomicMass.eventually_rpow_le_mul (inv_pos.2 hK) (by linarith)
  obtain ⟨r₂, hr₂, hr₂all⟩ := LQG.LQGMeasureNonatomicMass.exists_pos_of_eventually_nhdsGT (hev1.and hev2)
  refine exists_uniform_polyBound_of_sandwich (γ := γ)
    (Es := fun δ => {ν : Measure ℂ | ∀ z ∈ ball (0 : ℂ) (1 - 1 / 2 * δ),
        ENNReal.ofReal ((1 / 2 * δ) ^ ((2 + γ) ^ 2 / 2 + ζ / 2)) ≤ ν (ball z (1 / 2 * δ)) ∧
        ν (ball z (1 / 2 * δ)) ≤ ENNReal.ofReal ((1 / 2 * δ) ^ ((2 - γ) ^ 2 / 2 - ζ / 2))} ∩
      {ν : Measure ℂ | ∀ z ∈ ball (0 : ℂ) (1 - 3 / 2 * δ),
        ENNReal.ofReal ((3 / 2 * δ) ^ ((2 + γ) ^ 2 / 2 + ζ / 2)) ≤ ν (ball z (3 / 2 * δ)) ∧
        ν (ball z (3 / 2 * δ)) ≤ ENNReal.ofReal ((3 / 2 * δ) ^ ((2 - γ) ^ 2 / 2 - ζ / 2))})
    (Bm := fun δ => ⋂ z₀ ∈ D ∩ ball (0 : ℂ) (R + 1 / 2 * δ), {ν : Measure ℂ |
      ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + ζ)) ≤ ν (ball z₀ (1 / 2 * δ)) ∧
      ν (ball z₀ (3 / 2 * δ)) ≤ ENNReal.ofReal (δ ^ ((2 - γ) ^ 2 / 2 - ζ))})
    (Ew := fun δ => {ν | ∀ z ∈ ball (0 : ℂ) R, ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + ζ)) ≤ ν (ball z δ) ∧
      ν (ball z δ) ≤ ENNReal.ofReal (δ ^ ((2 - γ) ^ 2 / 2 - ζ))})
    (fun δ => MeasurableSet.biInter (hDc.mono inter_subset_left) fun z₀ _ =>
      (measurableSet_le measurable_const (Measure.measurable_coe measurableSet_ball)).inter
        (measurableSet_le (Measure.measurable_coe measurableSet_ball) measurable_const))
    (r₁ := min r₂ ((1 - R) / 2)) (lt_min hr₂ (by linarith)) (fun δ hδ hδr => ?_) ?_
  · have hδ2 : δ < r₂ := hδr.trans_le (min_le_left _ _)
    have hδR : 2 * δ ≤ 1 - R := by
      have := hδr.trans_le (min_le_right _ _)
      linarith
    obtain ⟨hlo, hhi⟩ := hr₂all δ hδ hδ2
    refine ⟨fun ν hν => ?_, fun ν hν => ?_⟩
    · obtain ⟨hν1, hν2⟩ := hν
      refine mem_iInter₂.2 fun z₀ hz₀ => ⟨?_, ?_⟩
      · have h := (hν1 z₀ (ball_subset_ball (by linarith) hz₀.2)).1
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hδ.le]
        exact hlo
      · have h := (hν2 z₀ (ball_subset_ball (by linarith) hz₀.2)).2
        refine h.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) hδ.le]
        calc (3 / 2 : ℝ) ^ ((2 - γ) ^ 2 / 2 - ζ / 2) * δ ^ ((2 - γ) ^ 2 / 2 - ζ / 2)
            ≤ (3 / 2 : ℝ) ^ ((2 - γ) ^ 2 / 2 - ζ / 2) *
              (((3 / 2) ^ ((2 - γ) ^ 2 / 2 - ζ / 2))⁻¹ * δ ^ ((2 - γ) ^ 2 / 2 - ζ)) :=
              mul_le_mul_of_nonneg_left hhi hK.le
          _ = δ ^ ((2 - γ) ^ 2 / 2 - ζ) := by rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
    · intro z hz
      obtain ⟨z₀, hz₀D, hzz₀⟩ := hD.exists_dist_lt z (half_pos hδ)
      have hz₀ : z₀ ∈ D ∩ ball (0 : ℂ) (R + 1 / 2 * δ) := by
        refine ⟨hz₀D, ?_⟩
        have htri := dist_triangle z₀ z 0
        rw [mem_ball] at hz ⊢
        rw [dist_comm z₀ z] at htri
        linarith
      obtain ⟨h1, h2⟩ := mem_iInter₂.1 hν z₀ hz₀
      exact ⟨h1.trans (measure_mono (ball_subset_ball' (by rw [dist_comm]; linarith))),
        (measure_mono (ball_subset_ball' (by linarith))).trans h2⟩
  · intro Ω _ P hC hcirc μ hcone
    have h := hA1 Ω P γ hC hcirc μ hγ hγ2 hcone (ζ / 2) (half_pos hζ) (by linarith)
    exact polyHighProb_inter (polyHighProb_comp_mul h (by norm_num : (0 : ℝ) < 1 / 2))
      (polyHighProb_comp_mul h (by norm_num : (0 : ℝ) < 3 / 2))

end MatedCRT.FirstPass.Derived
