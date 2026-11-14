import MatedCRT.FirstPass.S6j.ExitTailCombine
import MatedCRT.FirstPass.S6j.SuperpolyEnvelope
import MatedCRT.FirstPass.S6j.StepScaleRegime
import MatedCRT.FirstPass.S6j.CellDiamSmall
import MatedCRT.FirstPass.S3t.WalkAdjacency
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.Derived.MepsLowerAssembly

/-!
# [BG20, Lemma 6.9] from the uniform-start invariance principle

`exitTimeLowerTail_of_uniformStart` proves the estimate `(6.32)` of [BG20, Lemma 6.9] (arXiv:2003.10320), in the
form of the hypothesis `h632` of `mεCdf_lower_of_exitTimeLowerTail`, from the named literature input
`GMS21UniformStartInput` ([GMS21, Theorem 3.4], uniform in the starting point). The proof is the one of [BG20]:
on the cell-size event the walk event of `(6.28)` forces the stopped interpolated walk to move by `δ` before its
`K`-th displacement time of size `2δ^ℓ + 6c`; the invariance principle transfers this, up to `κ`, to planar Brownian
motion, where `(6.29)` bounds the probability by `C_p (5 δ^{ℓ-1})^p` for every `p`; the superpolynomial `ψ₀` is the
infimum over `p` of these bounds plus the tolerance `exp(-1/δ)`, cut off at `δ₁`.

`mεCdf_lower_of_uniformStart` is the lower half of [BG20, (1.8)] with `h632` supplied.
-/

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.ExitTimeLowerTail

/-- **[BG20, Lemma 6.9], estimate (6.32), from the uniform-start invariance principle.** For `0 < γ < 2`,
`ρ ∈ (0, 1)`, `ℓ > 1` and `ζ ∈ (0, 1)` there is a superpolynomial `ψ₀` such that for every valid environment and
`δ ∈ (0, 1)`, with probability tending to `1` as `ε → 0`, the walk from every `x ∈ V^ε(B_{ρ-δ})` leaves the cells of
`B_δ(η(εx))` before its `K`-th successive exit from the cells of the balls of radius `δ^ℓ`,
`K = ⌊δ^{-(2-ζ)(ℓ-1)}⌋`, with probability at most `ψ₀(δ)`. -/
theorem exitTimeLowerTail_of_uniformStart {𝒮 : SpaceFillingSLEModel} (hN4 : GMS21UniformStartInput 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ ℓ : ℝ, 1 < ℓ →
      ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ ψ₀ : ℝ → ℝ,
      ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧ ψ₀ 0 = 0 ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ - δ)),
          srwLaw (S.mult ε ω) x {y |
            vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y <
              SuccessiveExitGaps.succExit
                (fun z => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) z) (δ ^ ℓ)))
                ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ y} ≤ ENNReal.ofReal (ψ₀ δ)}ᶜ ≤ ENNReal.ofReal θ := by
  intro γ hγ0 hγ2 ρ hρ0 hρ1 ℓ hℓ ζ hζ0 hζ1
  have hζ'0 : 0 < ζ / 2 := by positivity
  have hζ'1 : ζ / 2 < 1 := by linarith
  choose C hC using fun p : ℕ =>
    ExitTailCombine.planarBrownianMotion_exit_by_stepTime_superpoly hζ'0 hζ'1 p
  have hℓ1 : 0 < ℓ - 1 := by linarith
  have hx : 0 < ζ * (ℓ - 1) / 2 := by positivity
  obtain ⟨δ₂, hδ₂0, hδ₂⟩ := StepScaleRegime.exists_small_rpow_neg_ge hx
  have hδ₁0 : 0 < min δ₂ ((1 - ρ) / 5) := lt_min hδ₂0 (by linarith)
  refine ⟨SuperpolyEnvelope.cutoff C 5 (ℓ - 1) (min δ₂ ((1 - ρ) / 5)),
    SuperpolyEnvelope.cutoff_superpoly C (by norm_num) hℓ1 hδ₁0, ?_⟩
  intro Ω _ S hS δ hδ0 hδ1 θ hθ
  by_cases hδδ₁ : min δ₂ ((1 - ρ) / 5) < δ
  · refine ⟨1, one_pos, fun ε _ _ => ?_⟩
    rw [ExitTailAssembly.compl_setOf_forall_srwLaw_le_eq_empty
      (SuperpolyEnvelope.cutoff_of_lt hδδ₁).ge, measure_empty]
    exact zero_le
  rw [not_lt] at hδδ₁
  have hδ₂δ : δ ≤ δ₂ := hδδ₁.trans (min_le_left _ _)
  have hδρ : δ ≤ (1 - ρ) / 5 := hδδ₁.trans (min_le_right _ _)
  have hδℓ : 0 < δ ^ ℓ := Real.rpow_pos_of_pos hδ0 ℓ
  have hδℓδ : δ ^ ℓ ≤ δ := StepScaleRegime.rpow_le_self_of_one_le hδ0 hδ1.le hℓ.le
  set R : ℝ := (1 + ρ) / 2 with hR
  set c : ℝ := δ ^ ℓ / 100 with hc
  set κ : ℝ := min (δ ^ ℓ / 100) (SuperpolyEnvelope.budget δ) with hκ
  have hc0 : 0 < c := by positivity
  have hκ0 : 0 < κ := lt_min (by positivity) (SuperpolyEnvelope.budget_pos hδ0)
  have hκ1 : κ ≤ δ ^ ℓ / 100 := min_le_left _ _
  have hκb : κ ≤ SuperpolyEnvelope.budget δ := min_le_right _ _
  obtain ⟨ha0, hr0, hr1, hKK⟩ := StepScaleRegime.stepScale_regime hδ0 hδ1 hℓ hζ0 hζ1 hc0.le le_rfl
    hκ0.le hκ1 (hδ₂ δ hδ0 hδ₂δ)
  have hr5 := StepScaleRegime.stepRatio_le hδ0 hδ1.le hℓ.le (c := c) le_rfl hκ1
  have har : 2 * (2 * δ ^ ℓ + 6 * c) + 2 * κ ≤
      (δ - c - 2 * κ) * ((2 * (2 * δ ^ ℓ + 6 * c) + 3 * κ) / (δ - c - 2 * κ)) := by
    rw [mul_div_cancel₀ _ ha0.ne']
    linarith
  have hR0 : 0 < R := by positivity
  have hR1 : R < 1 := by linarith
  have hρR : ρ < R := by linarith
  obtain ⟨ε₁, hε₁0, hε₁⟩ := hN4 γ hγ0 hγ2 Ω S hS R ρ hρ0 hρR κ hκ0 (θ / 2) (by positivity)
  obtain ⟨ε₂, hε₂0, hε₂⟩ :=
    CellDiamSmall.exists_eps_prob_not_cellDiam_le hγ0 hγ2 S hS hR0 hR1 hc0 (θ := θ / 2) (by positivity)
  refine ExitTailAssembly.exists_eps_measure_compl_le S.P
    ((TraceInputs68.ae_continuous_eta hS).and (TruncatedLaws.walk_cells_meet_ae hγ0 hγ2 S hS))
    ?_ hθ.le ⟨ε₁, hε₁0, hε₁⟩ ⟨ε₂, hε₂0, hε₂⟩
  intro ε hε ω hω₁ hω₂ hG
  obtain ⟨hη, hadj⟩ := hG
  intro x hx
  have hstep := ExitTailCombine.srwLaw_le_planarBrownianMotion_add hε.le hη (m := S.mult ε ω)
    (a := δ - c - 2 * κ) (K := ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊)
    (K' := ⌊((2 * (2 * δ ^ ℓ + 6 * c) + 3 * κ) / (δ - c - 2 * κ)) ^ (-(2 - ζ / 2))⌋₊)
    hδ0 hc0.le hδℓ (by linarith) (by linarith) (by linarith) hω₂ (hadj ε hε) hω₁
    (by linarith) har hKK hx
  refine SuperpolyEnvelope.le_ofReal_cutoff (by norm_num) hδ0.le hδδ₁ hr0.le hr5 hκb (fun p => ?_) hstep
  exact hC p (vertexPoint ε (S.η ω) x) ⟨δ - c - 2 * κ, ha0.le⟩
    (show (0 : ℝ≥0) < ⟨δ - c - 2 * κ, ha0.le⟩ from NNReal.coe_pos.mp ha0)
    ⟨(2 * (2 * δ ^ ℓ + 6 * c) + 3 * κ) / (δ - c - 2 * κ), hr0.le⟩
    (show (0 : ℝ≥0) < ⟨_, hr0.le⟩ from NNReal.coe_pos.mp hr0)
    (show (⟨_, hr0.le⟩ : ℝ≥0) < 1 from NNReal.coe_lt_one.mp hr1)

/-- **Lower half of [BG20, (1.8)] from the uniform-start invariance principle**: `mεCdf_lower_of_exitTimeLowerTail`
with the estimate `(6.32)` supplied by `exitTimeLowerTail_of_uniformStart`. -/
theorem mεCdf_lower_of_uniformStart {𝒮 : SpaceFillingSLEModel}
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮) (hN4 : GMS21UniformStartInput 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2 :=
  FirstPass.Derived.mεCdf_lower_of_exitTimeLowerTail h213 h214 (exitTimeLowerTail_of_uniformStart hN4)

end MatedCRT.ExitTimeLowerTail
