import MatedCRT.FirstPass.Frozen.S3c
import MatedCRT.FirstPass.Derived.ExitTimeMomentLogIntegral
import MatedCRT.FirstPass.Derived.GreenUpperBoundOfInputs

/-!
# Berestycki-Gwynne Proposition 5.1 from its probabilistic inputs

Berestycki-Gwynne (arXiv:2003.10320), Proposition 5.1, equation (5.1). The deterministic form
`ExitTimeMomentLogIntegral.exitTimeMoment_le_logIntegral` holds on the intersection of four events of
polynomially high probability:

* the Green kernel upper bound (BG20 Lemma 5.4, `GreenKernelUpperBoundStmt`), whose exponent may be decreased;
* the near-vertex count (BG20 (5.41)): at most `ε^{-1+α₀}` cells meet any ball `B_{ε^β}(z)`, `z ∈ B_ρ`;
* the crude Green function bound (BG20 Lemma 5.6, `GreenFunctionCrudeBoundStmt`) with `ζ = min (α₀/2) (1/2)`;
* the upper half of the degree-weighted cell-sum comparison (BG20 Lemma A.5, (A.21)) for Borel `D ⊆ B_ρ`;

together with the almost sure facts that `η` is continuous, proper and area-parametrized and that adjacent
cells meet. The exponents are `β = min β₀ (b/2)` (`β₀` from Lemma 5.4, `b` the Lipschitz exponent of
Lemma A.5), `α = min (α₀/2) α₁` (`α₁` from Lemma A.5), and the constant is `2 (1 - log 2)⁻¹ + 6 C`
(`C` from Lemma 5.4 at `ρ`).
-/

open HarmonicBalls

namespace MatedCRT

open Set Metric MeasureTheory Filter
open scoped ENNReal

namespace BG20Prop51Derived

/-- For `0 < ε ≤ 1`, `β ≤ b/2` and `ε^{b/2} ≤ C⁻¹`: `C ε^{-β} ≤ ε^{-b}`. -/
theorem mul_rpow_neg_le {ε β b C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 < C) (hβb : β ≤ b / 2)
    (hsmall : ε ^ (b / 2) ≤ C⁻¹) : C * ε ^ (-β) ≤ ε ^ (-b) := by
  have h3 : C ≤ ε ^ (-(b / 2)) := by
    rw [Real.rpow_neg hε.le]
    exact (le_inv_comm₀ (Real.rpow_pos_of_pos hε _) hC).1 hsmall
  have h4 : ε ^ (-β) ≤ ε ^ (-(b / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (neg_le_neg hβb)
  calc C * ε ^ (-β) ≤ ε ^ (-(b / 2)) * ε ^ (-(b / 2)) :=
        mul_le_mul h3 h4 (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg hε.le _)
    _ = ε ^ (-b) := by rw [← Real.rpow_add hε]; ring_nf

/-- **BG20 Proposition 5.1 from Lemma 5.4, (5.41), Lemma 5.6 and Lemma A.5.** The near-vertex count
`hnear` (BG20 (5.41), for every `β > 0`) and the upper half of BG20 Lemma A.5 (A.21) for Borel sets
`D ⊆ B_ρ` (`hA5`, exponents `α₁ = α(γ)`, `b = β(γ)` as in the source) enter as hypotheses. -/
theorem bG20Prop51_of_nearCount {𝒮 : SpaceFillingSLEModel} (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮)
    (hnear : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ β : ℝ, 0 < β → ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ z ∈ ball (0 : ℂ) ρ, ∀ s : Finset ℤ,
        (↑s : Set ℤ) ⊆ cellVertices ε (S.η ω) (ball z (ε ^ β)) → (s.card : ℝ) ≤ ε ^ (-1 + α₀)})
    (hA5 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α₁ b : ℝ, 0 < α₁ ∧ 0 < b ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 → PolyHighProb S.P fun ε => {ω | ∀ D : Set ℂ, MeasurableSet D →
        D ⊆ ball 0 ρ → ∀ g : ℂ → ℝ, (∀ x, 0 ≤ g x ∧ |g x| ≤ ε ^ (-b)) →
        (∀ x y, |g x - g y| ≤ ε ^ (-b) * ‖x - y‖) →
        ∀ w : ℤ → ℂ, (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ D) →
        ∑' k : cellVertices ε (S.η ω) D, (matedDeg (S.mult ε ω) k : ℝ) * g (w k) ≤
          6 * ε⁻¹ * ∫ x in thickening (ε ^ α₁) D, g x ∂S.μ ω + ε ^ (-1 + α₁)}) :
    BG20Prop51 𝒮 := by
  intro γ hγ hγ2
  obtain ⟨β₀, hβ₀, hG⟩ := h214 γ hγ hγ2
  obtain ⟨α₁, b, hα₁, hb, hA⟩ := hA5 γ hγ hγ2
  set β : ℝ := min β₀ (b / 2) with hβ_def
  have hβ : 0 < β := lt_min hβ₀ (half_pos hb)
  obtain ⟨α₀, hα₀, hN⟩ := hnear γ hγ hγ2 β hβ
  refine ⟨min (α₀ / 2) α₁, lt_min (half_pos hα₀) hα₁, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨C, hC, hGρ⟩ := hG ρ hρ hρ1
  have hlog2 : 0 < 1 - Real.log 2 := by have := Real.log_two_lt_d9; linarith
  refine ⟨2 * (1 - Real.log 2)⁻¹ + 6 * C, by positivity, fun Ω _ S hS => ?_⟩
  set ζ : ℝ := min (α₀ / 2) (1 / 2) with hζ_def
  have hζ : 0 < ζ := lt_min (half_pos hα₀) one_half_pos
  have hζ1 : ζ < 1 := (min_le_right _ _).trans_lt one_half_lt_one
  have hE := FirstPass36.polyHighProb_inter
    (FirstPass36.polyHighProb_inter (FirstPass36.polyHighProb_inter (hGρ Ω S hS)
      (hN ρ hρ hρ1 Ω S hS)) (h215 γ hγ hγ2 ρ ζ hρ hρ1 hζ hζ1 Ω S hS)) (hA Ω S hS ρ hρ hρ1)
  have hae : ∀ᵐ ω ∂S.P, Continuous (S.η ω) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
      (∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
        (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) ∧
      IsAreaParametrized (S.μ ω) (S.η ω) := by
    filter_upwards [TraceInputs68.ae_continuous_eta hS, hS.ae_tendsto_cocompact,
      TraceInputs68.ae_adjacent hγ hγ2 S hS, hS.isAreaParametrized] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨r₁, hr₁, hr₁h⟩ := exists_rpow_le_of_small (half_pos hb) (inv_pos.2 hC)
  refine S3cBridge.polyHighProb_mono_ae_small (r₁ := min r₁ 1) (lt_min hr₁ one_pos) hE hae ?_
  intro ε hε hεr ω hω hq
  obtain ⟨⟨⟨hGω, hNω⟩, hMω⟩, hAω⟩ := hω
  obtain ⟨hη, hp, hmeet, hpar⟩ := hq
  intro D hDm hDρ hμD a _ N
  have hε1 : ε ≤ 1 := (lt_of_lt_of_le hεr (min_le_right _ _)).le
  have hlf := isLocallyFiniteMult_of_cells_meet hη hp hε (hmeet ε hε)
  have hcons := S.mult_succ_ne_zero hε.le ω
  have hCε : C * ε ^ (-β) ≤ ε ^ (-b) :=
    mul_rpow_neg_le hε hε1 hC (min_le_right _ _) (hr₁h ε hε (lt_of_lt_of_le hεr (min_le_left _ _)))
  have hbd : C * (Real.log (ε ^ (-β)) + 1) ≤ ε ^ (-b) := by
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hε (-β))
    exact (mul_le_mul_of_nonneg_left (by linarith) hC.le).trans hCε
  have h1 : 1 ≤ ε ^ (-β) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (neg_nonpos.2 hβ.le)
  have hKM : ε ^ (-1 + α₀) * ε ^ (-ζ) ≤ ε ^ (-1 + min (α₀ / 2) α₁) := by
    rw [← Real.rpow_add hε]
    refine Real.rpow_le_rpow_of_exponent_ge hε hε1 ?_
    have := min_le_left (α₀ / 2) α₁
    have := min_le_left (α₀ / 2) (1 / 2 : ℝ)
    linarith
  exact ExitTimeMomentLogIntegral.exitTimeMoment_le_logIntegral hlf hcons hε hε1 hη hp hDρ hρ1.le
    hC.le h1 hbd hCε
    (fun x hx y hy hd => hGω x hx y hy
      ((Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_left β₀ (b / 2))).trans hd))
    (fun y hy s hs => hNω _
      (hDρ (InteriorCellGeometry.vertexPoint_mem_of_mem_interiorCellVertices hε.le hη hy)) s hs)
    (Real.rpow_nonneg hε.le _) hMω (fun c _ => FirstPass36.mdeg_pos_of_edge hlf (hcons c))
    (hAω D hDm hDρ) (min_le_right _ _) hKM
    (fun z => ExitTimeLogIntegral.measure_singleton_eq_zero_of_isAreaParametrized hpar z) hμD N a

end BG20Prop51Derived

end MatedCRT
