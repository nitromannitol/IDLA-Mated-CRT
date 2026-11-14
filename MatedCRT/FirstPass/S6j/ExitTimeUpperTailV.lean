import MatedCRT.FirstPass.S6j.ExitTailUpperStepV
import MatedCRT.FirstPass.S6j.ExitTailUpperBrownian
import MatedCRT.FirstPass.S6j.ExitTailAssembly
import MatedCRT.FirstPass.S6j.CellDiamSmall
import MatedCRT.FirstPass.S6j.SuperpolyEnvelope
import MatedCRT.FirstPass.S6j.ExitTailFloorScale
import MatedCRT.FirstPass.Derived.LimLimSmall

/-!
# BG20 Lemma 6.10, estimate (6.50), from the uniform-start invariance principle

For `0 < γ < 2` there is a superpolynomial `ψ₀` such that for every valid environment, with probability tending to
`1` as `ε → 0`, the walk from every `x ∈ V^ε(B_{1/2})` makes at least `K = ⌊δ^{-3}⌋` successive exits from the
cells meeting the balls `B_δ(η(ε ·))` before leaving the cells meeting `B_{1/2}` with probability at most
`ψ₀(δ)`. This is the full-cell form of the estimate (the exit set and the windows are the cells meeting the balls,
not the cells inside them); the input is `GMS21UniformStartInput`.
-/

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.ExitTimeUpperTailV

open MatedCRT.SuccessiveExitGaps MatedCRT.FirstPass.Derived

/-- **[BG20, Lemma 6.10], estimate (6.50), from the uniform-start invariance principle.** -/
theorem exitTimeUpperTailV_of_uniformStart {𝒮 : SpaceFillingSLEModel} (hN4 : GMS21UniformStartInput 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ψ₀ : ℝ → ℝ, ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2)),
          srwLaw (S.mult ε ω) x
            {X | ¬ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X ≤
              succExit (fun w => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) w) δ))
                ⌊δ ^ (-3 : ℝ)⌋₊ X} ≤ ENNReal.ofReal (ψ₀ δ)}) := by
  intro γ hγ0 hγ2
  choose C hC using fun p : ℕ =>
    ExitTailUpperBrownian.planarBrownianMotion_stays_by_stepTime_superpoly (ζ := 1 / 2) (by norm_num)
      (by norm_num) p
  obtain ⟨δ₂, hδ₂0, hδ₂⟩ := ExitTailFloorScale.exists_small_floor_le
  have hδ₁0 : 0 < min δ₂ (1 / 2) := lt_min hδ₂0 (by norm_num)
  have hcs := SuperpolyEnvelope.cutoff_superpoly C (A := 1 / 16) (β := 1) (δ₁ := min δ₂ (1 / 2))
    (by norm_num) one_pos hδ₁0
  refine ⟨SuperpolyEnvelope.cutoff C (1 / 16) 1 (min δ₂ (1 / 2)), ⟨hcs.1, hcs.2.2⟩, ?_⟩
  intro Ω _ S hS θ hθ
  refine ⟨min δ₂ (1 / 2), hδ₁0, fun δ hδ0 hδ => ?_⟩
  have hδδ₁ : δ ≤ min δ₂ (1 / 2) := hδ.le
  have hδ₂δ : δ ≤ δ₂ := hδδ₁.trans (min_le_left _ _)
  have hδ12 : δ ≤ 1 / 2 := hδδ₁.trans (min_le_right _ _)
  set c : ℝ := δ / 100 with hc
  set κ : ℝ := min (δ / 100) (SuperpolyEnvelope.budget δ) with hκ
  have hc0 : 0 < c := by positivity
  have hκ0 : 0 < κ := lt_min (by positivity) (SuperpolyEnvelope.budget_pos hδ0)
  have hκ1 : κ ≤ δ / 100 := min_le_left _ _
  have hκb : κ ≤ SuperpolyEnvelope.budget δ := min_le_right _ _
  obtain ⟨ε₁, hε₁0, hε₁⟩ := hN4 γ hγ0 hγ2 Ω S hS (7 / 8) (5 / 8) (by norm_num) (by norm_num) κ hκ0
    (θ / 2) (by positivity)
  obtain ⟨ε₂, hε₂0, hε₂⟩ :=
    CellDiamSmall.exists_eps_prob_not_cellDiam_le hγ0 hγ2 S hS (R := 7 / 8) (c := c) (by norm_num)
      (by norm_num) hc0 (θ := θ / 2) (by positivity)
  refine ExitTailAssembly.exists_eps_measure_compl_le S.P (TraceInputs68.ae_continuous_eta hS) ?_ hθ.le
    ⟨ε₁, hε₁0, hε₁⟩ ⟨ε₂, hε₂0, hε₂⟩
  intro ε hε ω hω₁ hω₂ hη x hx
  have hr1 : δ / 16 < 1 := by linarith
  have hstep := ExitTailUpperStepV.srwLaw_notExit_le_planarBrownianMotion_add_V hε.le hη (m := S.mult ε ω)
    (c := c) (δ := δ) (κ := κ) (r := δ / 8) (K := ⌊δ ^ (-3 : ℝ)⌋₊)
    (K' := ⌊(δ / 16) ^ (-(2 + 1 / 2 : ℝ))⌋₊) hδ0 (by linarith) (by linarith) (by linarith)
    (by linarith) (hδ₂ δ hδ0 hδ₂δ) hω₂ hω₁ hx
  refine SuperpolyEnvelope.le_ofReal_cutoff (A := 1 / 16) (β := 1) (r := δ / 16) (by norm_num) hδ0.le
    hδδ₁ (by positivity) (by rw [Real.rpow_one]; linarith) hκb (fun p => ?_) hstep
  have h2 := hC p (vertexPoint ε (S.η ω) x) 2 two_pos (δ / 16) (by positivity) hr1
  rwa [show (2 : ℝ) * (δ / 16) = δ / 8 by ring] at h2

end MatedCRT.ExitTimeUpperTailV
