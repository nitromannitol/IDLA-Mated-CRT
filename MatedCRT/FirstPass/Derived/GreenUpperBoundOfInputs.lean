import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.Derived.GreenLemma55Assembly
import MatedCRT.FirstPass.S3i.GoodEvent
import MatedCRT.FirstPass.S3c.ExitTimeBridge
import MatedCRT.FirstPass.S4S6c.TraceInputs68

/-!
# The Green function upper bound from its three probabilistic inputs (BG20 Lemma 5.4)

`MatedCRT.greenKernelUpperBoundStmt_of_inputs` derives `GreenKernelUpperBoundStmt` (BG20 Lemma 5.4)
from the cell size estimate (`CellSizeEstimateStmt`, BG20 Lemma 2.4) and three events of polynomially
high probability, each stated at the radii `ρ₀ = (1 + ρ) / 2` and `δ₀ = (1 - ρ) / 8` that the deterministic
skeleton `greenKernel_interiorCellVertices_le_log_of_harnack_of_cellSum` needs:

* the Harnack inequality on circles for the Green function killed on `V^ε(B_{ρ₀}) \ V^ε(∂B_{ρ₀})`
  (BG20 Proposition 3.8),
* the bound `∑ deg(k) (diam H_k / dist(η(b), H_k))² ≤ C₂ log (1/s)` over the cells outside `B_s(η(b))`
  (BG20 Lemma 5.3, steps 3-5),
* the segment paths from `η(b)` to the outside of `B_{ρ₀}` for almost every direction
  (BG20 Lemma 5.3, step 1).

The deterministic skeleton is applied on the intersection of these events with the almost sure
properties of a valid environment; the scales `ε^β ≤ s` are matched by `β = min β₁ β₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory Filter Topology HarmonicBalls LatticeProb

namespace MatedCRT

/-- A power with positive exponent is small for small arguments. -/
theorem exists_rpow_le_of_small {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r < r₁ → r ^ β ≤ c := by
  refine ⟨c ^ β⁻¹, Real.rpow_pos_of_pos hc _, fun r hr hrr => ?_⟩
  calc r ^ β ≤ (c ^ β⁻¹) ^ β := Real.rpow_le_rpow hr.le hrr.le hβ.le
    _ = c := Real.rpow_inv_rpow hc.le hβ.ne'

theorem greenKernelUpperBoundStmt_of_inputs {𝒮 : SpaceFillingSLEModel}
    (hsize : CellSizeEstimateStmt 𝒮)
    (hHarn : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ s : ℝ,
        ε ^ β ≤ s → s ≤ (1 - ρ) / 8 →
        ∀ a ∈ cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) b) s)),
        ∀ y ∈ cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) b) s)),
          greenKernel (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))) a b ≤
            C₁ * greenKernel (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))) y b})
    (hsum : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ s : ℝ,
        ε ^ β ≤ s → s ≤ (1 - ρ) / 8 →
        ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)) ∧
            k ∉ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) b) s)) →
          ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) *
            (diam (cell ε (S.η ω) k) /
              infDist (vertexPoint ε (S.η ω) b) (cell ε (S.η ω) k)) ^ 2 ≤
            C₂ * Real.log (1 / s)})
    (hpath : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ b ∈ interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)),
        ∃ (ℓ : ℝ) (Y : Finset ℤ) (F : Finset ℤ → List ℤ), (∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) ∧
        (∀ᵐ θ ∂uniformDirection,
          (segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ).Nodup) ∧
        (∀ᵐ θ ∂uniformDirection,
          (segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ).IsChain
            fun a c => S.mult ε ω a c ≠ 0) ∧
        (∀ᵐ θ ∂uniformDirection, ∃ p,
          segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ = b :: p ∧
          (∀ v ∈ b :: p, v ∈ cellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))) ∧
          (b :: p).getLast (List.cons_ne_nil b p) ∉
            interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)))}) :
    GreenKernelUpperBoundStmt 𝒮 := by
  intro γ hγ hγ2
  obtain ⟨β₁, hβ₁, hH⟩ := hHarn γ hγ hγ2
  obtain ⟨β₂, hβ₂, hS⟩ := hsum γ hγ hγ2
  refine ⟨min β₁ β₂, lt_min hβ₁ hβ₂, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨C₁, hC₁, hHρ⟩ := hH ρ hρ0 hρ1
  obtain ⟨C₂, hC₂, hSρ⟩ := hS ρ hρ0 hρ1
  have hδ₀ : 0 < (1 - ρ) / 8 := by linarith
  have hδ₀1 : (1 - ρ) / 8 ≤ 1 := by linarith
  have hlog : 0 ≤ Real.log (4 / ((1 - ρ) / 8)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ₀]; linarith
  refine ⟨4 * (C₁ * C₂) * (1 + Real.log (4 / ((1 - ρ) / 8))), by positivity, ?_⟩
  intro Ω _ S hSv
  classical
  have hq : 0 < 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 := by
    have h : 0 < (2 + γ) ^ 2 := by positivity
    have e : 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 := by ring
    rw [e]; positivity
  have hζ1 : 1 / (2 + γ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hDE := hsize γ hγ hγ2 (1 / (2 + γ) ^ 2) ((1 + ρ) / 2) (by positivity) hζ1 (by linarith)
    (by linarith) Ω S hSv
  obtain ⟨r₁, hr₁, hr₁h⟩ := exists_rpow_le_of_small (lt_min hβ₁ hβ₂) (half_pos hδ₀)
  obtain ⟨r₂, hr₂, hr₂h⟩ := exists_rpow_le_of_small hq (show 0 < (1 - ρ) / 8 / 4 by positivity)
  have hE := FirstPass36.polyHighProb_inter
    (FirstPass36.polyHighProb_inter (FirstPass36.polyHighProb_inter (hHρ Ω S hSv) (hSρ Ω S hSv))
      (hpath γ hγ hγ2 ρ hρ0 hρ1 Ω S hSv)) hDE
  have hae : ∀ᵐ ω ∂S.P, Continuous (S.η ω) ∧
      Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
      ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
        (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty := by
    filter_upwards [TraceInputs68.ae_continuous_eta hSv, hSv.ae_tendsto_cocompact,
      TraceInputs68.ae_adjacent hγ hγ2 S hSv] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine S3cBridge.polyHighProb_mono_ae_small (r₁ := min (min r₁ r₂) 1)
    (lt_min (lt_min hr₁ hr₂) one_pos) hE hae ?_
  intro r hr hrR ω hω hq'
  obtain ⟨⟨⟨hHω, hSω⟩, hPω⟩, hDω⟩ := hω
  obtain ⟨hη, hp, hmeet⟩ := hq'
  have hr1 : r < 1 := lt_of_lt_of_le hrR (min_le_right _ _)
  have hrr₁ : r < r₁ := lt_of_lt_of_le hrR ((min_le_left _ _).trans (min_le_left _ _))
  have hrr₂ : r < r₂ := lt_of_lt_of_le hrR ((min_le_left _ _).trans (min_le_right _ _))
  have hfin : (cellVertices r (S.η ω) (ball 0 ((1 + ρ) / 2))).Finite :=
    (cellVertices_finite_of_isCompact hη hp hr (isCompact_closedBall 0 ((1 + ρ) / 2))).subset
      fun k ⟨z, hzk, hz⟩ => ⟨z, hzk, ball_subset_closedBall hz⟩
  have hmin1 : r ^ β₁ ≤ r ^ (min β₁ β₂) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1.le (min_le_left _ _)
  have hmin2 : r ^ β₂ ≤ r ^ (min β₁ β₂) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1.le (min_le_right _ _)
  have hr₀ : r ^ (min β₁ β₂) ≤ (1 - ρ) / 8 / 2 := hr₁h r hr hrr₁
  have hdc : r ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2) ≤ (1 - ρ) / 8 / 4 := hr₂h r hr hrr₂
  have hlf := isLocallyFiniteMult_of_cells_meet hη hp hr (hmeet r hr)
  have key := greenKernel_interiorCellVertices_le_log_of_harnack_of_cellSum (m := S.mult r ω)
    (η := S.η ω) (ε := r) (ρ := ρ) (ρ₀ := (1 + ρ) / 2) (δ₀ := (1 - ρ) / 8)
    (dc := r ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2)) (r₀ := r ^ (min β₁ β₂)) (C₁ := C₁) (C₂ := C₂)
    hη hr hlf (S.mult_succ_ne_zero hr.le ω) (S.mult_symm r ω)
    (fun j k h => by rw [inter_comm]; exact hmeet r hr k j h) hfin (by linarith) (by linarith)
    hδ₀ hδ₀1 (by linarith) (Real.rpow_pos_of_pos hr _) (by linarith) hC₁.le hC₂.le
    (fun k hk => (hDω k hk).2)
    (fun b hb s hs1 hs2 a ha y hy => hHω b hb s (hmin1.trans hs1) hs2 a ha y hy) hPω
    (fun b hb s hs1 hs2 => by
      refine hSω b hb s (hmin2.trans hs1) hs2 _ ?_
      intro k hk
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hk
      exact hk)
  simp only [Set.mem_ofPred_eq]
  intro a ha b hb hab
  exact key a ha b hb hab

end MatedCRT
