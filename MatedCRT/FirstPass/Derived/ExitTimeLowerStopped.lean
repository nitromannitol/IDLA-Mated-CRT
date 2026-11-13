import MatedCRT.FirstPass.Derived.ExitTimeLowerLemma611Strong
import MatedCRT.FirstPass.Derived.MepsUpperCellSize
import MatedCRT.FirstPass.Derived.MepsUpperDeterministic
import MatedCRT.FirstPass.Derived.CellInballDisjoint

/-!
# Exit-time lower bound from the interior vertices of the half disc (Berestycki–Gwynne (2020), Lemma 6.11)

`exitTimeLowerStopped_half`: for `κ, θ > 0` there is `s > 0` such that, for every valid environment and all small
`q`, outside an event of probability at most `θ`, every vertex `x` whose embedded point lies in `B_{1/4}` satisfies
`P_x[τ_{I^q(B_{1/2})} < s / q] ≤ κ`, where `I^q(B_{1/2}) = V^q(B_{1/2}) \ V^q(∂B_{1/2})` are the interior vertices.

Proof. Lemma 6.11 in its strong form (`exitTimeLowerTail_611_strong`) with `ρ = 1/2` gives the bound
`P_x[τ_{B_δ(η(x))} < q⁻¹ δ^χ] ≤ ψ(δ)` for `x ∈ V^q(B_{1/2 - δ})`.  Fix `δ < 1/8` with `ψ(δ) ≤ κ` and put
`s = δ^χ`.  On the event that every cell meeting `B_{5/8}` has diameter `< 1/8`, for `x` with `‖η(x)‖ < 1/4` the
vertices of `V^q(B_δ(η(x)))` are interior vertices of `B_{1/2}`: their cells lie in `B_{1/4 + δ + 1/8} ⊂ B_{1/2}`.
Hence `τ_{I^q(B_{1/2})} ≥ τ_{V^q(B_δ(η(x)))}`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set Metric LatticeProb.Gauss
open scoped ENNReal

/-- **Exit-time lower bound from the interior vertices of `B_{1/2}`** (BG20 Lemma 6.11, uniform in the
environment): for `0 < γ < 2` and `κ, θ > 0` there is `s > 0` such that for every valid environment and all small
`q > 0`, with probability at least `1 - θ`, every vertex `x` with `η(q x) ∈ B_{1/4}` has
`P_x[τ_{I^q(B_{1/2})} < s q⁻¹] ≤ κ`. Inputs: the Green kernel lower bound `h213` (Lemma 2.13), the exit time
moment bound `h214` (Lemma 2.14) and the estimate (6.32) of BG20 Lemma 6.9, `h632`, in its printed form. -/
theorem exitTimeLowerStopped_half {𝒮 : SpaceFillingSLEModel}
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h632 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ ℓ : ℝ, 1 < ℓ →
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
                ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ y} ≤ ENNReal.ofReal (ψ₀ δ)}ᶜ ≤ ENNReal.ofReal θ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ → ∃ s : ℝ, 0 < s ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ q₀ : ℝ, 0 < q₀ ∧ ∀ q : ℝ, 0 < q → q < q₀ →
          S.P {ω | ∃ x : ℤ, vertexPoint q (S.η ω) x ∈ ball (0 : ℂ) (1 / 4) ∧
            ENNReal.ofReal κ < srwLaw (S.mult q ω) x
              {y | (vExitTime (interiorCellVertices q (S.η ω) (ball 0 (1 / 2))) y : ℝ≥0∞) <
                ENNReal.ofReal (q⁻¹ * s)}} ≤ ENNReal.ofReal θ := by
  classical
  intro γ hγ hγ2 κ hκ θ hθ
  have h2γ : 0 < 2 - γ := by linarith
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ, χ = 2 * (2 + γ) / (2 - γ) + 1 := ⟨_, rfl⟩
  have hχlt : 2 * (2 + γ) / (2 - γ) < χ := by rw [hχ]; linarith
  obtain ⟨ψ, ⟨-, -, hψt⟩, h611⟩ := exitTimeLowerTail_611_strong h213 h214 hγ hγ2 hχlt
    (ρ := 1 / 2) (by norm_num) (by norm_num) (h632 γ hγ hγ2 (1 / 2) (by norm_num) (by norm_num))
  obtain ⟨δ₀, hδ₀, h611δ⟩ := h611 (θ / 2) (by positivity)
  obtain ⟨δ₁, hδ₁, hψδ₁⟩ := LatticeProb.LQG.LQGMeasureNonatomicMass.exists_pos_of_eventually_nhdsGT
    ((hψt 1 one_pos).eventually (gt_mem_nhds one_pos))
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (min δ₁ κ) (min δ₀ (1 / 8)) / 2 := ⟨_, rfl⟩
  have hm0 : 0 < min (min δ₁ κ) (min δ₀ (1 / 8)) :=
    lt_min (lt_min hδ₁ hκ) (lt_min hδ₀ (by norm_num))
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδm : δ < min (min δ₁ κ) (min δ₀ (1 / 8)) := by rw [hδ]; linarith
  have hδδ₁ : δ < δ₁ := hδm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδκ : δ < κ := hδm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδδ₀ : δ < δ₀ := hδm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ8 : δ < 1 / 8 := hδm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hψδ : ψ δ < δ := by
    have h := hψδ₁ δ hδ0 hδδ₁
    rwa [Real.rpow_neg_one, inv_mul_lt_iff₀ hδ0, mul_one] at h
  have hχδ : 0 < δ ^ χ := Real.rpow_pos_of_pos hδ0 χ
  refine ⟨δ ^ χ, hχδ, fun Ω _ S hS => ?_⟩
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨ε₁, hε₁, h611ε⟩ := h611δ δ hδ0 hδδ₀ Ω S hS
  have hT2 := cellDiam_bad_tendsto_zero_of_cellSizeEstimate (cellSizeEstimateStmt_holds 𝒮) hγ hγ2 S hS
  have hθ2 : (0 : ℝ≥0∞) < ENNReal.ofReal (θ / 2) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨ε₂, hε₂, hsub2⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hT2.eventually (gt_mem_nhds hθ2))
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun q hq hqε₀ => ?_⟩
  have hE1 := h611ε q hq (hqε₀.trans_le (min_le_left _ _))
  have hE2 : S.P {ω | ∃ k : ℤ, (cell q (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty ∧
      1 / 8 ≤ diam (cell q (S.η ω) k)} < ENNReal.ofReal (θ / 2) :=
    hsub2 ⟨hq, hqε₀.trans_le (min_le_right _ _)⟩
  have hpar0 : S.P {ω | ¬ IsAreaParametrized (S.μ ω) (S.η ω)} = 0 :=
    ae_iff.1 hS.isAreaParametrized
  have hcov : {ω | ∃ x : ℤ, vertexPoint q (S.η ω) x ∈ ball (0 : ℂ) (1 / 4) ∧
      ENNReal.ofReal κ < srwLaw (S.mult q ω) x
        {y | (vExitTime (interiorCellVertices q (S.η ω) (ball 0 (1 / 2))) y : ℝ≥0∞) <
          ENNReal.ofReal (q⁻¹ * δ ^ χ)}} ⊆
      ({ω | ∀ x ∈ cellVertices q (S.η ω) (ball 0 (1 / 2 - δ)),
        srwLaw (S.mult q ω) x {y |
          (vExitTime (cellVertices q (S.η ω) (ball (vertexPoint q (S.η ω) x) δ)) y : ℝ≥0∞) <
            ENNReal.ofReal (q⁻¹ * δ ^ χ)} ≤ ENNReal.ofReal (ψ δ)}ᶜ ∪
        {ω | ∃ k : ℤ, (cell q (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty ∧
          1 / 8 ≤ diam (cell q (S.η ω) k)}) ∪ {ω | ¬ IsAreaParametrized (S.μ ω) (S.η ω)} := by
    intro ω hω
    obtain ⟨x, hx, hκx⟩ := hω
    by_contra hn
    have h1 : ∀ x ∈ cellVertices q (S.η ω) (ball 0 (1 / 2 - δ)),
        srwLaw (S.mult q ω) x {y |
          (vExitTime (cellVertices q (S.η ω) (ball (vertexPoint q (S.η ω) x) δ)) y : ℝ≥0∞) <
            ENNReal.ofReal (q⁻¹ * δ ^ χ)} ≤ ENNReal.ofReal (ψ δ) :=
      not_not.1 fun h => hn (Or.inl (Or.inl h))
    have hd : ∀ k : ℤ, (cell q (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty →
        diam (cell q (S.η ω) k) < 1 / 8 :=
      fun k hk => lt_of_not_ge fun h => hn (Or.inl (Or.inr ⟨k, hk, h⟩))
    have hpar : IsAreaParametrized (S.μ ω) (S.η ω) := not_not.1 fun h => hn (Or.inr h)
    have hcont : Continuous (S.η ω) := hpar.1
    have hxn : ‖vertexPoint q (S.η ω) x‖ < 1 / 4 := mem_ball_zero_iff.1 hx
    have hxV : x ∈ cellVertices q (S.η ω) (ball 0 (1 / 2 - δ)) :=
      ⟨vertexPoint q (S.η ω) x, Lemma68C12Geom.vertexPoint_mem_cell hq.le x,
        mem_ball_zero_iff.2 (by linarith)⟩
    have hincl : cellVertices q (S.η ω) (ball (vertexPoint q (S.η ω) x) δ) ⊆
        interiorCellVertices q (S.η ω) (ball 0 (1 / 2)) := by
      rintro y ⟨w, hwc, hwb⟩
      have hw1 : dist w (vertexPoint q (S.η ω) x) < δ := hwb
      have hw2 := dist_triangle w (vertexPoint q (S.η ω) x) 0
      rw [dist_zero_right, dist_zero_right] at hw2
      have hwn : ‖w‖ < 1 / 2 := by linarith
      have hdy := hd y ⟨w, hwc, mem_ball_zero_iff.2 (by linarith)⟩
      refine Set.mem_sdiff_of_mem ⟨w, hwc, mem_ball_zero_iff.2 hwn⟩ ?_
      rintro ⟨z, hzc, hzf⟩
      rw [frontier_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0), mem_sphere_zero_iff_norm] at hzf
      have hz1 := Metric.dist_le_diam_of_mem (isBounded_cell hcont y) hzc hwc
      have hz2 := dist_triangle z w 0
      rw [dist_zero_right, dist_zero_right] at hz2
      linarith
    have hsub : {y | (vExitTime (interiorCellVertices q (S.η ω) (ball 0 (1 / 2))) y : ℝ≥0∞) <
          ENNReal.ofReal (q⁻¹ * δ ^ χ)} ⊆
        {y | (vExitTime (cellVertices q (S.η ω) (ball (vertexPoint q (S.η ω) x) δ)) y : ℝ≥0∞) <
          ENNReal.ofReal (q⁻¹ * δ ^ χ)} :=
      fun y hy => lt_of_le_of_lt
        (ENat.toENNReal_le.2 (FiniteExitMomentHone68.vExitTime_mono_set hincl y)) hy
    have hle := (measure_mono hsub).trans
      ((h1 x hxV).trans (ENNReal.ofReal_le_ofReal (by linarith : ψ δ ≤ κ)))
    exact absurd hκx (not_lt.2 hle)
  calc S.P _ ≤ _ := measure_mono hcov
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) + 0 :=
        add_le_add (add_le_add hE1 hE2.le) hpar0.le
    _ = ENNReal.ofReal θ := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end MatedCRT.FirstPass.Derived
