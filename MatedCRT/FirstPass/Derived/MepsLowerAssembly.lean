import MatedCRT.FirstPass.Derived.ExitTimeLowerLemma611Strong
import MatedCRT.FirstPass.Derived.MepsUpperCellSize
import MatedCRT.FirstPass.Derived.MepsUpperDeterministic
import MatedCRT.FirstPass.Derived.MepsScalingOfCdfBounds
import MatedCRT.FirstPass.Derived.CellInballDisjoint

/-!
# Lower bound for the annealed exit-time distribution function `F_ε` (lower half of BG20 (1.8))

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), (1.8): `C⁻¹ ε⁻¹ ≤ m_ε ≤ C ε⁻¹`. This file proves the lower half in the form used by
`mepsScalingInput_of_cdf_bounds`: for `0 < γ < 2` there is `c₁ > 0`, independent of the environment, such that for
every valid environment `F_ε(c₁ ε⁻¹) < 1/2` for all small `ε`, where `F_ε` is the annealed distribution function of
the exit time of the embedded walk from `B_{1/2}` (`MatedCRTEnv.mεCdf`).

Proof. Apply Lemma 6.11 in its strong form (`exitTimeLowerTail_611_strong`) with `ρ = 1/4` and tolerance `1/8`,
and fix one `δ < 1/16` with `ψ(δ) ≤ δ` (possible since `ψ` is superpolynomial); put `c₁ = δ^χ/2`. On the event of
Lemma 6.11, intersected with the event that every cell meeting `B_{5/8}` has diameter `< 1/8`, the root vertex
`a^ε_0` lies in `V^ε(B_{1/4 - δ})` (its cell contains `0`), and every vertex of `V^ε(B_δ(η(a^ε_0)))` has its point
in `B_{1/2}`. Hence the exit time from `B_{1/2}` is at least `τ_{B_δ(η(a^ε_0))}`, and
`P[τ_{B_{1/2}} ≤ c₁ ε⁻¹] ≤ P[τ_{B_δ} < ε⁻¹ δ^χ] ≤ ψ(δ) ≤ 1/8`. The two bad events have probability at most `1/8`
each for small `ε`, so `F_ε(c₁ ε⁻¹) ≤ 3/8 < 1/2`.

The only input beyond the Green kernel lower bound (Lemma 2.13) and the exit time moment bound (Lemma 2.14) is
`h632`, the estimate (6.32), the conclusion of BG20 Lemma 6.9, in its printed form (superpolynomial function
depending only on `ζ`, `ℓ`, `γ` and the radius `ρ`).
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set Metric LatticeProb.Gauss
open scoped ENNReal

/-- **Lower half of BG20 (1.8)** (arXiv:2003.10320, p. 4): for `0 < γ < 2` there is `c₁ > 0` such that for every
valid environment `F_ε(c₁ ε⁻¹) < 1/2` for all sufficiently small `ε > 0`. Inputs: the Green kernel lower bound
`h213` (Lemma 2.13), the exit time moment bound `h214` (Lemma 2.14) and the estimate (6.32) of BG20 Lemma 6.9,
`h632`, in its printed form: for `ρ ∈ (0, 1)`, `ℓ > 1` and `ζ ∈ (0, 1)` there is a superpolynomial `ψ₀`, depending
only on `ζ`, `ℓ`, `γ`, `ρ`, such that for every valid environment and `δ ∈ (0, 1)`, with probability tending to `1`
as `ε → 0`, `P_x[τ_{B_δ(η(x))} < σ_K] ≤ ψ₀(δ)` for every `x ∈ V^ε(B_{ρ - δ})`, where `K = ⌊δ^{-(2-ζ)(ℓ-1)}⌋` and
`σ_k` are the successive exit times from the sets `V^ε(B_{δ^ℓ}(η(X_{σ_{k-1}})))`. -/
theorem mεCdf_lower_of_exitTimeLowerTail {𝒮 : SpaceFillingSLEModel}
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
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2 := by
  classical
  intro γ hγ hγ2
  have h2γ : 0 < 2 - γ := by linarith
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ, χ = 2 * (2 + γ) / (2 - γ) + 1 := ⟨_, rfl⟩
  have hχlt : 2 * (2 + γ) / (2 - γ) < χ := by rw [hχ]; linarith
  obtain ⟨ψ, ⟨-, -, hψt⟩, h611⟩ := exitTimeLowerTail_611_strong h213 h214 hγ hγ2 hχlt
    (ρ := 1 / 4) (by norm_num) (by norm_num) (h632 γ hγ hγ2 (1 / 4) (by norm_num) (by norm_num))
  obtain ⟨δ₀, hδ₀, h611δ⟩ := h611 (1 / 8) (by norm_num)
  -- the scale `δ`: `δ < δ₀`, `δ < 1/16` and `ψ(δ) < δ`
  obtain ⟨δ₁, hδ₁, hψδ₁⟩ := LatticeProb.LQG.LQGMeasureNonatomicMass.exists_pos_of_eventually_nhdsGT
    ((hψt 1 one_pos).eventually (gt_mem_nhds one_pos))
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min δ₁ (min δ₀ (1 / 16)) / 2 := ⟨_, rfl⟩
  have hm0 : 0 < min δ₁ (min δ₀ (1 / 16)) := lt_min hδ₁ (lt_min hδ₀ (by norm_num))
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδm : δ < min δ₁ (min δ₀ (1 / 16)) := by rw [hδ]; linarith
  have hδδ₁ : δ < δ₁ := hδm.trans_le (min_le_left _ _)
  have hδδ₀ : δ < δ₀ := hδm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ16 : δ < 1 / 16 := hδm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hψδ : ψ δ < δ := by
    have h := hψδ₁ δ hδ0 hδδ₁
    rwa [Real.rpow_neg_one, inv_mul_lt_iff₀ hδ0, mul_one] at h
  have hχδ : 0 < δ ^ χ := Real.rpow_pos_of_pos hδ0 χ
  refine ⟨δ ^ χ / 2, by positivity, fun Ω _ S hS => ?_⟩
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  -- the thresholds in `ε`
  obtain ⟨ε₁, hε₁, h611ε⟩ := h611δ δ hδ0 hδδ₀ Ω S hS
  have hT2 := cellDiam_bad_tendsto_zero_of_cellSizeEstimate (cellSizeEstimateStmt_holds 𝒮) hγ hγ2 S hS
  have h8 : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 8) := by simp
  obtain ⟨ε₂, hε₂, hsub2⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hT2.eventually (gt_mem_nhds h8))
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hεε₀ => ?_⟩
  have hE1 := h611ε ε hε (hεε₀.trans_le (min_le_left _ _))
  have hE2 : S.P {ω | ∃ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty ∧
      1 / 8 ≤ diam (cell ε (S.η ω) k)} < ENNReal.ofReal (1 / 8) :=
    hsub2 ⟨hε, hεε₀.trans_le (min_le_right _ _)⟩
  -- the good event
  set G : Set Ω := {ω | (∀ x ∈ cellVertices ε (S.η ω) (ball 0 (1 / 4 - δ)),
      srwLaw (S.mult ε ω) x {y |
        (vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y : ℝ≥0∞) <
          ENNReal.ofReal (ε⁻¹ * δ ^ χ)} ≤ ENNReal.ofReal (ψ δ)) ∧
    (∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty → diam (cell ε (S.η ω) k) < 1 / 8) ∧
    IsAreaParametrized (S.μ ω) (S.η ω)} with hG
  -- the integrand is at most `1/8` on `G`
  have hpt : ∀ ω ∈ G, srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0)
      {x | (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ χ / 2 * ε⁻¹)} ≤
        ENNReal.ofReal (1 / 8) := by
    intro ω ⟨h611ω, hd, hpar⟩
    have hcont : Continuous (S.η ω) := hpar.1
    have h0c : (0 : ℂ) ∈ cell ε (S.η ω) (vertexOf ε (S.η ω) 0) := zero_mem_cell_vertexOf hε.le hpar.2.1
    have hx₀ : vertexOf ε (S.η ω) 0 ∈ cellVertices ε (S.η ω) (ball 0 (1 / 4 - δ)) :=
      ⟨0, h0c, mem_ball_self (by linarith)⟩
    have hp : ‖vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) 0)‖ < 1 / 8 := by
      have h1 := Metric.dist_le_diam_of_mem (isBounded_cell hcont _)
        (Lemma68C12Geom.vertexPoint_mem_cell hε.le (vertexOf ε (S.η ω) 0)) h0c
      have h2 := hd _ ⟨0, h0c, mem_ball_self (by norm_num)⟩
      rw [dist_zero_right] at h1
      linarith
    -- every vertex of `V^ε(B_δ(η(a^ε_0)))` has its point in `B_{1/2}`
    have hincl : cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) 0)) δ) ⊆
        {k | vertexPoint ε (S.η ω) k ∈ ball 0 (1 / 2)} := by
      rintro y ⟨w, hwc, hwb⟩
      have hw1 : dist w (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) 0)) < δ := hwb
      have hw2 := dist_triangle w (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) 0)) 0
      rw [dist_zero_right, dist_zero_right] at hw2
      have hdy := hd y ⟨w, hwc, mem_ball_zero_iff.2 (by linarith)⟩
      have hy1 := Metric.dist_le_diam_of_mem (isBounded_cell hcont y)
        (Lemma68C12Geom.vertexPoint_mem_cell hε.le y) hwc
      have hy2 := dist_triangle (vertexPoint ε (S.η ω) y) w 0
      rw [dist_zero_right, dist_zero_right] at hy2
      show vertexPoint ε (S.η ω) y ∈ ball 0 (1 / 2)
      rw [mem_ball_zero_iff]
      linarith
    have hlt : ENNReal.ofReal (δ ^ χ / 2 * ε⁻¹) < ENNReal.ofReal (ε⁻¹ * δ ^ χ) := by
      have hpos : 0 < δ ^ χ * ε⁻¹ := mul_pos hχδ (inv_pos.2 hε)
      refine (ENNReal.ofReal_lt_ofReal_iff (by rw [mul_comm]; exact hpos)).2 ?_
      have e1 : δ ^ χ / 2 * ε⁻¹ = δ ^ χ * ε⁻¹ / 2 := by ring
      have e2 : ε⁻¹ * δ ^ χ = δ ^ χ * ε⁻¹ := mul_comm _ _
      rw [e1, e2]
      linarith
    have hsub : {x : ℕ → ℤ | (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞) ≤
        ENNReal.ofReal (δ ^ χ / 2 * ε⁻¹)} ⊆ {y |
          (vExitTime (cellVertices ε (S.η ω)
            (ball (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) 0)) δ)) y : ℝ≥0∞) <
          ENNReal.ofReal (ε⁻¹ * δ ^ χ)} := by
      intro x hx
      have h1 : vExitTime (cellVertices ε (S.η ω)
          (ball (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) 0)) δ)) x ≤
          embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x :=
        FiniteExitMomentHone68.vExitTime_mono_set hincl x
      exact lt_of_le_of_lt ((ENat.toENNReal_le.2 h1).trans hx) hlt
    refine (measure_mono hsub).trans ((h611ω _ hx₀).trans (ENNReal.ofReal_le_ofReal ?_))
    linarith
  -- the bad event is small
  have hGc : S.P Gᶜ ≤ ENNReal.ofReal (1 / 4) := by
    have hpar0 : S.P {ω | ¬ IsAreaParametrized (S.μ ω) (S.η ω)} = 0 :=
      ae_iff.1 hS.isAreaParametrized
    have hcov : Gᶜ ⊆ ({ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (1 / 4 - δ)),
        srwLaw (S.mult ε ω) x {y |
          (vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y : ℝ≥0∞) <
            ENNReal.ofReal (ε⁻¹ * δ ^ χ)} ≤ ENNReal.ofReal (ψ δ)}ᶜ ∪
        {ω | ∃ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty ∧
          1 / 8 ≤ diam (cell ε (S.η ω) k)}) ∪ {ω | ¬ IsAreaParametrized (S.μ ω) (S.η ω)} := by
      intro ω hω
      by_contra hn
      apply hω
      exact ⟨not_not.1 fun h => hn (Or.inl (Or.inl h)),
        fun k hk => lt_of_not_ge fun h => hn (Or.inl (Or.inr ⟨k, hk, h⟩)),
        not_not.1 fun h => hn (Or.inr h)⟩
    calc S.P Gᶜ ≤ _ := measure_mono hcov
      _ ≤ _ := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) + 0 :=
          add_le_add (add_le_add hE1 hE2.le) hpar0.le
      _ = ENNReal.ofReal (1 / 4) := by
          rw [add_zero, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  -- integrate
  have h12 : ENNReal.ofReal (1 / 2) = 1 / 2 := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  calc S.mεCdf ε (δ ^ χ / 2 * ε⁻¹)
      ≤ ∫⁻ ω, ((toMeasurable S.P Gᶜ).indicator 1 ω + ENNReal.ofReal (1 / 8)) ∂S.P := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ toMeasurable S.P Gᶜ
        · rw [indicator_of_mem hω, Pi.one_apply]
          exact prob_le_one.trans le_self_add
        · rw [indicator_of_notMem hω, zero_add]
          exact hpt ω (not_not.1 fun h => hω (subset_toMeasurable _ _ h))
    _ = S.P Gᶜ + ENNReal.ofReal (1 / 8) := by
        rw [lintegral_add_right _ measurable_const, lintegral_indicator_one
          (measurableSet_toMeasurable _ _), lintegral_const, measure_univ, mul_one,
          measure_toMeasurable]
    _ ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 8) := add_le_add hGc le_rfl
    _ < 1 / 2 := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← h12]
        exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

end MatedCRT.FirstPass.Derived
