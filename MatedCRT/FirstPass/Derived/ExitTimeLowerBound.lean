import MatedCRT.FirstPass.Derived.ExitTimeLowerOfGreen
import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd
import MatedCRT.FirstPass.S3i.GoodEvent
import MatedCRT.FirstPass.S6n

/-!
# Lower bound for the expected exit time from the Green kernel lower bound (BG20 Proposition 4.1)

Proposition 4.1 of Berestycki-Gwynne (arXiv 2003.10320, p. 20) says that, with polynomially high
probability as `ε → 0`, for every vertex `a` with cell meeting `B_{ρ - ε^{ω₁}}` and every radius
`r ∈ [ε^{ω₁}, dist(η(a), ∂B_ρ)]`,
  `ε⁻¹ μ_h(B_{cr}(η(a))) ≤ E^a[τ_A]`,  `A = V^ε(B_r(η(a))) \ V^ε(∂B_r(η(a)))`,
with `ω₁ = ω₁(γ) > 0` and `c = c(ρ, γ) ∈ (0, 1/3]`. The source derives it from the Green kernel lower
bound (Lemma 4.4, `GreenKernelLowerBoundStmt`): `E^a[τ_A] = ∑_{b ∈ A} g_A(a, b)`, and
`g_A(a, b) ≥ 1` for the vertices `b` whose cells meet `B_{cr}(η(a))`; their number is at least
`ε⁻¹ μ_h(B_{cr}(η(a)))` since the cells have `μ_h`-mass `ε` and cover the plane.

The printed argument ((4.19)-(4.20)) uses `|η(a) - η(b)| ≤ cr` for every such `b`, while the cell of
`b` only meets `B_{cr}(η(a))`; it also needs those `b` inside `A`. Both follow from the cell-size
estimate (Lemma 2.8, `cellSizeEstimateStmt_holds`, `diam H^ε_b ≤ ε^β` for cells meeting `B_ρ`,
`β = 1/(2+γ)²`) once `ω₁ ≤ β/2` and `c` is halved: every point of the cell of `b` lies within
`ε^β + cr ≤ 2cr` of `η(a)`.

## Main result

* `exitTimeLowerBound_of_greenLower`: BG20 Proposition 4.1 from `GreenKernelLowerBoundStmt`, with
  `ω₁ = min(ω₀, β/2)` and `c = min(e^{-2C}, 1/3)/2`.
-/

open MeasureTheory Metric Set HarmonicBalls
open scoped ENNReal

namespace MatedCRT.ExitTimeLowerBound

/-- Polynomially high probability is preserved by intersecting with an almost sure event and by
shrinking the range of the parameter to `(0, r₁)`. -/
theorem polyHighProb_of_ae_of_small {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E F : ℝ → Set Ω} {G : Set Ω} (h : PolyHighProb P E) (hG : ∀ᵐ ω ∂P, ω ∈ G) {r₁ : ℝ}
    (hr₁ : 0 < r₁) (hEF : ∀ r : ℝ, 0 < r → r < r₁ → E r ∩ G ⊆ F r) : PolyHighProb P F := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨p, hp, C, min r₀ r₁, lt_min hr₀ hr₁, fun r hr hrr => ?_⟩
  have hsub : (F r)ᶜ ⊆ (E r)ᶜ ∪ {ω | ω ∉ G} := by
    intro ω hω
    by_cases hE' : ω ∈ E r
    · by_cases hG' : ω ∈ G
      · exact absurd (hEF r hr (lt_of_lt_of_le hrr (min_le_right _ _)) ⟨hE', hG'⟩) hω
      · exact Or.inr hG'
    · exact Or.inl hE'
  calc P (F r)ᶜ ≤ P ((E r)ᶜ ∪ {ω | ω ∉ G}) := measure_mono hsub
    _ ≤ P (E r)ᶜ + P {ω | ω ∉ G} := measure_union_le _ _
    _ = P (E r)ᶜ := by rw [ae_iff.1 hG, add_zero]
    _ ≤ _ := hE r hr (lt_of_lt_of_le hrr (min_le_left _ _))

/-- A set whose diameter is bounded below by a positive number is bounded, so its points are within
any upper bound for the diameter of each other. -/
theorem dist_le_of_diam_le {s : Set ℂ} {t u : ℝ} (ht : 0 < t) (hlo : t ≤ diam s)
    (hup : diam s ≤ u) {w w' : ℂ} (hw : w ∈ s) (hw' : w' ∈ s) : dist w w' ≤ u := by
  have hb : Bornology.IsBounded s := by
    by_contra hnb
    have := Metric.diam_eq_zero_of_unbounded hnb
    linarith
  exact (Metric.dist_le_diam_of_mem hb hw hw').trans hup

/-- In `ℂ`, a point `x` of the closed disk `|x| ≤ ρ` is within `ρ - |x|` of the circle `∂B_ρ` (the
radial point `ρ x/|x|`, or `ρ` when `x = 0`). -/
theorem infDist_sphere_zero_le {x : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hx : ‖x‖ ≤ ρ) :
    infDist x (sphere 0 ρ) ≤ ρ - ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | h0
  · have hw : ((ρ : ℝ) : ℂ) ∈ sphere (0 : ℂ) ρ := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hρ]
    calc infDist 0 (sphere 0 ρ) ≤ dist (0 : ℂ) (ρ : ℂ) := infDist_le_dist_of_mem hw
      _ = ρ - ‖(0 : ℂ)‖ := by
        rw [dist_comm, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hρ, norm_zero,
          sub_zero]
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.2 h0
    have hw : ((ρ / ‖x‖ : ℝ) : ℂ) * x ∈ sphere (0 : ℂ) ρ := by
      rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (div_nonneg hρ hxpos.le), div_mul_cancel₀ _ hxpos.ne']
    have hneg : 1 - ρ / ‖x‖ ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hxpos, one_mul]
      exact hx
    calc infDist x (sphere 0 ρ) ≤ dist x (((ρ / ‖x‖ : ℝ) : ℂ) * x) := infDist_le_dist_of_mem hw
      _ = ρ - ‖x‖ := by
        rw [dist_eq_norm, show x - ((ρ / ‖x‖ : ℝ) : ℂ) * x = ((1 - ρ / ‖x‖ : ℝ) : ℂ) * x by
          push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hneg,
          neg_sub, sub_mul, div_mul_cancel₀ _ hxpos.ne', one_mul]

/-- `ε ≤ e^{-2C}` gives `e^{2C} ≤ ε⁻¹`. -/
theorem exp_le_inv_of_le_exp_neg {C ε : ℝ} (hε : 0 < ε) (hεC : ε ≤ Real.exp (-(2 * C))) :
    Real.exp (2 * C) ≤ ε⁻¹ := by
  have := inv_anti₀ hε hεC
  rwa [Real.exp_neg, inv_inv] at this

/-- The logarithmic term of the Green kernel lower bound at distinct points: if `|x - y| < c₀ r`
with `c₀ ≤ e^{-2C}` and `e^{2C} ≤ ε⁻¹`, then `e^{2C} ≤ (r/|x - y|) ∧ ε⁻¹`. -/
theorem exp_le_min_div_norm {C ε r c₀ : ℝ} {x y : ℂ} (hxy0 : x ≠ y)
    (hεinv : Real.exp (2 * C) ≤ ε⁻¹) (hr : 0 < r) (hc₀C : c₀ ≤ Real.exp (-(2 * C)))
    (hxy : ‖x - y‖ < c₀ * r) : Real.exp (2 * C) ≤ min (r / ‖x - y‖) ε⁻¹ := by
  refine le_min ?_ hεinv
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy0)
  rw [le_div_iff₀ hpos]
  have hec : Real.exp (2 * C) * c₀ ≤ 1 := by
    calc Real.exp (2 * C) * c₀ ≤ Real.exp (2 * C) * Real.exp (-(2 * C)) :=
          mul_le_mul_of_nonneg_left hc₀C (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc Real.exp (2 * C) * ‖x - y‖ ≤ Real.exp (2 * C) * (c₀ * r) :=
        mul_le_mul_of_nonneg_left hxy.le (Real.exp_pos _).le
    _ = (Real.exp (2 * C) * c₀) * r := by ring
    _ ≤ 1 * r := mul_le_mul_of_nonneg_right hec hr.le
    _ = r := one_mul r

/-- If `X ≥ e^{2C}` with `C > 0`, then `C⁻¹ log X - 1 ≥ 1`. -/
theorem one_le_inv_mul_log_sub_one {C X : ℝ} (hC : 0 < C) (hX : Real.exp (2 * C) ≤ X) :
    1 ≤ C⁻¹ * Real.log X - 1 := by
  have hlog : 2 * C ≤ Real.log X :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hX)).2 hX
  have h2 : C⁻¹ * (2 * C) = 2 := by
    rw [mul_comm 2 C, ← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  have := mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hC.le)
  linarith

/-- **BG20 Proposition 4.1 from the Green kernel lower bound (Lemma 4.4).** There is `ω₁ = ω₁(γ) > 0`
and, for each `ρ ∈ (0,1)`, a `c = c(ρ, γ) ∈ (0, 1/3]` such that with polynomially high probability
as `ε → 0`: for every `a ∈ V^ε(B_{ρ - ε^{ω₁}})` and `r ∈ [ε^{ω₁}, dist(η(a), ∂B_ρ)]`,
`ε⁻¹ μ_h(B_{cr}(η(a))) ≤ E^a[τ_A]` with `A = V^ε(B_r(η(a))) \ V^ε(∂B_r(η(a)))`. -/
theorem exitTimeLowerBound_of_greenLower {𝒮 : SpaceFillingSLEModel}
    (h213 : GreenKernelLowerBoundStmt 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ω₁ : ℝ, 0 < ω₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ c : ℝ, 0 < c ∧
      c ≤ 1 / 3 ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₁)), ∀ r : ℝ,
        ε ^ ω₁ ≤ r → r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ENNReal.ofReal ε⁻¹ * S.μ ω (ball (vertexPoint ε (S.η ω) a) (c * r)) ≤
          expectedExitTime (S.mult ε ω)
            (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a} := by
  intro γ hγ hγ2
  obtain ⟨ω₀, hω₀, h⟩ := h213 γ hγ hγ2
  set β : ℝ := 1 / (2 + γ) ^ 2 with hβ
  have hβpos : 0 < β := by positivity
  have hβ1 : β < 1 := by
    rw [hβ, div_lt_one (by positivity)]
    nlinarith
  have hexp : 2 / (2 + γ) ^ 2 - β = β := by rw [hβ]; ring
  set ω₁ : ℝ := min ω₀ (β / 2) with hω₁
  have hω₁ω₀ : ω₁ ≤ ω₀ := min_le_left _ _
  have hω₁β : ω₁ ≤ β / 2 := min_le_right _ _
  refine ⟨ω₁, lt_min hω₀ (half_pos hβpos), fun ρ hρ hρ1 => ?_⟩
  obtain ⟨C, hC, h'⟩ := h ρ hρ hρ1
  set c₀ : ℝ := min (Real.exp (-(2 * C))) (1 / 3) with hc₀
  have hc₀pos : 0 < c₀ := lt_min (Real.exp_pos _) (by norm_num)
  have hc₀C : c₀ ≤ Real.exp (-(2 * C)) := min_le_left _ _
  have hc₀3 : c₀ ≤ 1 / 3 := min_le_right _ _
  refine ⟨c₀ / 2, half_pos hc₀pos, by linarith, fun Ω _ S hS => ?_⟩
  set ε₁ : ℝ := min 1 (min (Real.exp (-(2 * C))) ((c₀ / 2) ^ (2 / β))) with hε₁
  have hε₁pos : 0 < ε₁ :=
    lt_min one_pos (lt_min (Real.exp_pos _) (Real.rpow_pos_of_pos (half_pos hc₀pos) _))
  refine polyHighProb_of_ae_of_small (G := {ω | IsAreaParametrized (S.μ ω) (S.η ω)})
    (FirstPass36.polyHighProb_inter (h' Ω S hS)
      (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮 γ hγ hγ2 β ρ hβpos hβ1 hρ hρ1 Ω S hS))
    hS.isAreaParametrized hε₁pos ?_
  rintro ε hε hεε₁ ω ⟨⟨hE1, hE2⟩, hG⟩
  have hG' : IsAreaParametrized (S.μ ω) (S.η ω) := hG
  -- thresholds on `ε`
  have hε1 : ε < 1 := lt_of_lt_of_le hεε₁ (min_le_left _ _)
  have hεC : ε ≤ Real.exp (-(2 * C)) :=
    (lt_of_lt_of_le hεε₁ ((min_le_right _ _).trans (min_le_left _ _))).le
  have hεc : ε < (c₀ / 2) ^ (2 / β) :=
    lt_of_lt_of_le hεε₁ ((min_le_right _ _).trans (min_le_right _ _))
  have hhalf : ε ^ (β / 2) ≤ c₀ / 2 := by
    have h1 : 2 / β * (β / 2) = 1 := by
      rw [div_mul_div_comm, mul_comm 2 β, div_self (mul_pos hβpos two_pos).ne']
    have := Real.rpow_le_rpow hε.le hεc.le (half_pos hβpos).le
    rwa [← Real.rpow_mul (half_pos hc₀pos).le, h1, Real.rpow_one] at this
  have hεω₁pos : 0 < ε ^ ω₁ := Real.rpow_pos_of_pos hε _
  have hεβ : ε ^ β ≤ c₀ / 2 * ε ^ ω₁ := by
    calc ε ^ β = ε ^ (β - ω₁) * ε ^ ω₁ := by rw [← Real.rpow_add hε, sub_add_cancel]
      _ ≤ ε ^ (β / 2) * ε ^ ω₁ :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by linarith)) hεω₁pos.le
      _ ≤ c₀ / 2 * ε ^ ω₁ := mul_le_mul_of_nonneg_right hhalf hεω₁pos.le
  have hεβω : ε ^ β ≤ ε ^ ω₁ := hεβ.trans (by nlinarith)
  have hεω₀ : ε ^ ω₀ ≤ ε ^ ω₁ := Real.rpow_le_rpow_of_exponent_ge hε hε1.le hω₁ω₀
  have hεinv : Real.exp (2 * C) ≤ ε⁻¹ := exp_le_inv_of_le_exp_neg hε hεC
  -- the cells meeting `B_ρ` have diameter at most `ε^β`
  have hcellB : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
      ∀ w ∈ cell ε (S.η ω) k, ∀ w' ∈ cell ε (S.η ω) k, dist w w' ≤ ε ^ β := by
    intro k hk w hw w' hw'
    obtain ⟨hlo, hup⟩ := hE2 k hk
    rw [hexp] at hup
    exact dist_le_of_diam_le (Real.rpow_pos_of_pos hε _) hlo hup hw hw'
  intro a ha r hr1 hr2
  set x := vertexPoint ε (S.η ω) a with hx
  have hsub0 : ball (0 : ℂ) (ρ - ε ^ ω₁) ⊆ ball 0 (ρ - ε ^ ω₀) := ball_subset_ball (by linarith)
  have ha0 : a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)) :=
    ha.mono (inter_subset_inter_right _ hsub0)
  have hr0 : ε ^ ω₀ ≤ r := hεω₀.trans hr1
  have hrpos : 0 < r := hεω₁pos.trans_le hr1
  obtain ⟨za, hza_cell, hza_ball⟩ := ha
  have hza : dist za 0 < ρ - ε ^ ω₁ := mem_ball.1 hza_ball
  have hacell : (cell ε (S.η ω) a ∩ ball 0 ρ).Nonempty :=
    ⟨za, hza_cell, mem_ball.2 (by linarith)⟩
  have hxza : dist x za ≤ ε ^ β :=
    hcellB a hacell x (Lemma68C12Geom.vertexPoint_mem_cell hε.le a) za hza_cell
  have hx0 : dist x 0 < ρ := by
    have := dist_triangle x za 0
    linarith
  have hinf : infDist x (sphere 0 ρ) ≤ ρ - ‖x‖ :=
    infDist_sphere_zero_le hρ.le (by rw [← dist_zero_right]; exact hx0.le)
  have hball : ball x r ⊆ ball 0 ρ := ball_subset_ball' (by rw [dist_zero_right]; linarith)
  have hcr : c₀ / 2 * r < r := by nlinarith
  have hcr3 : c₀ / 2 * r ≤ r / 3 := by nlinarith
  -- every point of a cell meeting `B_{cr}(x)` is within `c₀ r` of `x`
  have hkey : ∀ b ∈ cellVertices ε (S.η ω) (ball x (c₀ / 2 * r)),
      ∀ w ∈ cell ε (S.η ω) b, dist w x < c₀ * r := by
    intro b hb w hw
    obtain ⟨zb, hzb_cell, hzb_ball⟩ := hb
    have hbcell : (cell ε (S.η ω) b ∩ ball 0 ρ).Nonempty :=
      ⟨zb, hzb_cell, hball (ball_subset_ball hcr.le hzb_ball)⟩
    have h1 := hcellB b hbcell w hw zb hzb_cell
    have h2 := mem_ball.1 hzb_ball
    have h3 := dist_triangle w zb x
    have h4 : c₀ / 2 * ε ^ ω₁ ≤ c₀ / 2 * r :=
      mul_le_mul_of_nonneg_left hr1 (half_pos hc₀pos).le
    linarith
  have hWA : cellVertices ε (S.η ω) (ball x (c₀ / 2 * r)) ⊆
      interiorCellVertices ε (S.η ω) (ball x r) := by
    intro b hb
    refine ⟨?_, ?_⟩
    · obtain ⟨zb, hzb_cell, hzb_ball⟩ := hb
      exact ⟨zb, hzb_cell, ball_subset_ball hcr.le hzb_ball⟩
    · rintro ⟨w, hw_cell, hw_fr⟩
      rw [frontier_ball x hrpos.ne'] at hw_fr
      have := hkey b hb w hw_cell
      rw [mem_sphere.1 hw_fr] at this
      nlinarith
  have hgreen : ∀ b ∈ cellVertices ε (S.η ω) (ball x (c₀ / 2 * r)),
      1 ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball x r)) a b := by
    intro b hb
    have hb3 : b ∈ cellVertices ε (S.η ω) (ball x (r / 3)) := by
      obtain ⟨zb, hzb_cell, hzb_ball⟩ := hb
      exact ⟨zb, hzb_cell, ball_subset_ball hcr3 hzb_ball⟩
    have hGr := (hE1 a ha0 r hr0 hr2 b hb3).2
    have hyx : dist (vertexPoint ε (S.η ω) b) x < c₀ * r :=
      hkey b hb _ (Lemma68C12Geom.vertexPoint_mem_cell hε.le b)
    have hxy : ‖x - vertexPoint ε (S.η ω) b‖ < c₀ * r := by
      rw [← dist_eq_norm, dist_comm]
      exact hyx
    split_ifs at hGr with hab
    · exact le_trans (one_le_inv_mul_log_sub_one hC hεinv) hGr
    · exact le_trans
        (one_le_inv_mul_log_sub_one hC (exp_le_min_div_norm hab hεinv hrpos hc₀C hxy)) hGr
  have hμ := measure_le_mul_encard_cellVertices hG' hε (ball x (c₀ / 2 * r))
  have hW := encard_le_expectedExitTime_of_one_le_greenKernel (S.mult ε ω) a hWA hgreen
  calc ENNReal.ofReal ε⁻¹ * S.μ ω (ball x (c₀ / 2 * r))
      ≤ ENNReal.ofReal ε⁻¹ * (ENNReal.ofReal ε *
          ((cellVertices ε (S.η ω) (ball x (c₀ / 2 * r))).encard : ℝ≥0∞)) :=
        mul_le_mul' le_rfl hμ
    _ = ((cellVertices ε (S.η ω) (ball x (c₀ / 2 * r))).encard : ℝ≥0∞) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hε.le), inv_mul_cancel₀ hε.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ _ := hW

end MatedCRT.ExitTimeLowerBound
