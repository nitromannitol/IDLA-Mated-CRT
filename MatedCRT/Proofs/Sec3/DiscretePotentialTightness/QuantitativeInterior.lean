import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Equicontinuity

/-! Quantitative interior vertex modulus on every sufficiently small scale. -/

namespace MatedCRT.Tightness

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- Under an all-radii small-ball exit-potential bound, the proof of
Lemma 3.1 gives an explicit two-power modulus for vertex values. -/
theorem interior_vertex_two_power_estimate {m : ℕ → ℤ → ℤ → ℕ} {ε : ℕ → ℝ} {η : ℝ → ℂ} {u : ℕ → ℤ → ℝ}
    {μ : Measure ℂ} {D K : Set ℂ} {ρ C ξ A β α C₁ q : ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ n j k, m n j k ≠ 0 → (cell (ε n) η j ∩ cell (ε n) η k).Nonempty)
    (hsucc : ∀ n k, m n k (k + 1) ≠ 0) (hDo : IsOpen D) (hDρ : D ⊆ ball 0 ρ) (hK : IsCompact K) (hKD : K ⊆ D)
    (hC : 0 ≤ C) (hlap : ∀ n, ∀ a ∈ interiorCellVertices (ε n) η D, |mLaplacian (m n) (u n) a| ≤ C)
    (hbd : ∀ n, ∀ a ∈ cellVertices (ε n) η D, |u n a| ≤ C / ε n)
    (hξ : 0 < ξ) (hA : 0 ≤ A) (hβ : 0 < β) (hα : 0 < α) (hC₁ : 0 ≤ C₁)
    (hH : ∀ᶠ n in atTop, ∀ (x : ℂ) (r : ℝ), 0 < r → ball x r ⊆ ball 0 ρ → ∀ f : ℤ → ℝ,
      (∀ a ∈ interiorCellVertices (ε n) η (ball x r), matedLaplacian (m n) f a = 0) →
      ∀ a ∈ interiorCellVertices (ε n) η (ball x r), ∀ b ∈ cellVertices (ε n) η (ball x r),
        |f a - f b| * infDist (vertexPoint (ε n) η a) (frontier (ball x r)) ^ ξ ≤
          A * (⨆ a' : cellVertices (ε n) η (ball x r), |f a'|) *
            max (ε n ^ β) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ^ ξ)
    (hQ : ∀ᶠ n in atTop, ∀ D' : Set ℂ, D' ⊆ ball 0 ρ → ∀ a ∈ cellVertices (ε n) η D',
      expectedExitTime (m n) (interiorCellVertices (ε n) η D') a ≤
        ENNReal.ofReal (C₁ * (ε n)⁻¹) * largestExitTimeRV μ (thickening (ε n ^ α) D'))
    (hM : ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, 0 < R → R < R₁ →
      ∀ y ∈ ball (0 : ℂ) ρ, largestExitTimeRV μ (ball y R) ≤ ENNReal.ofReal (R ^ q)) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
      ∀ᶠ n in atTop, ∀ a ∈ cellVertices (ε n) η K, ∀ b ∈ cellVertices (ε n) η K,
        ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ≤ (R / 2) * (R / 2) →
        ε n * |u n a - u n b| ≤ A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q := by
  obtain ⟨r0, hr0, hr0D⟩ := hK.exists_cthickening_subset_open hDo hKD
  obtain ⟨R₁, hR₁, hM⟩ := hM
  refine ⟨min R₁ (min r0 1), lt_min hR₁ (lt_min hr0 one_pos), ?_⟩
  intro R hR hRlt
  have hRR₁ : R < R₁ := hRlt.trans_le (min_le_left _ _)
  have hRr0 : R < r0 := hRlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hR1 : R < 1 := hRlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hMR := hM R hR hRR₁
  set r : ℝ := R / 2 with hr_def
  have hr : 0 < r := by positivity
  have hr1 : r < 1 := by linarith
  have hδr : r * r < r := mul_lt_of_lt_one_right hr hr1
  have hδ : 0 < r * r := mul_pos hr hr
  obtain ⟨ε₀, hε₀, hcell⟩ := exists_cell_near_vertexPoint hη hp
    (show Bornology.IsBounded (cthickening r0 K) from hK.isBounded.cthickening) (s := r / 2) (by positivity)
  have hβev : ∀ᶠ n in atTop, ε n ^ β < r * r := (tendsto_rpow_of_tendsto_zero hε0 hβ).eventually (gt_mem_nhds hδ)
  have hαev : ∀ᶠ n in atTop, ε n ^ α < r := (tendsto_rpow_of_tendsto_zero hε0 hα).eventually (gt_mem_nhds hr)
  filter_upwards [hH, hQ, hε0.eventually (gt_mem_nhds hε₀), hβev, hαev] with n hHn hQn hεn hβn hαn a ha b _ hab
  obtain ⟨p, hpa, hpK⟩ := ha
  have haT : a ∈ cellVertices (ε n) η (cthickening r0 K) := ⟨p, hpa, self_subset_cthickening K hpK⟩
  have hpx : ‖p - vertexPoint (ε n) η a‖ < r / 2 := hcell (ε n) (hε n) hεn a haT p hpa
  have hB : ball (vertexPoint (ε n) η a) r ⊆ D := by
    intro z hz
    apply hr0D
    refine mem_cthickening_of_dist_le z p r0 K hpK ?_
    rw [mem_ball] at hz
    have h1 : dist (vertexPoint (ε n) η a) p < r / 2 := by rw [dist_comm, dist_eq_norm]; exact hpx
    linarith [dist_triangle z (vertexPoint (ε n) η a) p]
  have hBρ : ball (vertexPoint (ε n) η a) r ⊆ ball 0 ρ := hB.trans hDρ
  have hxρ : vertexPoint (ε n) η a ∈ ball (0 : ℂ) ρ := hBρ (mem_ball_self hr)
  have ha' : a ∈ interiorCellVertices (ε n) η (ball (vertexPoint (ε n) η a) r) := by
    refine ⟨⟨vertexPoint (ε n) η a, vertexPoint_mem_cell (hε n) a, mem_ball_self hr⟩, ?_⟩
    rintro ⟨w, hw, hwf⟩
    rw [frontier_ball _ hr.ne', mem_sphere, dist_eq_norm] at hwf
    have h1 := hcell (ε n) (hε n) hεn a haT w hw
    linarith
  have hb' : b ∈ cellVertices (ε n) η (ball (vertexPoint (ε n) η a) r) := by
    refine mem_cellVertices_of_vertexPoint_mem (hε n) ?_
    rw [mem_ball, dist_eq_norm, norm_sub_rev]
    linarith
  have hthick : thickening (ε n ^ α) (ball (vertexPoint (ε n) η a) r) ⊆ ball (vertexPoint (ε n) η a) R := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.1 hz
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle z y (vertexPoint (ε n) η a)]
  have hεinv : 0 ≤ (ε n)⁻¹ := inv_nonneg.2 (hε n).le
  have hMq0 : 0 ≤ C₁ * (ε n)⁻¹ * R ^ q := mul_nonneg (mul_nonneg hC₁ hεinv) (Real.rpow_nonneg hR.le _)
  have hQb : ∀ c ∈ interiorCellVertices (ε n) η (ball (vertexPoint (ε n) η a) r),
      expectedExitTime (m n) (interiorCellVertices (ε n) η (ball (vertexPoint (ε n) η a) r)) c ≤
        ENNReal.ofReal (C₁ * (ε n)⁻¹ * R ^ q) := by
    intro c hc
    calc expectedExitTime (m n) (interiorCellVertices (ε n) η (ball (vertexPoint (ε n) η a) r)) c
        ≤ ENNReal.ofReal (C₁ * (ε n)⁻¹) *
            largestExitTimeRV μ (thickening (ε n ^ α) (ball (vertexPoint (ε n) η a) r)) := hQn _ hBρ c hc.1
      _ ≤ ENNReal.ofReal (C₁ * (ε n)⁻¹) * ENNReal.ofReal (R ^ q) := by
          gcongr
          exact (largestExitTimeRV_mono hthick).trans (hMR _ hxρ)
      _ = ENNReal.ofReal (C₁ * (ε n)⁻¹ * R ^ q) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hC₁ hεinv)]
  have hest := ball_estimate (hε n) hη hp (hadj n) (hsucc n) hDo hC (hlap n) (hbd n) hr hB hξ.le hA hMq0
    (hHn _ r hr hBρ) hQb ha' rfl hb'
  have hmax : max (ε n ^ β) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ≤ r * r := max_le hβn.le hab
  have hmaxξ : max (ε n ^ β) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ^ ξ ≤ r ^ ξ * r ^ ξ := by
    calc max (ε n ^ β) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ^ ξ ≤ (r * r) ^ ξ :=
          Real.rpow_le_rpow (le_max_of_le_right (norm_nonneg _)) hmax hξ.le
      _ = r ^ ξ * r ^ ξ := Real.mul_rpow hr.le hr.le
  have hrξ : 0 < r ^ ξ := Real.rpow_pos_of_pos hr ξ
  have hCε : 0 ≤ A * (C / ε n) := mul_nonneg hA (div_nonneg hC (hε n).le)
  have h1 : |u n a - u n b| * r ^ ξ ≤ (A * (C / ε n) * r ^ ξ + 2 * C * (C₁ * (ε n)⁻¹ * R ^ q)) * r ^ ξ := by
    calc |u n a - u n b| * r ^ ξ ≤ A * (C / ε n) *
          max (ε n ^ β) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ^ ξ +
          2 * C * (C₁ * (ε n)⁻¹ * R ^ q) * r ^ ξ := hest
      _ ≤ A * (C / ε n) * (r ^ ξ * r ^ ξ) + 2 * C * (C₁ * (ε n)⁻¹ * R ^ q) * r ^ ξ :=
          add_le_add (mul_le_mul_of_nonneg_left hmaxξ hCε) le_rfl
      _ = (A * (C / ε n) * r ^ ξ + 2 * C * (C₁ * (ε n)⁻¹ * R ^ q)) * r ^ ξ := by ring
  have h2 : |u n a - u n b| ≤ A * (C / ε n) * r ^ ξ + 2 * C * (C₁ * (ε n)⁻¹ * R ^ q) :=
    le_of_mul_le_mul_right h1 hrξ
  have h3 : ε n * |u n a - u n b| ≤ A * C * r ^ ξ + 2 * C * C₁ * R ^ q := by
    calc ε n * |u n a - u n b| ≤ ε n * (A * (C / ε n) * r ^ ξ + 2 * C * (C₁ * (ε n)⁻¹ * R ^ q)) :=
          mul_le_mul_of_nonneg_left h2 (hε n).le
      _ = A * C * r ^ ξ * (ε n * (ε n)⁻¹) + 2 * C * C₁ * R ^ q * (ε n * (ε n)⁻¹) := by
          rw [div_eq_mul_inv]
          ring
      _ = A * C * r ^ ξ + 2 * C * C₁ * R ^ q := by rw [mul_inv_cancel₀ (hε n).ne', mul_one, mul_one]
  exact h3

end MatedCRT.Tightness
