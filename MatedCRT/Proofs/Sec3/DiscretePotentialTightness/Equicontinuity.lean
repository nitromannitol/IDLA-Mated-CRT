import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.EquicontinuityLemmas
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Proofs.Infra.Setting
import MatedCRT.Steps.Infra.MatingOfTrees

/-!
# Lemma 3.1: proof of `TightnessEquicontinuityStep` (lines 1028-1085)

* `interior_vertexEquicontinuous` (deterministic, along a sequence of scales): eq:equicontinuity before rescaling.
  For `a, b ∈ V(K)` with `|η(a) - η(b)| ≤ δ = r²`, `ball_estimate` on `B_r(η(a))`, with Lemma 2.18 and Lemma 2.17 at a
  radius `R = 2r` where `𝓜(B_R(y)) ≤ R^q`, gives `ε |u(a) - u(b)| ≤ A C r^ξ + 2 C C₁ R^q`.
* `closure_vertexEquicontinuous` (deterministic): up to the boundary, from the boundary estimate of Lemma 3.2 for
  `ε u^ε` on `V(D)` and the Hölder data on `V(∂D)`. A vertex of `V(∂D) \ V(D)` is replaced by a vertex of `V(D)` whose
  cell contains the same boundary point (`exists_mem_cellVertices_of_mem_closure`).
* `tightnessEquicontinuityStep_of_steps`: almost surely, the events of Lemmas 2.17, 2.18 and 3.2 (corrected) hold at
  all small scales of `e` (Borel-Cantelli, N3), hence eventually along `E(ω)`. The random `χ, C'` of the "moreover"
  part are handled by the countable family `χ_i = 1/(i+1)`, `C'_N = N + 1`.
-/

namespace MatedCRT.Tightness

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- The set form of `eventually_of_range`. -/
theorem eventually_mem_of_range {α : Type*} {e : ℕ → ℝ} (he : ∀ j, 0 < e j) {ε : ℕ → ℝ}
    (hεe : ∀ n, ε n ∈ range e) (hε0 : Tendsto ε atTop (𝓝 0)) {G : ℝ → Set α} {x : α}
    (h : ∀ᶠ j in atTop, x ∈ G (e j)) : ∀ᶠ n in atTop, x ∈ G (ε n) :=
  eventually_of_range (Q := fun r => x ∈ G r) he hεe hε0 h

/-- **Borel-Cantelli along random scales with values in polynomially summable scales** (N3): an event of polynomially
high probability holds, almost surely, at `E(ω, n)` for all large `n`. -/
theorem ae_eventually_mem_along {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : ℝ → Set Ω}
    (hG : PolyHighProb P G) {e : ℕ → ℝ} (he : IsPolySummableScales e) {E : Ω → ℕ → ℝ}
    (hEe : ∀ ω n, E ω n ∈ range e) (hEt : ∀ ω, Tendsto (E ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ G (E ω n) := by
  filter_upwards [ae_eventually_mem_of_polyHighProb hG he] with ω hω
  exact eventually_of_range (Q := fun r => ω ∈ G r) he.1 (hEe ω) (hEt ω) hω

/-- `ε^p → 0` along `ε → 0` for `p > 0`. -/
theorem tendsto_rpow_of_tendsto_zero {ε : ℕ → ℝ} (hε0 : Tendsto ε atTop (𝓝 0)) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n => ε n ^ p) atTop (𝓝 0) := by
  have h := ((continuous_id.rpow_const fun _ => Or.inr hp.le).tendsto 0).comp hε0
  simpa [Function.comp_def, Real.zero_rpow hp.ne'] using h

/-- **The interior estimate** (eq:equicontinuity before rescaling, lines 1028-1078). -/
theorem interior_vertexEquicontinuous {m : ℕ → ℤ → ℤ → ℕ} {ε : ℕ → ℝ} {η : ℝ → ℂ} {u : ℕ → ℤ → ℝ}
    {μ : Measure ℂ} {D K : Set ℂ} {ρ C ξ A β α C₁ q : ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ n j k, m n j k ≠ 0 → (cell (ε n) η j ∩ cell (ε n) η k).Nonempty)
    (hsucc : ∀ n k, m n k (k + 1) ≠ 0) (hDo : IsOpen D) (hDρ : D ⊆ ball 0 ρ) (hK : IsCompact K) (hKD : K ⊆ D)
    (hC : 0 ≤ C) (hlap : ∀ n, ∀ a ∈ interiorCellVertices (ε n) η D, |mLaplacian (m n) (u n) a| ≤ C)
    (hbd : ∀ n, ∀ a ∈ cellVertices (ε n) η D, |u n a| ≤ C / ε n)
    (hξ : 0 < ξ) (hA : 0 ≤ A) (hβ : 0 < β) (hα : 0 < α) (hC₁ : 0 ≤ C₁) (hq : 0 < q)
    (hH : ∀ᶠ n in atTop, ∀ (x : ℂ) (r : ℝ), 0 < r → ball x r ⊆ ball 0 ρ → ∀ f : ℤ → ℝ,
      (∀ a ∈ interiorCellVertices (ε n) η (ball x r), matedLaplacian (m n) f a = 0) →
      ∀ a ∈ interiorCellVertices (ε n) η (ball x r), ∀ b ∈ cellVertices (ε n) η (ball x r),
        |f a - f b| * infDist (vertexPoint (ε n) η a) (frontier (ball x r)) ^ ξ ≤
          A * (⨆ a' : cellVertices (ε n) η (ball x r), |f a'|) *
            max (ε n ^ β) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ^ ξ)
    (hQ : ∀ᶠ n in atTop, ∀ D' : Set ℂ, D' ⊆ ball 0 ρ → ∀ a ∈ cellVertices (ε n) η D',
      expectedExitTime (m n) (interiorCellVertices (ε n) η D') a ≤
        ENNReal.ofReal (C₁ * (ε n)⁻¹) * largestExitTimeRV μ (thickening (ε n ^ α) D'))
    (hM : ∀ R₀ : ℝ, 0 < R₀ → ∃ R : ℝ, 0 < R ∧ R < R₀ ∧
      ∀ y ∈ ball (0 : ℂ) ρ, largestExitTimeRV μ (ball y R) ≤ ENNReal.ofReal (R ^ q)) :
    IsVertexAsymptoticallyEquicontinuous ε η u K := by
  intro k hk
  obtain ⟨r0, hr0, hr0D⟩ := hK.exists_cthickening_subset_open hDo hKD
  have hg : Tendsto (fun R : ℝ => A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun R : ℝ => A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q :=
      (continuous_const.mul ((continuous_id.div_const 2).rpow_const fun _ => Or.inr hξ.le)).add
        (continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr hq.le))
    have h := hc.tendsto 0
    simpa [Real.zero_rpow hξ.ne', Real.zero_rpow hq.ne'] using h
  obtain ⟨R₀, hR₀, hR₀g⟩ := Metric.eventually_nhds_iff.1 (hg.eventually (gt_mem_nhds hk))
  obtain ⟨R, hR, hRlt, hMR⟩ := hM (min R₀ (min r0 1)) (lt_min hR₀ (lt_min hr0 one_pos))
  have hRR₀ : R < R₀ := hRlt.trans_le (min_le_left _ _)
  have hRr0 : R < r0 := hRlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hR1 : R < 1 := hRlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hgR : A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q < k :=
    hR₀g (by rw [Real.dist_eq, sub_zero, abs_of_pos hR]; exact hRR₀)
  set r : ℝ := R / 2 with hr_def
  have hr : 0 < r := by positivity
  have hr1 : r < 1 := by linarith
  have hδr : r * r < r := mul_lt_of_lt_one_right hr hr1
  have hδ : 0 < r * r := mul_pos hr hr
  obtain ⟨ε₀, hε₀, hcell⟩ := exists_cell_near_vertexPoint hη hp
    (show Bornology.IsBounded (cthickening r0 K) from hK.isBounded.cthickening) (s := r / 2) (by positivity)
  have hβev : ∀ᶠ n in atTop, ε n ^ β < r * r := (tendsto_rpow_of_tendsto_zero hε0 hβ).eventually (gt_mem_nhds hδ)
  have hαev : ∀ᶠ n in atTop, ε n ^ α < r := (tendsto_rpow_of_tendsto_zero hε0 hα).eventually (gt_mem_nhds hr)
  refine ⟨r * r, hδ, ?_⟩
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
  linarith

/-- **Equicontinuity up to the boundary** (lines 1082-1085). -/
theorem closure_vertexEquicontinuous {ε : ℕ → ℝ} {η : ℝ → ℂ} {u : ℕ → ℤ → ℝ} {D : Set ℂ} {χ C' K₀ ξ' : ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hsurj : Function.Surjective η) (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) (hχ : 0 < χ) (hC' : 0 ≤ C') (hK₀ : 0 ≤ K₀) (hξ' : 0 < ξ')
    (hdata : ∀ᶠ n in atTop, ∀ a ∈ cellVertices (ε n) η (frontier D), ∀ b ∈ cellVertices (ε n) η (frontier D),
      |u n a - u n b| ≤ C' / ε n * max (ε n) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ^ χ)
    (hHm : ∀ᶠ n in atTop, ∀ a ∈ cellVertices (ε n) η D, ∀ b ∈ cellVertices (ε n) η D,
      ε n * |u n a - u n b| ≤ K₀ * max (ε n) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ^ ξ') :
    IsVertexAsymptoticallyEquicontinuous ε η u (closure D) := by
  intro k hk
  have hg : Tendsto (fun s : ℝ => 2 * (C' * (2 * s) ^ χ) + K₀ * (5 * s) ^ ξ') (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun s : ℝ => 2 * (C' * (2 * s) ^ χ) + K₀ * (5 * s) ^ ξ' :=
      (continuous_const.mul (continuous_const.mul
        ((continuous_const.mul continuous_id).rpow_const fun _ => Or.inr hχ.le))).add
        (continuous_const.mul ((continuous_const.mul continuous_id).rpow_const fun _ => Or.inr hξ'.le))
    have h := hc.tendsto 0
    simpa [Real.zero_rpow hχ.ne', Real.zero_rpow hξ'.ne'] using h
  obtain ⟨s0, hs0, hs0g⟩ := Metric.eventually_nhds_iff.1 (hg.eventually (gt_mem_nhds hk))
  set s : ℝ := s0 / 2 with hs_def
  have hs : 0 < s := by positivity
  have hgs : 2 * (C' * (2 * s) ^ χ) + K₀ * (5 * s) ^ ξ' < k :=
    hs0g (by rw [Real.dist_eq, sub_zero, abs_of_pos hs]; linarith)
  obtain ⟨ε₀, hε₀, hcell⟩ := exists_cell_near_vertexPoint hη hp hDb.closure (s := s) hs
  refine ⟨s, hs, ?_⟩
  filter_upwards [hdata, hHm, hε0.eventually (gt_mem_nhds (lt_min hε₀ hs))] with n hdn hHn hεn
  have hεε₀ : ε n < ε₀ := hεn.trans_le (min_le_left _ _)
  have hεs : ε n < s := hεn.trans_le (min_le_right _ _)
  have hrep : ∀ a ∈ cellVertices (ε n) η (closure D), ∃ a' ∈ cellVertices (ε n) η D,
      ‖vertexPoint (ε n) η a - vertexPoint (ε n) η a'‖ < 2 * s ∧
        ε n * |u n a - u n a'| ≤ C' * (2 * s) ^ χ := by
    intro a ha
    by_cases haD : a ∈ cellVertices (ε n) η D
    · refine ⟨a, haD, by rw [sub_self, norm_zero]; linarith, ?_⟩
      rw [sub_self, abs_zero, mul_zero]
      exact mul_nonneg hC' (Real.rpow_nonneg (by linarith) _)
    · obtain ⟨z, hza, hzcl⟩ := ha
      have hzf : z ∈ frontier D := by
        rw [hDo.frontier_eq]
        exact ⟨hzcl, fun hzD => haD ⟨z, hza, hzD⟩⟩
      obtain ⟨a', ha'D, hza'⟩ := exists_mem_cellVertices_of_mem_closure hη hp hsurj (hε n) hzcl
      have ha'cl : a' ∈ cellVertices (ε n) η (closure D) := ⟨z, hza', hzcl⟩
      have h1 := hcell (ε n) (hε n) hεε₀ a ⟨z, hza, hzcl⟩ z hza
      have h2 := hcell (ε n) (hε n) hεε₀ a' ha'cl z hza'
      have hdist : ‖vertexPoint (ε n) η a - vertexPoint (ε n) η a'‖ < 2 * s := by
        calc ‖vertexPoint (ε n) η a - vertexPoint (ε n) η a'‖ =
            ‖(z - vertexPoint (ε n) η a') - (z - vertexPoint (ε n) η a)‖ := by congr 1; ring
          _ ≤ ‖z - vertexPoint (ε n) η a'‖ + ‖z - vertexPoint (ε n) η a‖ := norm_sub_le _ _
          _ < 2 * s := by linarith
      refine ⟨a', ha'D, hdist, ?_⟩
      have hd := hdn a ⟨z, hza, hzf⟩ a' ⟨z, hza', hzf⟩
      have hmax : max (ε n) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η a'‖ ≤ 2 * s :=
        max_le (by linarith) hdist.le
      have hmaxχ : max (ε n) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η a'‖ ^ χ ≤ (2 * s) ^ χ :=
        Real.rpow_le_rpow (le_max_of_le_left (hε n).le) hmax hχ.le
      calc ε n * |u n a - u n a'| ≤
            ε n * (C' / ε n * max (ε n) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η a'‖ ^ χ) :=
          mul_le_mul_of_nonneg_left hd (hε n).le
        _ = C' * max (ε n) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η a'‖ ^ χ * (ε n * (ε n)⁻¹) := by
          rw [div_eq_mul_inv]
          ring
        _ = C' * max (ε n) ‖vertexPoint (ε n) η a - vertexPoint (ε n) η a'‖ ^ χ := by
          rw [mul_inv_cancel₀ (hε n).ne', mul_one]
        _ ≤ C' * (2 * s) ^ χ := mul_le_mul_of_nonneg_left hmaxχ hC'
  intro a ha b hb hab
  obtain ⟨a', ha'D, hda, hua⟩ := hrep a ha
  obtain ⟨b', hb'D, hdb, hub⟩ := hrep b hb
  have hd' : ‖vertexPoint (ε n) η a' - vertexPoint (ε n) η b'‖ ≤ 5 * s := by
    calc ‖vertexPoint (ε n) η a' - vertexPoint (ε n) η b'‖ =
        ‖(vertexPoint (ε n) η a - vertexPoint (ε n) η b) - (vertexPoint (ε n) η a - vertexPoint (ε n) η a') +
          (vertexPoint (ε n) η b - vertexPoint (ε n) η b')‖ := by congr 1; ring
      _ ≤ ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ + ‖vertexPoint (ε n) η a - vertexPoint (ε n) η a'‖ +
          ‖vertexPoint (ε n) η b - vertexPoint (ε n) η b'‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ 5 * s := by linarith
  have hH' := hHn a' ha'D b' hb'D
  have hmax : max (ε n) ‖vertexPoint (ε n) η a' - vertexPoint (ε n) η b'‖ ≤ 5 * s := max_le (by linarith) hd'
  have hmaxξ : max (ε n) ‖vertexPoint (ε n) η a' - vertexPoint (ε n) η b'‖ ^ ξ' ≤ (5 * s) ^ ξ' :=
    Real.rpow_le_rpow (le_max_of_le_left (hε n).le) hmax hξ'.le
  have hK : K₀ * max (ε n) ‖vertexPoint (ε n) η a' - vertexPoint (ε n) η b'‖ ^ ξ' ≤ K₀ * (5 * s) ^ ξ' :=
    mul_le_mul_of_nonneg_left hmaxξ hK₀
  have t1 := abs_sub_le (u n a) (u n a') (u n b)
  have t2 := abs_sub_le (u n a') (u n b') (u n b)
  rw [abs_sub_comm (u n b') (u n b)] at t2
  have tsum : |u n a - u n b| ≤ |u n a - u n a'| + |u n a' - u n b'| + |u n b - u n b'| := by linarith
  have hmul := mul_le_mul_of_nonneg_left tsum (hε n).le
  rw [mul_add, mul_add] at hmul
  linarith

end MatedCRT.Tightness

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls Tightness
open scoped ENNReal

/-- **`TightnessEquicontinuityStep`** from Lemmas 2.17, 2.18, 3.2 (corrected) and `AdjacentCellsMeetAeStep`. -/
theorem tightnessEquicontinuityStep_of_steps {𝒮 : SpaceFillingSLEModel} (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮) : TightnessEquicontinuityStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS D hDρ hDo hDc e he E u C hdata
  obtain ⟨-, hEe, hEt, -, -, hCp, hlap, hbd⟩ := hdata
  obtain ⟨α, hα, h18α⟩ := h218 γ hγ hγ2
  obtain ⟨C₁, hC₁, h18C⟩ := h18α ρ hρ hρ1
  obtain ⟨q, hq, h17q⟩ := h217 γ hγ hγ2
  have h17 := (h17q ρ hρ hρ1 Ω S.P S.hC S.hcirc S.μ hS.isConeField).2
  obtain ⟨ξ, A, β, hξ, -, hA, hβ, -, hHχ⟩ := hH γ hγ hγ2 ρ hρ hρ1
  obtain ⟨_, _, _, _, _, hH1⟩ := hHχ 1 1 one_pos le_rfl one_pos
  have hχi : ∀ i : ℕ, (0 : ℝ) < 1 / ((i : ℝ) + 1) := fun i => by positivity
  have hχi1 : ∀ i : ℕ, 1 / ((i : ℝ) + 1) ≤ 1 := fun i =>
    (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
  have hNpos : ∀ N : ℕ, (0 : ℝ) < (N : ℝ) + 1 := fun N => by positivity
  choose ξ' Cc hξ'0 hξ'1 hCc hHij using fun i N : ℕ => hHχ (1 / ((i : ℝ) + 1)) ((N : ℝ) + 1) (hχi i) (hχi1 i)
    (hNpos N)
  have hEpos : ∀ ω n, 0 < E ω n := fun ω n => by
    obtain ⟨j, hj⟩ := hEe ω n
    rw [← hj]
    exact he.1 j
  have hDb : Bornology.IsBounded D := isBounded_ball.subset hDρ
  filter_upwards [ae_eventually_mem_along (h18C Ω S hS) he hEe hEt, ae_eventually_mem_of_polyHighProb h17 he,
    ae_eventually_mem_along (hH1 Ω S hS) he hEe hEt,
    ae_all_iff.2 fun i : ℕ => ae_all_iff.2 fun N : ℕ => ae_eventually_mem_along (hHij i N Ω S hS) he hEe hEt,
    hadj γ hγ hγ2 Ω S hS, hS.isAreaParametrized, hS.ae_tendsto_cocompact]
    with ω h18ω h17ω hHω hHijω hadjω hηω hpω
  have hlfn : ∀ n, IsLocallyFiniteMult (S.mult (E ω n) ω) := fun n =>
    isLocallyFiniteMult_of_cells hηω.1 hpω (hEpos ω n) (hadjω _ (hEpos ω n))
  refine ⟨fun K hK hKD => ?_, fun hhol => ?_⟩
  · -- the interior part
    have hM : ∀ R₀ : ℝ, 0 < R₀ → ∃ R : ℝ, 0 < R ∧ R < R₀ ∧
        ∀ y ∈ ball (0 : ℂ) ρ, largestExitTimeRV (S.μ ω) (ball y R) ≤ ENNReal.ofReal (R ^ q) := by
      intro R₀ hR₀
      obtain ⟨j, hj1, hj2⟩ := (h17ω.and (he.tendsto_zero.eventually (gt_mem_nhds hR₀))).exists
      exact ⟨e j, he.1 j, hj2, hj1⟩
    have hHball : ∀ᶠ n in atTop, ∀ (x : ℂ) (r : ℝ), 0 < r → ball x r ⊆ ball 0 ρ → ∀ f : ℤ → ℝ,
        (∀ a ∈ interiorCellVertices (E ω n) (S.η ω) (ball x r), matedLaplacian (S.mult (E ω n) ω) f a = 0) →
        ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) (ball x r), ∀ b ∈ cellVertices (E ω n) (S.η ω) (ball x r),
          |f a - f b| * infDist (vertexPoint (E ω n) (S.η ω) a) (frontier (ball x r)) ^ ξ ≤
            A * (⨆ a' : cellVertices (E ω n) (S.η ω) (ball x r), |f a'|) *
              max (E ω n ^ β) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ := by
      filter_upwards [hHω] with n hn x r hr hxr f hf
      exact (hn (ball x r) f hxr isOpen_ball ((convex_ball x r).isConnected (nonempty_ball.2 hr)) hf).1
    have hQ : ∀ᶠ n in atTop, ∀ D' : Set ℂ, D' ⊆ ball 0 ρ → ∀ a ∈ cellVertices (E ω n) (S.η ω) D',
        expectedExitTime (S.mult (E ω n) ω) (interiorCellVertices (E ω n) (S.η ω) D') a ≤
          ENNReal.ofReal (C₁ * (E ω n)⁻¹) * largestExitTimeRV (S.μ ω) (thickening (E ω n ^ α) D') := by
      filter_upwards [h18ω] with n hn D' hD' a ha
      exact (hn.2 D' hD' a ha).2
    exact interior_vertexEquicontinuous (m := fun n => S.mult (E ω n) ω) (hEpos ω) (hEt ω) hηω.1 hpω
      (fun n => hadjω _ (hEpos ω n)) (fun n k => S.mult_succ_ne_zero (hEpos ω n).le ω k) hDo hDρ hK hKD
      (hCp ω).le (hlap ω) (hbd ω) hξ hA.le hβ hα hC₁.le hq hHball hQ hM
  · -- the "moreover" part
    obtain ⟨hsc, hharm, χ, C', hχ, hχ1, hC', hdat⟩ := hhol
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hχ
    obtain ⟨N, hN⟩ := exists_nat_ge (2 * C')
    have hρ1' : 0 < 1 - ρ := by linarith
    obtain ⟨ε₀, hε₀, hcell⟩ := exists_cell_near_vertexPoint hηω.1 hpω hDb.closure (s := 1 - ρ) hρ1'
    have hclρ : closure D ⊆ closedBall (0 : ℂ) ρ := (closure_mono hDρ).trans closure_ball_subset_closedBall
    have hHm : ∀ᶠ n in atTop, ∀ a ∈ cellVertices (E ω n) (S.η ω) D, ∀ b ∈ cellVertices (E ω n) (S.η ω) D,
        E ω n * |u ω n a - u ω n b| ≤ max (Cc i N) (A * C ω) *
          max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ' i N := by
      filter_upwards [hHijω i N, (hEt ω).eventually (gt_mem_nhds (lt_min hε₀ one_pos))] with n hn hεn a ha b hb
      have hE := hEpos ω n
      have hεε₀ : E ω n < ε₀ := hεn.trans_le (min_le_left _ _)
      have hε1 : E ω n < 1 := hεn.trans_le (min_le_right _ _)
      have hfharm : ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
          matedLaplacian (S.mult (E ω n) ω) (fun b => E ω n * u ω n b) a = 0 := by
        intro a ha
        show mLaplacian _ (fun b => E ω n * u ω n b) a = 0
        rw [mLaplacian_const_mul (hlfn n), show mLaplacian (S.mult (E ω n) ω) (u ω n) a = 0 from hharm n a ha,
          mul_zero]
      have hnear : ∀ c ∈ cellVertices (E ω n) (S.η ω) (frontier D), ‖vertexPoint (E ω n) (S.η ω) c‖ < 1 := by
        intro c hc
        obtain ⟨z, hzc, hzf⟩ := hc
        have hzcl : z ∈ closure D := frontier_subset_closure hzf
        have h1 := hcell (E ω n) hE hεε₀ c ⟨z, hzc, hzcl⟩ z hzc
        have h2 : ‖z‖ ≤ ρ := by simpa using hclρ hzcl
        calc ‖vertexPoint (E ω n) (S.η ω) c‖ = ‖z - (z - vertexPoint (E ω n) (S.η ω) c)‖ := by congr 1; ring
          _ ≤ ‖z‖ + ‖z - vertexPoint (E ω n) (S.η ω) c‖ := norm_sub_le _ _
          _ < 1 := by linarith
      have hfdata : ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D), ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D),
          |E ω n * u ω n a - E ω n * u ω n b| ≤ ((N : ℝ) + 1) *
            max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ (1 / ((i : ℝ) + 1)) := by
        intro a ha b hb
        set X := max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ with hX
        have hX0 : 0 < X := lt_max_of_lt_left hE
        have hX2 : X ≤ 2 := by
          refine max_le (by linarith) ?_
          have := norm_sub_le (vertexPoint (E ω n) (S.η ω) a) (vertexPoint (E ω n) (S.η ω) b)
          linarith [hnear a ha, hnear b hb]
        have hd := hdat n hε1 a ha b hb
        have hpow := rpow_le_two_mul_rpow hX0 hX2 (hχi i).le hi.le hχ1
        have hXi : 0 ≤ X ^ (1 / ((i : ℝ) + 1)) := Real.rpow_nonneg hX0.le _
        rw [← mul_sub, abs_mul, abs_of_pos hE]
        calc E ω n * |u ω n a - u ω n b| ≤ E ω n * (C' / E ω n * X ^ χ) := mul_le_mul_of_nonneg_left hd hE.le
          _ = C' * X ^ χ * (E ω n * (E ω n)⁻¹) := by rw [div_eq_mul_inv]; ring
          _ = C' * X ^ χ := by rw [mul_inv_cancel₀ hE.ne', mul_one]
          _ ≤ C' * (2 * X ^ (1 / ((i : ℝ) + 1))) := mul_le_mul_of_nonneg_left hpow hC'.le
          _ = (2 * C') * X ^ (1 / ((i : ℝ) + 1)) := by ring
          _ ≤ ((N : ℝ) + 1) * X ^ (1 / ((i : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) hXi
      have hne : Nonempty (cellVertices (E ω n) (S.η ω) D) := ⟨⟨a, ha⟩⟩
      have hsup : (⨆ a' : cellVertices (E ω n) (S.η ω) D, |E ω n * u ω n a'|) ≤ C ω := by
        refine ciSup_le fun c => ?_
        rw [abs_mul, abs_of_pos hE]
        calc E ω n * |u ω n c| ≤ E ω n * (C ω / E ω n) := mul_le_mul_of_nonneg_left (hbd ω n c c.2) hE.le
          _ = C ω * (E ω n * (E ω n)⁻¹) := by rw [div_eq_mul_inv]; ring
          _ = C ω := by rw [mul_inv_cancel₀ hE.ne', mul_one]
      have hmain := (hn D (fun b => E ω n * u ω n b) hDρ hDo hDc hfharm).2 ⟨hsc, hfdata⟩ a ha b hb
      have hmaxpow : 0 ≤ max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ' i N :=
        Real.rpow_nonneg (le_max_of_le_left hE.le) _
      have hle : max (Cc i N) (A * ⨆ a' : cellVertices (E ω n) (S.η ω) D, |E ω n * u ω n a'|) ≤
          max (Cc i N) (A * C ω) := max_le_max le_rfl (mul_le_mul_of_nonneg_left hsup hA.le)
      calc E ω n * |u ω n a - u ω n b| = |E ω n * u ω n a - E ω n * u ω n b| := by
            rw [← mul_sub, abs_mul, abs_of_pos hE]
        _ ≤ _ := hmain
        _ ≤ max (Cc i N) (A * C ω) *
            max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ' i N :=
          mul_le_mul_of_nonneg_right hle hmaxpow
    have hdata' : ∀ᶠ n in atTop, ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D),
        ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D), |u ω n a - u ω n b| ≤
          C' / E ω n * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ χ := by
      filter_upwards [(hEt ω).eventually (gt_mem_nhds one_pos)] with n hn
      exact hdat n hn
    exact closure_vertexEquicontinuous (hEpos ω) (hEt ω) hηω.1 hpω hηω.2.2.1 hDo hDb hχ hC'.le
      (le_max_of_le_left (hCc i N).le) (hξ'0 i N) hdata' hHm

end MatedCRT
