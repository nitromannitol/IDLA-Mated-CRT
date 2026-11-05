import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PathEnvelope

/-!
# Lemma 3.6: small oscillation in the exit window near a regular exit

If a continuous path `p` started in `B_r(z)` leaves `cl(B_r(z))` immediately after its
exit time, then every path `g` close to `p` in the local uniform distance moves little
on the window `[τ_{B_{r-d}(z)}(g), τ_{B_r(z)}(g) + h]` for small `d, h`: on that window
`g` stays near its exit position. This is the deterministic input of the repaired
cell comparison (E-c2-8).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- Closeness in the local uniform distance controls the pointwise distance up to `T`. -/
theorem exists_localUniformDist_bound (p : ℝ≥0 → ℂ) (T : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ g : ℝ≥0 → ℂ, localUniformDist g p < ρ →
      ∀ t ≤ T, dist (g t) (p t) < δ := by
  refine ⟨(2 : ℝ)⁻¹ ^ (⌈T⌉₊ + 1) * min 1 δ, by positivity, fun g hg t ht => ?_⟩
  have htk : t ≤ ((⌈T⌉₊ + 1 : ℕ) : ℝ≥0) :=
    ht.trans ((Nat.le_ceil T).trans (by exact_mod_cast Nat.le_succ _))
  have hw := weighted_min_dist_le_localUniformDist g p (⌈T⌉₊) htk
  have hlt : min 1 (dist (g t) (p t)) < min 1 δ := by
    have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (⌈T⌉₊ + 1) := by positivity
    by_contra hcon
    have := mul_le_mul_of_nonneg_left (not_lt.mp hcon) hpos.le
    linarith
  by_contra hcon
  exact absurd hlt (not_lt.mpr (min_le_min le_rfl (not_lt.mp hcon)))

/-- **Small oscillation in the exit window.** -/
theorem exists_exitWindow_dist_le (p : ContinuousPath ℂ) (z : ℂ) {r : ℝ}
    (h0 : p 0 ∈ ball z r) (hfin : ContinuousPath.exitTime (ball z r) p < ⊤)
    (hregular : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) p).toNNReal,
      p t ∉ closedBall z r)
    {η : ℝ} (hη : 0 < η) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∃ h₀ : ℝ≥0, 0 < h₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ g : ℝ≥0 → ℂ,
      localUniformDist g p < ρ → ∀ s : ℝ≥0,
      pathExitTime (ball z (r - d₀)) g ≤ s →
      (s : ℝ≥0∞) ≤ pathExitTime (ball z r) g + h₀ →
      dist (g s) (pathExitPosition (ball z r) g) ≤ η := by
  obtain ⟨τ, hτeq⟩ : ∃ τ : ℝ≥0, ContinuousPath.exitTime (ball z r) p = τ :=
    ⟨_, (ENNReal.coe_toNNReal hfin.ne).symm⟩
  have hτto : (ContinuousPath.exitTime (ball z r) p).toNNReal = τ := by rw [hτeq]; rfl
  rw [hτto] at hregular
  have hτpos : (0 : ℝ) < τ := by
    have hfr := ContinuousPath.coordinate_exitTime_mem_frontier (ball z r) isOpen_ball p h0
      hfin.ne
    change p ((ContinuousPath.exitTime (ball z r) p).toNNReal) ∈ frontier (ball z r) at hfr
    rw [hτto, isOpen_ball.frontier_eq] at hfr
    rcases (NNReal.coe_nonneg τ).lt_or_eq with h | h
    · exact h
    · have : τ = 0 := NNReal.coe_eq_zero.1 h.symm
      rw [this] at hfr
      exact absurd h0 hfr.2
  obtain ⟨c, hc, hcont⟩ := Metric.continuous_iff.1 p.continuous τ (η / 4) (by linarith)
  set h₁ : ℝ := c / 4 with hh₁
  have hh₁pos : 0 < h₁ := by positivity
  set u : ℝ≥0 := (τ - h₁ : ℝ).toNNReal with hudef
  have hu_real : (u : ℝ) = max (τ - h₁) 0 := Real.coe_toNNReal' _
  have hu_lt : u < τ := by
    rw [← NNReal.coe_lt_coe, hu_real]
    exact max_lt (by linarith) hτpos
  have hu : (u : ℝ≥0∞) < ContinuousPath.exitTime (ball z r) p := by
    rw [hτeq]; exact_mod_cast hu_lt
  have hIoo : Ioo τ (τ + h₁.toNNReal) ∈ 𝓝[>] τ :=
    Ioo_mem_nhdsGT (lt_add_of_pos_right τ (Real.toNNReal_pos.2 hh₁pos))
  obtain ⟨v, hvp, hvI⟩ := (hregular.and_eventually hIoo).exists
  have hv_real : (v : ℝ) < τ + h₁ := by
    have := NNReal.coe_lt_coe.2 hvI.2
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hh₁pos.le] at this
  have huv : u ≤ v := (hu_lt.trans hvI.1).le
  obtain ⟨δ₁, hδ₁, hbounds⟩ := exists_uniform_ball_exit_bounds p z r huv hu hvp
  obtain ⟨a, ha, hmargin⟩ := exists_ball_margin_before_exit p z r hu
  set δ : ℝ := min (min δ₁ (a / 2)) (η / 4) with hδdef
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδa : δ ≤ a / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδη : δ ≤ η / 4 := min_le_right _ _
  obtain ⟨ρ, hρ, hclose⟩ := exists_localUniformDist_bound p (v + h₁.toNNReal) hδpos
  refine ⟨a / 2, by positivity, h₁.toNNReal, Real.toNNReal_pos.2 hh₁pos, ρ, hρ, ?_⟩
  intro g hg s hs1 hs2
  have hcl := hclose g hg
  obtain ⟨hlow, hup⟩ := hbounds g fun t ht => (hcl t (ht.trans le_self_add)).trans_le hδ1
  -- the inner exit time is at least `u`
  have hlow' : (u : ℝ≥0∞) ≤ pathExitTime (ball z (r - a / 2)) g := by
    unfold pathExitTime
    refine le_sInf ?_
    rintro _ ⟨t, rfl, ht⟩
    rw [ENNReal.coe_le_coe]
    by_contra hn
    have htu : t ≤ u := (not_le.mp hn).le
    have hd := hcl t (htu.trans (huv.trans le_self_add))
    have hm := hmargin t htu
    have htri := dist_triangle (g t) (p t) z
    exact ht (mem_ball.2 (by linarith))
  have hus : u ≤ s := ENNReal.coe_le_coe.1 (hlow'.trans hs1)
  obtain ⟨τg, hτg⟩ : ∃ τg : ℝ≥0, pathExitTime (ball z r) g = τg :=
    ⟨_, (ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top hup)).symm⟩
  rw [hτg] at hlow hup hs2
  have huτg : u ≤ τg := ENNReal.coe_le_coe.1 hlow
  have hτgv : τg ≤ v := ENNReal.coe_le_coe.1 hup
  have hsv : s ≤ v + h₁.toNNReal := by
    rw [← ENNReal.coe_add] at hs2
    exact (ENNReal.coe_le_coe.1 hs2).trans (by gcongr)
  have hpos : pathExitPosition (ball z r) g = g τg := by
    unfold pathExitPosition
    rw [hτg]
    rfl
  rw [hpos]
  -- time estimates in `ℝ`
  have hu_ge : τ - h₁ ≤ (u : ℝ) := by rw [hu_real]; exact le_max_left _ _
  have hs_le : (s : ℝ) ≤ v + h₁ := by
    have := NNReal.coe_le_coe.2 hsv
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hh₁pos.le] at this
  have hs_ge : (u : ℝ) ≤ s := NNReal.coe_le_coe.2 hus
  have hτg_ge : (u : ℝ) ≤ τg := NNReal.coe_le_coe.2 huτg
  have hτg_le : (τg : ℝ) ≤ v := NNReal.coe_le_coe.2 hτgv
  have hds : dist s τ < c := by
    rw [NNReal.dist_eq, abs_lt]
    constructor <;> linarith
  have hdτg : dist τg τ < c := by
    rw [NNReal.dist_eq, abs_lt]
    constructor <;> linarith
  have h1 := hcl s hsv
  have h2 := hcont s hds
  have h3 := hcont τg hdτg
  have h4 := hcl τg (hτgv.trans le_self_add)
  calc dist (g s) (g τg) ≤ dist (g s) (p s) + dist (p s) (p τ) + dist (p τ) (g τg) :=
        dist_triangle4 _ _ _ _
    _ ≤ dist (g s) (p s) + dist (p s) (p τ) + (dist (p τ) (p τg) + dist (p τg) (g τg)) := by
        gcongr
        exact dist_triangle _ _ _
    _ ≤ η := by
        rw [dist_comm (p τ) (p τg), dist_comm (p τg) (g τg)]
        linarith

end MatedCRT
