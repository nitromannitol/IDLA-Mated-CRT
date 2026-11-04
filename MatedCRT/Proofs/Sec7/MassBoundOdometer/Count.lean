import MatedCRT.Proofs.Sec7.MassBoundOdometer.Comparison

/-!
# Lemma 7.2: the counting bound for a fixed map (proof, lines 3025-3031)

For a fixed realization (continuous surjective `η`, cells meeting `B_ρ` of diameter `≤ δ`, the lower bound of
Lemma 2.16 for the Green's kernel), a ball `B_s(z)` with `V^ε(B_s(z)) ⊆ V^ε(B_ρ) \ Θ` and a scale `s` above the cell
size and above `ε^{ω₀}`:
`|V^ε(B_{𝐜₀ s}(z)) ∩ Λ^ε_t| ≤ 2 sup_{∂Θ} u^ε_t` (`ncard_cellVertices_inter_cluster_le`), with
`𝐜₀ = e^{-3C/2}/36` (`C` the constant of Lemma 2.16).

The comparison function is centred at a vertex `x₀ ∈ V^ε(B_{𝐜₀ s}(z)) ∩ Λ^ε_t`: `𝔣 = ∑_b g_D(·, b)` over
`b ∈ V^ε(B_{𝐜₀ s}(z)) ∩ Λ^ε_t`, with `D = V^ε(B_{s/4}(η(x₀))) \ V^ε(∂B_{s/4}(η(x₀)))`, so that Lemma 2.16 applies to
`g_D(x₀, b)` directly (the printed proof uses `D = V^ε(B_s(z)) \ V^ε(∂B_s(z))`, which needs the monotonicity of the
Green's kernel in the domain in addition). The cells of `D` lie in `B_{s/4}(η(x₀)) ⊆ B_s(z)` and adjacent cells meet,
so `∂D ⊆ V^ε(B_s(z))`, where `u^ε_t ≤ sup_{∂Θ} u^ε_t` (eq:upper-bound-on-ut).
-/

namespace MatedCRT.Sec7

open Set Metric

variable {ε : ℝ} {η : ℝ → ℂ}

theorem cell_isBounded (hη : Continuous η) (k : ℤ) : Bornology.IsBounded (cell ε η k) :=
  (isCompact_Icc.image hη).isBounded

theorem vertexPoint_mem_cell (hε : 0 ≤ ε) (k : ℤ) : vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩

/-- For a surjective `η`, the cells cover `ℂ`. -/
theorem exists_mem_cell (hε : 0 < ε) (hsurj : Function.Surjective η) (w : ℂ) : ∃ k : ℤ, w ∈ cell ε η k := by
  obtain ⟨τ, rfl⟩ := hsurj w
  refine ⟨⌈τ / ε⌉, τ, ⟨?_, ?_⟩, rfl⟩
  · have h := Int.ceil_lt_add_one (τ / ε)
    have h' : (⌈τ / ε⌉ : ℝ) - 1 < τ / ε := by linarith
    rw [lt_div_iff₀ hε] at h'
    linarith [mul_comm ε ((⌈τ / ε⌉ : ℝ) - 1)]
  · have h := Int.le_ceil (τ / ε)
    rw [div_le_iff₀ hε] at h
    linarith [mul_comm ε (⌈τ / ε⌉ : ℝ)]

/-- A cell of a vertex of `V^ε(B_r(c)) \ V^ε(∂B_r(c))` lies in `B_r(c)` (`η` continuous; intermediate values). -/
theorem cell_subset_ball_of_mem_interiorCellVertices (hη : Continuous η) {c : ℂ} {r : ℝ} {k : ℤ}
    (hk : k ∈ interiorCellVertices ε η (ball c r)) : cell ε η k ⊆ ball c r := by
  intro z hz
  obtain ⟨⟨y, hyc, hyb⟩, hkf⟩ : (cell ε η k ∩ ball c r).Nonempty ∧
      ¬ (cell ε η k ∩ frontier (ball c r)).Nonempty := hk
  have hr : r ≠ 0 := by
    rintro rfl
    simp at hyb
  rw [frontier_ball c hr] at hkf
  by_contra hzb
  obtain ⟨s, hs, rfl⟩ : ∃ s ∈ Icc (ε * (k - 1)) (ε * k), η s = z := hz
  obtain ⟨s', hs', rfl⟩ : ∃ s ∈ Icc (ε * (k - 1)) (ε * k), η s = y := hyc
  have hcont : ContinuousOn (fun τ => dist (η τ) c) (uIcc s' s) := (hη.dist continuous_const).continuousOn
  have hmem : r ∈ uIcc (dist (η s') c) (dist (η s) c) := by
    rw [mem_ball] at hyb
    rw [mem_ball, not_lt] at hzb
    exact Set.mem_uIcc.2 (Or.inl ⟨hyb.le, hzb⟩)
  obtain ⟨τ, hτ, hτr⟩ := intermediate_value_uIcc hcont hmem
  exact hkf ⟨η τ, ⟨τ, Set.uIcc_subset_Icc hs' hs hτ, rfl⟩, mem_sphere.2 hτr⟩

/-- A point at distance `τ ≥ 0` from `y₀` with norm `‖y₀‖ + τ`. -/
theorem exists_norm_eq_add (y₀ : ℂ) {τ : ℝ} (hτ : 0 ≤ τ) : ∃ y : ℂ, ‖y - y₀‖ = τ ∧ ‖y‖ = ‖y₀‖ + τ := by
  by_cases h : y₀ = 0
  · subst h
    refine ⟨(τ : ℂ), ?_, ?_⟩
    · rw [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
    · rw [norm_zero, zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
  · have hn : ‖y₀‖ ≠ 0 := norm_ne_zero_iff.2 h
    have hq : 0 ≤ τ / ‖y₀‖ := div_nonneg hτ (norm_nonneg _)
    refine ⟨y₀ + ((τ / ‖y₀‖ : ℝ) : ℂ) * y₀, ?_, ?_⟩
    · rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq,
        div_mul_cancel₀ _ hn]
    · have e : y₀ + ((τ / ‖y₀‖ : ℝ) : ℂ) * y₀ = ((1 + τ / ‖y₀‖ : ℝ) : ℂ) * y₀ := by
        push_cast
        ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), add_mul, one_mul,
        div_mul_cancel₀ _ hn]

/-- If every point of `B_s(z)` has norm `< R` and `‖y₀ - z‖ < a ≤ s`, then `‖y₀‖ + (s - a) < R`. -/
theorem norm_add_lt_of_ball {z y₀ : ℂ} {s a R : ℝ} (hR : ∀ y ∈ ball z s, ‖y‖ < R) (hy₀ : ‖y₀ - z‖ < a)
    (has : a ≤ s) : ‖y₀‖ + (s - a) < R := by
  obtain ⟨y, hy1, hy2⟩ := exists_norm_eq_add y₀ (sub_nonneg.2 has)
  have hy : y ∈ ball z s := by
    rw [mem_ball, dist_eq_norm]
    calc ‖y - z‖ = ‖(y - y₀) + (y₀ - z)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - y₀‖ + ‖y₀ - z‖ := norm_add_le _ _
      _ < (s - a) + a := by rw [hy1]; linarith
      _ = s := by ring
  rw [← hy2]
  exact hR y hy

/-- If `V^ε(B_s(z)) ⊆ V^ε(B_ρ)`, the cells cover `ℂ` and the cells meeting `B_ρ` have diameter `≤ δ`, then
`B_s(z) ⊆ B_{ρ + δ}`. -/
theorem norm_lt_of_mem_ball (hε : 0 < ε) (hη : Continuous η) (hsurj : Function.Surjective η) {ρ δ : ℝ}
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ δ) {z : ℂ} {s : ℝ}
    (hsub : cellVertices ε η (ball z s) ⊆ cellVertices ε η (ball 0 ρ)) {y : ℂ} (hy : y ∈ ball z s) :
    ‖y‖ < ρ + δ := by
  obtain ⟨k, hk⟩ := exists_mem_cell hε hsurj y
  obtain ⟨p, hpk, hp⟩ := hsub ⟨y, hk, hy⟩
  have h1 : dist y p ≤ δ := (dist_le_diam_of_mem (cell_isBounded hη k) hk hpk).trans (hdiam k ⟨p, hpk, hp⟩)
  rw [mem_ball_zero_iff] at hp
  rw [dist_eq_norm] at h1
  linarith [norm_sub_norm_le y p]

variable {m : ℤ → ℤ → ℕ} {ρ t : ℝ}

/-- **Lemma 7.2 for a fixed map** (lines 3001-3031), for `s` above the cell size `δ` and above `ε^{ω₀}`. -/
theorem ncard_cellVertices_inter_cluster_le (hε : 0 < ε) (ht : 0 < t) (hρ : 0 < ρ)
    (hη : Continuous η) (hsurj : Function.Surjective η)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    (hR1 : ∀ A : Set ℤ, A.Finite → ∀ b, ∀ a ∈ A,
      mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    {δ ω₀ C₁ c₀ : ℝ} (hC₁ : 0 < C₁) (hc₀ : c₀ = Real.exp (-(3 / 2) * C₁) / 36)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ δ)
    (hgreen : ∀ a ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₀)), ∀ r : ℝ, ε ^ ω₀ ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρ) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
        C₁⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
          greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    {Θ : Set ℤ} (hΘ : Θ ⊆ cellVertices ε η (ball 0 ρ)) (h0 : (0 : ℤ) ∈ Θ) {s : ℝ} {z : ℂ} (hs : 0 < s)
    (hδ : δ ≤ c₀ * s) (hω : ε ^ ω₀ ≤ s / 4) (hεc : 1 / (16 * c₀) ≤ ε⁻¹)
    (hsz : cellVertices ε η (ball z s) ⊆ cellVertices ε η (ball 0 ρ) \ Θ) :
    ((cellVertices ε η (ball z (c₀ * s)) ∩ matedDiscreteCluster m ε η ρ t).ncard : ℝ) ≤
      2 * ⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b := by
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    positivity
  have hc₀le : c₀ ≤ 1 / 36 := by
    rw [hc₀]
    have : Real.exp (-(3 / 2) * C₁) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have h36 : c₀ * s ≤ 1 / 36 * s := mul_le_mul_of_nonneg_right hc₀le hs.le
  have hVρ : (cellVertices ε η (ball 0 ρ)).Finite := hfin.subset (cellVertices_mono ball_subset_closedBall)
  have hΘfin : Θ.Finite := hVρ.subset hΘ
  have hM0 : 0 ≤ ⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b :=
    Real.iSup_nonneg fun c => stoppedOdometer_nonneg hε ht c
  have hoff : ∀ y ∉ Θ, stoppedOdometer m ε η ρ t y ≤ ⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b :=
    fun y hy => stoppedOdometer_le_iSup_vBoundary hε ht hsymm hlf hsucc hfin hlap hΘfin h0 hy
  have hsmall : cellVertices ε η (ball z (c₀ * s)) ⊆ cellVertices ε η (ball z s) :=
    cellVertices_mono (ball_subset_ball (by linarith))
  have hKfin : (cellVertices ε η (ball z (c₀ * s)) ∩ matedDiscreteCluster m ε η ρ t).Finite :=
    hVρ.subset fun k hk => (hsz (hsmall hk.1)).1
  rcases (cellVertices ε η (ball z (c₀ * s)) ∩ matedDiscreteCluster m ε η ρ t).eq_empty_or_nonempty with
    hK | ⟨x₀, hx₀K, -⟩
  · rw [hK, Set.ncard_empty, Nat.cast_zero]
    linarith
  obtain ⟨p₁, hp₁c, hp₁b⟩ := id hx₀K
  -- cells of `V^ε(B_s(z))` have diameter `≤ δ`
  have hcellδ : ∀ k ∈ cellVertices ε η (ball z s), ∀ w ∈ cell ε η k, ∀ w' ∈ cell ε η k, dist w w' ≤ δ :=
    fun k hk w hw w' hw' => (dist_le_diam_of_mem (cell_isBounded hη k) hw hw').trans (hdiam k (hsz hk).1)
  have hcz : dist (vertexPoint ε η x₀) z < 2 * c₀ * s := by
    have h1 := hcellδ x₀ (hsmall hx₀K) _ (vertexPoint_mem_cell hε.le x₀) _ hp₁c
    have h2 : dist p₁ z < c₀ * s := hp₁b
    linarith [dist_triangle (vertexPoint ε η x₀) p₁ z]
  have hKpts : ∀ b ∈ cellVertices ε η (ball z (c₀ * s)), ∀ w ∈ cell ε η b, dist w z < 2 * c₀ * s := by
    intro b hb w hw
    obtain ⟨q, hqc, hqb⟩ := id hb
    have h1 := hcellδ b (hsmall hb) _ hw _ hqc
    have h2 : dist q z < c₀ * s := hqb
    linarith [dist_triangle w q z]
  -- the domain `D` of the comparison function
  have hKD : ∀ b ∈ cellVertices ε η (ball z (c₀ * s)),
      b ∈ interiorCellVertices ε η (ball (vertexPoint ε η x₀) (s / 4)) := by
    intro b hb
    have hclose : ∀ w ∈ cell ε η b, dist w (vertexPoint ε η x₀) < s / 4 := fun w hw => by
      have := hKpts b hb w hw
      linarith [dist_triangle w z (vertexPoint ε η x₀), dist_comm z (vertexPoint ε η x₀)]
    obtain ⟨q, hqc, -⟩ := id hb
    refine ⟨⟨q, hqc, hclose q hqc⟩, ?_⟩
    rintro ⟨w, hwc, hwf⟩
    rw [frontier_ball _ (ne_of_gt (by linarith : (0 : ℝ) < s / 4))] at hwf
    exact (hclose w hwc).ne hwf
  have hball : ball (vertexPoint ε η x₀) (s / 4) ⊆ ball z s := by
    intro y hy
    have : dist y (vertexPoint ε η x₀) < s / 4 := hy
    show dist y z < s
    linarith [dist_triangle y (vertexPoint ε η x₀) z]
  have hDs : interiorCellVertices ε η (ball (vertexPoint ε η x₀) (s / 4)) ⊆ cellVertices ε η (ball z s) :=
    fun k hk => cellVertices_mono hball hk.1
  have hbDs : vBoundary m (interiorCellVertices ε η (ball (vertexPoint ε η x₀) (s / 4))) ⊆
      cellVertices ε η (ball z s) := by
    rintro b ⟨-, a, ha, hab⟩
    obtain ⟨w, hwa, hwb⟩ := hadj a b hab
    exact ⟨w, hwb, hball (cell_subset_ball_of_mem_interiorCellVertices hη ha hwa)⟩
  have hDfin : (interiorCellVertices ε η (ball (vertexPoint ε η x₀) (s / 4))).Finite :=
    hVρ.subset fun k hk => (hsz (hDs hk)).1
  have hΔ : ∀ x ∈ interiorCellVertices ε η (ball (vertexPoint ε η x₀) (s / 4)),
      (if x ∈ hKfin.toFinset then ((mdeg m x : ℕ) : ℝ)⁻¹ else 0) ≤
        mLaplacian m (stoppedOdometer m ε η ρ t) x := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => (hsz (hDs hx)).2 (h ▸ h0)
    split_ifs with hxF
    · have hxΛ : x ∈ matedDiscreteCluster m ε η ρ t := (hKfin.mem_toFinset.1 hxF).2
      have h : mLaplacian m (stoppedOdometer m ε η ρ t) x = ((mdeg m x : ℕ) : ℝ)⁻¹ := hlap x hxΛ hx0
      exact h.ge
    · exact mLaplacian_stoppedOdometer_nonneg hε ht hlap hx0
  have hsum := sum_greenKernel_le_of_laplacian hlf hsucc hDfin (hR1 _ hDfin)
    (fun x => stoppedOdometer_nonneg hε ht x) hΔ (fun y hy => hoff y fun hyΘ => (hsz (hbDs hy)).2 hyΘ)
    (hKD x₀ hx₀K)
  -- Lemma 2.16: `g_D(x₀, b) ≥ 1/2`
  have hR : ∀ y ∈ ball z s, ‖y‖ < ρ + δ := fun y hy =>
    norm_lt_of_mem_ball hε hη hsurj hdiam (fun k hk => (hsz hk).1) hy
  have hx₀mem : x₀ ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₀)) := by
    refine ⟨p₁, hp₁c, ?_⟩
    have hp : ‖p₁ - z‖ < c₀ * s := by
      rw [← dist_eq_norm]
      exact hp₁b
    have h1 := norm_add_lt_of_ball hR hp (by linarith)
    rw [mem_ball_zero_iff]
    linarith
  have hcR := norm_add_lt_of_ball hR (show ‖vertexPoint ε η x₀ - z‖ < 2 * c₀ * s by
    rw [← dist_eq_norm]
    exact hcz) (by linarith)
  have hr2 : s / 4 ≤ infDist (vertexPoint ε η x₀) (sphere 0 ρ) := by
    have hne : (sphere (0 : ℂ) ρ).Nonempty :=
      ⟨(ρ : ℂ), by rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]⟩
    rw [le_infDist hne]
    intro y hy
    rw [mem_sphere_zero_iff_norm] at hy
    rw [dist_eq_norm, norm_sub_rev]
    linarith [norm_sub_norm_le y (vertexPoint ε η x₀)]
  have hE : Real.exp ((3 / 2) * C₁) ≤ 1 / (16 * c₀) := by
    rw [le_div_iff₀ (by linarith), hc₀]
    have : Real.exp ((3 / 2) * C₁) * Real.exp (-(3 / 2) * C₁) = 1 := by
      rw [← Real.exp_add, show (3 / 2) * C₁ + -(3 / 2) * C₁ = 0 by ring, Real.exp_zero]
    nlinarith [this]
  have hlow : ∀ b ∈ cellVertices ε η (ball z (c₀ * s)),
      (1 / 2 : ℝ) ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η x₀) (s / 4))) x₀ b := by
    intro b hb
    obtain ⟨q, hqc, hqb⟩ := id hb
    have hb3 : b ∈ cellVertices ε η (ball (vertexPoint ε η x₀) (s / 4 / 3)) := by
      refine ⟨q, hqc, ?_⟩
      have : dist q z < c₀ * s := hqb
      show dist q (vertexPoint ε η x₀) < s / 4 / 3
      linarith [dist_triangle q z (vertexPoint ε η x₀), dist_comm z (vertexPoint ε η x₀)]
    have hg := hgreen x₀ hx₀mem (s / 4) hω hr2 b hb3
    have hXge : Real.exp ((3 / 2) * C₁) ≤ (if vertexPoint ε η x₀ = vertexPoint ε η b then ε⁻¹
        else min (s / 4 / ‖vertexPoint ε η x₀ - vertexPoint ε η b‖) ε⁻¹) := by
      split_ifs with heq
      · exact hE.trans hεc
      · refine le_min (hE.trans ?_) (hE.trans hεc)
        have hd : 0 < ‖vertexPoint ε η x₀ - vertexPoint ε η b‖ := norm_pos_iff.2 (sub_ne_zero.2 heq)
        have hd' : ‖vertexPoint ε η x₀ - vertexPoint ε η b‖ < 4 * c₀ * s := by
          have := hKpts b hb _ (vertexPoint_mem_cell hε.le b)
          rw [← dist_eq_norm, dist_comm]
          linarith [dist_triangle (vertexPoint ε η b) z (vertexPoint ε η x₀), dist_comm z (vertexPoint ε η x₀)]
        rw [div_le_div_iff₀ (by linarith) hd]
        linarith
    have hlog := Real.log_le_log (Real.exp_pos _) hXge
    rw [Real.log_exp] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hC₁.le)
    have hval : C₁⁻¹ * ((3 / 2) * C₁) = 3 / 2 := by
      rw [mul_comm (3 / 2 : ℝ) C₁, ← mul_assoc, inv_mul_cancel₀ hC₁.ne', one_mul]
    linarith
  have hcard : ∑ _b ∈ hKfin.toFinset, (1 / 2 : ℝ) ≤
      ∑ b ∈ hKfin.toFinset, greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η x₀) (s / 4))) x₀ b :=
    Finset.sum_le_sum fun b hb => hlow b (hKfin.mem_toFinset.1 hb).1
  rw [Finset.sum_const, nsmul_eq_mul] at hcard
  rw [Set.ncard_eq_toFinset_card _ hKfin]
  linarith

end MatedCRT.Sec7
