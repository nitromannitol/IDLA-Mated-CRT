import MatedCRT.Proofs.Sec4.SubsequentialProperties.LaplacianUpper
import HarmonicBalls.Proofs.Potential.GreenBall
import HarmonicBalls.Proofs.Potential.GreenPositivity

/-!
# Lemma 4.8, item 3: discs in the non-coincidence set eventually lie in the discrete cluster

Step 3 of the proof of Lemma 4.8 (paper/idla_mated_crt-corrected.tex, l.1892-1909, (discrete-cluster-contained)):
if `cl(B_s(z)) ⊆ {x ∈ B_ρ : x = 0 ∨ w(x) > -t (c₀/6) G_{B_ρ}(0, x)}`, then for small `ε` along the subsequence,
`V^ε(B_s(z)) \ V^ε(∂B_s(z)) ⊆ Λ^ε_t`.

* away from the pole: a positive gap on a compact set (`exists_pos_le_of_isCompact`), the uniform convergence of the
  rescaled Green's function on annuli (Lemma 3.3 along a subsequence, `ae_greenKernel_unif_annuli`) and of the
  rescaled odometer, at a point of the cell whose least cell is the vertex;
* at the pole (the paper's "the pole `0` included"): `G_{B_ρ}(0, ·)` is large near `0`
  (`log_div_le_greenFunction`, HarmonicBalls); the discrete minimum principle for the superharmonic
  `g^ε_{B_ρ}(0, ·)` (`greenKernelLaplacianStep`, Lemma 2.13) bounds the discrete obstacle near `0` by its values on
  `V^ε(∂B_{r₁})`, where Lemma 3.3 applies.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls Real

/-- The rescaled Green's function `ḡ^ε = m_ε⁻¹ ε⁻¹ g^ε_{B_ρ}(a^ε_0, a^ε_x)` of Lemma 3.3 (`y = 0`, `B_r(z) = B_ρ`). -/
noncomputable def rescaledGreenKernel {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ ε : ℝ) (ω : Ω)
    (x : ℂ) : ℝ :=
  rescale (S.mε ε) ε (S.η ω) (fun a => ε⁻¹ * greenKernel (S.mult ε ω)
    (interiorCellVertices ε (S.η ω) (ball 0 ρ)) (vertexOf ε (S.η ω) 0) a) x

/-- **Lemma 3.3 along a subsequence, uniformly on annuli**: almost surely, for every `j`, eventually
`|ḡ^ε - (c₀/6) G_{B_ρ}(0, ·)| ≤ 1/(j+1)` on `cl(B_ρ) \ B_{ρ/(j+2)}`. -/
theorem ae_greenKernel_unif_annuli (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ' : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {εs : ℕ → ℝ} (hε : ∀ n, 0 < εs n)
    (hε0 : Tendsto εs atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ j : ℕ, ∀ᶠ k in atTop,
      ∀ x ∈ closedBall (0 : ℂ) ρ \ ball 0 (ρ / ((j : ℝ) + 2)),
        |rescaledGreenKernel S ρ (εs (φ k)) ω x - S.c₀ / 6 * greenFunction (ball 0 ρ) 0 x| ≤
          1 / ((j : ℝ) + 1) := by
  have hj2 : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 2 := fun j => by positivity
  have hr_pos : ∀ j : ℕ, 0 < ρ / ((j : ℝ) + 2) := fun j => div_pos hρ (hj2 j)
  have hr_lt : ∀ j : ℕ, ρ / ((j : ℝ) + 2) < ρ := fun j =>
    div_lt_self hρ (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith)
  have hδ : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  have hρn : ‖(ρ : ℂ)‖ = ρ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have hsub : ∀ j : ℕ, closedBall (0 : ℂ) ρ \ ball 0 (ρ / ((j : ℝ) + 2)) ⊆ closedBall 0 ρ \ {0} :=
    fun j y hy => ⟨hy.1, fun h0 => hy.2 (by rw [Set.mem_singleton_iff.1 h0]; exact mem_ball_self (hr_pos j))⟩
  have hdist : ∀ j : ℕ, 0 < infDist (0 : ℂ) (closedBall (0 : ℂ) ρ \ ball 0 (ρ / ((j : ℝ) + 2))) := by
    intro j
    have hne : (closedBall (0 : ℂ) ρ \ ball 0 (ρ / ((j : ℝ) + 2))).Nonempty :=
      ⟨(ρ : ℂ), mem_closedBall.2 (le_of_eq (by rw [dist_zero_right, hρn])),
        fun h => lt_asymm (hr_lt j) (by rwa [mem_ball, dist_zero_right, hρn] at h)⟩
    refine lt_of_lt_of_le (hr_pos j) ((le_infDist hne).2 fun y hy => ?_)
    have hy2 := hy.2
    rw [mem_ball] at hy2
    rw [dist_comm]
    exact not_lt.1 hy2
  obtain ⟨φ, hφ, hφae⟩ := exists_strictMono_ae_eventually_mem_all (fun j => h33 γ hγ hγ' ρ hρ hρ' Ω S hS ρ 0 0 hρ
    subset_rfl (mem_ball_self hρ) _ (hδ j) _ (hsub j) (hdist j)) hε hε0
  exact ⟨φ, hφ, hφae⟩

/-- `K G_{B_ρ}(0, ·)` is large near the pole, for `K > 0`. -/
theorem exists_radius_le_greenFunction {ρ K : ℝ} (hρ : 0 < ρ) (hK : 0 < K) (M : ℝ) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ ρ / 4 ∧ ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ ≤ 2 * r₁ →
      M ≤ K * greenFunction (ball 0 ρ) 0 x := by
  set L : ℝ := 2 * π * M / K with hL
  refine ⟨min (ρ / 8) (ρ / 2 * Real.exp (-L) / 2), lt_min (by positivity) (by positivity),
    (min_le_left _ _).trans (by linarith), fun x hx hxr => ?_⟩
  have hxr' : ‖x‖ ≤ ρ / 2 * Real.exp (-L) := by
    have := min_le_right (ρ / 8) (ρ / 2 * Real.exp (-L) / 2)
    linarith
  have hxρ : ‖x‖ < ρ / 2 := by
    have := min_le_left (ρ / 8) (ρ / 2 * Real.exp (-L) / 2)
    linarith
  have hG : (2 * π)⁻¹ * Real.log (ρ / 2 / ‖x - 0‖) ≤ greenFunction (ball 0 ρ) x 0 :=
    log_div_le_greenFunction isBounded_ball (by positivity) (closedBall_subset_ball (by linarith))
      (by rwa [sub_zero]) (by rwa [sub_zero])
  rw [sub_zero, ← greenFunction_ball_comm] at hG
  have hlog : L ≤ Real.log (ρ / 2 / ‖x‖) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hx]
    calc Real.exp L * ‖x‖ ≤ Real.exp L * (ρ / 2 * Real.exp (-L)) :=
          mul_le_mul_of_nonneg_left hxr' (Real.exp_pos L).le
      _ = ρ / 2 := by rw [Real.exp_neg]; field_simp
  have hπ : 0 < 2 * π := by positivity
  calc M = K * ((2 * π)⁻¹ * L) := by rw [hL]; field_simp
    _ ≤ K * ((2 * π)⁻¹ * Real.log (ρ / 2 / ‖x‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hπ.le)) hK.le
    _ ≤ K * greenFunction (ball 0 ρ) 0 x := mul_le_mul_of_nonneg_left hG hK.le

/-- A function continuous and positive on a compact set has a positive lower bound there. -/
theorem exists_pos_le_of_isCompact {K : Set ℂ} (hK : IsCompact K) {F : ℂ → ℝ} (hF : ContinuousOn F K)
    (hpos : ∀ x ∈ K, 0 < F x) : ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ x ∈ K, g₀ ≤ F x := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, fun x hx => by rw [hKe] at hx; exact absurd hx (Set.notMem_empty x)⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne hF
    exact ⟨F x₀, hpos x₀ hx₀, fun x hx => hmin hx⟩

/-- **Discs in the non-coincidence set eventually lie in the discrete cluster** (pathwise). -/
theorem eventually_interiorCellVertices_subset_cluster {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) {ρ : ℝ} (hρ : 0 < ρ)
    (harea : IsAreaParametrized (S.μ ω) (S.η ω)) (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hlf : ∀ ε, 0 < ε → IsLocallyFiniteMult (S.mult ε ω))
    (hcells : ∀ ε, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmax : ∀ ε, 0 < ε → ∀ A : Set ℤ, A.Nonempty → A.Finite → ∀ u : ℤ → ℝ, IsSubharmonicOn (S.mult ε ω) u A →
      ∀ a ∈ A, ∃ b ∈ vBoundary (S.mult ε ω) A, u a ≤ u b)
    {εk : ℕ → ℝ} (hεk : ∀ k, 0 < εk k) (hεk0 : Tendsto εk atTop (𝓝 0))
    (hv0 : ∀ ε, 0 < ε → vertexOf ε (S.η ω) 0 = 0)
    (hg : ∀ j : ℕ, ∀ᶠ k in atTop, ∀ x ∈ closedBall (0 : ℂ) ρ \ ball 0 (ρ / ((j : ℝ) + 2)),
      |rescaledGreenKernel S ρ (εk k) ω x - S.c₀ / 6 * greenFunction (ball 0 ρ) 0 x| ≤ 1 / ((j : ℝ) + 1))
    (hc : 0 < S.c₀ / 6) {t : ℝ} (ht : 0 < t) {w : ℂ → ℝ} (hwc : ContinuousOn w (closedBall 0 ρ))
    (hconv : TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εk k) ω) w atTop
      (closedBall 0 ρ))
    {z : ℂ} {s : ℝ} (hs : 0 < s)
    (hD : closedBall z s ⊆
      {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x < w x}) :
    ∀ᶠ k in atTop, interiorCellVertices (εk k) (S.η ω) (ball z s) ⊆
      matedDiscreteCluster (S.mult (εk k) ω) (εk k) (S.η ω) ρ t := by
  -- a lower bound for `w`
  obtain ⟨b₀, hb₀⟩ := (isCompact_closedBall (0 : ℂ) ρ).bddBelow_image hwc
  have hwB : ∀ x ∈ closedBall (0 : ℂ) ρ, b₀ ≤ w x := fun x hx => hb₀ ⟨x, hx, rfl⟩
  -- the pole radius
  obtain ⟨r₁, hr₁, hr₁ρ, hr₁G⟩ := exists_radius_le_greenFunction hρ (mul_pos ht hc) (-b₀ + 3)
  -- the gap away from the pole
  have hKc : IsCompact (closedBall z s \ ball 0 (r₁ / 2)) := (isCompact_closedBall z s).diff isOpen_ball
  obtain ⟨g₀, hg₀, hgap⟩ := exists_pos_le_of_isCompact hKc
    (F := fun x => w x + t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)
    (by
      refine (hwc.mono fun x hx => ball_subset_closedBall (hD hx.1).1).add
        (ContinuousOn.mul continuousOn_const ((continuousOn_greenFunction_ball (mem_ball_self hρ)).mono ?_))
      intro x hx h0
      rw [Set.mem_singleton_iff] at h0
      exact hx.2 (by rw [h0]; exact mem_ball_self (by linarith)))
    (by
      intro x hx
      have hx0 : x ≠ 0 := fun h0 => hx.2 (by rw [h0]; exact mem_ball_self (by linarith))
      rcases (hD hx.1).2 with h | h
      · exact absurd h hx0
      · show 0 < w x + t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x
        linarith)
  -- accuracies
  obtain ⟨g', hg'⟩ : ∃ g' : ℝ, g' = min g₀ 1 := ⟨_, rfl⟩
  have hg'pos : 0 < g' := by rw [hg']; exact lt_min hg₀ one_pos
  have hg'1 : g' ≤ g₀ := by rw [hg']; exact min_le_left _ _
  have hg'2 : g' ≤ 1 := by rw [hg']; exact min_le_right _ _
  obtain ⟨j, hj⟩ := exists_nat_gt (max (4 * t / g') (2 * ρ / r₁))
  have hj1 : t / ((j : ℝ) + 1) < g' / 4 := by
    have h := (le_max_left _ _).trans_lt hj
    rw [div_lt_iff₀ hg'pos] at h
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hj2 : ρ / ((j : ℝ) + 2) ≤ r₁ / 2 := by
    have h := (le_max_right _ _).trans_lt hj
    rw [div_lt_iff₀ hr₁] at h
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- cell sizes
  obtain ⟨ε₀, hε₀, hcellsz⟩ := Tightness.exists_cell_near_vertexPoint harea.1 hp
    (isBounded_closedBall (x := (0 : ℂ)) (r := ρ)) (s := r₁ / 4) (by positivity)
  have hunif := Metric.tendstoUniformlyOn_iff.1 hconv (g' / 4) (by positivity)
  filter_upwards [hunif, hg j, hεk0.eventually (gt_mem_nhds hε₀)] with k hunifk hgk hεk₀
  -- abbreviations
  have hε := hεk k
  have hlfk := hlf (εk k) hε
  have hA : (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)).Finite :=
    (Tightness.cellVertices_finite harea.1 hp hε isBounded_ball).subset fun b hb => hb.1
  have hm0 : 0 ≤ (S.mε (εk k))⁻¹ := inv_nonneg.2 (S.mε_nonneg _)
  -- the rescaled obstacle at a point whose least cell is `a`
  have hobs : ∀ (a : ℤ) (x : ℂ), vertexOf (εk k) (S.η ω) x = a →
      (S.mε (εk k))⁻¹ * matedObstacle (S.mult (εk k) ω) (εk k) (S.η ω) ρ t a =
        -t * rescaledGreenKernel S ρ (εk k) ω x := by
    intro a x hx
    simp only [rescaledGreenKernel, rescale, matedObstacle, ballInterior, hv0 _ hε, hx]
    ring
  -- the rescaled odometer at such a point
  have hodo : ∀ (a : ℤ) (x : ℂ), vertexOf (εk k) (S.η ω) x = a → x ∈ closedBall (0 : ℂ) ρ →
      w x - g' / 4 < (S.mε (εk k))⁻¹ * matedLeastSupersolution (S.mult (εk k) ω) (εk k) (S.η ω) ρ t a := by
    intro a x hx hxB
    have h := hunifk x hxB
    rw [Real.dist_eq, abs_lt] at h
    have he : rescaledMatedLeastSupersolution S ρ t (εk k) ω x =
        (S.mε (εk k))⁻¹ * matedLeastSupersolution (S.mult (εk k) ω) (εk k) (S.η ω) ρ t a := by
      simp only [rescaledMatedLeastSupersolution, rescale, hx]
    linarith [h.2]
  -- the Green's function lower bound at a point of an annulus
  have hgreen : ∀ x : ℂ, r₁ / 2 ≤ ‖x‖ → ‖x‖ ≤ ρ →
      S.c₀ / 6 * greenFunction (ball 0 ρ) 0 x - 1 / ((j : ℝ) + 1) ≤ rescaledGreenKernel S ρ (εk k) ω x := by
    intro x hx1 hx2
    have hxO : x ∈ closedBall (0 : ℂ) ρ \ ball 0 (ρ / ((j : ℝ) + 2)) := by
      refine ⟨by rw [mem_closedBall, dist_zero_right]; exact hx2, fun h => ?_⟩
      rw [mem_ball, dist_zero_right] at h
      linarith
    linarith [(abs_le.1 (hgk x hxO)).1]
  intro a ha
  have hcell := cell_subset_ball_of_mem_interiorCellVertices harea.1 hs ha
  obtain ⟨xa, hxa, hva⟩ := exists_vertexOf_eq_of_area_parametrized harea hp hε a
  have hxaD : xa ∈ closedBall z s := ball_subset_closedBall (hcell hxa)
  have hxaB : xa ∈ ball (0 : ℂ) ρ := (hD hxaD).1
  have hxaB' : xa ∈ closedBall (0 : ℂ) ρ := ball_subset_closedBall hxaB
  have haB : a ∈ cellVertices (εk k) (S.η ω) (closedBall 0 ρ) :=
    show (cell (εk k) (S.η ω) a ∩ closedBall 0 ρ).Nonempty from ⟨xa, hxa, hxaB'⟩
  refine ⟨show (cell (εk k) (S.η ω) a ∩ ball 0 ρ).Nonempty from ⟨xa, hxa, hxaB⟩, ?_⟩
  -- it remains: `obstacle a < w̃ a`
  refine lt_of_mul_lt_mul_left ?_ hm0
  have hwa := hodo a xa hva hxaB'
  have hwaB := hwB xa hxaB'
  by_cases hfar : r₁ / 2 ≤ ‖xa‖
  · -- away from the pole
    have hxK : xa ∈ closedBall z s \ ball 0 (r₁ / 2) := ⟨hxaD, by
      rw [mem_ball, dist_zero_right]; exact not_lt.2 hfar⟩
    have hgapx : g₀ ≤ w xa + t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 xa := hgap xa hxK
    have hgx := hgreen xa hfar (by rw [mem_closedBall, dist_zero_right] at hxaB'; exact hxaB')
    rw [hobs a xa hva]
    have : -t * rescaledGreenKernel S ρ (εk k) ω xa ≤
        -t * (S.c₀ / 6 * greenFunction (ball 0 ρ) 0 xa) + t / ((j : ℝ) + 1) := by
      have := mul_le_mul_of_nonneg_left hgx ht.le
      rw [mul_sub] at this
      have e : t * (1 / ((j : ℝ) + 1)) = t / ((j : ℝ) + 1) := by ring
      linarith
    linarith
  · -- near the pole
    push Not at hfar
    -- the cell of `a` lies in `B_{r₁}`
    have hcellr : cell (εk k) (S.η ω) a ⊆ ball (0 : ℂ) r₁ := by
      intro y hy
      have h1 := hcellsz (εk k) hε hεk₀ a haB y hy
      have h2 := hcellsz (εk k) hε hεk₀ a haB xa hxa
      rw [mem_ball, dist_zero_right]
      have h3 := norm_sub_norm_le y xa
      have h4 := norm_sub_le_norm_sub_add_norm_sub y (vertexPoint (εk k) (S.η ω) a) xa
      rw [norm_sub_rev (vertexPoint (εk k) (S.η ω) a) xa] at h4
      linarith
    have hr₁ρ' : r₁ < ρ := by linarith
    have haA₁ : a ∈ interiorCellVertices (εk k) (S.η ω) (ball 0 r₁) := by
      refine ⟨show (cell (εk k) (S.η ω) a ∩ ball 0 r₁).Nonempty from ⟨xa, hxa, hcellr hxa⟩, ?_⟩
      rintro ⟨y, hy, hys⟩
      rw [frontier_ball 0 hr₁.ne', mem_sphere, dist_zero_right] at hys
      have := hcellr hy
      rw [mem_ball, dist_zero_right] at this
      linarith
    have hA₁sub : interiorCellVertices (εk k) (S.η ω) (ball 0 r₁) ⊆
        interiorCellVertices (εk k) (S.η ω) (ball 0 ρ) :=
      interiorCellVertices_subset_of_ball_subset harea.1 hr₁ hρ (ball_subset_ball hr₁ρ'.le)
    have hA₁ : (interiorCellVertices (εk k) (S.η ω) (ball 0 r₁)).Finite := hA.subset hA₁sub
    -- the origin is an interior vertex of `B_ρ`
    have h0A : (0 : ℤ) ∈ interiorCellVertices (εk k) (S.η ω) (ball 0 ρ) := by
      have hvp0 : vertexPoint (εk k) (S.η ω) 0 = 0 := by
        simp only [vertexPoint, Int.cast_zero, mul_zero]; exact harea.2.1
      have h0B : (0 : ℤ) ∈ cellVertices (εk k) (S.η ω) (closedBall 0 ρ) :=
        show (cell (εk k) (S.η ω) 0 ∩ closedBall 0 ρ).Nonempty from
          ⟨vertexPoint (εk k) (S.η ω) 0, Tightness.vertexPoint_mem_cell hε 0,
            by rw [hvp0]; exact mem_closedBall_self hρ.le⟩
      have hc0 : ∀ y ∈ cell (εk k) (S.η ω) 0, ‖y‖ < r₁ / 4 := fun y hy => by
        have := hcellsz (εk k) hε hεk₀ 0 h0B y hy
        rwa [hvp0, sub_zero] at this
      refine ⟨show (cell (εk k) (S.η ω) 0 ∩ ball 0 ρ).Nonempty from
          ⟨vertexPoint (εk k) (S.η ω) 0, Tightness.vertexPoint_mem_cell hε 0,
            by rw [hvp0]; exact mem_ball_self hρ⟩, ?_⟩
      rintro ⟨y, hy, hys⟩
      rw [frontier_ball 0 hρ.ne', mem_sphere, dist_zero_right] at hys
      have := hc0 y hy
      linarith
    -- the discrete minimum principle for `g^ε(0, ·)` on `V^ε(B_{r₁}) \ V^ε(∂B_{r₁})`
    have hsubu : IsSubharmonicOn (S.mult (εk k) ω)
        (fun b => (-1 : ℝ) * greenKernel (S.mult (εk k) ω) (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)) 0 b)
        (interiorCellVertices (εk k) (S.η ω) (ball 0 r₁)) := by
      intro b hb
      rw [mLaplacian_const_mul, greenKernelLaplacianStep (S.mult (εk k) ω) _ (S.mult_symm _ ω) hlfk
        (fun i => S.mult_succ_ne_zero hε.le ω i) hA 0 h0A b (hA₁sub hb)]
      have h1 : (0 : ℝ) ≤ ((mdeg (S.mult (εk k) ω) 0 : ℕ) : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
      have h2 : (0 : ℝ) ≤ if b = 0 then 1 else 0 := by split_ifs <;> norm_num
      nlinarith [mul_nonneg h1 h2]
    obtain ⟨b, hb, hab⟩ := hmax (εk k) hε _ ⟨a, haA₁⟩ hA₁ _ hsubu a haA₁
    have hab' : (-1 : ℝ) * greenKernel (S.mult (εk k) ω) (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)) 0 a ≤
        (-1 : ℝ) * greenKernel (S.mult (εk k) ω) (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)) 0 b := hab
    have hgab : greenKernel (S.mult (εk k) ω) (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)) 0 b ≤
        greenKernel (S.mult (εk k) ω) (interiorCellVertices (εk k) (S.η ω) (ball 0 ρ)) 0 a := by linarith
    -- the boundary vertex `b`
    obtain ⟨yb, hybb, hybs⟩ := vBoundary_interiorCellVertices_subset harea.1 hr₁ (hcells (εk k) hε) hb
    rw [mem_sphere, dist_zero_right] at hybs
    have hbB : b ∈ cellVertices (εk k) (S.η ω) (closedBall 0 ρ) :=
      show (cell (εk k) (S.η ω) b ∩ closedBall 0 ρ).Nonempty from
        ⟨yb, hybb, by rw [mem_closedBall, dist_zero_right]; linarith⟩
    obtain ⟨xb, hxb, hvb⟩ := exists_vertexOf_eq_of_area_parametrized harea hp hε b
    have hxbn : r₁ / 2 ≤ ‖xb‖ ∧ ‖xb‖ ≤ 2 * r₁ := by
      have h1 := hcellsz (εk k) hε hεk₀ b hbB xb hxb
      have h2 := hcellsz (εk k) hε hεk₀ b hbB yb hybb
      have h4 := norm_sub_le_norm_sub_add_norm_sub xb (vertexPoint (εk k) (S.η ω) b) yb
      rw [norm_sub_rev (vertexPoint (εk k) (S.η ω) b) yb] at h4
      have h5 := norm_sub_norm_le xb yb
      have h6 := norm_sub_norm_le yb xb
      rw [norm_sub_rev yb xb] at h6
      constructor <;> linarith
    have hxbpos : 0 < ‖xb‖ := by linarith [hxbn.1]
    have hGb := hr₁G xb hxbpos hxbn.2
    have hgxb := hgreen xb hxbn.1 (by linarith [hxbn.2])
    -- the obstacle at `a` is at most the obstacle at `b`
    have hobsab : (S.mε (εk k))⁻¹ * matedObstacle (S.mult (εk k) ω) (εk k) (S.η ω) ρ t a ≤
        (S.mε (εk k))⁻¹ * matedObstacle (S.mult (εk k) ω) (εk k) (S.η ω) ρ t b := by
      refine mul_le_mul_of_nonneg_left ?_ hm0
      simp only [matedObstacle, ballInterior]
      have htε : 0 ≤ t / εk k := div_nonneg ht.le hε.le
      exact mul_le_mul_of_nonpos_left hgab (neg_nonpos.2 htε)
    rw [hobs b xb hvb] at hobsab
    have hb1 : -t * rescaledGreenKernel S ρ (εk k) ω xb ≤
        -t * (S.c₀ / 6 * greenFunction (ball 0 ρ) 0 xb) + t / ((j : ℝ) + 1) := by
      have := mul_le_mul_of_nonneg_left hgxb ht.le
      rw [mul_sub] at this
      have e : t * (1 / ((j : ℝ) + 1)) = t / ((j : ℝ) + 1) := by ring
      linarith
    have hb2 : -t * (S.c₀ / 6 * greenFunction (ball 0 ρ) 0 xb) ≤ b₀ - 3 := by
      have e : -t * (S.c₀ / 6 * greenFunction (ball 0 ρ) 0 xb) =
          -(t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 xb) := by ring
      linarith
    linarith

end MatedCRT
