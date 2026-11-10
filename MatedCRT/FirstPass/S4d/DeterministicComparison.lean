import MatedCRT.FirstPass.S4d.StrictGapReduction
import MatedCRT.FirstPass.S4d.ExitTimeBall
import MatedCRT.FirstPass.Frozen.S2g
import MatedCRT.FirstPass.Frozen.S5c
import MatedCRT.FirstPass.Frozen.S4d
import HarmonicBalls.Draft.Section2
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-!
# FIRST PASS, Proposition 4.2 (q4): the deterministic comparison `Λ_s ⊆ 𝒞_t` (ChatGPT Section 2)

Task fp-S4d-4-2-assembly. For one realization of the cone family and `0 < s < t` with `t < T_ρ`, the earlier harmonic
ball lies in the unregularized obstacle cluster at time `t` (`StrictGapDeterministicComparisonStep`).

Argument (notes/fp-gaps/CHATGPT-4-2-strict-gap-proof.md, Section 2), with `w_u` the least supersolution, `G` the disc
Green function `G_{B_ρ}(0,·)`, `W = Λ_s \ {0}`, and `f = v_t - v_s = (w_t - w_s) + (t - s) G`, `v_u = w_u + u G`:
* `v_u ≥ 0` off the pole (`leastSupersolution_ge_obstacle`, from the infimum over supersolutions);
* `v_s ≤ 0` off `Λ_s` (`odometer_nonpos_of_not_mem`, from `Λ_s = int cl C_s`);
* `Δf ≤ 0` in `W` (`laplacianLE_sub_of_hasLaplacian` and HB `LaplacianLE.add_const_mul_of_hasLaplacian_zero`);
* `f → +∞` at the pole; `f ≥ 0` on `W` by the minimum principle on `Λ_s \ B̄_a`; `f > 0` on `W` by the strong minimum
  principle on the connected set `W` (puncture connectedness);
* hence `v_t = v_s + f > 0` on `W`, so `Λ_s ⊆ 𝒞_t`.

External inputs (explicit hypotheses): `GreenFunctionBallStmt` (HB Draft), `FrozenPunctureConnected` (Frozen/S4d.lean),
`FPStrongMinimumPrinciple` (Frozen/S5c.lean), `FrozenSuperharmonicMinimumPrinciple` and `FrozenGreenDiscPole`
(Frozen/S2g.lean).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls

/-- Lower bound of the least supersolution (ChatGPT Section 2.1, eq. (7)): `w_u(x) ≥ -u G(0,x)` off the pole, for
`u ≥ 0`, since the infimum runs over supersolutions, each bounded below by the obstacle, and `0` is a supersolution. -/
theorem leastSupersolution_ge_obstacle {μ : Measure ℂ} {r u : ℝ} (hu : 0 ≤ u) {x : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ 0) :
    -u * greenFunction (ball 0 r) 0 x ≤ leastSupersolution μ r 0 u x := by
  unfold leastSupersolution
  refine le_csInf ⟨(0 : ℂ → ℝ) x, 0, zero_mem_supersolutions μ r 0 hu, rfl⟩ ?_
  rintro _ ⟨w, hw, rfl⟩
  exact hw.2.2 x hx hxz

/-- Boundary value (ChatGPT Section 2.1, eq. (10)): if `Λ = int cl C_u` (obstacle characterization), then
`v_u = w_u + u G ≤ 0` at every `x ∈ B_ρ \ {0}` outside `Λ`. Proof: if `v_u(x) > 0`, continuity gives a neighbourhood of
`x` inside `C_u`, hence `x ∈ int cl C_u = Λ`. -/
theorem odometer_nonpos_of_not_mem {μ : Measure ℂ} {ρ u : ℝ} {Λ : Set ℂ}
    (hobs : Λ = interior (closure (cluster μ ρ 0 u)))
    (hwc : ContinuousOn (leastSupersolution μ ρ 0 u) (closedBall 0 ρ))
    (hGc : ContinuousOn (greenFunction (ball 0 ρ) 0) (closedBall 0 ρ \ {0}))
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) ρ) (hx0 : x ≠ 0) (hxΛ : x ∉ Λ) :
    leastSupersolution μ ρ 0 u x + u * greenFunction (ball 0 ρ) 0 x ≤ 0 := by
  by_contra hpos0
  have hpos := not_le.mp hpos0
  have hwA : ContinuousAt (leastSupersolution μ ρ 0 u) x :=
    hwc.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
  have hGA : ContinuousAt (greenFunction (ball 0 ρ) 0) x :=
    hGc.continuousAt (mem_of_superset ((isOpen_ball.inter isOpen_compl_singleton).mem_nhds ⟨hx, hx0⟩)
      (fun y hy => ⟨ball_subset_closedBall hy.1, hy.2⟩))
  have hvA : ContinuousAt (fun y => leastSupersolution μ ρ 0 u y + u * greenFunction (ball 0 ρ) 0 y) x :=
    hwA.add (continuousAt_const.mul hGA)
  have hev : ∀ᶠ y in 𝓝 x, 0 < leastSupersolution μ ρ 0 u y + u * greenFunction (ball 0 ρ) 0 y :=
    Filter.Tendsto.eventually hvA (lt_mem_nhds hpos)
  have hcl : cluster μ ρ 0 u ∈ 𝓝 x := by
    filter_upwards [hev, isOpen_ball.mem_nhds hx] with y hy hyb
    exact ⟨hyb, Or.inr (by linarith)⟩
  have hint : x ∈ interior (cluster μ ρ 0 u) := mem_interior_iff_mem_nhds.mpr hcl
  apply hxΛ
  rw [hobs]
  exact interior_mono subset_closure hint

/-- Distributional comparison of the odometer difference (ChatGPT Section 2.2, eq. (12)): if `W ⊆ Λ_s ⊆ Λ_t` and
`Δw_u = μ|Λ_u` in `U ⊇ W`, then `Δ(w_t - w_s) ≤ 0` in `W`, because `∫ φ dμ|Λ_t = ∫ φ dμ|Λ_s` for every test function
`φ` supported in `W`. -/
theorem laplacianLE_sub_of_hasLaplacian {μ : Measure ℂ} {U W Λs Λt : Set ℂ} {wt ws : ℂ → ℝ}
    (hW : W ⊆ Λs) (hst : Λs ⊆ Λt) (hWU : W ⊆ U)
    (hwt : HasLaplacian wt (μ.restrict Λt) 0 U) (hws : HasLaplacian ws (μ.restrict Λs) 0 U) :
    LaplacianLE (fun x => wt x - ws x) 0 W := by
  refine ⟨(hwt.1.sub hws.1).mono_set hWU, fun φ hφ _ _ => ?_⟩
  have hφU : IsTestFunction U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hWU⟩
  have hzero : ∀ x, x ∉ Λs → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hW (hφ.2.2 h)))
  have hsame : ∫ x, φ x ∂(μ.restrict Λt) = ∫ x, φ x ∂(μ.restrict Λs) := by
    have h1 : ∫ x, φ x ∂(μ.restrict Λt) = ∫ x, φ x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hzero x (fun h => hx (hst h)))
    have h2 : ∫ x, φ x ∂(μ.restrict Λs) = ∫ x, φ x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    rw [h1, h2]
  have hi1 := integrable_mul_laplacian_of_test hwt.1 hφU
  have hi2 := integrable_mul_laplacian_of_test hws.1 hφU
  have hwt' := (hwt.2 φ hφU).2.2
  have hws' := (hws.2 φ hφU).2.2
  simp only [sub_mul]
  rw [integral_sub hi1 hi2, hwt', hws']
  simp only [integral_zero_measure, sub_zero]
  linarith [hsame]

/-- The disc Green function, as a distribution on `B_ρ`, has zero Laplacian in an open set `W` not containing the pole:
`ΔG = -δ_0` in `B_ρ` (HB `GreenFunctionBallStmt`) and `φ(0) = 0` for test functions supported in `W`. -/
theorem hasLaplacian_zero_of_pole_notMem {G : ℂ → ℝ} {U W : Set ℂ}
    (hG : HasLaplacian G 0 (Measure.dirac 0) U) (hWU : W ⊆ U) (h0 : (0 : ℂ) ∉ W) :
    HasLaplacian G 0 0 W := by
  refine ⟨hG.1.mono_set hWU, fun φ hφ => ?_⟩
  have hφU : IsTestFunction U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hWU⟩
  obtain ⟨-, -, hG'⟩ := hG.2 φ hφU
  have h0φ : φ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h => h0 (hφ.2.2 h))
  rw [integral_zero_measure, integral_dirac, h0φ] at hG'
  refine ⟨integrable_zero_measure, integrable_zero_measure, ?_⟩
  simp only [integral_zero_measure, sub_self]
  rw [hG']
  simp

/-- **Deterministic comparison (ChatGPT Section 2; the statement `StrictGapDeterministicComparisonStep`).** For one
realization of the cone family, `0 < s < t < T_ρ` gives `Λ_s ⊆ 𝒞_t`, the unregularized obstacle cluster of `μ` in `B_ρ`
at time `t`. -/
theorem strictGapDeterministicComparison_of_frozen
    (hG : GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole) : StrictGapDeterministicComparisonStep := by
  intro μ Λ hΛ ρ hρ s t hs hst hexit
  have ht : 0 < t := lt_trans hs hst
  have hr0 : 0 < ρ / 3 := by linarith
  have hr : ρ / 3 < ρ := by linarith
  have hΛt : Λ t ⊆ ball (0 : ℂ) (ρ / 3) := subset_ball_of_lt_clusterExitTime hΛ ht hexit
  have hsub : Λ s ⊆ Λ t := hΛ.2.1.monotoneOn (Set.mem_Ioi.mpr hs) (Set.mem_Ioi.mpr ht) hst.le
  have hΛs : Λ s ⊆ ball (0 : ℂ) (ρ / 3) := hsub.trans hΛt
  obtain ⟨hobs_t, hwc_t, hlap_t, -⟩ := hΛ.2.2 t (ρ / 3) ht hr0 hΛt ρ hr
  obtain ⟨hobs_s, hwc_s, hlap_s, -⟩ := hΛ.2.2 s (ρ / 3) hs hr0 hΛs ρ hr
  have hΛs_open : IsOpen (Λ s) := (hΛ.1 s hs).1
  have h0Λs : (0 : ℂ) ∈ Λ s := (hΛ.1 s hs).2.1
  have hconn : IsConnected (Λ s) := hΛ.2.1.isConnected s hs
  obtain ⟨hGc, hGtend⟩ := hpole ρ hρ
  have hGlap : HasLaplacian (greenFunction (ball 0 ρ) 0) 0 (Measure.dirac 0) (ball 0 ρ) :=
    (hG ρ hρ 0 (mem_ball_self hρ)).1
  have hct : 0 < t - s := by linarith
  -- the punctured set `W` and the function `f = v_t - v_s`
  set W : Set ℂ := Λ s \ {0} with hWdef
  have hWsub : W ⊆ Λ s := sdiff_subset
  have hWball : W ⊆ ball (0 : ℂ) ρ := fun x hx => ball_subset_ball (by linarith : ρ / 3 ≤ ρ) (hΛs hx.1)
  have h0W : (0 : ℂ) ∉ W := fun h => h.2 rfl
  have hWopen : IsOpen W := hΛs_open.sdiff isClosed_singleton
  have hWconn : IsConnected W := hpc (Λ s) hΛs_open hconn 0 h0Λs
  set f : ℂ → ℝ := fun x => (leastSupersolution μ ρ 0 t x - leastSupersolution μ ρ 0 s x)
      + (t - s) * greenFunction (ball 0 ρ) 0 x with hfdef
  have hLE : LaplacianLE f 0 W :=
    LaplacianLE.add_const_mul_of_hasLaplacian_zero
      (laplacianLE_sub_of_hasLaplacian hWsub hsub hWball hlap_t hlap_s)
      (hasLaplacian_zero_of_pole_notMem hGlap hWball h0W) (t - s)
  have hfc : ContinuousOn f (closedBall 0 ρ \ {0}) :=
    ((hwc_t.mono sdiff_subset).sub (hwc_s.mono sdiff_subset)).add (continuousOn_const.mul hGc)
  have hfcW : ContinuousOn f W := hfc.mono (fun x hx => ⟨ball_subset_closedBall (hWball hx), hx.2⟩)
  -- positivity of `f` near the pole
  have hball0 : (0 : ℂ) ∈ ball (0 : ℂ) ρ := mem_ball_self hρ
  have hcont0 : ContinuousAt (fun x => leastSupersolution μ ρ 0 t x - leastSupersolution μ ρ 0 s x) 0 :=
    (hwc_t.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hball0) ball_subset_closedBall)).sub
      (hwc_s.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hball0) ball_subset_closedBall))
  have hA : ∀ᶠ x in 𝓝 (0 : ℂ), (leastSupersolution μ ρ 0 t 0 - leastSupersolution μ ρ 0 s 0) - 1
      < leastSupersolution μ ρ 0 t x - leastSupersolution μ ρ 0 s x :=
    Filter.Tendsto.eventually hcont0 (lt_mem_nhds (by linarith))
  have hB : ∀ᶠ x in 𝓝[≠] (0 : ℂ),
      (|leastSupersolution μ ρ 0 t 0 - leastSupersolution μ ρ 0 s 0| + 2) / (t - s)
        < greenFunction (ball 0 ρ) 0 x :=
    hGtend.eventually_gt_atTop _
  have hnear : ∀ᶠ x in 𝓝[≠] (0 : ℂ), 0 < f x := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hA, hB] with x hx1 hx2
    have hcx := mul_lt_mul_of_pos_left hx2 hct
    have hKe : (t - s) * ((|leastSupersolution μ ρ 0 t 0 - leastSupersolution μ ρ 0 s 0| + 2) / (t - s))
        = |leastSupersolution μ ρ 0 t 0 - leastSupersolution μ ρ 0 s 0| + 2 := by
      field_simp
    have hab := neg_abs_le (leastSupersolution μ ρ 0 t 0 - leastSupersolution μ ρ 0 s 0)
    show 0 < (leastSupersolution μ ρ 0 t x - leastSupersolution μ ρ 0 s x)
      + (t - s) * greenFunction (ball 0 ρ) 0 x
    linarith
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hnear)
  obtain ⟨δ, hδ, hδΛ⟩ := Metric.isOpen_iff.mp hΛs_open 0 h0Λs
  -- the radius `a` of the excised ball, with `a < ε` and `B_a ⊆ Λ_s`
  set a : ℝ := min ε δ / 2 with hadef
  have ha : 0 < a := by positivity
  have haε : a < ε := by
    have := min_le_left ε δ
    linarith
  have haδ : a < δ := by
    have := min_le_right ε δ
    linarith
  have hdist_a : dist (a : ℂ) 0 = a := by
    simp [abs_of_pos ha]
  have ha0 : (a : ℂ) ∉ ({0} : Set ℂ) := by
    simp [ha.ne']
  have haΛ : (a : ℂ) ∈ Λ s := hδΛ (by rw [mem_ball, hdist_a]; exact haδ)
  have hfa : 0 < f (a : ℂ) := hεP (by rw [hdist_a]; exact haε) ha0
  have hyW : (a : ℂ) ∈ W := ⟨haΛ, ha0⟩
  -- the excised set `U_a = Λ_s \ B̄_a`
  set U : Set ℂ := Λ s \ closedBall (0 : ℂ) a with hUdef
  have hUopen : IsOpen U := hΛs_open.sdiff isClosed_closedBall
  have hUsub : U ⊆ W := fun x hx => ⟨hx.1, fun h0x => hx.2 (by
    rw [mem_singleton_iff.mp h0x]; exact mem_closedBall_self ha.le)⟩
  have hUbdd : Bornology.IsBounded U := isBounded_ball.subset (fun x hx => hΛs hx.1)
  have hcl_ball : closure U ⊆ closedBall (0 : ℂ) (ρ / 3) := closure_minimal
    (fun y hy => ball_subset_closedBall (hΛs hy.1)) isClosed_closedBall
  have hcl_a : closure U ⊆ {x : ℂ | a ≤ ‖x‖} := closure_minimal (fun y hy => by
      have h := hy.2
      rw [mem_closedBall, dist_zero_right, not_le] at h
      exact h.le) (isClosed_le continuous_const continuous_norm)
  have hcl_sub : closure U ⊆ closedBall 0 ρ \ {0} := fun x hx =>
    ⟨closedBall_subset_closedBall (by linarith) (hcl_ball hx), fun h0x => by
      have h1 : a ≤ ‖x‖ := hcl_a hx
      rw [mem_singleton_iff.mp h0x, norm_zero] at h1
      linarith⟩
  have hfc' : ContinuousOn f (closure U) := hfc.mono hcl_sub
  have hLEU : LaplacianLE f 0 U := hLE.mono_set hUsub
  -- the frontier of `U` carries nonnegative boundary values
  have hfront : ∀ x ∈ frontier U, 0 ≤ f x := by
    intro x hx
    have hxcl : x ∈ closure U := hx.1
    have hxnot : x ∉ U := by
      have := hx.2
      rwa [hUopen.interior_eq] at this
    have hx0 : x ≠ 0 := fun h0x => by
      have h1 : a ≤ ‖x‖ := hcl_a hxcl
      rw [h0x, norm_zero] at h1
      linarith
    by_cases hxΛ : x ∈ Λ s
    · have hxa : x ∈ closedBall (0 : ℂ) a := by
        by_contra hc
        exact hxnot ⟨hxΛ, hc⟩
      have hna : ‖x‖ ≤ a := by
        have h := hxa
        rw [mem_closedBall, dist_zero_right] at h
        exact h
      have hax : a ≤ ‖x‖ := hcl_a hxcl
      have hd : dist x 0 < ε := by
        rw [dist_zero_right]
        linarith
      exact (hεP hd hx0).le
    · have hxball : x ∈ ball (0 : ℂ) ρ := closedBall_subset_ball (by linarith) (hcl_ball hxcl)
      have hvs := odometer_nonpos_of_not_mem hobs_s hwc_s hGc hxball hx0 hxΛ
      have hvt := leastSupersolution_ge_obstacle (μ := μ) ht.le (ball_subset_closedBall hxball) hx0
      rw [neg_mul] at hvt
      have e : f x = (leastSupersolution μ ρ 0 t x + t * greenFunction (ball 0 ρ) 0 x)
          - (leastSupersolution μ ρ 0 s x + s * greenFunction (ball 0 ρ) 0 x) := by
        simp only [hfdef]
        ring
      linarith
  have hmin : ∀ x ∈ U, 0 ≤ f x := hwmp U f hUopen hUbdd hfc' hLEU hfront
  -- `f ≥ 0` on `W`, then `f > 0` on `W` by the strong minimum principle
  have hnonneg : ∀ x ∈ W, 0 ≤ f x := by
    intro x hx
    by_cases hxa : ‖x‖ ≤ a
    · have hd : dist x 0 < ε := by
        rw [dist_zero_right]
        linarith
      exact (hεP hd hx.2).le
    · apply hmin x
      refine ⟨hx.1, fun hc => hxa ?_⟩
      have h := hc
      rw [mem_closedBall, dist_zero_right] at h
      exact h
  have hpos : ∀ x ∈ W, 0 < f x := by
    intro x hx
    refine lt_of_le_of_ne (hnonneg x hx) (fun h0x => ?_)
    have hzero := hsmp W f hWopen hWconn hfcW hLE hnonneg x hx h0x.symm (a : ℂ) hyW
    linarith
  -- conclusion: `Λ_s ⊆ 𝒞_t`
  intro x hx
  refine ⟨ball_subset_ball (by linarith : ρ / 3 ≤ ρ) (hΛs hx), ?_⟩
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · right
    have hxW : x ∈ W := ⟨hx, hx0⟩
    have hfx := hpos x hxW
    have hvs := leastSupersolution_ge_obstacle (μ := μ) hs.le (ball_subset_closedBall (ball_subset_ball (by linarith : ρ / 3 ≤ ρ) (hΛs hx))) hx0
    rw [neg_mul] at hvs
    have e : f x = (leastSupersolution μ ρ 0 t x + t * greenFunction (ball 0 ρ) 0 x)
        - (leastSupersolution μ ρ 0 s x + s * greenFunction (ball 0 ρ) 0 x) := by
      simp only [hfdef]
      ring
    rw [neg_mul]
    linarith

end MatedCRT
