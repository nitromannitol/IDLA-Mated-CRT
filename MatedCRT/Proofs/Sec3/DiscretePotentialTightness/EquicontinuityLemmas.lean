import MatedCRT.Steps.Sec3.DiscretePotentialTightness
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Dirichlet
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.ExitTime

/-!
# Lemma 3.1, the analytic part: lemmas

* `ae_eventually_mem_of_polyHighProb`: Borel-Cantelli along polynomially summable scales (N3).
* `eventually_of_range`: an event holding at all small scales `e_j` holds eventually along a random sequence `ε_n → 0`
  with values in `{e_j}`.
* `ball_estimate`: the estimate of lines 1036-1072 at one scale, on the ball `B = B_r(η(a))`. Write `u = f + (u - f)`
  with `f` the harmonic extension of `u` from the complement of `A = V(B) \ V(∂B)`. Then
  `|u - f| ≤ C Q_A ≤ C M_q` (Lemma 2.13, eq:discrete-exit-laplacian) and `sup_{V(B)} |f| ≤ C ε⁻¹`. The first estimate
  of Lemma 3.2 bounds `f(a) - f(b)`.
* `exists_mem_cellVertices_of_mem_closure`: a point of `cl(D)` lies in a cell that meets `D`. This is used for the
  boundary vertices in the "moreover" part.
-/

namespace MatedCRT.Tightness

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-! ## Scales -/

/-- **Borel-Cantelli along polynomially summable scales.** -/
theorem ae_eventually_mem_of_polyHighProb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : ℝ → Set Ω}
    (hG : PolyHighProb P G) {e : ℕ → ℝ} (he : IsPolySummableScales e) :
    ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ω ∈ G (e j) := by
  obtain ⟨p, hp, C, r₀, hr₀, hPE⟩ := hG
  have hsum := he.2 p hp
  have hlim : ∀ᶠ j in atTop, e j < r₀ := by
    have h2 : ∀ᶠ j in atTop, e j ^ p < r₀ ^ p :=
      hsum.tendsto_atTop_zero.eventually (gt_mem_nhds (Real.rpow_pos_of_pos hr₀ p))
    exact h2.mono fun j hj => (Real.rpow_lt_rpow_iff (he.1 j).le hr₀.le hp).1 hj
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hlim
  have hsumJ : Summable fun j => |C| * e (j + J) ^ p := ((summable_nat_add_iff J).2 hsum).mul_left |C|
  have hbound : ∀ j, P (G (e (j + J)))ᶜ ≤ ENNReal.ofReal (|C| * e (j + J) ^ p) := fun j =>
    (hPE _ (he.1 _) (hJ _ (Nat.le_add_left J j))).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (he.1 _).le _)))
  have htsum : ∑' j, P (G (e (j + J)))ᶜ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg (abs_nonneg C) (Real.rpow_nonneg (he.1 _).le _)) hsumJ]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem htsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine eventually_atTop.2 ⟨N + J, fun j hj => ?_⟩
  have h := hN (j - J) (by omega)
  rw [Nat.sub_add_cancel (by omega : J ≤ j)] at h
  simpa using h

/-- Polynomially summable scales tend to `0`. -/
theorem _root_.MatedCRT.IsPolySummableScales.tendsto_zero {e : ℕ → ℝ} (he : IsPolySummableScales e) :
    Tendsto e atTop (𝓝 0) := by
  have h := (he.2 1 one_pos).tendsto_atTop_zero
  simpa only [Real.rpow_one] using h

theorem exists_pos_le_of_lt (e : ℕ → ℝ) (he : ∀ j, 0 < e j) (J : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ j < J, c ≤ e j := by
  induction J with
  | zero => exact ⟨1, one_pos, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ J ih =>
    obtain ⟨c, hc, hcJ⟩ := ih
    refine ⟨min c (e J), lt_min hc (he J), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact (min_le_left _ _).trans (hcJ j hj)
    · exact min_le_right _ _

/-- An event holding at all small scales `e_j` holds eventually along `ε_n → 0` with values in `{e_j}`. -/
theorem eventually_of_range {e : ℕ → ℝ} (he : ∀ j, 0 < e j) {ε : ℕ → ℝ} (hεe : ∀ n, ε n ∈ range e)
    (hε0 : Tendsto ε atTop (𝓝 0)) {Q : ℝ → Prop} (h : ∀ᶠ j in atTop, Q (e j)) : ∀ᶠ n in atTop, Q (ε n) := by
  obtain ⟨J, hJ⟩ := eventually_atTop.1 h
  obtain ⟨c, hc, hcJ⟩ := exists_pos_le_of_lt e he J
  filter_upwards [hε0.eventually (gt_mem_nhds hc)] with n hn
  obtain ⟨j, hj⟩ := hεe n
  rw [← hj] at hn ⊢
  by_cases hjJ : J ≤ j
  · exact hJ j hjJ
  · exact absurd (hcJ j (not_le.1 hjJ)) (not_le.2 hn)

/-! ## Elementary facts -/

/-- `𝓜` is monotone. -/
theorem largestExitTimeRV_mono {μ : Measure ℂ} {D₁ D₂ : Set ℂ} (h : D₁ ⊆ D₂) :
    largestExitTimeRV μ D₁ ≤ largestExitTimeRV μ D₂ :=
  iSup₂_le fun z hz => le_iSup₂_of_le z (h hz) (lintegral_mono_set h)

/-- `x^χ ≤ 2 x^{χ'}` for `0 < x ≤ 2` and `0 ≤ χ' ≤ χ ≤ 1`. -/
theorem rpow_le_two_mul_rpow {x χ χ' : ℝ} (hx : 0 < x) (hx2 : x ≤ 2) (hχ' : 0 ≤ χ') (hle : χ' ≤ χ)
    (hχ1 : χ ≤ 1) : x ^ χ ≤ 2 * x ^ χ' := by
  rcases le_or_gt x 1 with h1 | h1
  · have e1 := Real.rpow_le_rpow_of_exponent_ge hx h1 hle
    have e2 : 0 ≤ x ^ χ' := Real.rpow_nonneg hx.le _
    linarith
  · have e1 : x ^ χ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1.le hχ1
    rw [Real.rpow_one] at e1
    have e2 : 1 ≤ x ^ χ' := Real.one_le_rpow h1.le hχ'
    linarith

theorem mLaplacian_const_mul {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (c : ℝ) (u : ℤ → ℝ) (a : ℤ) :
    mLaplacian m (fun b => c * u b) a = c * mLaplacian m u a := by
  rw [mLaplacian_eq_div hlf, mLaplacian_eq_div hlf, lapSum_smul', mul_div_assoc]

/-! ## Cells and balls -/

variable {ε : ℝ} {η : ℝ → ℂ}

/-- Local finiteness of a map whose adjacent vertices have intersecting cells. -/
theorem isLocallyFiniteMult_of_cells {m : ℤ → ℤ → ℕ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) : IsLocallyFiniteMult m := fun a =>
  (cellVertices_finite hη hp hε (K := cell ε η a) (isCompact_Icc.image hη).isBounded).subset fun b hb => by
    obtain ⟨z, hza, hzb⟩ := hadj a b hb
    exact ⟨z, hzb, hza⟩

/-- A cell of `V(B) \ V(∂B)` lies in the ball `B` (cells are connected). -/
theorem cell_subset_ball (hη : Continuous η) {x : ℂ} {r : ℝ} (hr : 0 < r) {k : ℤ}
    (hk : k ∈ interiorCellVertices ε η (ball x r)) : cell ε η k ⊆ ball x r := by
  have hconn : IsPreconnected (cell ε η k) := isPreconnected_Icc.image η hη.continuousOn
  refine hconn.subset_of_closure_inter_subset isOpen_ball hk.1 ?_
  rintro z ⟨hzcl, hzc⟩
  rw [closure_ball x hr.ne'] at hzcl
  rcases (mem_closedBall.1 hzcl).lt_or_eq with h | h
  · exact h
  · exact (hk.2 ⟨z, hzc, by rw [frontier_ball x hr.ne']; exact h⟩).elim

/-- The distance from the centre to the boundary of a ball. -/
theorem le_infDist_frontier_ball {x : ℂ} {r : ℝ} (hr : 0 < r) : r ≤ infDist x (frontier (ball x r)) := by
  rw [frontier_ball x hr.ne']
  by_contra h
  rw [not_le] at h
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff (NormedSpace.sphere_nonempty.2 hr.le)).1 h
  rw [mem_sphere, dist_comm] at hy
  linarith

/-- A point of `cl(D)` lies in a cell meeting `D`. -/
theorem exists_mem_cellVertices_of_mem_closure (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : 0 < ε) {D : Set ℂ} {z : ℂ} (hz : z ∈ closure D) :
    ∃ a', a' ∈ cellVertices ε η D ∧ z ∈ cell ε η a' := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  set F : Set ℤ := cellVertices ε η (closedBall z 1) ∩ cellVertices ε η D with hF_def
  have hF : F.Finite := (cellVertices_finite hη hp hε isBounded_closedBall).subset inter_subset_left
  have hclosed : IsClosed (⋃ a' ∈ F, cell ε η a') :=
    hF.isClosed_biUnion fun a' _ => (isCompact_Icc.image hη).isClosed
  have hzU : z ∈ (⋃ a' ∈ F, cell ε η a')ᶜ := by
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    exact fun a' ha' hz' => hno a' ha'.2 hz'
  have hnhds : (⋃ a' ∈ F, cell ε η a')ᶜ ∩ ball z 1 ∈ 𝓝 z :=
    inter_mem (hclosed.isOpen_compl.mem_nhds hzU) (ball_mem_nhds z one_pos)
  obtain ⟨p, ⟨hpU, hpB⟩, hpD⟩ := mem_closure_iff_nhds.1 hz _ hnhds
  have hpc := mem_cell_vertexOf hη hp hsurj hε p
  have hmem : vertexOf ε η p ∈ F := ⟨⟨p, hpc, ball_subset_closedBall hpB⟩, ⟨p, hpc, hpD⟩⟩
  exact hpU (mem_iUnion₂.2 ⟨_, hmem, hpc⟩)

/-! ## The estimate at one scale on a ball -/

/-- **The estimate of lines 1036-1072 at one scale.** On the ball `B = B_r(x)` with `x = η(a)`, `B ⊆ D`, given
Lemma 3.2's first estimate on `B` and the bound `Q_A ≤ M_q` on `A = V(B) \ V(∂B)` (Lemma 2.18):
`|u(a) - u(b)| r^ξ ≤ A (C/ε) (ε^β ∨ |η(a) - η(b)|)^ξ + 2 C M_q r^ξ` for `a ∈ A`, `b ∈ V(B)`. -/
theorem ball_estimate {m : ℤ → ℤ → ℕ} (hε : 0 < ε) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsucc : ∀ k, m k (k + 1) ≠ 0) {D : Set ℂ} (hDo : IsOpen D) {u : ℤ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hlap : ∀ a ∈ interiorCellVertices ε η D, |mLaplacian m u a| ≤ C)
    (hbd : ∀ a ∈ cellVertices ε η D, |u a| ≤ C / ε)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hB : ball x r ⊆ D) {ξ A β Mq : ℝ} (hξ : 0 ≤ ξ) (hA : 0 ≤ A) (hMq : 0 ≤ Mq)
    (hH : ∀ f : ℤ → ℝ, (∀ a ∈ interiorCellVertices ε η (ball x r), matedLaplacian m f a = 0) →
      ∀ a ∈ interiorCellVertices ε η (ball x r), ∀ b ∈ cellVertices ε η (ball x r),
        |f a - f b| * infDist (vertexPoint ε η a) (frontier (ball x r)) ^ ξ ≤
          A * (⨆ a' : cellVertices ε η (ball x r), |f a'|) *
            max (ε ^ β) ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ)
    (hQ : ∀ c ∈ interiorCellVertices ε η (ball x r),
      expectedExitTime m (interiorCellVertices ε η (ball x r)) c ≤ ENNReal.ofReal Mq)
    {a b : ℤ} (ha : a ∈ interiorCellVertices ε η (ball x r)) (hax : vertexPoint ε η a = x)
    (hb : b ∈ cellVertices ε η (ball x r)) :
    |u a - u b| * r ^ ξ ≤
      A * (C / ε) * max (ε ^ β) ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ + 2 * C * Mq * r ^ ξ := by
  have hlf := isLocallyFiniteMult_of_cells hη hp hε hadj
  have hAfin : (interiorCellVertices ε η (ball x r)).Finite :=
    (cellVertices_finite hη hp hε isBounded_ball).subset fun k hk => hk.1
  have hesc := escape_of_adjacent_succ hsucc hAfin
  have hsub : ∀ k ∈ interiorCellVertices ε η (ball x r), cell ε η k ⊆ ball x r :=
    fun k hk => cell_subset_ball hη hr hk
  have hAD : ∀ k ∈ interiorCellVertices ε η (ball x r), k ∈ interiorCellVertices ε η D := by
    intro k hk
    obtain ⟨z, hz, hzB⟩ := hk.1
    refine ⟨⟨z, hz, hB hzB⟩, ?_⟩
    rintro ⟨w, hw, hwf⟩
    rw [hDo.frontier_eq] at hwf
    exact hwf.2 (hB (hsub k hk hw))
  have hdeg : ∀ k, mdeg m k ≠ 0 := fun k => mdeg_ne_zero_of_ne_zero hlf (hsucc k)
  have hu' : ∀ k ∈ interiorCellVertices ε η (ball x r), |lapSum hlf u k| ≤ C * (mdeg m k : ℝ) := by
    intro k hk
    rw [← mLaplacian_mul_mdeg hlf u k, abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_right (hlap k (hAD k hk)) (Nat.cast_nonneg _)
  have hM : ∀ k ∈ interiorCellVertices ε η (ball x r), ∀ c, m k c ≠ 0 →
      c ∉ interiorCellVertices ε η (ball x r) → |u c| ≤ C / ε := by
    intro k hk c hkc _
    obtain ⟨z, hzk, hzc⟩ := hadj k c hkc
    exact hbd c ⟨z, hzc, hB (hsub k hk hzk)⟩
  have hQfin : ∀ c ∈ interiorCellVertices ε η (ball x r),
      expectedExitTime m (interiorCellVertices ε η (ball x r)) c ≠ ⊤ :=
    fun c hc => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hQ c hc)
  have hw0 : ∀ c ∉ interiorCellVertices ε η (ball x r),
      (expectedExitTime m (interiorCellVertices ε η (ball x r)) c).toReal = 0 := fun c hc => by
    rw [expectedExitTime_eq_zero_of_not_mem m hc, ENNReal.toReal_zero]
  have hw : ∀ c ∈ interiorCellVertices ε η (ball x r),
      lapSum hlf (fun c => (expectedExitTime m (interiorCellVertices ε η (ball x r)) c).toReal) c =
        -(mdeg m c : ℝ) :=
    fun c hc => lapSum_expectedExitTime hlf hQfin hc (hdeg c)
  obtain ⟨f, hfoff, hf, hfbd, hvf⟩ := exists_harmonic_decomposition hlf hAfin hesc hM hu' hw0 hw
  have hQle : ∀ c, (expectedExitTime m (interiorCellVertices ε η (ball x r)) c).toReal ≤ Mq := by
    intro c
    by_cases hc : c ∈ interiorCellVertices ε η (ball x r)
    · exact ENNReal.toReal_le_of_le_ofReal hMq (hQ c hc)
    · rw [hw0 c hc]
      exact hMq
  have hharm : ∀ k ∈ interiorCellVertices ε η (ball x r), matedLaplacian m f k = 0 := by
    intro k hk
    show mLaplacian m f k = 0
    rw [mLaplacian_eq_div hlf, hf k hk, zero_div]
  have hne : Nonempty (cellVertices ε η (ball x r)) := ⟨⟨b, hb⟩⟩
  have hsup : (⨆ a' : cellVertices ε η (ball x r), |f a'|) ≤ C / ε := by
    refine ciSup_le fun c => ?_
    by_cases hc : (c : ℤ) ∈ interiorCellVertices ε η (ball x r)
    · exact hfbd c hc
    · rw [hfoff c hc]
      obtain ⟨z, hz, hzB⟩ := c.2
      exact hbd c ⟨z, hz, hB hzB⟩
  have h1 := hH f hharm a ha b hb
  have hd : r ≤ infDist (vertexPoint ε η a) (frontier (ball x r)) := by
    rw [hax]
    exact le_infDist_frontier_ball hr
  have hrξ : r ^ ξ ≤ infDist (vertexPoint ε η a) (frontier (ball x r)) ^ ξ := Real.rpow_le_rpow hr.le hd hξ
  have hmax : 0 ≤ max (ε ^ β) ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ :=
    Real.rpow_nonneg (le_max_of_le_right (norm_nonneg _)) _
  have h2 : |f a - f b| * r ^ ξ ≤ A * (C / ε) * max (ε ^ β) ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ :=
    calc |f a - f b| * r ^ ξ ≤ |f a - f b| * infDist (vertexPoint ε η a) (frontier (ball x r)) ^ ξ :=
          mul_le_mul_of_nonneg_left hrξ (abs_nonneg _)
      _ ≤ A * (⨆ a' : cellVertices ε η (ball x r), |f a'|) *
            max (ε ^ β) ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ := h1
      _ ≤ A * (C / ε) * max (ε ^ β) ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsup hA) hmax
  have e1 := abs_le.1 (show |u a - f a| ≤
    C * (expectedExitTime m (interiorCellVertices ε η (ball x r)) a).toReal from hvf a)
  have e2 := abs_le.1 (show |u b - f b| ≤
    C * (expectedExitTime m (interiorCellVertices ε η (ball x r)) b).toReal from hvf b)
  have e3 := mul_le_mul_of_nonneg_left (hQle a) hC
  have e4 := mul_le_mul_of_nonneg_left (hQle b) hC
  have h3 : |u a - u b| ≤ |f a - f b| + 2 * C * Mq := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self (f a - f b), neg_abs_le (f a - f b), e1.1, e1.2, e2.1, e2.2]
  have hr0 : 0 ≤ r ^ ξ := Real.rpow_nonneg hr.le _
  calc |u a - u b| * r ^ ξ ≤ (|f a - f b| + 2 * C * Mq) * r ^ ξ := mul_le_mul_of_nonneg_right h3 hr0
    _ = |f a - f b| * r ^ ξ + 2 * C * Mq * r ^ ξ := by ring
    _ ≤ A * (C / ε) * max (ε ^ β) ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ + 2 * C * Mq * r ^ ξ := by
        linarith [h2]

end MatedCRT.Tightness
