import LatticeProb.Prob.BrownianModulus
import LatticeProb.Prob.CorrelatedBMConeTimes
import LatticeProb.Prob.CorrelatedBMSeparatedHalves
import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Prob.CorrelatedBMForwardPositive

/-!
# No two-sided cone point of planar Brownian motion for one symmetric wedge

Let `μ` be the law of a two-sided standard planar Brownian motion `w` (`IsCorrelatedBM2 (√2) μ`),
let `0 < θ < π` and let `D` be the closed wedge `{z | |cos (θ / 2) z₂| ≤ sin (θ / 2) z₁}` of
angle `θ` around the positive first axis. A time `t` is a two-sided cone point of radius `ρ` when
`w u - w t ∈ D` for every `u ∈ [t - ρ, t + ρ]` (`IsSymmetricConePoint`). This file proves that for
every `s > 0` and `K`, almost surely no `t ∈ [-K, K]` is a two-sided cone point of radius `2 s`
(`measure_symmetricConePoint_eq_zero`).

The proof is the direct argument for a fixed wedge (Le Gall, *Some properties of planar Brownian
motion*, Chapter III). Cut `[-K, K]` into cells of length `1/n` with left ends `c`.

* Off the event that some coordinate moves by `r` within a time `1/n` in `[-K, K]`
  (`oscEvent`, of probability at most `8 (2Kn + 1) exp (-r² n / 256)` by the modulus of
  continuity of Brownian motion), a cone point `t` in the cell of `c` forces the forward and the
  backward increments `w (c ± u) - w c`, `u ∈ [0, s]`, to stay in `D` shifted back by `2 r`
  (`subset_oscEvent_union_barriers`).
* The forward and the backward increments at `c` are independent (`indepFun_centered_opposite_halves`),
  and each stays in the shifted wedge with probability at most `K₀ (r / √s)^β` for some `β > 1`
  (`forward_wedge_barrier_subcritical_positive`).
* With `r = n^{-κ}`, `1/(2β) < κ < 1/2`, the sum `8 (2Kn + 1) exp (-n^{1 - 2κ} / 256) +
  (2Kn + 1) K₀² (C n^{-κ})^{2β}` tends to `0`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open MatedCRTHarmonic.MatedCRT LatticeProb LatticeProb.CorrelatedBM
open scoped ENNReal NNReal

namespace MatedCRT.PlanarBMConePoints

/-- `t` is a two-sided cone point of `w` of radius `ρ` for the closed wedge of angle `θ` around the
positive first axis: `|cos (θ / 2) (w u - w t)₂| ≤ sin (θ / 2) (w u - w t)₁` for `u ∈ [t - ρ, t + ρ]`. -/
def IsSymmetricConePoint (θ ρ : ℝ) (w : Path2) (t : ℝ) : Prop :=
  ∀ u ∈ Icc (t - ρ) (t + ρ),
    |Real.cos (θ / 2) * ((w u).2 - (w t).2)| ≤ Real.sin (θ / 2) * ((w u).1 - (w t).1)

private theorem lrCoord_zero_apply (t : ℝ) (w : Path2) : lrCoord 0 t w = (w t).1 := by
  simp [lrCoord]

private theorem lrCoord_one_apply (t : ℝ) (w : Path2) : lrCoord 1 t w = (w t).2 := by
  simp [lrCoord]

/-! ### Deterministic steps -/

/-- A point of the closed wedge `{|b z₂| ≤ a z₁}`, `0 ≤ a, b ≤ 1`, moved by a vector with
coordinates of size at most `r` lies in the wedge shifted back by `2 r`. -/
theorem abs_mul_add_le_of_mem_wedge {a b r d₁ d₂ e₁ e₂ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hd : |b * d₂| ≤ a * d₁) (he₁ : |e₁| ≤ r) (he₂ : |e₂| ≤ r) :
    |b * (d₂ + e₂)| ≤ 2 * r + a * (d₁ + e₁) := by
  have h1 : |b * (d₂ + e₂)| ≤ |b * d₂| + b * |e₂| := by
    rw [mul_add]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul b e₂, abs_of_nonneg hb0]
  have h2 : b * |e₂| ≤ r := (mul_le_of_le_one_left (abs_nonneg e₂) hb1).trans he₂
  have h3 : -(a * e₁) ≤ r := by
    have h4 : -(a * e₁) ≤ a * |e₁| := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs e₁) ha0
    exact h4.trans ((mul_le_of_le_one_left (abs_nonneg e₁) ha1).trans he₁)
  linarith

/-- A continuous function bounded by `C` at the rational points of `[0, s]`, `s > 0`, is bounded by
`C` on `[0, s]`. -/
theorem forall_mem_Icc_le_of_forall_rat {g : ℝ → ℝ} (hg : Continuous g) {s C : ℝ} (hs : 0 < s)
    (h : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ s → g q ≤ C) : ∀ x ∈ Icc 0 s, g x ≤ C := by
  have hcl : IsClosed {x | g x ≤ C} := isClosed_le hg continuous_const
  have hsub : Ioo 0 s ∩ range ((↑) : ℚ → ℝ) ⊆ {x | g x ≤ C} := by
    rintro x ⟨hx, q, rfl⟩
    exact h q hx.1.le hx.2.le
  have h1 : Ioo 0 s ⊆ closure (Ioo 0 s ∩ range ((↑) : ℚ → ℝ)) :=
    Dense.open_subset_closure_inter (Rat.denseRange_cast (𝕜 := ℝ)) isOpen_Ioo
  have h2 : closure (Ioo (0 : ℝ) s) ⊆ {x | g x ≤ C} :=
    closure_minimal (h1.trans (closure_minimal hsub hcl)) hcl
  intro x hx
  rw [← closure_Ioo hs.ne] at hx
  exact h2 hx

/-! ### Barrier events at a fixed time -/

/-- The increments `w (c + d v) - w c`, `v ≥ 0`, of the two coordinates. -/
def halfIncrements (c d : ℝ) (ω : Path2) (p : Fin 2 × ℝ≥0) : ℝ :=
  coneIncr p.1 (c + d * (p.2 : ℝ)) c ω

/-- Increment families that stay at the rational times of `[0, s]` in the closed wedge
`{|b z₂| ≤ a z₁}` shifted back by `q`. -/
def ratBarrierSet (a b q s : ℝ) : Set (Fin 2 × ℝ≥0 → ℝ) :=
  ⋂ u : {u : ℚ // 0 ≤ (u : ℝ) ∧ (u : ℝ) ≤ s},
    {f | |b * f (1, Real.toNNReal (u.1 : ℝ))| ≤ q + a * f (0, Real.toNNReal (u.1 : ℝ))}

theorem measurableSet_ratBarrierSet (a b q s : ℝ) : MeasurableSet (ratBarrierSet a b q s) :=
  MeasurableSet.iInter fun _ => measurableSet_le (by fun_prop) (by fun_prop)

theorem continuous_lrCoord_affine (i : Fin 2) (c d : ℝ) (ω : Path2) :
    Continuous fun x : ℝ => lrCoord i (c + d * x) ω := by
  fin_cases i
  · exact continuous_fst.comp (ω.continuous.comp (by fun_prop))
  · exact continuous_snd.comp (ω.continuous.comp (by fun_prop))

theorem coneIncr_recenterPath (i : Fin 2) (c d t : ℝ) (ω : Path2) :
    coneIncr i t 0 (recenterPath c d ω) = coneIncr i (c + d * t) c ω := by
  fin_cases i <;> simp [coneIncr, lrCoord, recenterPath]

/-- The rational barrier event of the increments at `c` lies in the strict barrier event of the
recentred path with a larger offset. -/
theorem preimage_ratBarrierSet_subset {a b q q' s : ℝ} (hs : 0 < s) (hqq' : q < q') (c d : ℝ) :
    halfIncrements c d ⁻¹' ratBarrierSet a b q s ⊆
      recenterPath c d ⁻¹' openSymmetricWedgeBarrier a b q' s := by
  intro ω hω
  have hω' : halfIncrements c d ω ∈ ratBarrierSet a b q s := hω
  simp only [ratBarrierSet, mem_iInter, mem_ofPred_eq] at hω'
  simp only [mem_preimage, openSymmetricWedgeBarrier, mem_ofPred_eq]
  intro t ht
  have hg : Continuous fun x : ℝ =>
      |b * coneIncr 1 (c + d * x) c ω| - a * coneIncr 0 (c + d * x) c ω := by
    refine (continuous_const.mul ?_).abs.sub (continuous_const.mul ?_) <;>
      exact (continuous_lrCoord_affine _ c d ω).sub continuous_const
  have key := forall_mem_Icc_le_of_forall_rat hg (C := q) hs (fun u hu0 hus => by
    have hmem := hω' ⟨u, hu0, hus⟩
    simp only [halfIncrements, Real.coe_toNNReal _ hu0] at hmem
    linarith) t ht
  beta_reduce at key
  rw [coneIncr_recenterPath, coneIncr_recenterPath]
  linarith

/-- Each of the forward and the backward increments at `c` stays in the shifted wedge with the
probability bound of the forward wedge barrier. -/
theorem measure_preimage_ratBarrierSet_le {μ : Measure Path2} (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ)
    {θ β K₀ : ℝ}
    (hK : ∀ {ν : Measure Path2}, IsCorrelatedBM2 (Real.sqrt 2) ν →
      ∀ (q : ℝ) (T : ℝ≥0), 0 < q → 0 < (T : ℝ) →
        ν.real (openSymmetricWedgeBarrier (Real.sin (θ / 2)) (Real.cos (θ / 2)) q T) ≤
          K₀ * ((q / (Real.sin (θ / 2) * Real.sqrt 2)) / Real.sqrt (T : ℝ)) ^ β)
    {q q' : ℝ} (hq : 0 < q) (hqq' : q < q') {s : ℝ≥0} (hs : 0 < (s : ℝ)) (c : ℝ) {d : ℝ}
    (hd : |d| = 1) :
    μ (halfIncrements c d ⁻¹' ratBarrierSet (Real.sin (θ / 2)) (Real.cos (θ / 2)) q s) ≤
      ENNReal.ofReal (K₀ * ((q' / (Real.sin (θ / 2) * Real.sqrt 2)) / Real.sqrt (s : ℝ)) ^ β) := by
  have hν := isCorrelatedBM2_map_recenterPath hμ c d hd
  have : IsProbabilityMeasure (μ.map (recenterPath c d)) := hν.isProbabilityMeasure
  calc μ (halfIncrements c d ⁻¹' ratBarrierSet (Real.sin (θ / 2)) (Real.cos (θ / 2)) q s)
      ≤ μ (recenterPath c d ⁻¹'
          openSymmetricWedgeBarrier (Real.sin (θ / 2)) (Real.cos (θ / 2)) q' s) :=
        measure_mono (preimage_ratBarrierSet_subset hs hqq' c d)
    _ ≤ μ.map (recenterPath c d)
          (openSymmetricWedgeBarrier (Real.sin (θ / 2)) (Real.cos (θ / 2)) q' s) :=
        Measure.le_map_apply (continuous_recenterPath c d).measurable.aemeasurable _
    _ = ENNReal.ofReal ((μ.map (recenterPath c d)).real
          (openSymmetricWedgeBarrier (Real.sin (θ / 2)) (Real.cos (θ / 2)) q' s)) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hK hν q' s (hq.trans hqq') hs)

/-- The backward and the forward barrier events at a fixed time are independent. -/
theorem measure_preimage_ratBarrierSet_inter {μ : Measure Path2} (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ)
    (a b q s c : ℝ) :
    μ (halfIncrements c (-1) ⁻¹' ratBarrierSet a b q s ∩
        halfIncrements c 1 ⁻¹' ratBarrierSet a b q s) =
      μ (halfIncrements c (-1) ⁻¹' ratBarrierSet a b q s) *
        μ (halfIncrements c 1 ⁻¹' ratBarrierSet a b q s) :=
  (indepFun_centered_opposite_halves hμ (d := 1) (by simp) c).measure_inter_preimage_eq_mul _ _
    (measurableSet_ratBarrierSet a b q s) (measurableSet_ratBarrierSet a b q s)

/-! ### The oscillation event -/

/-- Some coordinate of `w` moves by at least `r` between two times of `[-K, K]` at distance at
most `η`. -/
def oscEvent (K η r : ℝ) : Set Path2 :=
  {w | ∃ i : Fin 2, ∃ t ∈ Icc (-K) K, ∃ c ∈ Icc (-K) K,
    |t - c| ≤ η ∧ r ≤ |lrCoord i t w - lrCoord i c w|}

/-- The modulus of continuity of the two coordinates on `[-K, K]` at the scale `1/n`. -/
theorem measure_oscEvent_le {μ : Measure Path2} (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ) (K : ℕ)
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    μ (oscEvent K (n : ℝ)⁻¹ r) ≤
      ENNReal.ofReal (8 * (2 * K * n + 1) * Real.exp (-(r ^ 2 * n / 256))) := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  let B : Fin 2 → ℝ≥0 → Path2 → ℝ := fun i v =>
    coneComb (if i = 0 then 1 else 0) (if i = 0 then 0 else 1) (-(K : ℝ) + 1 * v) (-(K : ℝ))
  have hB : ∀ i, IsBrownianReal (B i) μ := by
    intro i
    fin_cases i
    · exact isBrownianReal_coneComb hμ (by simp) (by simp) _
    · exact isBrownianReal_coneComb hμ (by simp) (by simp) _
  have hBeval : ∀ (i : Fin 2) (x : ℝ) (w : Path2), -(K : ℝ) ≤ x →
      B i (Real.toNNReal (x + K)) w = lrCoord i x w - lrCoord i (-(K : ℝ)) w := by
    intro i x w hx
    have hx' : (Real.toNNReal (x + K) : ℝ) = x + K := Real.coe_toNNReal _ (by linarith)
    fin_cases i <;> simp [B, coneComb, coneIncr, hx']
  let T : ℝ≥0 := 2 * K
  let η : ℝ≥0 := (n : ℝ≥0)⁻¹
  have hη : 0 < η := by positivity
  have hsub : oscEvent K (n : ℝ)⁻¹ r ⊆ ⋃ i : Fin 2,
      {ω | ∃ s t : ℝ≥0, s ≤ T ∧ t ≤ T ∧ |(s : ℝ) - t| ≤ η ∧ r ≤ |B i s ω - B i t ω|} := by
    rintro w ⟨i, t, ht, c, hc, htc, hrw⟩
    refine mem_iUnion.2 ⟨i, Real.toNNReal (t + K), Real.toNNReal (c + K), ?_, ?_, ?_, ?_⟩
    · rw [Real.toNNReal_le_iff_le_coe]
      simp only [T, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast]
      linarith [ht.2]
    · rw [Real.toNNReal_le_iff_le_coe]
      simp only [T, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast]
      linarith [hc.2]
    · rw [Real.coe_toNNReal _ (by linarith [ht.1]), Real.coe_toNNReal _ (by linarith [hc.1])]
      simpa [η, add_sub_add_right_eq_sub] using htc
    · rw [hBeval i t w ht.1, hBeval i c w hc.1]
      simpa using hrw
  have hceil : ⌈((T : ℝ) / (η : ℝ))⌉₊ = 2 * K * n := by
    have : (T : ℝ) / (η : ℝ) = ((2 * K * n : ℕ) : ℝ) := by
      simp only [T, η, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_inv]
      push_cast
      field_simp
    rw [this, Nat.ceil_natCast]
  have hexp : (r / 2) ^ 2 / (32 * (2 * (η : ℝ))) = r ^ 2 * n / 256 := by
    simp only [η, NNReal.coe_inv, NNReal.coe_natCast]
    field_simp
    ring
  calc μ (oscEvent K (n : ℝ)⁻¹ r)
      ≤ ∑ i : Fin 2, μ {ω | ∃ s t : ℝ≥0, s ≤ T ∧ t ≤ T ∧ |(s : ℝ) - t| ≤ η ∧
          r ≤ |B i s ω - B i t ω|} :=
        (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _i : Fin 2, ((2 * K * n + 1 : ℕ) : ℝ≥0∞) *
          (4 * ENNReal.ofReal (Real.exp (-(r ^ 2 * n / 256)))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := measure_exists_modulus_le (hB i) T η hη hr
        rwa [hceil, hexp] at h
    _ = ENNReal.ofReal (8 * (2 * K * n + 1) * Real.exp (-(r ^ 2 * n / 256))) := by
        rw [Fin.sum_univ_two, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
        · congr 1
          push_cast
          ring
        all_goals positivity

/-! ### Covering the cone points -/

/-- At a time `c ≤ t` with `t - c ≤ s`, a two-sided cone point `t` of radius `2 s` and coordinates
that move by at most `r` between `c` and `t` force the increments of `w` at `c`, forward (`d = 1`)
and backward (`d = -1`), to stay in the wedge shifted back by `2 r`. -/
theorem mem_preimage_ratBarrierSet_of_cone {θ s r c t : ℝ} {w : Path2} (hθ0 : 0 < θ)
    (hθπ : θ < Real.pi) (hcone : IsSymmetricConePoint θ (2 * s) w t) (hct : c ≤ t)
    (htc : t - c ≤ s) (hosc : ∀ i, |lrCoord i t w - lrCoord i c w| ≤ r) {d : ℝ}
    (hd : d = 1 ∨ d = -1) :
    w ∈ halfIncrements c d ⁻¹'
      ratBarrierSet (Real.sin (θ / 2)) (Real.cos (θ / 2)) (2 * r) s := by
  have hθ2 : θ / 2 < Real.pi / 2 := by linarith
  have ha0 : 0 ≤ Real.sin (θ / 2) :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).le
  have hb0 : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ2.le⟩
  simp only [mem_preimage, ratBarrierSet, mem_iInter]
  rintro ⟨u, hu0, hus⟩
  simp only [mem_ofPred_eq, halfIncrements, Real.coe_toNNReal _ hu0]
  have hp : c + d * u ∈ Icc (t - 2 * s) (t + 2 * s) := by
    rcases hd with rfl | rfl <;> constructor <;> linarith
  have h := hcone _ hp
  have h0 := hosc 0
  have h1 := hosc 1
  rw [lrCoord_zero_apply, lrCoord_zero_apply] at h0
  rw [lrCoord_one_apply, lrCoord_one_apply] at h1
  have key := abs_mul_add_le_of_mem_wedge ha0 (Real.sin_le_one _) hb0 (Real.cos_le_one _) h h0 h1
  simp only [coneIncr, lrCoord_zero_apply, lrCoord_one_apply]
  have e1 : (w (c + d * u)).2 - (w c).2 =
      ((w (c + d * u)).2 - (w t).2) + ((w t).2 - (w c).2) := by ring
  have e0 : (w (c + d * u)).1 - (w c).1 =
      ((w (c + d * u)).1 - (w t).1) + ((w t).1 - (w c).1) := by ring
  rw [e1, e0]
  exact key

/-- The cone points of radius `2 s` in `[-K, K]` lie in the oscillation event at the scale `1/n`
or in a forward and backward barrier event at one of the times `-K + k/n`, `k ≤ 2Kn`. -/
theorem subset_oscEvent_union_barriers {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) {s : ℝ} (K : ℕ)
    {n : ℕ} (hn : 0 < n) (hns : (n : ℝ)⁻¹ ≤ s) (r : ℝ) :
    {w | ∃ t ∈ Icc (-(K : ℝ)) K, IsSymmetricConePoint θ (2 * s) w t} ⊆
      oscEvent K (n : ℝ)⁻¹ r ∪ ⋃ k ∈ Finset.range (2 * K * n + 1),
        (halfIncrements (-(K : ℝ) + k / n) (-1) ⁻¹'
            ratBarrierSet (Real.sin (θ / 2)) (Real.cos (θ / 2)) (2 * r) s ∩
          halfIncrements (-(K : ℝ) + k / n) 1 ⁻¹'
            ratBarrierSet (Real.sin (θ / 2)) (Real.cos (θ / 2)) (2 * r) s) := by
  rintro w ⟨t, ht, hcone⟩
  by_cases hw : w ∈ oscEvent K (n : ℝ)⁻¹ r
  · exact Or.inl hw
  right
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have htK : 0 ≤ (t + K) * n := mul_nonneg (by linarith [ht.1]) hn'.le
  set k := ⌊(t + K) * n⌋₊ with hk
  have hk0 : (k : ℝ) ≤ (t + K) * n := Nat.floor_le htK
  have hk1 : (t + K) * n < k + 1 := Nat.lt_floor_add_one _
  have hkle : k ≤ 2 * K * n := by
    have : (k : ℝ) ≤ ((2 * K * n : ℕ) : ℝ) := by
      push_cast
      nlinarith [ht.2]
    exact_mod_cast this
  refine mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (by omega), ?_⟩
  set c : ℝ := -(K : ℝ) + k / n with hc
  have hkn : (k : ℝ) / n ≤ t + K := (div_le_iff₀ hn').2 hk0
  have hkn1 : t + K < (k + 1) / n := (lt_div_iff₀ hn').2 hk1
  have hct : c ≤ t := by linarith
  have htc : t - c ≤ (n : ℝ)⁻¹ := by
    have : (k + 1 : ℝ) / n = k / n + (n : ℝ)⁻¹ := by rw [add_div, one_div]
    linarith
  have hcK : c ∈ Icc (-(K : ℝ)) K := by
    have : 0 ≤ (k : ℝ) / n := by positivity
    constructor <;> linarith [ht.2]
  have hosc : ∀ i, |lrCoord i t w - lrCoord i c w| ≤ r := by
    intro i
    by_contra hlt
    exact hw ⟨i, t, ht, c, hcK, by rw [abs_of_nonneg (by linarith)]; exact htc, (not_le.1 hlt).le⟩
  exact ⟨mem_preimage_ratBarrierSet_of_cone hθ0 hθπ hcone hct (htc.trans hns) hosc (Or.inr rfl),
    mem_preimage_ratBarrierSet_of_cone hθ0 hθπ hcone hct (htc.trans hns) hosc (Or.inl rfl)⟩

/-! ### Asymptotics -/

theorem tendsto_natCast_mul_exp_neg_rpow {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(c * (n : ℝ) ^ δ))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero δ⁻¹ c hc).comp
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop)
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_rpow_inv (Nat.cast_nonneg n) hδ.ne', neg_mul]

theorem tendsto_exp_neg_mul_rpow {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-(c * (n : ℝ) ^ δ))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc)

theorem tendsto_natCast_rpow_neg {e : ℝ} (he : 0 < e) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-e)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop he).comp tendsto_natCast_atTop_atTop

/-! ### The fixed wedge -/

/-- **No two-sided cone point for one symmetric wedge.** For `0 < θ < π`, `s > 0` and `K`, almost
surely no time of `[-K, K]` is a two-sided cone point of radius `2 s` of a two-sided standard planar
Brownian motion for the closed wedge of angle `θ` around the positive first axis. -/
theorem measure_symmetricConePoint_eq_zero {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ) {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) {s : ℝ}
    (hs : 0 < s) (K : ℕ) :
    μ {w | ∃ t ∈ Icc (-(K : ℝ)) K, IsSymmetricConePoint θ (2 * s) w t} = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s' : ℝ≥0, (s' : ℝ) = s := ⟨s.toNNReal, Real.coe_toNNReal _ hs.le⟩
  have hπθ : 1 < Real.pi / θ := (one_lt_div hθ0).2 hθπ
  set p : ℝ := (1 + Real.pi / θ) / 2 with hp
  set β : ℝ := (1 + p) / 2 with hβ
  have hβ1 : 1 < β := by rw [hβ, hp]; linarith
  have hβp : β < p := by rw [hβ, hp]; linarith
  have hpθ : p * θ < Real.pi := by
    have : p < Real.pi / θ := by rw [hp]; linarith
    calc p * θ < Real.pi / θ * θ := mul_lt_mul_of_pos_right this hθ0
      _ = Real.pi := div_mul_cancel₀ _ hθ0.ne'
  obtain ⟨K₀, hK₀, hK⟩ :=
    forward_wedge_barrier_subcritical_positive hθ0 hθπ (by linarith) hβp hpθ
  set κ : ℝ := (1 / (2 * β) + 1 / 2) / 2 with hκ
  have hβ0 : 0 < β := by linarith
  have h2β : 1 / (2 * β) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hκ1 : κ < 1 / 2 := by rw [hκ]; linarith
  have hκβ : 1 < 2 * κ * β := by
    have : 1 / (2 * β) < κ := by rw [hκ]; linarith
    rw [div_lt_iff₀ (by positivity)] at this
    linarith
  have ha0 : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set A : ℝ := 3 / (Real.sin (θ / 2) * Real.sqrt 2) / Real.sqrt (s : ℝ) with hA
  have hA0 : 0 ≤ A := by positivity
  -- the bound at the scale `1/n`
  let f : ℕ → ℝ := fun n =>
    8 * (2 * K * n + 1) * Real.exp (-(((n : ℝ) ^ (-κ)) ^ 2 * n / 256)) +
      (2 * K * n + 1) * (K₀ * (A * (n : ℝ) ^ (-κ)) ^ β) ^ 2
  have hbound : ∀ n : ℕ, 0 < n → (n : ℝ)⁻¹ ≤ s →
      μ {w | ∃ t ∈ Icc (-(K : ℝ)) K, IsSymmetricConePoint θ (2 * s) w t} ≤
        ENNReal.ofReal (f n) := by
    intro n hn hns
    set r : ℝ := (n : ℝ) ^ (-κ) with hr
    have hr0 : 0 < r := Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) _
    have hb : ∀ k : ℕ, μ (halfIncrements (-(K : ℝ) + k / n) (-1) ⁻¹'
          ratBarrierSet (Real.sin (θ / 2)) (Real.cos (θ / 2)) (2 * r) s ∩
        halfIncrements (-(K : ℝ) + k / n) 1 ⁻¹'
          ratBarrierSet (Real.sin (θ / 2)) (Real.cos (θ / 2)) (2 * r) s) ≤
        ENNReal.ofReal ((K₀ * (A * r) ^ β) ^ 2) := by
      intro k
      have h3 : (3 * r / (Real.sin (θ / 2) * Real.sqrt 2)) / Real.sqrt (s : ℝ) = A * r := by
        rw [hA]; ring
      have hle : ∀ d : ℝ, |d| = 1 → μ (halfIncrements (-(K : ℝ) + k / n) d ⁻¹'
          ratBarrierSet (Real.sin (θ / 2)) (Real.cos (θ / 2)) (2 * r) s) ≤
            ENNReal.ofReal (K₀ * (A * r) ^ β) := by
        intro d hd
        have := measure_preimage_ratBarrierSet_le hμ hK (by positivity : 0 < 2 * r)
          (by linarith : 2 * r < 3 * r) hs (-(K : ℝ) + k / n) hd
        rwa [h3] at this
      rw [measure_preimage_ratBarrierSet_inter hμ, sq, ENNReal.ofReal_mul]
      · exact mul_le_mul' (hle (-1) (by simp)) (hle 1 (by simp))
      · positivity
    calc μ {w | ∃ t ∈ Icc (-(K : ℝ)) K, IsSymmetricConePoint θ (2 * s) w t}
        ≤ μ (oscEvent K (n : ℝ)⁻¹ r) + ∑ k ∈ Finset.range (2 * K * n + 1),
            μ (halfIncrements (-(K : ℝ) + k / n) (-1) ⁻¹'
              ratBarrierSet (Real.sin (θ / 2)) (Real.cos (θ / 2)) (2 * r) s ∩
            halfIncrements (-(K : ℝ) + k / n) 1 ⁻¹'
              ratBarrierSet (Real.sin (θ / 2)) (Real.cos (θ / 2)) (2 * r) s) :=
          (measure_mono (subset_oscEvent_union_barriers hθ0 hθπ K hn hns r)).trans
            ((measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _)))
      _ ≤ ENNReal.ofReal (8 * (2 * K * n + 1) * Real.exp (-(r ^ 2 * n / 256))) +
            ∑ _k ∈ Finset.range (2 * K * n + 1), ENNReal.ofReal ((K₀ * (A * r) ^ β) ^ 2) :=
          add_le_add (measure_oscEvent_le hμ K hn hr0) (Finset.sum_le_sum fun k _ => hb k)
      _ = ENNReal.ofReal (f n) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
          · congr 1
            simp only [f, hr]
            push_cast
            ring
          all_goals positivity
  -- the bound tends to zero
  have hf : Tendsto f atTop (𝓝 0) := by
    have hδ : 0 < 1 - 2 * κ := by linarith
    have h1 := tendsto_natCast_mul_exp_neg_rpow hδ (by norm_num : (0 : ℝ) < 1 / 256)
    have h2 := tendsto_exp_neg_mul_rpow hδ (by norm_num : (0 : ℝ) < 1 / 256)
    have h3 := tendsto_natCast_rpow_neg (by linarith : 0 < 2 * κ * β - 1)
    have h4 := tendsto_natCast_rpow_neg (by positivity : 0 < 2 * κ * β)
    have hlim : Tendsto (fun n : ℕ =>
        8 * (2 * K * ((n : ℝ) * Real.exp (-(1 / 256 * (n : ℝ) ^ (1 - 2 * κ)))) +
            Real.exp (-(1 / 256 * (n : ℝ) ^ (1 - 2 * κ)))) +
          (K₀ * A ^ β) ^ 2 * (2 * K * (n : ℝ) ^ (-(2 * κ * β - 1)) +
            (n : ℝ) ^ (-(2 * κ * β)))) atTop (𝓝 0) := by
      have := ((((h1.const_mul (2 * K : ℝ)).add h2).const_mul 8).add
        (((h3.const_mul (2 * K : ℝ)).add h4).const_mul ((K₀ * A ^ β) ^ 2)))
      simpa using this
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have e1 : ((n : ℝ) ^ (-κ)) ^ 2 * n / 256 = 1 / 256 * (n : ℝ) ^ (1 - 2 * κ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le, ← Real.rpow_add_one hn'.ne']
      ring_nf
    have e2 : (A * (n : ℝ) ^ (-κ)) ^ β = A ^ β * (n : ℝ) ^ (-(κ * β)) := by
      rw [Real.mul_rpow hA0 (Real.rpow_nonneg hn'.le _), ← Real.rpow_mul hn'.le, neg_mul]
    have e3 : (n : ℝ) ^ (-(κ * β)) * (n : ℝ) ^ (-(κ * β)) = (n : ℝ) ^ (-(2 * κ * β)) := by
      rw [← Real.rpow_add hn']
      ring_nf
    have e4 : (n : ℝ) * (n : ℝ) ^ (-(2 * κ * β)) = (n : ℝ) ^ (-(2 * κ * β - 1)) := by
      rw [show -(2 * κ * β - 1) = -(2 * κ * β) + 1 by ring, Real.rpow_add_one hn'.ne']
      ring
    simp only [f, e1, e2]
    rw [← e4, ← e3]
    ring
  have hev : ∀ᶠ n : ℕ in atTop,
      μ {w | ∃ t ∈ Icc (-(K : ℝ)) K, IsSymmetricConePoint θ (2 * s) w t} ≤
        ENNReal.ofReal (f n) := by
    filter_upwards [eventually_gt_atTop ⌈(s : ℝ)⁻¹⌉₊] with n hn
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
    have hn' : (s : ℝ)⁻¹ < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
    refine hbound n hn0 ?_
    rw [inv_le_comm₀ (Nat.cast_pos.2 hn0) (by exact_mod_cast hs)]
    exact hn'.le
  have hlim0 := ENNReal.tendsto_ofReal hf
  rw [ENNReal.ofReal_zero] at hlim0
  exact le_antisymm (ge_of_tendsto hlim0 hev) zero_le

end MatedCRT.PlanarBMConePoints
