import MatedCRT.FirstPass.Derived.ChartStopPathContinuity
import MatedCRT.FirstPass.Derived.InterpolatedWalkPath

/-!
# The frozen chart path of a walk and the chart image of the stopped limiting path

A walk on the cells of a window is *frozen* before its first step to a cell which is not inside the window, and its
positions are drawn in the inverse chart of the window. This file proves the deterministic part of the comparison of
Berestycki–Gwynne (2020), proof of Lemma 7.21 (written answer MQ-sbl-35, lines 40-47): if the interpolated planar
walks converge locally uniformly to a path `y` which leaves `{D ≥ 0}` no later than the window `{D > 0}`, then the
interpolated frozen chart paths converge to the chart image `ψ ∘ y(· ∧ τ)` of `y` stopped at its exit time `τ` from
the window.

The positions `P k i` of the walk at level `k` and the predicate `In k i` ("the `i`-th position is inside") are
abstract. Only two properties link them to the signed distances `Dk k` of the windows: an inside position has
`Dk k > 0`, and a position with `Dk k > r k` is inside, where `r k → 0` bounds the cell diameters.

* `MatedCRT.FrozenPath.frozenIdx`: the index of the frozen position at step `i`.
* `MatedCRT.FrozenPath.tendsto_linPath_meshValues`: re-interpolating a convergent sequence of paths at the mesh times
  `i / m k`, `m k → ∞`, does not change the limit.
* `MatedCRT.FrozenPath.tendsto_linPath_frozen`: the main statement.

The exit time of the frozen walk lies between a mesh time at which the planar walk is strictly inside the window and
the first mesh time at which it is strictly outside its closure; both tend to `τ` (at a crossing every strict exterior
visit of `y` persists on an open time interval, which contains mesh times for large `k`).
-/

set_option autoImplicit false

open Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

namespace FrozenPath

/-! ### Paths interpolating sequences -/

/-- The path `t ↦ linInterp a (m t)` interpolating the sequence `a` at the time step `1 / m`. -/
noncomputable def linPath (a : ℕ → ℂ) {m : ℝ} (hm : 0 ≤ m) : ContinuousPath ℂ :=
  interpPathCM (fun j : ℤ => a j.toNat) hm (fun i => (i : ℤ))

theorem linPath_apply (a : ℕ → ℂ) {m : ℝ} (hm : 0 ≤ m) (t : ℝ≥0) :
    linPath a hm t = linInterp a (m * t) := by
  simp [linPath, interpPathFn]

theorem interpPathCM_eq_linPath (V : ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) (x : ℕ → ℤ) :
    interpPathCM V hm x = linPath (fun i => V (x i)) hm := by
  ext t
  rw [linPath_apply]
  rfl

theorem linInterp_nat (a : ℕ → ℂ) (n : ℕ) : linInterp a (n : ℝ) = a n := by
  simp [linInterp]

/-- A linearly interpolated value is a convex combination of the two neighbouring values. -/
theorem norm_linInterp_sub_le (a : ℕ → ℂ) {s : ℝ} (hs : 0 ≤ s) (c : ℂ) :
    ‖linInterp a s - c‖ ≤ max ‖a ⌊s⌋₊ - c‖ ‖a (⌊s⌋₊ + 1) - c‖ := by
  set θ : ℝ := s - ⌊s⌋₊ with hθ
  have hθ0 : 0 ≤ θ := sub_nonneg.2 (Nat.floor_le hs)
  have hθ1 : θ ≤ 1 := by
    have := Nat.lt_floor_add_one s
    linarith
  have heq : linInterp a s - c =
      ((1 - θ : ℝ) : ℂ) * (a ⌊s⌋₊ - c) + ((θ : ℝ) : ℂ) * (a (⌊s⌋₊ + 1) - c) := by
    simp only [linInterp]
    rw [← hθ]
    push_cast
    ring
  rw [heq]
  calc ‖((1 - θ : ℝ) : ℂ) * (a ⌊s⌋₊ - c) + ((θ : ℝ) : ℂ) * (a (⌊s⌋₊ + 1) - c)‖
      ≤ ‖((1 - θ : ℝ) : ℂ) * (a ⌊s⌋₊ - c)‖ + ‖((θ : ℝ) : ℂ) * (a (⌊s⌋₊ + 1) - c)‖ := norm_add_le _ _
    _ = (1 - θ) * ‖a ⌊s⌋₊ - c‖ + θ * ‖a (⌊s⌋₊ + 1) - c‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
          Real.norm_of_nonneg hθ0]
    _ ≤ (1 - θ) * max ‖a ⌊s⌋₊ - c‖ ‖a (⌊s⌋₊ + 1) - c‖ + θ * max ‖a ⌊s⌋₊ - c‖ ‖a (⌊s⌋₊ + 1) - c‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hθ0)
    _ = max ‖a ⌊s⌋₊ - c‖ ‖a (⌊s⌋₊ + 1) - c‖ := by ring

/-- Interpolating a sequence frozen from the index `σ` on is interpolating the sequence up to the time `σ`. -/
theorem linInterp_min (a : ℕ → ℂ) (σ : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    linInterp (fun i => a (min i σ)) s = linInterp a (min s (σ : ℝ)) := by
  rcases le_or_gt (σ : ℝ) s with h | h
  · rw [min_eq_right h, linInterp_nat]
    have hfl : σ ≤ ⌊s⌋₊ := Nat.le_floor h
    simp only [linInterp]
    rw [min_eq_right hfl, min_eq_right (by omega : σ ≤ ⌊s⌋₊ + 1)]
    push_cast
    ring
  · rw [min_eq_left h.le]
    have hfl : ⌊s⌋₊ < σ := (Nat.floor_lt hs).2 h
    simp only [linInterp]
    rw [min_eq_left hfl.le, min_eq_left (by omega : ⌊s⌋₊ + 1 ≤ σ)]

/-! ### Locally uniform convergence of paths -/

section Uniform

variable {E : Type*} [PseudoMetricSpace E]

theorem tendsto_of_forall_dist_lt {F : ℕ → C(ℝ≥0, E)} {L : C(ℝ≥0, E)}
    (h : ∀ T : ℝ≥0, ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, ∀ t ≤ T, dist (F k t) (L t) < e) :
    Tendsto F atTop (𝓝 L) := by
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨T, hT⟩ := hK.bddAbove
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  filter_upwards [h T e he] with k hk t ht
  rw [dist_comm]
  exact hk t (hT ht)

theorem eventually_forall_dist_lt {F : ℕ → C(ℝ≥0, E)} {L : C(ℝ≥0, E)} (h : Tendsto F atTop (𝓝 L))
    (T : ℝ≥0) {e : ℝ} (he : 0 < e) : ∀ᶠ k in atTop, ∀ t ≤ T, dist (F k t) (L t) < e := by
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff_forall_isCompact] at h
  have h' := Metric.tendstoUniformlyOn_iff.1 (h (Icc 0 T) isCompact_Icc) e he
  filter_upwards [h'] with k hk t ht
  rw [dist_comm]
  exact hk t ⟨zero_le, ht⟩

end Uniform

theorem coe_toNNReal_div (i : ℕ) {m : ℝ} (hm : 0 ≤ m) : ((Real.toNNReal (i / m) : ℝ≥0) : ℝ) = i / m :=
  Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg i) hm)

/-- **Re-interpolation at the mesh times.** If `H k → L` locally uniformly and `m k → ∞`, the paths interpolating the
values `H k (i / m k)` at the time step `1 / m k` converge to `L`. -/
theorem tendsto_linPath_meshValues {H : ℕ → ContinuousPath ℂ} {L : ContinuousPath ℂ}
    (hH : Tendsto H atTop (𝓝 L)) {m : ℕ → ℝ} (hm0 : ∀ k, 0 ≤ m k) (hm : Tendsto m atTop atTop) :
    Tendsto (fun k => linPath (fun i => H k (Real.toNNReal (i / m k))) (hm0 k)) atTop (𝓝 L) := by
  refine tendsto_of_forall_dist_lt fun T e he => ?_
  have hUC := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T + 1)).uniformContinuousOn_of_continuous
    L.continuous.continuousOn
  obtain ⟨δ, hδ, hδL⟩ := Metric.uniformContinuousOn_iff.1 hUC (e / 2) (by linarith)
  have h1 := eventually_forall_dist_lt hH (T + 1) (half_pos he)
  have h2 : ∀ᶠ k in atTop, max 1 (1 / δ) < m k := hm.eventually_gt_atTop _
  filter_upwards [h1, h2] with k hk hmk t ht
  rw [linPath_apply, dist_eq_norm]
  have hm1 : 1 < m k := lt_of_le_of_lt (le_max_left _ _) hmk
  have hmpos : 0 < m k := by linarith
  have hmδ : 1 / m k < δ := by
    have h3 : 1 / δ < m k := lt_of_le_of_lt (le_max_right _ _) hmk
    rw [div_lt_iff₀ hmpos]
    rw [div_lt_iff₀ hδ] at h3
    linarith
  have hm1' : 1 / m k < 1 := by
    rw [div_lt_one hmpos]
    exact hm1
  have hs0 : 0 ≤ m k * t := mul_nonneg (hm0 k) t.2
  have hts : (t : ℝ) = m k * t / m k := by
    rw [mul_div_cancel_left₀ _ hmpos.ne']
  have htT : (t : ℝ) ≤ T := by exact_mod_cast ht
  have key : ∀ j : ℕ, (j : ℝ) ≤ m k * t + 1 → m k * t - 1 ≤ j →
      ‖H k (Real.toNNReal (j / m k)) - L t‖ < e := by
    intro j hj1 hj2
    have hτ : ((Real.toNNReal (j / m k) : ℝ≥0) : ℝ) = j / m k := coe_toNNReal_div j (hm0 k)
    have hdist : dist (Real.toNNReal (j / m k)) t < δ := by
      rw [NNReal.dist_eq, hτ, hts, ← sub_div, abs_div, abs_of_pos hmpos, div_lt_iff₀ hmpos]
      have : |(j : ℝ) - m k * t| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
      rw [div_lt_iff₀ hmpos] at hmδ
      linarith
    have hτT : Real.toNNReal (j / m k) ≤ T + 1 := by
      rw [← NNReal.coe_le_coe, hτ, NNReal.coe_add, NNReal.coe_one]
      have hle : (j : ℝ) / m k ≤ (m k * t + 1) / m k := div_le_div_of_nonneg_right hj1 hmpos.le
      rw [add_div, ← hts] at hle
      linarith
    have htT1 : t ≤ T + 1 := le_trans ht le_self_add
    have hA := hk _ hτT
    have hB := hδL _ ⟨zero_le, hτT⟩ t ⟨zero_le, htT1⟩ hdist
    rw [← dist_eq_norm]
    calc dist (H k (Real.toNNReal (j / m k))) (L t)
        ≤ dist (H k (Real.toNNReal (j / m k))) (L (Real.toNNReal (j / m k))) +
          dist (L (Real.toNNReal (j / m k))) (L t) := dist_triangle _ _ _
      _ < e / 2 + e / 2 := add_lt_add hA hB
      _ = e := by ring
  refine lt_of_le_of_lt (norm_linInterp_sub_le _ hs0 _) (max_lt ?_ ?_)
  · exact key ⌊m k * t⌋₊ (by linarith [Nat.floor_le hs0]) (by linarith [Nat.lt_floor_add_one (m k * t)])
  · exact key (⌊m k * t⌋₊ + 1) (by push_cast; linarith [Nat.floor_le hs0])
      (by push_cast; linarith [Nat.lt_floor_add_one (m k * t)])

/-! ### The frozen index -/

open Classical in
/-- **The index of the frozen position at step `i`**: `i` while the positions `0, …, i` are all inside, afterwards
the last of these indices. -/
noncomputable def frozenIdx (In : ℕ → Prop) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if ∀ j ≤ i + 1, In j then i + 1 else frozenIdx In i

theorem frozenIdx_eq_self {In : ℕ → Prop} {i : ℕ} (h : ∀ j ≤ i, In j) : frozenIdx In i = i := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [frozenIdx]
    exact ite_eq_left h

open Classical in
/-- Before the first position outside, the frozen index is the step; afterwards it is the last inside index. -/
theorem frozenIdx_eq_min {In : ℕ → Prop} (hex : ∃ j, ¬ In j) (i : ℕ) :
    frozenIdx In i = min i (Nat.find hex - 1) := by
  induction i with
  | zero => simp [frozenIdx]
  | succ i ih =>
    simp only [frozenIdx]
    by_cases h : ∀ j ≤ i + 1, In j
    · rw [ite_eq_left h]
      have hlt : i + 1 < Nat.find hex := by
        by_contra hle
        exact Nat.find_spec hex (h _ (not_lt.1 hle))
      rw [min_eq_left (show i + 1 ≤ Nat.find hex - 1 by omega)]
    · rw [ite_eq_right h, ih]
      obtain ⟨j, hj, hjn⟩ : ∃ j ≤ i + 1, ¬ In j := by
        by_contra hc
        exact h fun j hj => by_contra fun hn => hc ⟨j, hj, hn⟩
      have hle : Nat.find hex ≤ j := Nat.find_min' hex hjn
      rw [min_eq_right (show Nat.find hex - 1 ≤ i by omega),
        min_eq_right (show Nat.find hex - 1 ≤ i + 1 by omega)]

open Classical in
theorem mem_of_le_find_sub_one {In : ℕ → Prop} (hex : ∃ j, ¬ In j) {j : ℕ} (hj : j ≤ Nat.find hex - 1)
    (h0 : In 0) : In j := by
  have hN : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact this h0
  by_contra hn
  have := Nat.find_min' hex hn
  omega

/-! ### The main statement -/

open Classical in
/-- The exit time of the frozen walk: `(N - 1) / m` for the first index `N` of a position outside, `∞` if there is
none. -/
noncomputable def frozenTime (In : ℕ → Prop) (m : ℝ) : ℝ≥0∞ :=
  if hex : ∃ j, ¬ In j then ((Real.toNNReal (((Nat.find hex - 1 : ℕ) : ℝ) / m) : ℝ≥0) : ℝ≥0∞) else ⊤

/-- The frozen planar path is the planar path stopped at the exit time of the frozen walk. -/
theorem linPath_frozenIdx {a : ℕ → ℂ} {In : ℕ → Prop} {m : ℝ} (hm : 0 < m) :
    linPath (fun i => a (frozenIdx In i)) hm.le = (linPath a hm.le).comp (exitClamp (frozenTime In m)) := by
  classical
  ext t
  rw [ContinuousMap.comp_apply, linPath_apply, linPath_apply, exitClamp_apply]
  unfold frozenTime
  by_cases hex : ∃ j, ¬ In j
  · rw [dite_eq_left hex, ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe]
    have hfz : (fun i => a (frozenIdx In i)) = fun i => a (min i (Nat.find hex - 1)) :=
      funext fun i => by rw [frozenIdx_eq_min hex i]
    rw [hfz, linInterp_min a _ (mul_nonneg hm.le (NNReal.coe_nonneg t))]
    congr 1
    rw [NNReal.coe_min, coe_toNNReal_div _ hm.le, mul_min_of_nonneg _ _ hm.le, mul_div_cancel₀ _ hm.ne']
  · rw [dite_eq_right hex, ite_eq_left rfl]
    have hall : ∀ j, In j := fun j => by_contra fun hn => hex ⟨j, hn⟩
    have hfz : (fun i => a (frozenIdx In i)) = a :=
      funext fun i => by rw [frozenIdx_eq_self fun j _ => hall j]
    rw [hfz]

/-- **The frozen chart paths converge to the chart image of the stopped limiting path.** Let `m k → ∞`, `r k → 0`,
`ψk k → ψ`, `Dk k → D` locally uniformly, and let the planar paths interpolating the positions `P k` at the time
step `1 / m k` converge to `y`. Suppose that the position `0` is inside, that an inside position has `Dk k > 0` and
that a position with `Dk k > r k` is inside. If `y` leaves `{D ≥ 0}` no later than `{D > 0}`, then the paths
interpolating the chart values `ψk k` of the positions frozen before the first position outside converge to
`ψ ∘ y(· ∧ τ)`, `τ` the exit time of `y` from `{D > 0}`. -/
theorem tendsto_linPath_frozen {y : ContinuousPath ℂ} {ψ : C(ℂ, ℂ)} {D : C(ℂ, ℝ)}
    (hcross : ContinuousPath.exitTime {z | 0 ≤ D z} y ≤ ContinuousPath.exitTime (gapDomain D) y)
    {m r : ℕ → ℝ} (hm0 : ∀ k, 0 ≤ m k) (hm : Tendsto m atTop atTop) (hr : Tendsto r atTop (𝓝 0))
    {ψk : ℕ → C(ℂ, ℂ)} (hψ : Tendsto ψk atTop (𝓝 ψ)) {Dk : ℕ → C(ℂ, ℝ)} (hD : Tendsto Dk atTop (𝓝 D))
    {P : ℕ → ℕ → ℂ} {In : ℕ → ℕ → Prop}
    (hI : Tendsto (fun k => linPath (P k) (hm0 k)) atTop (𝓝 y))
    (h1 : ∀ k i, In k i → 0 < Dk k (P k i)) (h2 : ∀ k i, r k < Dk k (P k i) → In k i)
    (h0 : ∀ k, In k 0) :
    Tendsto (fun k => linPath (fun i => ψk k (P k (frozenIdx (In k) i))) (hm0 k)) atTop
      (𝓝 (chartStopPath (gapDomain D) ψ y)) := by
  classical
  set I : ℕ → ContinuousPath ℂ := fun k => linPath (P k) (hm0 k)
  set τ : ℝ≥0∞ := ContinuousPath.exitTime (gapDomain D) y
  set tk : ℕ → ℝ≥0∞ := fun k => frozenTime (In k) (m k) with htk
  -- the signed distances along the planar paths converge
  have hg : Tendsto (fun k => (Dk k).comp (I k)) atTop (𝓝 (D.comp y)) :=
    (ContinuousMap.continuous_comp'.tendsto (y, D)).comp (hI.prodMk_nhds hD)
  -- the values of the planar path at the mesh times
  have hmesh : ∀ k (i : ℕ), 0 < m k → I k (Real.toNNReal (i / m k)) = P k i := by
    intro k i hmk
    show linPath (P k) (hm0 k) (Real.toNNReal (i / m k)) = P k i
    rw [linPath_apply, coe_toNNReal_div i (hm0 k), mul_div_cancel₀ _ hmk.ne', linInterp_nat]
  -- the exit time of the frozen walk tends to `τ`
  have htime : Tendsto tk atTop (𝓝 τ) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨T₂, haT₂, hT₂τ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
      obtain ⟨T₁, haT₁, hT₁₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 haT₂
      have hT₁₂' : T₁ < T₂ := ENNReal.coe_lt_coe.1 hT₁₂
      have hpos : ∀ s ∈ Icc (0 : ℝ≥0) T₂, 0 < D (y s) := by
        intro s hs
        have hlt : (s : ℝ≥0∞) < pathExitTime (Ioi (0 : ℝ)) ⇑(D.comp y) := by
          rw [← exitTime_gapDomain]
          exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) hT₂τ
        exact GapExit.mem_of_lt_pathExitTime hlt
      obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le : (0 : ℝ≥0) ≤ T₂))
        (D.comp y).continuous.continuousOn
      set c : ℝ := D (y s₀)
      have hc0 : 0 < c := hpos s₀ hs₀
      have hev1 := eventually_forall_dist_lt hg T₂ (half_pos hc0)
      have hev2 : ∀ᶠ k in atTop, r k < c / 2 := hr.eventually (eventually_lt_nhds (half_pos hc0))
      have hgap : (0 : ℝ) < (T₂ : ℝ) - T₁ := sub_pos.2 hT₁₂'
      have hev3 : ∀ᶠ k in atTop, max 1 (1 / ((T₂ : ℝ) - T₁)) < m k := hm.eventually_gt_atTop _
      filter_upwards [hev1, hev2, hev3] with k hk1 hk2 hk3
      have hmk : 0 < m k := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hk3.le)
      have hinv : 1 / m k < (T₂ : ℝ) - T₁ := by
        have h3 : 1 / ((T₂ : ℝ) - T₁) < m k := lt_of_le_of_lt (le_max_right _ _) hk3
        rw [div_lt_iff₀ hmk]
        rw [div_lt_iff₀ hgap] at h3
        linarith
      -- every mesh index up to `m T₂` is inside
      have hin : ∀ i : ℕ, (i : ℝ) ≤ m k * T₂ → In k i := by
        intro i hi
        have hsT : Real.toNNReal (i / m k) ≤ T₂ := by
          rw [← NNReal.coe_le_coe, coe_toNNReal_div i (hm0 k), div_le_iff₀ hmk]
          linarith
        have hd := hk1 _ hsT
        rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, hmesh k i hmk, Real.dist_eq] at hd
        have hmn : c ≤ D (y (Real.toNNReal (i / m k))) := isMinOn_iff.1 hmin _ ⟨zero_le, hsT⟩
        refine h2 k i ?_
        have := (abs_lt.1 hd).1
        linarith
      refine lt_of_lt_of_le haT₁ ?_
      simp only [htk, frozenTime]
      by_cases hex : ∃ j, ¬ In k j
      · rw [dite_eq_left hex, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
          Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hmk.le), le_div_iff₀ hmk]
        have hN : m k * T₂ < (Nat.find hex : ℝ) := by
          by_contra hle
          exact Nat.find_spec hex (hin _ (not_lt.1 hle))
        have hN1 : 1 ≤ Nat.find hex := by
          by_contra h
          have h' : Nat.find hex = 0 := by omega
          have := Nat.find_spec hex
          rw [h'] at this
          exact this (h0 k)
        have hcast : ((Nat.find hex - 1 : ℕ) : ℝ) = (Nat.find hex : ℝ) - 1 := by
          rw [Nat.cast_sub hN1, Nat.cast_one]
        rw [hcast]
        rw [div_lt_iff₀ hmk] at hinv
        nlinarith
      · rw [dite_eq_right hex]
        exact le_top
    · -- a strict exterior visit before `a`
      have hlt : pathExitTime (Ici (0 : ℝ)) ⇑(D.comp y) < a := by
        rw [← exitTime_setOf_nonneg]
        exact lt_of_le_of_lt hcross ha
      obtain ⟨t', ht'a, ht'⟩ := GapExit.exists_lt_of_pathExitTime_lt hlt
      have hneg : D (y t') < 0 := by
        simp only [ContinuousMap.comp_apply, mem_Ici, not_le] at ht'
        exact ht'
      obtain ⟨b, ht'b, hba⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht'a
      have ht'b' : (t' : ℝ) < b := by exact_mod_cast ENNReal.coe_lt_coe.1 ht'b
      set c : ℝ := -D (y t') with hc
      have hc0 : 0 < c := by linarith
      obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.1 (D.comp y).continuous t' (c / 2) (half_pos hc0)
      have hδ'0 : 0 < min δ ((b : ℝ) - t') := lt_min hδ (sub_pos.2 ht'b')
      have hδ'δ : min δ ((b : ℝ) - t') ≤ δ := min_le_left _ _
      have hδ'b : min δ ((b : ℝ) - t') ≤ (b : ℝ) - t' := min_le_right _ _
      have hev1 := eventually_forall_dist_lt hg (t' + 1) (half_pos hc0)
      have hev3 : ∀ᶠ k in atTop, max 1 (1 / min δ ((b : ℝ) - t')) < m k := hm.eventually_gt_atTop _
      filter_upwards [hev1, hev3] with k hk1 hk3
      have hmk1 : 1 < m k := lt_of_le_of_lt (le_max_left _ _) hk3
      have hmk : 0 < m k := lt_trans one_pos hmk1
      have hinv : 1 / m k < min δ ((b : ℝ) - t') := by
        have h3 : 1 / min δ ((b : ℝ) - t') < m k := lt_of_le_of_lt (le_max_right _ _) hk3
        rw [div_lt_iff₀ hmk]
        rw [div_lt_iff₀ hδ'0] at h3
        linarith
      have hinv1 : 1 / m k < 1 := by
        rw [div_lt_one hmk]
        exact hmk1
      -- the mesh index just after `t'`
      set i : ℕ := ⌈m k * t'⌉₊ with hi
      have hmt : 0 ≤ m k * t' := mul_nonneg hmk.le t'.2
      have hi1 : m k * t' ≤ i := Nat.le_ceil _
      have hi2 : (i : ℝ) < m k * t' + 1 := Nat.ceil_lt_add_one hmt
      set si : ℝ≥0 := Real.toNNReal (i / m k) with hsi
      have hsi' : (si : ℝ) = i / m k := coe_toNNReal_div i (hm0 k)
      have hsi1 : (t' : ℝ) ≤ si := by
        rw [hsi', le_div_iff₀ hmk]
        linarith [mul_comm (t' : ℝ) (m k)]
      have hsi2 : (si : ℝ) < t' + 1 / m k := by
        rw [hsi', div_lt_iff₀ hmk, add_mul, one_div_mul_cancel hmk.ne']
        linarith [mul_comm (t' : ℝ) (m k)]
      have hsiT : si ≤ t' + 1 := by
        rw [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_one]
        linarith
      have hdist : dist si t' < δ := by
        rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 hsi1)]
        linarith
      have hDy : D (y si) < -c / 2 := by
        have := hδc si hdist
        simp only [ContinuousMap.comp_apply, Real.dist_eq] at this
        have := (abs_lt.1 this).2
        linarith
      have hd := hk1 si hsiT
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, Real.dist_eq] at hd
      have hDk : Dk k (I k si) < 0 := by
        have := (abs_lt.1 hd).2
        linarith
      rw [hsi, hmesh k i hmk] at hDk
      have hout : ¬ In k i := fun h => absurd (h1 k i h) (not_lt.2 hDk.le)
      have hex : ∃ j, ¬ In k j := ⟨i, hout⟩
      simp only [htk, frozenTime]
      rw [dite_eq_left hex]
      have hle : Nat.find hex ≤ i := Nat.find_min' hex hout
      have hfin : Real.toNNReal (((Nat.find hex - 1 : ℕ) : ℝ) / m k) < b := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hmk.le)]
        have h4 : ((Nat.find hex - 1 : ℕ) : ℝ) ≤ i := by
          have : Nat.find hex - 1 ≤ i := by omega
          exact_mod_cast this
        have h5 : ((Nat.find hex - 1 : ℕ) : ℝ) / m k ≤ i / m k := div_le_div_of_nonneg_right h4 hmk.le
        rw [← hsi'] at h5
        linarith
      exact lt_trans (ENNReal.coe_lt_coe.2 hfin) hba
  -- the frozen planar paths converge to the stopped path
  have hJ : Tendsto (fun k => (I k).comp (exitClamp (tk k))) atTop (𝓝 (y.comp (exitClamp τ))) :=
    (ContinuousMap.continuous_comp'.tendsto (exitClamp τ, y)).comp
      ((continuous_exitClamp.tendsto τ |>.comp htime).prodMk_nhds hI)
  have hH : Tendsto (fun k => (ψk k).comp ((I k).comp (exitClamp (tk k)))) atTop
      (𝓝 (chartStopPath (gapDomain D) ψ y)) :=
    (ContinuousMap.continuous_comp'.tendsto (y.comp (exitClamp τ), ψ)).comp (hJ.prodMk_nhds hψ)
  have hlim := tendsto_linPath_meshValues hH hm0 hm
  refine hlim.congr' ?_
  filter_upwards [hm.eventually_gt_atTop 0] with k hmk
  congr 1
  funext i
  have hfr := linPath_frozenIdx (a := P k) (In := In k) hmk
  rw [ContinuousMap.comp_apply]
  congr 1
  show ((linPath (P k) (hm0 k)).comp (exitClamp (frozenTime (In k) (m k)))) (Real.toNNReal (i / m k)) =
    P k (frozenIdx (In k) i)
  rw [← hfr, linPath_apply, coe_toNNReal_div i (hm0 k), mul_div_cancel₀ _ hmk.ne', linInterp_nat]

end FrozenPath

end MatedCRT
