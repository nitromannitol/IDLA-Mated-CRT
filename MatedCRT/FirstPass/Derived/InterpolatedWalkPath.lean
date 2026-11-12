import MatedCRT.Defs.Setting

/-!
# The interpolated embedded walk as a continuous path depending measurably on the walk

For a labelling `v : ℤ → ℂ` of the vertices, a speed `m ≥ 0` and a walk `x : ℕ → ℤ`, the path
`t ↦ (1 - θ) v(x n) + θ v(x (n+1))`, `n = ⌊m t⌋₊`, `θ = m t - n` (the interpolated embedded walk
`MatedCRT.interpolatedWalk`, line 734 and Section 3.3 of the draft) is continuous in `t`.
This defines `interpPathCM v hm x : ContinuousPath ℂ = C(ℝ≥0, ℂ)`, and `x ↦ interpPathCM v hm x`
is continuous for the product topology on `ℕ → ℤ` and the compact-open topology, hence measurable
for the product `σ`-algebra and the Borel `σ`-algebra of the compact-open topology.

The proof compares the interpolation on `[0, N]` with the finite sum of clamped increments
`a₀ + ∑_{k<N} (a_{k+1} - a_k) · clamp₀¹(s - k)`, which depends on `x` through finitely many
coordinates and is continuous in `s`.
-/

open Filter Topology MarkovProcess
open scoped NNReal

namespace MatedCRT

/-- Linear interpolation of the sequence `a` at the real time `s ≥ 0`
(the shape of `interpolatedWalk`). -/
noncomputable def linInterp (a : ℕ → ℂ) (s : ℝ) : ℂ :=
  ((1 - (s - ⌊s⌋₊) : ℝ) : ℂ) * a ⌊s⌋₊ + ((s - ⌊s⌋₊ : ℝ) : ℂ) * a (⌊s⌋₊ + 1)

/-- The finite sum `a₀ + ∑_{k<N} (a_{k+1} - a_k) · clamp₀¹(s - k)`; it equals `linInterp a s` for
`0 ≤ s` with `⌊s⌋₊ < N`. -/
noncomputable def linInterpTrunc (a : ℕ → ℂ) (N : ℕ) (s : ℝ) : ℂ :=
  a 0 + ∑ k ∈ Finset.range N, (a (k + 1) - a k) * ((max 0 (min 1 (s - k)) : ℝ) : ℂ)

theorem continuous_linInterpTrunc (a : ℕ → ℂ) (N : ℕ) : Continuous (linInterpTrunc a N) := by
  unfold linInterpTrunc
  refine continuous_const.add (continuous_finsetSum _ fun k _ => continuous_const.mul ?_)
  exact Complex.continuous_ofReal.comp
    (continuous_const.max (continuous_const.min (continuous_id.sub continuous_const)))

theorem linInterpTrunc_congr {a b : ℕ → ℂ} {N : ℕ} (h : ∀ k ≤ N, a k = b k) (s : ℝ) :
    linInterpTrunc a N s = linInterpTrunc b N s := by
  unfold linInterpTrunc
  rw [h 0 (Nat.zero_le _)]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < N := Finset.mem_range.1 hk
  rw [h k hk'.le, h (k + 1) hk']

theorem linInterp_eq_linInterpTrunc (a : ℕ → ℂ) {s : ℝ} (hs : 0 ≤ s) {N : ℕ} (hN : ⌊s⌋₊ < N) :
    linInterp a s = linInterpTrunc a N s := by
  have hn_le : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs
  have hs_lt : s < ⌊s⌋₊ + 1 := Nat.lt_floor_add_one s
  unfold linInterpTrunc
  have hsub : ∑ k ∈ Finset.range N, (a (k + 1) - a k) * ((max 0 (min 1 (s - k)) : ℝ) : ℂ)
      = ∑ k ∈ Finset.range (⌊s⌋₊ + 1), (a (k + 1) - a k) * ((max 0 (min 1 (s - k)) : ℝ) : ℂ) := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro k _ hk'
    have hk2 : ⌊s⌋₊ + 1 ≤ k := by simpa using hk'
    have hk3 : ((⌊s⌋₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk2
    push_cast at hk3
    have h0 : s - k < 0 := by linarith
    have hc : max 0 (min 1 (s - k)) = 0 := by
      rw [min_eq_right (by linarith)]
      exact max_eq_left h0.le
    simp [hc]
  rw [hsub, Finset.sum_range_succ]
  have hone : ∀ k ∈ Finset.range ⌊s⌋₊, (a (k + 1) - a k) * ((max 0 (min 1 (s - k)) : ℝ) : ℂ)
      = a (k + 1) - a k := by
    intro k hk
    have hk2 : (k : ℝ) + 1 ≤ ⌊s⌋₊ := by exact_mod_cast Finset.mem_range.1 hk
    have hc : max 0 (min 1 (s - k)) = 1 := by
      rw [min_eq_left (by linarith), max_eq_right zero_le_one]
    simp [hc]
  rw [Finset.sum_congr rfl hone, Finset.sum_range_sub a]
  have hlast : max 0 (min 1 (s - (⌊s⌋₊ : ℕ))) = s - ⌊s⌋₊ := by
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  rw [hlast]
  unfold linInterp
  push_cast
  ring

/-- The interpolation of the embedded walk (the function underlying `interpolatedWalk`):
`t ↦ (1 - θ) v(x n) + θ v(x (n+1))` with `n = ⌊m t⌋₊`, `θ = m t - n`. -/
noncomputable def interpPathFn (v : ℤ → ℂ) (m : ℝ) (x : ℕ → ℤ) (t : ℝ≥0) : ℂ :=
  linInterp (fun k => v (x k)) (m * t)

theorem interpolatedWalk_eq_interpPathFn (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) (x : ℕ → ℤ) (t : ℝ≥0) :
    interpolatedWalk ε η m x t = interpPathFn (vertexPoint ε η) m x t := rfl

/-- Joint continuity in the walk (product topology, `ℤ` discrete) and the time. -/
theorem continuous_interpPathFn_uncurry (v : ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) :
    Continuous (fun p : (ℕ → ℤ) × ℝ≥0 => interpPathFn v m p.1 p.2) := by
  refine continuous_iff_continuousAt.2 fun ⟨x0, t0⟩ => ?_
  set N : ℕ := ⌊m * (t0 : ℝ)⌋₊ + 2 with hN
  have hlt : m * (t0 : ℝ) < N := by
    have := Nat.lt_floor_add_one (m * (t0 : ℝ))
    rw [hN]; push_cast; linarith
  have h1 : ∀ᶠ t : ℝ≥0 in 𝓝 t0, m * (t : ℝ) < N :=
    (continuous_const.mul NNReal.continuous_coe).continuousAt.eventually_lt continuousAt_const hlt
  have h1' : ∀ᶠ p : (ℕ → ℤ) × ℝ≥0 in 𝓝 (x0, t0), m * (p.2 : ℝ) < N :=
    Filter.Tendsto.eventually (continuousAt_snd (p := (x0, t0))) h1
  have h2 : ∀ᶠ p : (ℕ → ℤ) × ℝ≥0 in 𝓝 (x0, t0), ∀ k ∈ Finset.range (N + 1), p.1 k = x0 k := by
    refine (Filter.eventually_all_finset _).2 fun k _ => ?_
    have hk : ContinuousAt (fun p : (ℕ → ℤ) × ℝ≥0 => p.1 k) (x0, t0) :=
      ((continuous_apply k).comp continuous_fst).continuousAt
    exact hk.eventually (isOpen_discrete ({x0 k} : Set ℤ) |>.mem_nhds rfl)
  have hg : Continuous (fun p : (ℕ → ℤ) × ℝ≥0 =>
      linInterpTrunc (fun k => v (x0 k)) N (m * (p.2 : ℝ))) :=
    (continuous_linInterpTrunc _ N).comp (continuous_const.mul (NNReal.continuous_coe.comp continuous_snd))
  refine hg.continuousAt.congr ?_
  filter_upwards [h1', h2] with p hp1 hp2
  have hfl : ⌊m * (p.2 : ℝ)⌋₊ < N := (Nat.floor_lt (mul_nonneg hm (NNReal.coe_nonneg p.2))).2 hp1
  unfold interpPathFn
  rw [linInterp_eq_linInterpTrunc _ (mul_nonneg hm (NNReal.coe_nonneg p.2)) hfl]
  refine linInterpTrunc_congr (fun k hk => ?_) _
  rw [hp2 k (Finset.mem_range.2 (Nat.lt_succ_of_le hk))]

theorem continuous_interpPathFn (v : ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) (x : ℕ → ℤ) :
    Continuous (interpPathFn v m x) :=
  (continuous_interpPathFn_uncurry v hm).comp (continuous_const.prodMk continuous_id)

/-- The interpolated embedded walk as a continuous path `ℝ≥0 → ℂ` (an element of `ContinuousPath ℂ`). -/
noncomputable def interpPathCM (v : ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) (x : ℕ → ℤ) : ContinuousPath ℂ where
  toFun := interpPathFn v m x
  continuous_toFun := continuous_interpPathFn v hm x

@[simp] theorem interpPathCM_apply (v : ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) (x : ℕ → ℤ) (t : ℝ≥0) :
    interpPathCM v hm x t = interpPathFn v m x t := rfl

theorem interpPathCM_vertexPoint (ε : ℝ) (η : ℝ → ℂ) {m : ℝ} (hm : 0 ≤ m) (x : ℕ → ℤ) (t : ℝ≥0) :
    interpPathCM (vertexPoint ε η) hm x t = interpolatedWalk ε η m x t := rfl

/-- `x ↦ interpPathCM v hm x` is continuous from `ℕ → ℤ` (product topology) to the continuous paths
(compact-open topology). -/
theorem continuous_interpPathCM (v : ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) :
    Continuous (interpPathCM v hm) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_interpPathFn_uncurry v hm)

/-- `x ↦ interpPathCM v hm x` is measurable (product `σ`-algebra on `ℕ → ℤ`, Borel `σ`-algebra of
the compact-open topology on `ContinuousPath ℂ`). -/
theorem measurable_interpPathCM (v : ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) :
    Measurable (interpPathCM v hm) :=
  (continuous_interpPathCM v hm).measurable

theorem measurable_interpolatedWalk_apply (ε : ℝ) (η : ℝ → ℂ) {m : ℝ} (hm : 0 ≤ m) (t : ℝ≥0) :
    Measurable (fun x : ℕ → ℤ => interpolatedWalk ε η m x t) :=
  (ContinuousPath.continuous_eval t).measurable.comp (measurable_interpPathCM (vertexPoint ε η) hm)

end MatedCRT
