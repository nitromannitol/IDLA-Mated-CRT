import MatedCRT.FirstPass.S2i.CircleCode

/-! # Grid decoder of circle codes

For a dense sequence `D` of the circle carrier and a code `x : ℕ → ℝ` (dense values `x k ≈ p (D k)`), the grid decoder
`profileDec D hD x q` is the limit superior of the values `x (gridIndex N q)` along the grid `2^{-N}`, where
`gridIndex N q` is the least index `k` with `dist (D k) q < (1/2)^N`. It is jointly measurable in `(x, q)`
(`measurable_profileDec`), and it recovers every continuous circle average process from its code
(`profileDec_circleCode`). This is the measurable continuous-profile decoder used by the global family factor
(`FirstPass/S2i/GlobalFactor.lean`). -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- Some dense point is within `(1/2)^N` of every `q`. -/
theorem exists_grid {D : ℕ → CirclePt} (hD : DenseRange D) (N : ℕ) (q : CirclePt) :
    ∃ k : ℕ, dist (D k) q < (1 / 2 : ℝ) ^ N := by
  obtain ⟨y, ⟨k, rfl⟩, hy⟩ := Dense.exists_dist_lt hD q (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) N)
  exact ⟨k, by rw [dist_comm]; exact hy⟩

open Classical in
/-- The grid index: the least `k` with `dist (D k) q < (1/2)^N`. -/
noncomputable def gridIndex {D : ℕ → CirclePt} (hD : DenseRange D) (N : ℕ) (q : CirclePt) : ℕ :=
  Nat.find (exists_grid hD N q)

open Classical in
theorem measurable_gridIndex {D : ℕ → CirclePt} (hD : DenseRange D) (N : ℕ) :
    Measurable (gridIndex hD N) := by
  unfold gridIndex
  refine measurable_find (fun q => exists_grid hD N q) (fun k => ?_)
  exact measurableSet_lt (continuous_const.dist continuous_id).measurable measurable_const

/-- The grid decoder: the upper limit of the grid values of the code `x` at `q`. -/
noncomputable def profileDec {D : ℕ → CirclePt} (hD : DenseRange D) (x : ℕ → ℝ) (q : CirclePt) : ℝ :=
  limsup (fun N : ℕ => x (gridIndex hD N q)) atTop

/-- The evaluation `(x, k) ↦ x k` is measurable on the product with the countable index set. -/
theorem measurable_eval_code : Measurable (fun w : (ℕ → ℝ) × ℕ => w.1 w.2) :=
  measurable_from_prod_countable_left fun k => measurable_pi_apply k

/-- The grid decoder is jointly measurable in the code and the point. -/
theorem measurable_profileDec {D : ℕ → CirclePt} (hD : DenseRange D) :
    Measurable (fun z : (ℕ → ℝ) × CirclePt => profileDec hD z.1 z.2) := by
  unfold profileDec
  refine Measurable.limsup (fun N => ?_)
  exact measurable_eval_code.comp ((measurable_fst).prodMk ((measurable_gridIndex hD N).comp measurable_snd))

/-- A continuous circle average process is recovered from its code by the grid decoder. -/
theorem profileDec_circleCode {D : ℕ → CirclePt} (hD : DenseRange D) {p : CirclePt → ℝ} (hp : Continuous p)
    (q : CirclePt) : profileDec hD (circleCode D p) q = p q := by
  have hgi : Tendsto (fun N : ℕ => D (gridIndex hD N q)) atTop (𝓝 q) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    have h := Nat.find_spec (exists_grid hD N q)
    exact h.le
  have hlim : Tendsto (fun N : ℕ => p (D (gridIndex hD N q))) atTop (𝓝 (p q)) :=
    (hp.continuousAt (x := q)).tendsto.comp hgi
  exact hlim.limsup_eq

end MatedCRT
