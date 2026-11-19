import MatedCRT.FirstPass.Derived.RevuzWeightedRiemannBounds

/-!
# The Riemann-sum limit for the weighted-start clock integral

Let `A` be a positive continuous additive functional of planar Brownian motion with Revuz measure `μ_A`, let `h ≥ 0`
with `∫ h dμ_A < ∞`, and split `(0, r]` into the `N + 1` windows of length `r / (N + 1)`. The expected discretization
error `e_N = ∫ dx E_x[Σ_k ∫_{(kδ,(k+1)δ]} min (K|B_s - B_{kδ}|) C · h(B_s) dĀ_s]` tends to `0`: pathwise it is at most
`K η ∫_{(0,r]} h dĀ` once the mesh is below the modulus of uniform continuity of the path on `[0, r]` at scale `η`,
and it is dominated by `C ∫_{(0,r]} h dĀ`, whose expectation is `C r ∫ h dμ_A`.

Combined with the two-sided Riemann-sum bounds, this shows that `∫ dx E_x[g(B_0) ∫_{(0,r]} h dĀ]` depends on the
clock only through its Revuz measure, for every `g ≥ 0` with `g(x) ≤ g(y) + min (K|x - y|) C`
(Fukushima–Oshima–Takeda (2011), proof of Theorem 5.1.4; Revuz–Yor (1999), Chapter X, Theorem 2.6).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- `N + 1` windows of length `r / (N + 1)` cover `(0, r]`. -/
theorem natCast_succ_mul_div_succ (r : ℝ≥0) (N : ℕ) :
    (((N + 1 : ℕ) : ℝ≥0) * (r / ((N : ℝ≥0) + 1)) : ℝ≥0) = r := by
  rw [Nat.cast_succ]
  exact mul_div_cancel₀ r (by positivity)

/-- **Pathwise bound of the discretization error.** If the integrand modulus is at most `c` on every window, the
discretization error is at most `c` times the window integral over `(0, Nδ]`. -/
theorem clockRiemannError_le_mul (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (h : ℂ → ℝ≥0∞) (K C : ℝ≥0∞) (δ : ℝ≥0)
    (N : ℕ) (ω : ContinuousPath ℂ) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hloc : ∀ k < N, ∀ s ∈ Ioc (((k : ℝ≥0) * δ : ℝ≥0) : ℝ) (((k : ℝ≥0) * δ : ℝ≥0) + δ),
      min (K * edist (ω s.toNNReal) (ω ((k : ℝ≥0) * δ))) C ≤ c) :
    clockRiemannError A h K C δ N ω ≤ c * clockWindowIntegral A h ((N : ℝ≥0) * δ : ℝ≥0) ω := by
  rw [clockWindowIntegral_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [← lintegral_const_mul' c _ hc]
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  gcongr
  exact hloc k (Finset.mem_range.1 hk) s hs

/-- **Pathwise convergence of the discretization error.** Along every path whose window integral over `(0, r]` is
finite, the discretization error for the mesh `r / (N + 1)` tends to `0`. -/
theorem tendsto_clockRiemannError (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (h : ℂ → ℝ≥0∞) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (C : ℝ≥0∞) (r : ℝ≥0) {ω : ContinuousPath ℂ} (hω : clockWindowIntegral A h r ω ≠ ∞) :
    Tendsto (fun N : ℕ => clockRiemannError A h K C (r / ((N : ℝ≥0) + 1)) (N + 1) ω) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hM : K * clockWindowIntegral A h r ω ≠ ∞ := ENNReal.mul_ne_top hK hω
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt hM hε.ne'
  have huc : UniformContinuousOn (fun u : ℝ≥0 => ω u) (Icc 0 r) :=
    isCompact_Icc.uniformContinuousOn_of_continuous ω.continuous.continuousOn
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.1 huc η (by exact_mod_cast hη)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((r : ℝ) / d)
  filter_upwards [eventually_ge_atTop n₀] with N hN
  generalize hδ : r / ((N : ℝ≥0) + 1) = δ
  have hNδ : ((N + 1 : ℕ) : ℝ≥0) * δ = r := by rw [← hδ]; exact natCast_succ_mul_div_succ r N
  have hr : ((N : ℝ) + 1) * (δ : ℝ) = r := by
    have := congrArg NNReal.toReal hNδ
    push_cast at this
    exact this
  have hδd : (δ : ℝ) < d := by
    have hN1 : (r : ℝ) / d < (N : ℝ) + 1 := hn₀.trans_le (by exact_mod_cast hN.trans (Nat.le_succ N))
    rw [div_lt_iff₀ hd] at hN1
    nlinarith [δ.coe_nonneg, (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
  have hloc : ∀ k < N + 1, ∀ s ∈ Ioc (((k : ℝ≥0) * δ : ℝ≥0) : ℝ) (((k : ℝ≥0) * δ : ℝ≥0) + δ),
      min (K * edist (ω s.toNNReal) (ω ((k : ℝ≥0) * δ))) C ≤ K * η := by
    intro k hk s hs
    have hk' : (k : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_of_lt hk
    have hkδ : (((k : ℝ≥0) * δ : ℝ≥0) : ℝ) + δ ≤ r := by
      rw [← hr, NNReal.coe_mul, NNReal.coe_natCast]
      nlinarith [mul_le_mul_of_nonneg_right hk' δ.coe_nonneg]
    have hs0 : 0 ≤ s := (NNReal.coe_nonneg _).trans hs.1.le
    have hsr : s.toNNReal ∈ Icc 0 r := ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 (hs.2.trans hkδ)⟩
    have hkr : ((k : ℝ≥0) * δ : ℝ≥0) ∈ Icc 0 r :=
      ⟨zero_le, NNReal.coe_le_coe.1 (le_trans (le_add_of_nonneg_right δ.coe_nonneg) hkδ)⟩
    have hdd : dist s.toNNReal ((k : ℝ≥0) * δ) < d := by
      rw [NNReal.dist_eq, Real.coe_toNNReal s hs0, abs_of_nonneg (sub_nonneg.2 hs.1.le)]
      linarith [hs.2]
    have he : edist (ω s.toNNReal) (ω ((k : ℝ≥0) * δ)) ≤ η := by
      rw [edist_dist]
      exact (ENNReal.ofReal_le_ofReal (hdist _ hsr _ hkr hdd).le).trans_eq (ENNReal.ofReal_coe_nnreal)
    refine (min_le_left _ _).trans ?_
    gcongr
  have hb := clockRiemannError_le_mul A h K C δ (N + 1) ω (ENNReal.mul_ne_top hK ENNReal.coe_ne_top) hloc
  rw [hNδ] at hb
  refine hb.trans (le_trans ?_ hηε.le)
  rw [mul_comm K, mul_assoc]

/-- **The expected discretization error tends to `0`** for the mesh `r / (N + 1)`, when `∫ h dμ_A < ∞`. -/
theorem tendsto_lintegral_clockRiemannError {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) (hfin : ∫⁻ y, h y ∂revuz planarLaw A ≠ ∞) {K C : ℝ≥0∞} (hK : K ≠ ∞)
    (hC : C ≠ ∞) (r : ℝ≥0) :
    Tendsto (fun N : ℕ => ∫⁻ ω, clockRiemannError A h K C (r / ((N : ℝ≥0) + 1)) (N + 1) ω
      ∂(volume : Measure ℂ).bind planarLaw) atTop (𝓝 0) := by
  have hWm : Measurable (clockWindowIntegral A h r) := measurable_clockWindowIntegral hA.meas hh r
  have hWfin : ∫⁻ ω, clockWindowIntegral A h r ω ∂(volume : Measure ℂ).bind planarLaw ≠ ∞ := by
    rw [lintegral_bind_planarLaw hWm, lintegral_clockWindowIntegral_eq hA hh r.coe_nonneg]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have key := tendsto_lintegral_of_dominated_convergence (μ := (volume : Measure ℂ).bind planarLaw)
    (F := fun N ω => clockRiemannError A h K C (r / ((N : ℝ≥0) + 1)) (N + 1) ω) (f := fun _ => 0) (fun ω => C * clockWindowIntegral A h r ω)
    (fun N => measurable_clockRiemannError hA.meas hh K C _ _)
    (fun N => ae_of_all _ fun ω => by
      have hb := clockRiemannError_le_mul A h K C (r / ((N : ℝ≥0) + 1)) (N + 1) ω hC
        fun _ _ _ _ => min_le_right _ _
      rwa [natCast_succ_mul_div_succ r N] at hb)
    (by rw [lintegral_const_mul C hWm]; exact ENNReal.mul_ne_top hC hWfin)
    ((ae_lt_top hWm hWfin).mono fun ω hω => tendsto_clockRiemannError A h hK C r hω.ne)
  simpa only [lintegral_zero] using key

/-- **The weighted-start clock integral depends only on the Revuz measure.** If two positive continuous additive
functionals `A`, `A'` of planar Brownian motion have the same Revuz measure `μ`, then for `h ≥ 0` with
`∫ h dμ < ∞` and `g ≥ 0` with `g(x) ≤ g(y) + min (K|x - y|) C`,
`∫ dx E_x[g(B_0) ∫_{(0,r]} h dĀ] = ∫ dx E_x[g(B_0) ∫_{(0,r]} h dĀ']`. -/
theorem lintegral_eval_zero_mul_clockWindowIntegral_eq_of_revuz_eq {A A' : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hA' : IsPCAF planarLaw A') (hμ : revuz planarLaw A = revuz planarLaw A')
    {g h : ℂ → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) (hfin : ∫⁻ y, h y ∂revuz planarLaw A ≠ ∞)
    {K C : ℝ≥0∞} (hK : K ≠ ∞) (hC : C ≠ ∞) (hgm : ∀ x y, g x ≤ g y + min (K * edist x y) C) (r : ℝ≥0) :
    ∫⁻ x, ∫⁻ ω, g (ω 0) * clockWindowIntegral A h r ω ∂planarLaw x =
      ∫⁻ x, ∫⁻ ω, g (ω 0) * clockWindowIntegral A' h r ω ∂planarLaw x := by
  have hfin' : ∫⁻ y, h y ∂revuz planarLaw A' ≠ ∞ := hμ ▸ hfin
  have half : ∀ {B B' : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}, IsPCAF planarLaw B → IsPCAF planarLaw B' →
      revuz planarLaw B = revuz planarLaw B' → ∫⁻ y, h y ∂revuz planarLaw B ≠ ∞ →
      ∫⁻ y, h y ∂revuz planarLaw B' ≠ ∞ →
      ∫⁻ x, ∫⁻ ω, g (ω 0) * clockWindowIntegral B h r ω ∂planarLaw x ≤
        ∫⁻ x, ∫⁻ ω, g (ω 0) * clockWindowIntegral B' h r ω ∂planarLaw x := by
    intro B B' hB hB' hBμ hBf hB'f
    have hbd : ∀ N : ℕ, (∫⁻ x, ∫⁻ ω, g (ω 0) * clockWindowIntegral B h r ω ∂planarLaw x) ≤
        (∫⁻ x, ∫⁻ ω, g (ω 0) * clockWindowIntegral B' h r ω ∂planarLaw x) +
          (∫⁻ ω, clockRiemannError B' h K C (r / ((N : ℝ≥0) + 1)) (N + 1) ω
            ∂(volume : Measure ℂ).bind planarLaw) +
          ∫⁻ ω, clockRiemannError B h K C (r / ((N : ℝ≥0) + 1)) (N + 1) ω
            ∂(volume : Measure ℂ).bind planarLaw := by
      intro N
      have h1 := (lintegral_eval_zero_mul_clockWindowIntegral_riemann_bounds hB hg hh hgm
        (r / ((N : ℝ≥0) + 1)) (N + 1)).1
      have h2 := (lintegral_eval_zero_mul_clockWindowIntegral_riemann_bounds hB' hg hh hgm
        (r / ((N : ℝ≥0) + 1)) (N + 1)).2
      rw [natCast_succ_mul_div_succ r N] at h1 h2
      rw [hBμ] at h1
      exact h1.trans (by gcongr)
    have hlim' := ((tendsto_const_nhds
      (x := ∫⁻ x, ∫⁻ ω, g (ω 0) * clockWindowIntegral B' h r ω ∂planarLaw x)).add
        (tendsto_lintegral_clockRiemannError hB' hh hB'f hK hC r)).add
      (tendsto_lintegral_clockRiemannError hB hh hBf hK hC r)
    rw [add_zero, add_zero] at hlim'
    exact ge_of_tendsto' hlim' hbd
  exact le_antisymm (half hA hA' hμ hfin hfin') (half hA' hA hμ.symm hfin' hfin)

end MatedCRT
