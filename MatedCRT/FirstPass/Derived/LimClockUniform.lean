import MatedCRT.Proofs.Sec3.KilledOccupation.LimClockKernel
import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockApprox
import MatedCRT.Proofs.Sec3.KilledOccupation.ConeClockTransfer
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockProof

/-!
# The limit occupation clock as a uniform limit of the regularized clocks

Fix a family `ψ` of circle averages, a path `b`, an exit time `σ` and scales `ε_k`. Write
`Ψ_k(s) = regClockFun γ (ε k) ψ σ b s = ∫_0^{s ∧ σ(b)} ε_k^{γ²/2} e^{γ ψ̃(ε_k, b_u)} du` for the regularized clocks.
If each `Ψ_k` is finite and continuous and the quenched gaps `clockGapFun` between consecutive scales are eventually
at most `(1/2)^k`, then the clocks converge uniformly on `ℝ≥0` to a continuous nondecreasing clock `G` with `G 0 = 0`,
stopped at `σ(b)`, and the limit clock `limClockFun` of `LimClockFun.lean` is `ofReal ∘ G`. Consequently the Stieltjes
kernel `limClockKernel` of the limit clock gives `[0, t]` the mass `G t`. This is the deterministic part of the
identification of the occupation measure of the Liouville clock (Garban-Rhodes-Vargas, Liouville Brownian motion,
Theorem 2.7; Berestycki, Diffusion in planar Liouville quantum gravity, Sections 2-3): along a Borel-Cantelli
subsequence of scales, the regularized clocks converge uniformly, and the limit clock is their uniform limit.

* `exists_tendstoUniformly_of_rat_gap_le_geometric`: continuous real functions on `ℝ≥0` whose consecutive gaps at the
  rational times are eventually at most `(1/2)^k` converge uniformly to a continuous function.
* `regClockFun_mono`, `regClockFun_min`, `regClockFun_zero`, `regClockFun_eq_withDensity_Iic`: elementary properties
  of the regularized clocks; the last one writes `Ψ_k` as the distribution function of `w_k(b_u) du` on `[0, σ(b)]`.
* `exists_limClockFun_eq_uniform_limit`, `exists_limClockKernel_Iic_eq_uniform_limit`: the identification.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The nonnegative rationals are dense in `ℝ≥0`. -/
lemma dense_range_nnratCast_nnreal : Dense (Set.range ((↑) : ℚ≥0 → ℝ≥0)) :=
  dense_of_exists_between fun _ _ hab => by
    obtain ⟨q, h1, h2⟩ := exists_nnrat_btwn_nnreal hab
    exact ⟨q, ⟨q, rfl⟩, h1, h2⟩

/-- Continuous real functions `f k` on `ℝ≥0` whose consecutive gaps `|f k q - f (k+1) q|` at the rational times `q`
are eventually at most `(1/2)^k` converge uniformly on `ℝ≥0` to a continuous function. The gap bound extends from the
rational times to all times by continuity and density, and the geometric bound makes the sequence uniformly Cauchy. -/
theorem exists_tendstoUniformly_of_rat_gap_le_geometric {f : ℕ → ℝ≥0 → ℝ} (hcont : ∀ k, Continuous (f k))
    (hgap : ∀ᶠ k in atTop, ∀ q : ℚ≥0, |f k q - f (k + 1) q| ≤ (1 / 2 : ℝ) ^ k) :
    ∃ G : ℝ≥0 → ℝ, Continuous G ∧ TendstoUniformly f G atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hgap
  have hall : ∀ k, N ≤ k → ∀ t, |f k t - f (k + 1) t| ≤ (1 / 2 : ℝ) ^ k := by
    intro k hk t
    have hcl : IsClosed {t | |f k t - f (k + 1) t| ≤ (1 / 2 : ℝ) ^ k} :=
      isClosed_le ((hcont k).sub (hcont (k + 1))).abs continuous_const
    have hsub : Set.range ((↑) : ℚ≥0 → ℝ≥0) ⊆ {t | |f k t - f (k + 1) t| ≤ (1 / 2 : ℝ) ^ k} := by
      rintro _ ⟨q, rfl⟩
      exact hN k hk q
    have h := closure_minimal hsub hcl
    rw [dense_range_nnratCast_nnreal.closure_eq] at h
    exact h (Set.mem_univ t)
  have hgeo : ∀ t m, dist (f (m + N) t) (f (m + 1 + N) t) ≤ (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ m := by
    intro t m
    rw [Real.dist_eq, show m + 1 + N = m + N + 1 by omega, mul_comm, ← pow_add]
    exact hall (m + N) (Nat.le_add_left N m) t
  have hr : (1 / 2 : ℝ) < 1 := by norm_num
  have hcs : ∀ t, CauchySeq fun k => f k t := fun t =>
    (cauchySeq_shift N).1
      (cauchySeq_of_le_geometric (f := fun m => f (m + N) t) (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ N) hr (hgeo t))
  have hG : ∀ t, Tendsto (fun k => f k t) atTop (𝓝 (limUnder atTop fun k => f k t)) := fun t =>
    (hcs t).tendsto_limUnder
  have hbound : ∀ t m, dist (f (m + N) t) (limUnder atTop fun k => f k t) ≤
      (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ m / (1 - 1 / 2) := fun t m =>
    dist_le_of_le_geometric_of_tendsto (f := fun m => f (m + N) t) (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ N) hr (hgeo t)
      ((tendsto_add_atTop_iff_nat N).2 (hG t)) m
  have h0 : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ m / (1 - 1 / 2)) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) hr).const_mul
      ((1 / 2 : ℝ) ^ N)).div_const (1 - 1 / 2)
    rwa [mul_zero, zero_div] at h
  have hU : TendstoUniformly f (fun t => limUnder atTop fun k => f k t) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    obtain ⟨M, hM⟩ := eventually_atTop.1 (h0.eventually (gt_mem_nhds hδ))
    refine eventually_atTop.2 ⟨M + N, fun k hk t => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + N := ⟨k - N, by omega⟩
    rw [dist_comm]
    exact (hbound t m).trans_lt (hM m (by omega))
  exact ⟨_, hU.continuous (Eventually.of_forall hcont).frequently, hU⟩

section RegClock

variable (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ)

/-- The regularized clock is nondecreasing in time. -/
theorem regClockFun_mono : Monotone (regClockFun γ ε ψ σ b) := fun _ _ hst =>
  lintegral_mono_set (Icc_subset_Icc_right (min_le_min hst le_rfl))

/-- The regularized clock is stopped at the exit time `σ(b)`. -/
theorem regClockFun_min (t : ℝ≥0) : regClockFun γ ε ψ σ b (min t (σ b)) = regClockFun γ ε ψ σ b t := by
  unfold regClockFun
  rw [min_assoc, min_self]

/-- The regularized clock at any time is at most its value at the exit time. -/
theorem regClockFun_le_exit (t : ℝ≥0) : regClockFun γ ε ψ σ b t ≤ regClockFun γ ε ψ σ b (σ b) := by
  rw [← regClockFun_min γ ε ψ σ b t]
  exact regClockFun_mono γ ε ψ σ b (min_le_right _ _)

/-- The regularized clock vanishes at time `0`: `[0, 0 ∧ σ(b)]` is a single point, of Lebesgue measure `0`. -/
theorem regClockFun_zero : regClockFun γ ε ψ σ b 0 = 0 := by
  unfold regClockFun
  rw [min_eq_left zero_le, Icc_self]
  exact setLIntegral_measure_zero _ _ (lebNN_singleton 0)

/-- The regularized clock is the distribution function of the measure `ε^{γ²/2} e^{γ ψ̃(ε, b_u)} du` on
`[0, σ(b)]`: its value at `t` is the mass of `[0, t]`. -/
theorem regClockFun_eq_withDensity_Iic (t : ℝ≥0) :
    regClockFun γ ε ψ σ b t = ((lebNN.restrict (Icc 0 (σ b))).withDensity fun u =>
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u)))) (Iic t) := by
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic t ∩ Icc 0 (σ b) = Icc 0 (min t (σ b)) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
    tauto
  rw [hset]
  rfl

/-- **Lipschitz bound for the regularized clock.** If the integrand `ε^{γ²/2} e^{γ ψ̃(ε, b_u)}` is at most `M` for
`u ≤ σ(b)`, then `Ψ(t) ≤ Ψ(s) + M (t - s)` for `s ≤ t`. -/
theorem regClockFun_le_add_mul_of_le (M : ℝ≥0) (hM : ∀ u ≤ σ b,
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u))) ≤ M)
    {s t : ℝ≥0} (hst : s ≤ t) :
    regClockFun γ ε ψ σ b t ≤ regClockFun γ ε ψ σ b s + (M : ℝ≥0∞) * ((t - s : ℝ≥0) : ℝ≥0∞) := by
  have hsub : Icc (0 : ℝ≥0) (min s (σ b)) ⊆ Icc 0 (min t (σ b)) :=
    Icc_subset_Icc_right (min_le_min hst le_rfl)
  have hmin : min t (σ b) - min s (σ b) ≤ t - s := by
    rw [tsub_le_iff_right]
    rcases le_total s (σ b) with h | h
    · rw [min_eq_left h, tsub_add_cancel_of_le hst]
      exact min_le_left _ _
    · rw [min_eq_right h, min_eq_right (h.trans hst)]
      exact le_add_self
  unfold regClockFun
  rw [← lintegral_inter_add_sdiff (B := Icc (0 : ℝ≥0) (min s (σ b))) _ (Icc (0 : ℝ≥0) (min t (σ b)))
    measurableSet_Icc, inter_eq_right.2 hsub]
  refine add_le_add le_rfl ?_
  calc ∫⁻ u in Icc 0 (min t (σ b)) \ Icc 0 (min s (σ b)),
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u))) ∂lebNN
      ≤ ∫⁻ _ in Icc 0 (min t (σ b)) \ Icc 0 (min s (σ b)), (M : ℝ≥0∞) ∂lebNN :=
        setLIntegral_mono measurable_const fun u hu => hM u (hu.1.2.trans (min_le_right _ _))
    _ = (M : ℝ≥0∞) * lebNN (Icc 0 (min t (σ b)) \ Icc 0 (min s (σ b))) := setLIntegral_const _ _
    _ ≤ (M : ℝ≥0∞) * ((t - s : ℝ≥0) : ℝ≥0∞) := by
        rw [measure_sdiff hsub measurableSet_Icc.nullMeasurableSet
          (by rw [lebNN_Icc]; exact ENNReal.coe_ne_top), lebNN_Icc, lebNN_Icc, ← ENNReal.coe_sub]
        exact mul_le_mul_of_nonneg_left (ENNReal.coe_le_coe.2 hmin) zero_le

/-- If the integrand of the regularized clock is bounded along the path up to the exit time, the clock is finite and
its real value is a continuous (indeed `M`-Lipschitz) function of time. -/
theorem regClockFun_ne_top_and_continuous_of_le (M : ℝ≥0) (hM : ∀ u ≤ σ b,
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u))) ≤ M) :
    regClockFun γ ε ψ σ b (σ b) ≠ ∞ ∧ Continuous fun t => (regClockFun γ ε ψ σ b t).toReal := by
  have hMt : ∀ r : ℝ≥0, (M : ℝ≥0∞) * (r : ℝ≥0∞) ≠ ∞ := fun r =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hfin : ∀ t, regClockFun γ ε ψ σ b t ≠ ∞ := fun t => by
    refine ne_top_of_le_ne_top ?_ (regClockFun_le_add_mul_of_le γ ε ψ σ b M hM (zero_le : (0 : ℝ≥0) ≤ t))
    rw [regClockFun_zero, zero_add]
    exact hMt _
  refine ⟨hfin _, LipschitzWith.continuous (K := M) (LipschitzWith.of_dist_le_mul fun s t => ?_)⟩
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, dist_comm s]
    exact this t s ((le_total s t).resolve_left hst)
  show dist (regClockFun γ ε ψ σ b s).toReal (regClockFun γ ε ψ σ b t).toReal ≤ M * dist s t
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin s, hMt _⟩)
    (regClockFun_le_add_mul_of_le γ ε ψ σ b M hM hst)
  rw [ENNReal.toReal_add (hfin s) (hMt _), ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal,
    NNReal.coe_sub hst] at h1
  have h2 := ENNReal.toReal_mono (hfin t) (regClockFun_mono γ ε ψ σ b hst)
  have h3 := NNReal.coe_le_coe.2 hst
  rw [Real.dist_eq, NNReal.dist_eq, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  linarith

end RegClock

/-- **Identification of the limit clock as a uniform limit.** Let the regularized clocks
`Ψ_k = regClockFun γ (ε k) ψ σ b` be finite at the exit time `σ(b)` and continuous in time, and let the quenched gaps
`clockGapFun γ σ (ε k) (ε (k+1)) (ψ, b)` be eventually at most `(1/2)^k`. Then there is a continuous nondecreasing
`G : ℝ≥0 → ℝ` with `G 0 = 0`, stopped at `σ(b)`, such that `Ψ_k → G` uniformly on `ℝ≥0` and the limit clock
`limClockFun γ ε ψ σ b` is `ofReal ∘ G`. -/
theorem exists_limClockFun_eq_uniform_limit (γ : ℝ) (ε : ℕ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ)
    (hfin : ∀ k, regClockFun γ (ε k) ψ σ b (σ b) ≠ ∞)
    (hcont : ∀ k, Continuous fun t => (regClockFun γ (ε k) ψ σ b t).toReal)
    (hgap : ∀ᶠ k in atTop, clockGapFun γ σ (ε k) (ε (k + 1)) (ψ, b) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) :
    ∃ G : ℝ≥0 → ℝ, Continuous G ∧ Monotone G ∧ G 0 = 0 ∧ (∀ t, G (min t (σ b)) = G t) ∧
      TendstoUniformly (fun k t => (regClockFun γ (ε k) ψ σ b t).toReal) G atTop ∧
      ∀ t, limClockFun γ ε ψ σ b t = ENNReal.ofReal (G t) := by
  have hfin' : ∀ k t, regClockFun γ (ε k) ψ σ b t ≠ ∞ := fun k t =>
    ne_top_of_le_ne_top (hfin k) (regClockFun_le_exit γ (ε k) ψ σ b t)
  have hgap' : ∀ᶠ k in atTop, ∀ q : ℚ≥0, |(regClockFun γ (ε k) ψ σ b q).toReal -
      (regClockFun γ (ε (k + 1)) ψ σ b q).toReal| ≤ (1 / 2 : ℝ) ^ k := by
    filter_upwards [hgap] with k hk q
    have hk' : (⨆ q : ℚ≥0, ennDist (regClockFun γ (ε k) ψ σ b (q : ℝ≥0))
        (regClockFun γ (ε (k + 1)) ψ σ b (q : ℝ≥0))) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := hk
    have h1 : ENNReal.ofReal |(regClockFun γ (ε k) ψ σ b q).toReal -
        (regClockFun γ (ε (k + 1)) ψ σ b q).toReal| ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
      refine le_trans ?_ (le_trans (le_iSup (fun q : ℚ≥0 => ennDist (regClockFun γ (ε k) ψ σ b (q : ℝ≥0))
        (regClockFun γ (ε (k + 1)) ψ σ b (q : ℝ≥0))) q) hk')
      have h2 := ofReal_le_ennDist_ofReal
        (η := |(regClockFun γ (ε k) ψ σ b q).toReal - (regClockFun γ (ε (k + 1)) ψ σ b q).toReal|)
        (ENNReal.toReal_nonneg (a := regClockFun γ (ε k) ψ σ b q))
        (ENNReal.toReal_nonneg (a := regClockFun γ (ε (k + 1)) ψ σ b q)) le_rfl
      rwa [ENNReal.ofReal_toReal (hfin' k q), ENNReal.ofReal_toReal (hfin' (k + 1) q)] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  obtain ⟨G, hGc, hU⟩ := exists_tendstoUniformly_of_rat_gap_le_geometric hcont hgap'
  have hlim : ∀ t, Tendsto (fun k => (regClockFun γ (ε k) ψ σ b t).toReal) atTop (𝓝 (G t)) :=
    hU.tendsto_at
  have hGmono : Monotone G := fun s t hst =>
    le_of_tendsto_of_tendsto' (hlim s) (hlim t) fun k =>
      ENNReal.toReal_mono (hfin' k t) (regClockFun_mono γ (ε k) ψ σ b hst)
  have hGmin : ∀ t, G (min t (σ b)) = G t := fun t =>
    tendsto_nhds_unique (by simpa only [regClockFun_min] using hlim (min t (σ b))) (hlim t)
  have hG0 : G 0 = 0 := by
    refine tendsto_nhds_unique (hlim 0) ?_
    simp only [regClockFun_zero, ENNReal.toReal_zero]
    exact tendsto_const_nhds
  have hlimsup : ∀ q : ℝ≥0,
      Filter.limsup (fun k => regClockFun γ (ε k) ψ σ b q) atTop = ENNReal.ofReal (G q) := by
    intro q
    have h := (ENNReal.continuous_ofReal.tendsto (G q)).comp (hlim q)
    refine Eq.trans ?_ h.limsup_eq
    congr 1
    funext k
    exact (ENNReal.ofReal_toReal (hfin' k q)).symm
  refine ⟨G, hGc, hGmono, hG0, hGmin, hU, fun t => ?_⟩
  unfold limClockFun
  have hinf : (⨅ q : {q : ℚ≥0 // t < (q : ℝ≥0)},
      Filter.limsup (fun k => regClockFun γ (ε k) ψ σ b (q.1 : ℝ≥0)) atTop) =
      ⨅ q : {q : ℚ≥0 // t < (q : ℝ≥0)}, ENNReal.ofReal (G (min (q.1 : ℝ≥0) (σ b))) :=
    iInf_congr fun q => by rw [hlimsup, hGmin]
  rw [hinf, iInf_rat_gt_ofReal_eq hGmono hGc (σ b) t, hGmin]

/-- **The Stieltjes kernel of the limit clock is `dG`.** Under the hypotheses of
`exists_limClockFun_eq_uniform_limit`, the truncated limit clock `limClockTrunc` at `(ψ, b)` is the uniform limit `G`
of the regularized clocks, and the Stieltjes kernel `limClockKernel` gives `[0, t]` the mass `G t`. -/
theorem exists_limClockKernel_Iic_eq_uniform_limit (γ : ℝ) (ε : ℕ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ)
    (hfin : ∀ k, regClockFun γ (ε k) ψ σ b (σ b) ≠ ∞)
    (hcont : ∀ k, Continuous fun t => (regClockFun γ (ε k) ψ σ b t).toReal)
    (hgap : ∀ᶠ k in atTop, clockGapFun γ σ (ε k) (ε (k + 1)) (ψ, b) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) :
    ∃ G : ℝ≥0 → ℝ, Continuous G ∧ Monotone G ∧ G 0 = 0 ∧ (∀ t, G (min t (σ b)) = G t) ∧
      TendstoUniformly (fun k t => (regClockFun γ (ε k) ψ σ b t).toReal) G atTop ∧
      limClockTrunc γ ε σ (ψ, b) = G ∧ ∀ t, limClockKernel γ ε σ (ψ, b) (Iic t) = ENNReal.ofReal (G t) := by
  obtain ⟨G, hGc, hGmono, hG0, hGmin, hU, hlimc⟩ :=
    exists_limClockFun_eq_uniform_limit γ ε σ ψ b hfin hcont hgap
  have hGnn : ∀ t, 0 ≤ G t := fun t => hG0 ▸ hGmono zero_le
  have hsup : (⨆ q : ℚ≥0, limClockFun γ ε (ψ, b).1 σ (ψ, b).2 (q : ℝ≥0)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := G (σ b))) (iSup_le fun q => ?_)
    show limClockFun γ ε ψ σ b (q : ℝ≥0) ≤ ENNReal.ofReal (G (σ b))
    rw [hlimc, ← hGmin (q : ℝ≥0)]
    exact ENNReal.ofReal_le_ofReal (hGmono (min_le_right _ _))
  have htrunc : limClockTrunc γ ε σ (ψ, b) = G := by
    rw [limClockTrunc_of_iSup_ne_top γ ε σ (ψ, b) hsup]
    funext t
    show (limClockFun γ ε ψ σ b t).toReal = G t
    rw [hlimc, ENNReal.toReal_ofReal (hGnn t)]
  refine ⟨G, hGc, hGmono, hG0, hGmin, hU, htrunc, fun t => ?_⟩
  rw [limClockKernel_Iic, htrunc, hG0, sub_zero]

/-- **H2 on the event of bounded integrands.** If, for every `k`, the integrand of the regularized clock at scale
`ε k` is bounded along the path `b` up to the exit time `σ(b)` (as on the event where the circle averages are
continuous), and the quenched gaps between consecutive scales are eventually at most `(1/2)^k`, the conclusion of
`exists_limClockKernel_Iic_eq_uniform_limit` holds. -/
theorem exists_limClockKernel_Iic_eq_uniform_limit_of_bdd (γ : ℝ) (ε : ℕ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ)
    (hbd : ∀ k, ∃ M : ℝ≥0, ∀ u ≤ σ b,
      ENNReal.ofReal ((ε k) ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ (ε k) (b u))) ≤ M)
    (hgap : ∀ᶠ k in atTop, clockGapFun γ σ (ε k) (ε (k + 1)) (ψ, b) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) :
    ∃ G : ℝ≥0 → ℝ, Continuous G ∧ Monotone G ∧ G 0 = 0 ∧ (∀ t, G (min t (σ b)) = G t) ∧
      TendstoUniformly (fun k t => (regClockFun γ (ε k) ψ σ b t).toReal) G atTop ∧
      limClockTrunc γ ε σ (ψ, b) = G ∧ ∀ t, limClockKernel γ ε σ (ψ, b) (Iic t) = ENNReal.ofReal (G t) := by
  choose M hM using hbd
  exact exists_limClockKernel_Iic_eq_uniform_limit γ ε σ ψ b
    (fun k => (regClockFun_ne_top_and_continuous_of_le γ (ε k) ψ σ b (M k) (hM k)).1)
    (fun k => (regClockFun_ne_top_and_continuous_of_le γ (ε k) ψ σ b (M k) (hM k)).2) hgap

end MatedCRT.KilledOccupation
