import HarmonicBalls.Proofs.LBM.MonotoneClockUniformLimit
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dense-time limits of monotone clocks

Deterministic upgrade behind the stopped-clock proposition (source `env-steps.tex` lines 1207-1224,
Bou-Rabee and Gwynne, arXiv:2211.04891, Section 3). A family of monotone clocks that converges at
every nonnegative rational time to a limit `a` converges at every nonnegative time to `a`. When `a`
is continuous, the convergence is locally uniform on compact time intervals. No stochastic
hypothesis enters.

The locally uniform statement is obtained from
`HarmonicBalls.MonotoneClockUniformLimit.monotone_clock_uniform_limit` (Harmonic-Balls-LQG, commit
2382446), which is reused. That lemma needs the limit to be monotone. Monotonicity of the limit is
derived here from rational monotonicity and continuity (`monotoneOn_limit_of_rat`).

The clocks are only assumed monotone eventually in `n`, since the killed dyadic approximations need
not be monotone for finitely many scales.
-/

open Filter Topology Set
open scoped NNReal

namespace MatedCRT.StoppedClockDenseLimit

/-- A continuous limit on `[0, ∞)` of eventually monotone clocks that converge at nonnegative
rational times is monotone on `[0, ∞)`. -/
theorem monotoneOn_limit_of_rat {C : ℕ → ℝ → ℝ} {a : ℝ → ℝ}
    (hC : ∀ᶠ n in atTop, MonotoneOn (C n) (Ici 0))
    (ha : ContinuousOn a (Ici 0))
    (hlim : ∀ q : ℚ, 0 ≤ q → Tendsto (fun n => C n q) atTop (𝓝 (a q))) :
    MonotoneOn a (Ici 0) := by
  -- Monotonicity of the limit at two nonnegative rational times.
  have hrat : ∀ p r : ℚ, 0 ≤ p → p ≤ r → a p ≤ a r := by
    intro p r hp hpr
    have hr : (0 : ℚ) ≤ r := hp.trans hpr
    refine le_of_tendsto_of_tendsto (hlim p hp) (hlim r hr) ?_
    exact hC.mono fun n hn => hn (mem_Ici.mpr (by exact_mod_cast hp))
      (mem_Ici.mpr (by exact_mod_cast hr)) (by exact_mod_cast hpr)
  -- `a x ≤ a r` for a real `x ≥ 0` and a rational `r > x`: approximate `x` from above.
  have hup : ∀ x : ℝ, 0 ≤ x → ∀ r : ℚ, x < (r : ℝ) → a x ≤ a r := by
    intro x hx r hxr
    have hex : ∀ k : ℕ, ∃ p : ℚ, x < (p : ℝ) ∧ (p : ℝ) < min (r : ℝ) (x + 1 / ((k : ℝ) + 1)) := by
      intro k
      refine exists_rat_btwn (lt_min hxr ?_)
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    choose p hp1 hp2 using hex
    have hupper : Tendsto (fun k : ℕ => x + 1 / ((k : ℝ) + 1)) atTop (𝓝 x) := by
      have hconst : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
      simpa using Filter.Tendsto.add hconst tendsto_one_div_add_atTop_nhds_zero_nat
    have hp_lim : Tendsto (fun k => (p k : ℝ)) atTop (𝓝 x) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
        (fun k => (hp1 k).le) (fun k => (hp2 k).le.trans (min_le_right _ _))
    have hmem : Tendsto (fun k => (p k : ℝ)) atTop (𝓝[Ici 0] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hp_lim, Eventually.of_forall fun k => le_trans hx (hp1 k).le⟩
    have hA : Tendsto (fun k => a (p k : ℝ)) atTop (𝓝 (a x)) :=
      (show Tendsto a (𝓝[Ici 0] x) (𝓝 (a x)) from ha x hx).comp hmem
    refine le_of_tendsto hA (Eventually.of_forall fun k => ?_)
    have hp0 : (0 : ℚ) ≤ p k := by exact_mod_cast le_trans hx (hp1 k).le
    have hpr : p k ≤ r := by
      have h := (hp2 k).trans_le (min_le_left _ _)
      exact_mod_cast h.le
    exact hrat (p k) r hp0 hpr
  -- `a q ≤ a y` for a rational `q ≥ 0` and a real `y > q`: approximate `y` from below.
  have hdown : ∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ y : ℝ, 0 ≤ y → (q : ℝ) < y → a q ≤ a y := by
    intro q hq y _hy hqy
    have hex : ∀ k : ℕ, ∃ s : ℚ, max (q : ℝ) (y - 1 / ((k : ℝ) + 1)) < (s : ℝ) ∧ (s : ℝ) < y := by
      intro k
      refine exists_rat_btwn (max_lt hqy ?_)
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    choose s hs1 hs2 using hex
    have hlower : Tendsto (fun k : ℕ => y - 1 / ((k : ℝ) + 1)) atTop (𝓝 y) := by
      have hconst : Tendsto (fun _ : ℕ => y) atTop (𝓝 y) := tendsto_const_nhds
      simpa using Filter.Tendsto.sub hconst tendsto_one_div_add_atTop_nhds_zero_nat
    have hs_lim : Tendsto (fun k => (s k : ℝ)) atTop (𝓝 y) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
        (fun k => (le_max_right _ _).trans (hs1 k).le) (fun k => (hs2 k).le)
    have hmem : Tendsto (fun k => (s k : ℝ)) atTop (𝓝[Ici 0] y) :=
      tendsto_nhdsWithin_iff.mpr ⟨hs_lim, Eventually.of_forall fun k =>
        hq.trans ((le_max_left _ _).trans (hs1 k).le)⟩
    have hA : Tendsto (fun k => a (s k : ℝ)) atTop (𝓝 (a y)) :=
      (show Tendsto a (𝓝[Ici 0] y) (𝓝 (a y)) from ha y _hy).comp hmem
    refine ge_of_tendsto hA (Eventually.of_forall fun k => ?_)
    have hqs : q ≤ s k := by
      have h := (le_max_left _ _).trans (hs1 k).le
      exact_mod_cast h
    exact hrat q (s k) (by exact_mod_cast hq) hqs
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
    exact (hup x (mem_Ici.mp hx) q hq1).trans
      (hdown q ((mem_Ici.mp hx).trans hq1.le) y (mem_Ici.mp hy) hq2)

/-- **Deterministic dense-time limit (real time).** If the clocks `C n` are eventually monotone on
`[0, ∞)` and converge at every nonnegative rational time to `a`, and `a` is continuous on
`[0, ∞)`, then `C n t → a t` for every `t ≥ 0`. -/
theorem tendsto_of_rat_limit {C : ℕ → ℝ → ℝ} {a : ℝ → ℝ}
    (hC : ∀ᶠ n in atTop, MonotoneOn (C n) (Ici 0))
    (ha : ContinuousOn a (Ici 0))
    (hlim : ∀ q : ℚ, 0 ≤ q → Tendsto (fun n => C n q) atTop (𝓝 (a q)))
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => C n t) atTop (𝓝 (a t)) := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · rw [← h0]
    simpa using hlim 0 le_rfl
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.mp (ha t ht) (ε / 2) (half_pos hε)
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show max 0 (t - δ) < t from max_lt hpos (by linarith))
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show t < t + δ by linarith)
    have hp1' : t - δ < (p : ℝ) := lt_of_le_of_lt (le_max_right _ _) hp1
    have hp0 : (0 : ℝ) ≤ p := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hp1)
    have hr0 : (0 : ℝ) ≤ r := ht.trans hr1.le
    have hpt : dist (p : ℝ) t < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
    have hrt : dist (r : ℝ) t < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
    have hap := hcont (mem_Ici.mpr hp0) hpt
    have har := hcont (mem_Ici.mpr hr0) hrt
    have hlp := Metric.tendsto_nhds.mp (hlim p (by exact_mod_cast hp0)) (ε / 2) (half_pos hε)
    have hlr := Metric.tendsto_nhds.mp (hlim r (by exact_mod_cast hr0)) (ε / 2) (half_pos hε)
    filter_upwards [hC, hlp, hlr] with n hmono hnp hnr
    have h1 : C n p ≤ C n t := hmono (mem_Ici.mpr hp0) (mem_Ici.mpr ht) hp2.le
    have h2 : C n t ≤ C n r := hmono (mem_Ici.mpr ht) (mem_Ici.mpr hr0) hr1.le
    rw [Real.dist_eq, abs_sub_lt_iff] at hnp hnr hap har ⊢
    obtain ⟨hnp1, hnp2⟩ := hnp
    obtain ⟨hnr1, hnr2⟩ := hnr
    obtain ⟨hap1, hap2⟩ := hap
    obtain ⟨har1, har2⟩ := har
    constructor <;> linarith

/-- **Locally uniform dense-time limit (real time).** Under the hypotheses of `tendsto_of_rat_limit`,
`C n → a` uniformly on every compact interval `[0, T]`. -/
theorem eventually_abs_sub_lt_of_rat_limit {C : ℕ → ℝ → ℝ} {a : ℝ → ℝ}
    (hC : ∀ᶠ n in atTop, MonotoneOn (C n) (Ici 0))
    (ha : ContinuousOn a (Ici 0))
    (hlim : ∀ q : ℚ, 0 ≤ q → Tendsto (fun n => C n q) atTop (𝓝 (a q)))
    {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, |C n t - a t| < ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  have hC' : ∀ m : ℕ, MonotoneOn (C (m + N)) (Ici 0) := fun m => hN (m + N) (Nat.le_add_left N m)
  have hlim' : ∀ q : ℚ, 0 ≤ q → Tendsto (fun m => C (m + N) q) atTop (𝓝 (a q)) :=
    fun q hq => (tendsto_add_atTop_iff_nat N).mpr (hlim q hq)
  have hmono : MonotoneOn a (Ici 0) :=
    monotoneOn_limit_of_rat (Eventually.of_forall hC') ha hlim'
  have key := HarmonicBalls.MonotoneClockUniformLimit.monotone_clock_uniform_limit
    (fun m => C (m + N)) a hC' ha hmono hlim' T hT ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp key
  refine eventually_atTop.mpr ⟨M + N, fun n hn => ?_⟩
  have h := hM (n - N) (by omega)
  rwa [Nat.sub_add_cancel (by omega : N ≤ n)] at h

/-- **Dense-time limit for nonnegative real time.** Monotone clocks `K n : ℝ≥0 → ℝ`, eventually in
`n`, converging at each nonnegative rational time to a continuous limit `a`, converge at every
time `t : ℝ≥0` to `a t`. -/
theorem tendsto_nnreal_of_rat_limit {K : ℕ → ℝ≥0 → ℝ} {a : ℝ≥0 → ℝ}
    (hK : ∀ᶠ n in atTop, Monotone (K n)) (ha : Continuous a)
    (hrat : ∀ q : ℚ, 0 ≤ q →
      Tendsto (fun n => K n (Real.toNNReal (q : ℝ))) atTop (𝓝 (a (Real.toNNReal (q : ℝ))))) :
    ∀ t : ℝ≥0, Tendsto (fun n => K n t) atTop (𝓝 (a t)) := by
  intro t
  have hC : ∀ᶠ n in atTop, MonotoneOn (fun x : ℝ => K n (Real.toNNReal x)) (Ici 0) :=
    hK.mono fun n hn _x _ _y _ hxy => hn (Real.toNNReal_le_toNNReal hxy)
  have hcont : ContinuousOn (fun x : ℝ => a (Real.toNNReal x)) (Ici 0) :=
    (ha.comp continuous_real_toNNReal).continuousOn
  have key := tendsto_of_rat_limit hC hcont (fun q hq => hrat q hq) (t := (t : ℝ)) t.2
  simpa using key

/-- **Locally uniform dense-time limit for nonnegative real time.** Under the hypotheses of
`tendsto_nnreal_of_rat_limit`, `K n → a` uniformly on `[0, T]`. -/
theorem eventually_abs_sub_lt_nnreal_of_rat_limit {K : ℕ → ℝ≥0 → ℝ} {a : ℝ≥0 → ℝ}
    (hK : ∀ᶠ n in atTop, Monotone (K n)) (ha : Continuous a)
    (hrat : ∀ q : ℚ, 0 ≤ q →
      Tendsto (fun n => K n (Real.toNNReal (q : ℝ))) atTop (𝓝 (a (Real.toNNReal (q : ℝ)))))
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T → |K n t - a t| < ε := by
  have hC : ∀ᶠ n in atTop, MonotoneOn (fun x : ℝ => K n (Real.toNNReal x)) (Ici 0) :=
    hK.mono fun n hn _x _ _y _ hxy => hn (Real.toNNReal_le_toNNReal hxy)
  have hcont : ContinuousOn (fun x : ℝ => a (Real.toNNReal x)) (Ici 0) :=
    (ha.comp continuous_real_toNNReal).continuousOn
  have key := eventually_abs_sub_lt_of_rat_limit hC hcont (fun q hq => hrat q hq)
    (T := (T : ℝ)) T.2 hε
  filter_upwards [key] with n hn t ht
  have h := hn (t : ℝ) ⟨t.2, by exact_mod_cast ht⟩
  simpa using h

end MatedCRT.StoppedClockDenseLimit
