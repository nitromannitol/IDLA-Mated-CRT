import MatedCRT.FirstPass.Derived.StopAtExitCmpContinuity
import MatedCRT.FirstPass.S6j.CmpEDistPointwise

/-!
# Continuity of the exit time and of the stopped path at a regular exit, for uniform convergence

Let `U ⊆ ℂ` be open and let `f` be a continuous path which leaves `U` at a finite time `τ` and exits
regularly: it visits the complement of `closure U` at times arbitrarily close to `τ` from above
(`MatedCRT.TruncatedLaws.RegularExit`). If paths `g i` converge to `f` uniformly on `[0, ∞)`, then

* the exit times converge: `pathExitTime U (g i) → τ` (before `τ` the compact arc `f([0, s])` has a
  neighbourhood inside `U`; just after `τ` the path `f` is at positive distance from `closure U`);
* the stopped paths converge uniformly: `sup_t |g i (t ∧ τ_i) - f (t ∧ τ)| → 0` (uniform continuity
  of `f` on `[0, τ + 1]`).

The uniform distance dominates the distance `cmpEDist` of curves modulo time parametrization (take
the identity reparametrization), and, unlike `cmpEDist`, it is a countable supremum for continuous
paths, hence measurable in a random path. This is the deterministic half of the uniform-start
continuity of planar Brownian motion stopped at the exit of a disc, used to move the start point
of the Brownian motion in the uniform-start invariance principle (`MatedCRT.GMS21UniformStartInput`).

## Main statements

* `MatedCRT.StopAtExitCmp.tendsto_pathExitTime_of_uniform`
* `MatedCRT.StopAtExitCmp.tendsto_iSup_edist_stopAtExit_of_uniform`
* `MatedCRT.StopAtExitCmp.tendsto_iSup_edist_stopAtExit_add_const`: the case `g i = f + v i`,
  `v i → 0` (translated start points).
* `MatedCRT.StopAtExitCmp.tendsto_iSup_edist_stopAtExit_add_const_of_regularExit`: the same with the
  hypothesis in the form `RegularExit U f`.
-/

open Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

variable {ι : Type*} {l : Filter ι}

/-- **Continuity of the exit time at a regular exit.** If the continuous path `f` leaves the open
set `U` at a finite time and visits the complement of `closure U` at times arbitrarily close to its
exit time from above, then the exit time from `U` is continuous at `f` for uniform convergence of
paths on `[0, ∞)`. -/
theorem tendsto_pathExitTime_of_uniform {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ}
    (hf : Continuous f) (hfin : pathExitTime U f ≠ ⊤)
    (hreg : ∃ᶠ t in 𝓝[>] (pathExitTime U f).toNNReal, f t ∉ closure U)
    {g : ι → ℝ≥0 → ℂ} (hg : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ t, dist (g i t) (f t) < ε) :
    Tendsto (fun i => pathExitTime U (g i)) l (𝓝 (pathExitTime U f)) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨s, has, hsτ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    have hK : IsCompact (f '' Icc 0 s) := isCompact_Icc.image hf
    have hKU : f '' Icc 0 s ⊆ U := by
      rintro _ ⟨t, ht, rfl⟩
      exact mem_of_lt_exitTime (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) hsτ)
    obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU hKU
    filter_upwards [hg δ hδ] with i hi
    refine lt_of_lt_of_le has (le_exitTime_of_forall_le_mem fun t ht => hthick ?_)
    exact mem_thickening_iff.2 ⟨f t, ⟨t, ⟨by positivity, ht⟩, rfl⟩, hi t⟩
  · have hτa : ((pathExitTime U f).toNNReal : ℝ≥0∞) < a := by rwa [ENNReal.coe_toNNReal hfin]
    obtain ⟨s, hτs, hsa⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hτa
    have hτs' : (pathExitTime U f).toNNReal < s := ENNReal.coe_lt_coe.1 hτs
    obtain ⟨t₀, ht₀f, ht₀I⟩ := (hreg.and_eventually (Ioo_mem_nhdsGT hτs')).exists
    have hopen : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen (f t₀) ht₀f
    filter_upwards [hg ε hε] with i hi
    have hout : g i t₀ ∉ U := fun hmem => hball (mem_ball.2 (hi t₀)) (subset_closure hmem)
    exact lt_of_le_of_lt (exitTime_le_of_not_mem hout)
      (lt_trans (ENNReal.coe_lt_coe.2 ht₀I.2) hsa)

/-- **Uniform continuity of the stopping map at a regular exit.** If the continuous path `f` leaves
the open set `U` at a finite time and exits regularly, and the paths `g i` converge to `f`
uniformly on `[0, ∞)`, then the paths stopped at their exit times from `U` converge uniformly:
`sup_t |stopAtExit U (g i) t - stopAtExit U f t| → 0`. -/
theorem tendsto_iSup_edist_stopAtExit_of_uniform {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ}
    (hf : Continuous f) (hfin : pathExitTime U f ≠ ⊤)
    (hreg : ∃ᶠ t in 𝓝[>] (pathExitTime U f).toNNReal, f t ∉ closure U)
    {g : ι → ℝ≥0 → ℂ} (hg : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ t, dist (g i t) (f t) < ε) :
    Tendsto (fun i => ⨆ t, edist (stopAtExit U (g i) t) (stopAtExit U f t)) l (𝓝 0) := by
  set τ : ℝ≥0 := (pathExitTime U f).toNNReal with hτ
  have hexit := tendsto_pathExitTime_of_uniform hU hf hfin hreg hg
  have hfin_ev : ∀ᶠ i in l, pathExitTime U (g i) ≠ ⊤ :=
    (hexit.eventually (eventually_lt_nhds (lt_top_iff_ne_top.2 hfin))).mono fun _ h => h.ne
  have hreal : Tendsto (fun i => ((pathExitTime U (g i)).toNNReal : ℝ)) l (𝓝 (τ : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp ((ENNReal.tendsto_toNNReal hfin).comp hexit)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr
  have huc := (isCompact_Icc (a := (0 : ℝ≥0)) (b := τ + 1)).uniformContinuousOn_of_continuous
    hf.continuousOn
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 huc (r / 2) (half_pos hrpos)
  filter_upwards [hfin_ev, hg (r / 2) (half_pos hrpos),
    Metric.tendsto_nhds.1 hreal (min δ 1) (lt_min hδ one_pos)] with i hfi hgi hτi
  refine iSup_le fun t => ?_
  rw [CmpEDistPointwise.stopAtExit_eq_min_of_exit_ne_top hfi,
    CmpEDistPointwise.stopAtExit_eq_min_of_exit_ne_top hfin, ← hτ]
  set τi : ℝ≥0 := (pathExitTime U (g i)).toNNReal with hτi_def
  have hd : |(τi : ℝ) - τ| < min δ 1 := by
    rw [← Real.dist_eq]
    exact hτi
  have hmin : dist (min t τi) (min t τ) < δ := by
    have h := abs_min_sub_min_le_max (t : ℝ) (τi : ℝ) (t : ℝ) (τ : ℝ)
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h
    rw [NNReal.dist_eq, NNReal.coe_min, NNReal.coe_min]
    exact lt_of_le_of_lt h (lt_of_lt_of_le hd (min_le_left _ _))
  have hτi1 : τi ≤ τ + 1 := by
    have h := (abs_lt.1 hd).2
    rw [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_one]
    linarith [min_le_right δ 1]
  have hmemi : min t τi ∈ Icc (0 : ℝ≥0) (τ + 1) :=
    ⟨by positivity, (min_le_right _ _).trans hτi1⟩
  have hmem : min t τ ∈ Icc (0 : ℝ≥0) (τ + 1) :=
    ⟨by positivity, (min_le_right _ _).trans le_self_add⟩
  calc edist (g i (min t τi)) (f (min t τ))
      ≤ edist (g i (min t τi)) (f (min t τi)) + edist (f (min t τi)) (f (min t τ)) :=
        edist_triangle _ _ _
    _ ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) := by
        rw [edist_dist, edist_dist]
        exact add_le_add (ENNReal.ofReal_le_ofReal (hgi _).le)
          (ENNReal.ofReal_le_ofReal (hδf _ hmemi _ hmem hmin).le)
    _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_add (half_pos hrpos).le (half_pos hrpos).le, add_halves]
    _ ≤ ε := hrε.le

/-- **Translated start points.** If the continuous path `f` leaves the open set `U` at a finite
time and exits regularly, then for translates `f + v i` with `v i → 0` the stopped paths converge
uniformly to the stopped path of `f`. -/
theorem tendsto_iSup_edist_stopAtExit_add_const {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ}
    (hf : Continuous f) (hfin : pathExitTime U f ≠ ⊤)
    (hreg : ∃ᶠ t in 𝓝[>] (pathExitTime U f).toNNReal, f t ∉ closure U)
    {v : ι → ℂ} (hv : Tendsto v l (𝓝 0)) :
    Tendsto (fun i => ⨆ t, edist (stopAtExit U (fun s => f s + v i) t) (stopAtExit U f t)) l
      (𝓝 0) :=
  tendsto_iSup_edist_stopAtExit_of_uniform hU hf hfin hreg fun ε hε =>
    (Metric.tendsto_nhds.1 hv ε hε).mono fun i hi t => by simpa [dist_eq_norm] using hi

/-- `tendsto_iSup_edist_stopAtExit_add_const` with the regular exit in the form
`pathExitTime U f ≠ ⊤ ∧ RegularExit U f`, as produced for planar Brownian motion by
`MatedCRT.StopAtExitCmp.ae_regularExit_ball_planarBrownian`. -/
theorem tendsto_iSup_edist_stopAtExit_add_const_of_regularExit {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ≥0 → ℂ} (hf : Continuous f)
    (hreg : pathExitTime U f ≠ ⊤ ∧ MatedCRT.TruncatedLaws.RegularExit U f)
    {v : ι → ℂ} (hv : Tendsto v l (𝓝 0)) :
    Tendsto (fun i => ⨆ t, edist (stopAtExit U (fun s => f s + v i) t) (stopAtExit U f t)) l
      (𝓝 0) :=
  tendsto_iSup_edist_stopAtExit_add_const hU hf hreg.1 (hreg.2.resolve_left hreg.1) hv

end MatedCRT.StopAtExitCmp
