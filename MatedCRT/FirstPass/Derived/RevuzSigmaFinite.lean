import MatedCRT.FirstPass.Derived.RevuzMarkovAgainstClock
import MatedCRT.FirstPass.Derived.RevuzClockInverseIntegral
import MatedCRT.FirstPass.Derived.RevuzLintegral
import MatedCRT.FirstPass.Derived.RevuzOptionalAdditivity
import MatedCRT.FirstPass.Derived.RevuzBrownianReach

/-!
# The Revuz measure of a PCAF with a good clock is σ-finite

Let `A` be a positive continuous additive functional of planar Brownian motion whose clock is good
(almost surely strictly increasing and unbounded).  Its Revuz measure with respect to Lebesgue
measure, `μ(S) = ∫ dz E_z ∫_{(0,1]} 1_S(B_s) dA_s`, is `σ`-finite (Fukushima–Oshima–Takeda (2011),
Theorem 5.1.3; Revuz–Yor (1999), X §2).

The `σ`-finite cover is explicit.  Let `G_n` be the set of paths starting in the closed disc of
radius `n` whose (rational-time regularized) clock at time `1` is at most `n`, and
`S_n = {y | P_y(G_n) ≥ 1 / n}`.  Then `⋃ S_n = ℂ`, and

`μ(S_n) ≤ n² ∫ dz P_z(∃ s ≤ 1, ‖B_s‖ ≤ n) < ∞`.

Proof of the bound, for a fixed starting point `z`: pass from the clock to its right inverse
`τ_r` (`∫_{(0,1]} f(B_s) dA_s = ∫_0^{A_1} f(B_{τ_r}) dr`), bound `1_{S_n}(y) ≤ n P_y(G_n)` and use
the strong Markov property at `τ_r` to replace `P_{B_{τ_r}}(G_n)` by the indicator that the path
shifted at `τ_r` lies in `G_n`.  By additivity of the clock at the optional time `τ_r`,
`A_{τ_r + 1} = r + Ā_1 ∘ θ_{τ_r}`, so on that event `A_1 - n ≤ r ≤ A_1` and the path visits the disc
of radius `n` before time `1`; the `dr`-integral is then at most `n`.  The integral over `z` of
the visiting probability is finite by the Gaussian tail of planar Brownian motion.
-/

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess
open scoped NNReal ENNReal Topology

namespace MatedCRT

/-- Paths starting in the closed disc of radius `n` whose regularized clock at time `1` is at
most `n`. -/
def revuzGoodPaths (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (n : ℕ) : Set (ContinuousPath ℂ) :=
  {ω | ‖ω 0‖ ≤ n ∧ regularize A 1 ω ≤ (n : ℝ≥0)}

/-- The `n`-th set of the `σ`-finite cover of the Revuz measure: starting points from which planar
Brownian motion follows a path of `revuzGoodPaths A n` with probability at least `1 / n`. -/
def revuzCover (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (n : ℕ) : Set ℂ :=
  {y | (n : ℝ≥0∞)⁻¹ ≤ planarLaw y (revuzGoodPaths A n)}

theorem measurableSet_revuzGoodPaths {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (n : ℕ) : MeasurableSet (revuzGoodPaths A n) := by
  show MeasurableSet ({ω : ContinuousPath ℂ | ‖ω 0‖ ≤ n} ∩ {ω | regularize A 1 ω ≤ (n : ℝ≥0)})
  exact (measurableSet_le (PlanarBrownianSpace.measurable_eval_path (0 : ℝ≥0)).norm measurable_const).inter
    (measurableSet_le (measurable_regularize hA 1) measurable_const)

theorem measurableSet_revuzCover {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (n : ℕ) : MeasurableSet (revuzCover A n) :=
  measurableSet_le measurable_const
    (Measure.measurable_measure.1 measurable_planarLaw _ (measurableSet_revuzGoodPaths hA n))

theorem monotone_revuzGoodPaths (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) :
    Monotone (revuzGoodPaths A) := by
  intro m n hmn ω hω
  exact ⟨hω.1.trans (by exact_mod_cast hmn), hω.2.trans (by exact_mod_cast hmn)⟩

theorem iUnion_revuzGoodPaths (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) :
    ⋃ n, revuzGoodPaths A n = univ := by
  refine eq_univ_of_forall fun ω => mem_iUnion.2 ?_
  obtain ⟨n, hn⟩ := exists_nat_ge (max ‖ω 0‖ (regularize A 1 ω : ℝ))
  refine ⟨n, (le_max_left _ _).trans hn, ?_⟩
  have h : (regularize A 1 ω : ℝ) ≤ n := (le_max_right _ _).trans hn
  exact_mod_cast h

/-- Every starting point lies in some set of the cover. -/
theorem exists_mem_revuzCover (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (y : ℂ) :
    ∃ n : ℕ, y ∈ revuzCover A (n + 1) := by
  have : IsProbabilityMeasure (planarLaw y) := by unfold planarLaw; infer_instance
  have hlim : Tendsto (fun n => planarLaw y (revuzGoodPaths A n)) atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := planarLaw y) (monotone_revuzGoodPaths A)
    rw [iUnion_revuzGoodPaths, measure_univ] at h
    exact h
  have h1 : ∀ᶠ n in atTop, (2 : ℝ≥0∞)⁻¹ < planarLaw y (revuzGoodPaths A n) :=
    hlim.eventually (lt_mem_nhds (ENNReal.inv_lt_one.2 (by norm_num)))
  have h2 : ∀ᶠ n : ℕ in atTop, (n : ℝ≥0∞)⁻¹ ≤ 2⁻¹ := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact ENNReal.inv_le_inv.2 (by exact_mod_cast hn)
  obtain ⟨n, ⟨hn1, hn2⟩, hn3⟩ := ((h1.and h2).and (eventually_ge_atTop 1)).exists
  refine ⟨n - 1, ?_⟩
  rw [Nat.sub_add_cancel hn3]
  exact hn2.trans hn1.le

/-- **Additivity of the clock at its right inverse, as an inequality.**  For a fixed level `r`,
almost surely `A_1 ≤ r + c` whenever the regularized clock of the path shifted at `τ_r` is at most
`c` at time `1` (from `A_{τ_r + 1} = A_{τ_r} + Ā_1 ∘ θ_{τ_r}` at the optional version of `τ_r` and
`A_{τ_r} = r`). -/
theorem ae_clock_one_le_of_regularize_shift_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) (r c : ℝ≥0) :
    ∀ᵐ ω ∂planarLaw z,
      regularize A 1 (ContinuousPath.shift (clockInverse A r ω) ω) ≤ c → A 1 ω ≤ r + c := by
  obtain ⟨T, hTm, hTae⟩ := exists_optionalTime_ae_eq_clockInverse hA hG z
  filter_upwards [hTae, ae_add_regularize_shift_optionalTime hA z (T r) (hTm r), hA.path z, hG z]
    with ω hT hadd hp hg hle
  have hTr : T r ω = (clockInverse A r ω : WithTop ℝ≥0) := hT r
  have h := hadd (by rw [hTr]; exact WithTop.coe_lt_top _) 1
  rw [hTr, WithTop.untopD_coe] at h
  have hne : ∃ t, r < A t ω := (hg.2.eventually (eventually_gt_atTop r)).exists
  have hAr : A (clockInverse A r ω) ω = r := apply_clockInverse_eq hp.1 hp.2.1 hp.2.2 hne
  calc A 1 ω ≤ A (clockInverse A r ω + 1) ω := hp.2.2 le_add_self
    _ = r + regularize A 1 (ContinuousPath.shift (clockInverse A r ω) ω) := by rw [h, hAr]
    _ ≤ r + c := add_le_add le_rfl hle

/-- **The Revuz mass of `S_n` seen from one starting point.**  For every `z`,
`E_z ∫_{(0,1]} P_{B_s}(G_n) dA_s ≤ n P_z(∃ s ≤ 1, ‖B_s‖ ≤ n)`. -/
theorem lintegral_occupationMeasure_goodPaths_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) (n : ℕ) :
    ∫⁻ ω, ∫⁻ x, planarLaw x (revuzGoodPaths A n)
        ∂occupationMeasure (fun t => regularize A t ω) ω ∂planarLaw z ≤
      n * planarLaw z {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ ‖ω s‖ ≤ n} := by
  set G := revuzGoodPaths A n with hG_def
  have hGm : MeasurableSet G := measurableSet_revuzGoodPaths hA.meas n
  set E : Set (ContinuousPath ℂ) := {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ ‖ω s‖ ≤ n} with hE_def
  set ν : Measure ℝ := volume.restrict (Ioi 0) with hν
  -- the integrand of the strong Markov property
  set H : ℝ≥0 × ContinuousPath ℂ → ℝ≥0∞ :=
    fun p => (Iic (1 : ℝ≥0)).indicator 1 p.1 * G.indicator 1 p.2 with hH_def
  have hH : Measurable H :=
    ((measurable_const.indicator measurableSet_Iic).comp measurable_fst).mul
      ((measurable_const.indicator hGm).comp measurable_snd)
  -- its upper bound, remembering the clock through `A_1 ≤ r + n`
  set D : Set (ContinuousPath ℂ × ℝ) := {p | A 1 p.1 ≤ p.2.toNNReal + n} with hD
  have hDm : MeasurableSet D :=
    measurableSet_le ((hA.meas 1).comp measurable_fst)
      ((measurable_real_toNNReal.comp measurable_snd).add measurable_const)
  set U : ContinuousPath ℂ → ℝ → ℝ≥0∞ := fun ω r =>
    (Iic (1 : ℝ≥0)).indicator 1 (clockInverse (regularize A) r.toNNReal ω) *
      {ω' : ContinuousPath ℂ | ‖ω' 0‖ ≤ n}.indicator 1
        (ContinuousPath.shift (clockInverse (regularize A) r.toNNReal ω) ω) * D.indicator 1 (ω, r) with hU_def
  have hτ' : Measurable fun p : ContinuousPath ℂ × ℝ => clockInverse (regularize A) p.2.toNNReal p.1 :=
    (measurable_clockInverse_uncurry (measurable_regularize hA.meas) (regularize_monotone A)).comp
      ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)
  have hshift : Measurable fun p : ContinuousPath ℂ × ℝ =>
      ContinuousPath.shift (clockInverse (regularize A) p.2.toNNReal p.1) p.1 :=
    (ContinuousPath.continuous_shift (alpha := ℂ)).measurable.comp (hτ'.prodMk measurable_fst)
  have hL : Measurable fun p : ContinuousPath ℂ × ℝ =>
      H (clockInverse (regularize A) p.2.toNNReal p.1, ContinuousPath.shift (clockInverse (regularize A) p.2.toNNReal p.1) p.1) :=
    hH.comp (hτ'.prodMk hshift)
  have hUm : Measurable (Function.uncurry U) := by
    have hB : MeasurableSet {ω' : ContinuousPath ℂ | ‖ω' 0‖ ≤ n} :=
      measurableSet_le (PlanarBrownianSpace.measurable_eval_path (0 : ℝ≥0)).norm measurable_const
    exact ((((measurable_const.indicator measurableSet_Iic).comp hτ').mul
      ((measurable_const.indicator hB).comp hshift)).mul (measurable_const.indicator hDm))
  have hg : Measurable fun x : ℂ => planarLaw x G :=
    Measure.measurable_measure.1 measurable_planarLaw _ hGm
  have hreg := ae_clockInverse_regularize_eq hA z
  -- Step 1: from the clock to its right inverse, and the levels `r ≤ A_1` as `τ_r ≤ 1`.
  have hstep1 : ∀ᵐ ω ∂planarLaw z,
      ∫⁻ x, planarLaw x G ∂occupationMeasure (fun t => regularize A t ω) ω =
        ∫⁻ r, ∫⁻ ω', H (clockInverse A r.toNNReal ω, ω')
          ∂planarLaw (ω (clockInverse A r.toNNReal ω)) ∂ν := by
    filter_upwards [ae_lintegral_occupationMeasure_eq_clockInverse hA hG z hg, hA.path z, hG z]
      with ω hω hp hgc
    rw [hω, ← Ioi_inter_Iic, inter_comm, ← Measure.restrict_restrict measurableSet_Iic,
      ← lintegral_indicator measurableSet_Iic]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    simp only [hH_def]
    rw [lintegral_const_mul _ (measurable_one.indicator hGm), lintegral_indicator_one hGm]
    have hne : ∃ t, r.toNNReal < A t ω := (hgc.2.eventually (eventually_gt_atTop _)).exists
    have hiff : r ∈ Iic (A 1 ω : ℝ) ↔ clockInverse A r.toNNReal ω ∈ Iic (1 : ℝ≥0) := by
      rw [mem_Iic, mem_Iic, clockInverse_le_iff hp.1 hp.2.1 hgc.1 hne,
        Real.toNNReal_le_iff_le_coe]
    by_cases hmem : r ∈ Iic (A 1 ω : ℝ)
    · rw [indicator_of_mem hmem, indicator_of_mem (hiff.1 hmem), Pi.one_apply, one_mul]
    · rw [indicator_of_notMem hmem, indicator_of_notMem (fun h => hmem (hiff.2 h)), zero_mul]
  -- Step 2: the per-level almost sure bound of the shifted integrand.
  have hstep2 : ∀ r : ℝ, ∀ᵐ ω ∂planarLaw z,
      H (clockInverse (regularize A) r.toNNReal ω, ContinuousPath.shift (clockInverse (regularize A) r.toNNReal ω) ω) ≤ U ω r := by
    intro r
    filter_upwards [hreg, ae_clock_one_le_of_regularize_shift_le hA hG z r.toNNReal n] with ω hr hc
    by_cases h1 : clockInverse (regularize A) r.toNNReal ω ∈ Iic (1 : ℝ≥0)
    · by_cases h2 : ContinuousPath.shift (clockInverse (regularize A) r.toNNReal ω) ω ∈ G
      · have h3 : (ω, r) ∈ D := by
          have := hc (by rw [← hr r.toNNReal]; exact h2.2)
          exact this
        have h2' : ContinuousPath.shift (clockInverse (regularize A) r.toNNReal ω) ω ∈
            {ω' : ContinuousPath ℂ | ‖ω' 0‖ ≤ n} := h2.1
        simp only [hH_def, hU_def, indicator_of_mem h1, indicator_of_mem h2,
          indicator_of_mem h2', indicator_of_mem h3, Pi.one_apply, mul_one, le_refl]
      · simp only [hH_def, indicator_of_notMem h2, mul_zero, zero_le]
    · simp only [hH_def, indicator_of_notMem h1, zero_mul, zero_le]
  -- Step 3: for a good path, the levels counted by `U` have Lebesgue measure at most `n`.
  have hstep3 : ∀ᵐ ω ∂planarLaw z, ∫⁻ r, U ω r ∂ν ≤ n * E.indicator 1 ω := by
    filter_upwards [hreg, hA.path z, hG z] with ω hr hp hgc
    have hpt : ∀ r ∈ Ioi (0 : ℝ), U ω r ≤
        E.indicator 1 ω * (Icc ((A 1 ω : ℝ) - n) (A 1 ω)).indicator 1 r := by
      intro r hr0
      have hr0' : (0 : ℝ) < r := hr0
      by_cases hU0 : U ω r = 0
      · rw [hU0]; exact zero_le
      · simp only [hU_def, mul_eq_zero, indicator_apply_eq_zero, Pi.one_apply, one_ne_zero,
          imp_false, not_or, not_not] at hU0
        obtain ⟨⟨h1, h2⟩, h3⟩ := hU0
        have h1' : clockInverse A r.toNNReal ω ≤ 1 := by rw [← hr]; exact h1
        have hne : ∃ t, r.toNNReal < A t ω := (hgc.2.eventually (eventually_gt_atTop _)).exists
        have hle : r.toNNReal ≤ A 1 ω := (clockInverse_le_iff hp.1 hp.2.1 hgc.1 hne).1 h1'
        have hE : ω ∈ E := by
          refine ⟨clockInverse A r.toNNReal ω, h1', ?_⟩
          have h2' : ‖ContinuousPath.shift (clockInverse (regularize A) r.toNNReal ω) ω 0‖ ≤ n := h2
          rwa [ContinuousPath.shift_apply, add_zero, hr] at h2'
        have h3' : A 1 ω ≤ r.toNNReal + n := h3
        have hIcc : r ∈ Icc ((A 1 ω : ℝ) - n) (A 1 ω) := by
          have ha : (A 1 ω : ℝ) ≤ r + n := by
            have := NNReal.coe_le_coe.2 h3'
            rwa [NNReal.coe_add, Real.coe_toNNReal r hr0'.le, NNReal.coe_natCast] at this
          have hb : r ≤ (A 1 ω : ℝ) := by
            have := NNReal.coe_le_coe.2 hle
            rwa [Real.coe_toNNReal r hr0'.le] at this
          exact ⟨by linarith, hb⟩
        rw [indicator_of_mem hE, indicator_of_mem hIcc, Pi.one_apply, Pi.one_apply, one_mul]
        have hU1 : U ω r ≤ 1 := by
          simp only [hU_def]
          refine mul_le_one' (mul_le_one' ?_ ?_) ?_ <;>
            exact indicator_le_self' (fun _ _ => zero_le_one) _ |>.trans (by simp)
        exact hU1
    calc ∫⁻ r, U ω r ∂ν
        ≤ ∫⁻ r, E.indicator 1 ω * (Icc ((A 1 ω : ℝ) - n) (A 1 ω)).indicator 1 r ∂ν :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpt))
      _ = E.indicator 1 ω * ν (Icc ((A 1 ω : ℝ) - n) (A 1 ω)) := by
          rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_Icc),
            lintegral_indicator_one measurableSet_Icc]
      _ ≤ E.indicator 1 ω * volume (Icc ((A 1 ω : ℝ) - n) (A 1 ω)) :=
          mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
      _ = n * E.indicator 1 ω := by
          rw [Real.volume_Icc, sub_sub_cancel, ENNReal.ofReal_natCast, mul_comm]
  -- Assembly.
  calc ∫⁻ ω, ∫⁻ x, planarLaw x G ∂occupationMeasure (fun t => regularize A t ω) ω ∂planarLaw z
      = ∫⁻ ω, ∫⁻ r, ∫⁻ ω', H (clockInverse A r.toNNReal ω, ω')
          ∂planarLaw (ω (clockInverse A r.toNNReal ω)) ∂ν ∂planarLaw z := lintegral_congr_ae hstep1
    _ = ∫⁻ ω, ∫⁻ r, H (clockInverse A r.toNNReal ω,
          ContinuousPath.shift (clockInverse A r.toNNReal ω) ω) ∂ν ∂planarLaw z :=
        (lintegral_lintegral_shift_clockInverse_eq hA hG z ν hH).symm
    _ = ∫⁻ ω, ∫⁻ r, H (clockInverse (regularize A) r.toNNReal ω, ContinuousPath.shift (clockInverse (regularize A) r.toNNReal ω) ω) ∂ν ∂planarLaw z := by
        refine lintegral_congr_ae ?_
        filter_upwards [hreg] with ω h
        simp only [h]
    _ = ∫⁻ r, ∫⁻ ω, H (clockInverse (regularize A) r.toNNReal ω, ContinuousPath.shift (clockInverse (regularize A) r.toNNReal ω) ω)
          ∂planarLaw z ∂ν := lintegral_lintegral_swap hL.aemeasurable
    _ ≤ ∫⁻ r, ∫⁻ ω, U ω r ∂planarLaw z ∂ν :=
        lintegral_mono fun r => lintegral_mono_ae (hstep2 r)
    _ = ∫⁻ ω, ∫⁻ r, U ω r ∂ν ∂planarLaw z := (lintegral_lintegral_swap hUm.aemeasurable).symm
    _ ≤ ∫⁻ ω, n * E.indicator 1 ω ∂planarLaw z := lintegral_mono_ae hstep3
    _ ≤ n * planarLaw z E := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n)]
        exact mul_le_mul' le_rfl (lintegral_indicator_one_le E)

/-- **The Revuz measure of `S_n` is finite:**
`μ(S_n) ≤ n² ∫ dz P_z(∃ s ≤ 1, ‖B_s‖ ≤ n)`. -/
theorem revuz_revuzCover_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {n : ℕ} (hn : n ≠ 0) :
    revuz planarLaw A (revuzCover A n) ≤
      n * n * ∫⁻ z, planarLaw z {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ ‖ω s‖ ≤ n} := by
  have hGm := measurableSet_revuzGoodPaths hA.meas n
  have hg : Measurable fun x : ℂ => planarLaw x (revuzGoodPaths A n) :=
    Measure.measurable_measure.1 measurable_planarLaw _ hGm
  calc revuz planarLaw A (revuzCover A n)
      = ∫⁻ x, (revuzCover A n).indicator 1 x ∂revuz planarLaw A :=
        (lintegral_indicator_one (measurableSet_revuzCover hA.meas n)).symm
    _ ≤ ∫⁻ x, n * planarLaw x (revuzGoodPaths A n) ∂revuz planarLaw A := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ revuzCover A n
        · rw [indicator_of_mem hx, Pi.one_apply,
            ← ENNReal.mul_inv_cancel (by exact_mod_cast hn) (ENNReal.natCast_ne_top n)]
          exact mul_le_mul' le_rfl hx
        · rw [indicator_of_notMem hx]
          exact zero_le
    _ = n * ∫⁻ z, ∫⁻ ω, ∫⁻ x, planarLaw x (revuzGoodPaths A n)
          ∂occupationMeasure (fun t => regularize A t ω) ω ∂planarLaw z ∂volume := by
        rw [lintegral_const_mul _ hg, lintegral_revuz measurable_planarLaw hA.meas hg]
    _ ≤ n * ∫⁻ z, n * planarLaw z {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ ‖ω s‖ ≤ n} :=
        mul_le_mul' le_rfl (lintegral_mono fun z =>
          lintegral_occupationMeasure_goodPaths_le hA hG z n)
    _ = n * n * ∫⁻ z, planarLaw z {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ ‖ω s‖ ≤ n} := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n), mul_assoc]

theorem revuz_revuzCover_lt_top {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {n : ℕ} (hn : n ≠ 0) :
    revuz planarLaw A (revuzCover A n) < ∞ :=
  (revuz_revuzCover_le hA hG hn).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) (ENNReal.natCast_lt_top n))
      (lintegral_planarLaw_exists_norm_le_lt_top n))

/-- **The Revuz measure of a PCAF of planar Brownian motion with a good clock is `σ`-finite**
(Fukushima–Oshima–Takeda (2011), Theorem 5.1.3): the sets `S_{n+1}` form a countable cover by
sets of finite Revuz measure. -/
theorem sigmaFinite_revuz {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) :
    SigmaFinite (revuz planarLaw A) :=
  ⟨⟨{ set := fun n => revuzCover A (n + 1)
      set_mem := fun _ => mem_univ _
      finite := fun n => revuz_revuzCover_lt_top hA hG (Nat.succ_ne_zero n)
      spanning := eq_univ_of_forall fun y => mem_iUnion.2 (exists_mem_revuzCover A y) }⟩⟩

end MatedCRT
