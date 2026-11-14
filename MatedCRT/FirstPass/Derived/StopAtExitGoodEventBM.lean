import MatedCRT.FirstPass.Derived.StopAtExitGoodEvent
import MatedCRT.FirstPass.Derived.BrownianRegularExitBall

/-!
# The good event of the stopping map has probability close to one

`MatedCRT.StopAtExitCmp.GoodStop U T η d ε f` is a measurable event, defined at rational times, on which stopping at
the exit time from `U` has the explicit modulus of continuity `cmpEDist g f < min ε d ⇒
cmpEDist (stopAtExit U g) (stopAtExit U f) ≤ 2 ε`. Here the parameters are discretized: `GoodStopN U N ε f` asks for
`GoodStop U T (1 / m) (1 / k) ε f` for some integers `T ≤ N` and `1 ≤ m, k ≤ N`. This event increases with `N`, is
measurable, and gives the modulus `min ε (1 / N)`, uniform over the event.

Every continuous path which leaves the open set `U` at a finite time and exits regularly (it visits the complement
of `closure U` at times arbitrarily close to the exit time from above) lies in `GoodStopN U N ε` for `N` large.
Hence, for every finite measure on paths under which almost every path exits `U` regularly at a finite time, the
measure of the complement of `GoodStopN U N ε` tends to `0` as `N → ∞`; in particular for planar Brownian motion
started in a disc and stopped at its exit from the disc. This is the step that turns the almost sure continuity of
the stopping map into a bound with a measurable exceptional event, as the uniform-start invariance principle
`MatedCRT.GMS21UniformStartInput` needs.

## Main statements

* `MatedCRT.StopAtExitCmp.GoodStopN`, `goodStopN_mono`, `measurable_goodStopN`,
  `measurableSet_goodStopN_continuousPath`, `cmpEDist_stopAtExit_le_of_goodStopN`.
* `MatedCRT.StopAtExitCmp.exists_goodStopN`: coverage at a regular finite exit.
* `MatedCRT.StopAtExitCmp.tendsto_measure_not_goodStopN`,
  `tendsto_planarBrownianMotion_not_goodStopN_ball`: the complement has small probability.
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- The good events `GoodStop U T η d ε` with integer horizon `T ≤ N` and scales `η = 1 / m`, `d = 1 / k`,
`1 ≤ m, k ≤ N`. -/
def GoodStopN (U : Set ℂ) (N : ℕ) (ε : ℝ) (f : ℝ≥0 → ℂ) : Prop :=
  ∃ T m k : ℕ, T ≤ N ∧ m ≤ N ∧ k ≤ N ∧ 0 < m ∧ 0 < k ∧
    GoodStop U (T : ℝ≥0) (m : ℝ≥0)⁻¹ (k : ℝ)⁻¹ ε f

/-- `GoodStopN U N ε` increases with `N`. -/
theorem goodStopN_mono {U : Set ℂ} {ε : ℝ} {f : ℝ≥0 → ℂ} {N N' : ℕ} (hNN' : N ≤ N')
    (h : GoodStopN U N ε f) : GoodStopN U N' ε f := by
  obtain ⟨T, m, k, hT, hm, hk, hm0, hk0, hg⟩ := h
  exact ⟨T, m, k, hT.trans hNN', hm.trans hNN', hk.trans hNN', hm0, hk0, hg⟩

/-- **Uniform modulus on `GoodStopN`.** For a continuous path `f` in `GoodStopN U N ε`, every path `g` within curve
distance `min ε (1 / N)` of `f` has, once stopped at its exit time from `U`, curve distance at most `2 ε` from `f`
stopped at its exit time. -/
theorem cmpEDist_stopAtExit_le_of_goodStopN {U : Set ℂ} {N : ℕ} {ε : ℝ} {f : ℝ≥0 → ℂ}
    (hf : Continuous f) (hgood : GoodStopN U N ε f) {g : ℝ≥0 → ℂ}
    (hg : cmpEDist g f < ENNReal.ofReal (min ε (N : ℝ)⁻¹)) :
    cmpEDist (stopAtExit U g) (stopAtExit U f) ≤ ENNReal.ofReal (2 * ε) := by
  obtain ⟨T, m, k, -, -, hk, hm0, hk0, hg'⟩ := hgood
  have hη : (0 : ℝ≥0) < (m : ℝ≥0)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hm0)
  refine cmpEDist_stopAtExit_le_of_goodStop hf hη hg' (lt_of_lt_of_le hg (ENNReal.ofReal_le_ofReal ?_))
  exact min_le_min le_rfl (inv_anti₀ (Nat.cast_pos.2 hk0) (Nat.cast_le.2 hk))

/-- **Measurability.** For a family of paths `F ω` whose coordinates and exit time from `U` are measurable
functions of `ω`, the event `GoodStopN U N ε (F ω)` is measurable. -/
theorem measurable_goodStopN {Ω : Type*} [MeasurableSpace Ω] {U : Set ℂ} (N : ℕ) (ε : ℝ)
    {F : Ω → ℝ≥0 → ℂ} (hF : ∀ t, Measurable fun ω => F ω t)
    (hτ : Measurable fun ω => pathExitTime U (F ω)) :
    Measurable fun ω => GoodStopN U N ε (F ω) := by
  unfold GoodStopN
  refine Measurable.exists fun T => Measurable.exists fun m => Measurable.exists fun k => ?_
  exact measurable_const.and (measurable_const.and (measurable_const.and (measurable_const.and
    (measurable_const.and (measurable_goodStop _ _ _ _ hF hτ)))))

/-- `GoodStopN U N ε` is a Borel set of continuous paths for every open set `U`. -/
theorem measurableSet_goodStopN_continuousPath {U : Set ℂ} (hU : IsOpen U) (N : ℕ) (ε : ℝ) :
    MeasurableSet {ω : ContinuousPath ℂ | GoodStopN U N ε ⇑ω} :=
  measurableSet_setOfPred.2 (measurable_goodStopN N ε
    (fun t => (ContinuousPath.continuous_eval t).measurable) (ContinuousPath.measurable_exitTime U hU))

/-- **Coverage at a regular exit.** Let `U` be open and let `f` be a continuous path which leaves `U` at a finite
time `τ` and visits the complement of `closure U` at times arbitrarily close to `τ` from above. Then for every
`ε > 0`, `f` lies in `GoodStopN U N ε` for some `N`. -/
theorem exists_goodStopN {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ} (hf : Continuous f)
    (hfin : pathExitTime U f ≠ ⊤)
    (hreg : ∃ᶠ t in 𝓝[>] (pathExitTime U f).toNNReal, f t ∉ closure U) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, GoodStopN U N ε f := by
  set τ : ℝ≥0 := (pathExitTime U f).toNNReal with hτdef
  have hτ : pathExitTime U f = τ := (ENNReal.coe_toNNReal hfin).symm
  set T : ℕ := ⌈τ⌉₊ + 1 with hTdef
  -- the time scale `η = 1 / m` from the uniform continuity of `f` on `[0, T + 1]`
  obtain ⟨η₀, hη₀, hη₀f⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ≥0)) (b := (T : ℝ≥0) + 1)).uniformContinuousOn_of_continuous
      hf.continuousOn) ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hη₀)
  set m : ℕ := n + 1 with hmdef
  have hm0 : 0 < m := Nat.succ_pos n
  set η : ℝ≥0 := (m : ℝ≥0)⁻¹ with hηdef
  have hηpos : 0 < η := inv_pos.2 (Nat.cast_pos.2 hm0)
  have hηreal : (η : ℝ) = 1 / ((n : ℝ) + 1) := by
    rw [hηdef, NNReal.coe_inv, NNReal.coe_natCast, hmdef, Nat.cast_succ, one_div]
  have hη2 : 2 * (η : ℝ) < η₀ := by
    rw [hηreal]
    linarith
  have hη1 : (η : ℝ) ≤ 1 := by
    rw [hηreal, div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- an exit witness at a rational time, with a ball outside `closure U`
  obtain ⟨s, hs_out, hs_mem⟩ : ∃ s, f s ∉ closure U ∧ s ∈ Ioo τ (τ + η / 2) :=
    (hreg.and_eventually (Ioo_mem_nhdsGT (lt_add_of_pos_right τ (half_pos hηpos)))).exists
  obtain ⟨d₁, hd₁, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl (f s) hs_out
  obtain ⟨q, hq1, hq2, hq3⟩ :=
    exists_ratTime_near hf s (half_pos hd₁) (half_pos (NNReal.coe_pos.2 hηpos))
  have hs2 : (s : ℝ) < τ + η / 2 := by
    have h := NNReal.coe_lt_coe.2 hs_mem.2
    push_cast at h
    exact h
  -- up to time `τ - η / 4`, `f` stays in a compact subset of `U`
  have hA : IsCompact (Icc (0 : ℝ≥0) τ ∩ {t : ℝ≥0 | t + η / 4 ≤ τ}) :=
    isCompact_Icc.inter_right (isClosed_le (continuous_id.add continuous_const) continuous_const)
  have hKU : f '' (Icc (0 : ℝ≥0) τ ∩ {t : ℝ≥0 | t + η / 4 ≤ τ}) ⊆ U := by
    rintro _ ⟨t, ⟨_, ht⟩, rfl⟩
    apply mem_of_lt_exitTime
    rw [hτ]
    exact_mod_cast lt_of_lt_of_le (lt_add_of_pos_right t (div_pos hηpos (by norm_num))) ht
  obtain ⟨d₂, hd₂, hthick⟩ := (hA.image hf).exists_thickening_subset_open hU hKU
  -- the space scale `d = 1 / k`
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (lt_min (half_pos hd₁) hd₂)
  set k : ℕ := j + 1 with hkdef
  have hk0 : 0 < k := Nat.succ_pos j
  have hkreal : (k : ℝ)⁻¹ < min (d₁ / 2) d₂ := by
    rw [hkdef, Nat.cast_succ, ← one_div]
    exact hj
  refine ⟨max T (max m k), T, m, k, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _), hm0, hk0, ⟨⟨q, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [hτ]
    exact ENNReal.coe_lt_coe.2 (hs_mem.1.trans hq1)
  · rw [hτ, ← ENNReal.coe_add, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add]
    linarith
  · have hceil : (τ : ℝ) ≤ (⌈τ⌉₊ : ℝ) := by
      have h := NNReal.coe_le_coe.2 (Nat.le_ceil τ)
      rwa [NNReal.coe_natCast] at h
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast, hTdef, Nat.cast_succ]
    linarith
  · intro w hw hwU
    have hmem : w ∈ ball (f s) d₁ := by
      rw [mem_ball]
      have hwk : dist w (f (ratTime q)) < d₁ / 2 := hw.trans (hkreal.trans_le (min_le_left _ _))
      linarith [dist_triangle w (f (ratTime q)) (f s)]
    exact hball hmem (subset_closure hwU)
  · intro q₁ q₂ h1 h2 h12
    exact (hη₀f _ ⟨zero_le, h1⟩ _ ⟨zero_le, h2⟩ (h12.trans hη2)).le
  · intro q₁ hq₁ w hw
    rw [hτ] at hq₁
    have h' : ratTime q₁ + η / 4 < τ := ENNReal.coe_lt_coe.1 hq₁
    apply hthick
    refine mem_thickening_iff.2 ⟨f (ratTime q₁), ⟨ratTime q₁, ⟨⟨zero_le, le_self_add.trans h'.le⟩, h'.le⟩, rfl⟩,
      ?_⟩
    exact hw.trans (hkreal.trans_le (min_le_right _ _))

/-- Coverage at a regular finite exit, in the form `MatedCRT.TruncatedLaws.RegularExit`. -/
theorem exists_goodStopN_of_regularExit {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ} (hf : Continuous f)
    (hfin : pathExitTime U f ≠ ⊤) (hreg : MatedCRT.TruncatedLaws.RegularExit U f) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, GoodStopN U N ε f :=
  exists_goodStopN hU hf hfin (hreg.resolve_left hfin) hε

/-- **The complement of the good event has small probability.** For a finite measure on continuous paths under
which almost every path leaves the open set `U` at a finite time and exits it regularly, the measure of the
complement of `GoodStopN U N ε` tends to `0` as `N → ∞`. -/
theorem tendsto_measure_not_goodStopN {μ : Measure (ContinuousPath ℂ)} [IsFiniteMeasure μ] {U : Set ℂ}
    (hU : IsOpen U)
    (hae : ∀ᵐ (b : ContinuousPath ℂ) ∂μ, pathExitTime U ⇑b ≠ ⊤ ∧ MatedCRT.TruncatedLaws.RegularExit U ⇑b) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => μ {b | ¬ GoodStopN U N ε ⇑b}) atTop (𝓝 0) := by
  have hmeas : ∀ N : ℕ, MeasurableSet {b : ContinuousPath ℂ | ¬ GoodStopN U N ε ⇑b} :=
    fun N => (measurableSet_goodStopN_continuousPath hU N ε).compl
  have hanti : Antitone fun N : ℕ => {b : ContinuousPath ℂ | ¬ GoodStopN U N ε ⇑b} :=
    fun N N' hNN' b hb hb' => hb (goodStopN_mono hNN' hb')
  have hzero : μ (⋂ N : ℕ, {b : ContinuousPath ℂ | ¬ GoodStopN U N ε ⇑b}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro b hb hgood
    obtain ⟨N, hN⟩ := exists_goodStopN_of_regularExit hU b.continuous hgood.1 hgood.2 hε
    exact mem_iInter.1 hb N hN
  rw [← hzero]
  exact tendsto_measure_iInter_atTop (fun N => (hmeas N).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩

/-- **Planar Brownian motion.** For planar Brownian motion started at a point `c` of the disc `ball z r`, the
probability of the complement of `GoodStopN (ball z r) N ε` tends to `0` as `N → ∞`. -/
theorem tendsto_planarBrownianMotion_not_goodStopN_ball {c z : ℂ} {r : ℝ} (hc : c ∈ ball z r) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun N : ℕ => planarBrownianMotion c {b | ¬ GoodStopN (ball z r) N ε ⇑b}) atTop (𝓝 0) :=
  tendsto_measure_not_goodStopN isOpen_ball (ae_regularExit_ball_planarBrownian hc) hε

end MatedCRT.StopAtExitCmp
