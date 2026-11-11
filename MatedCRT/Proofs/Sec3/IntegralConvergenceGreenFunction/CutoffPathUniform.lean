import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockPathUniform
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.CutoffInverse
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkMeasurability
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PathEnvelope

/-!
# Lemma 3.4: cutoff approximate paths converge in the local uniform distance

Deterministic core of `LBMPathFunctionalMeasurableStep` (paper argument). Let `G` be a
time change clock and `F n` strictly increasing approximate clocks converging to `G` uniformly on compact time intervals.
The cutoff approximate inverses `cutInv (F n) (c n)`, for any cutoff sequence `c` tending to infinity, time-change a
continuous path `b` into paths that converge to `b ∘ clockInverse G` in the local uniform distance `localUniformDist`, which
metrizes local uniform convergence (Theorem 2.11 of the paper). The cutoff is eventually irrelevant on each compact interval.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The tail of the local uniform series from index `m` on is at most `2 ^ (-m)`. -/
theorem tsum_luTerm_add_le (f g : ℝ≥0 → ℂ) (m : ℕ) :
    ∑' i, luTerm f g (i + m) ≤ (2 : ℝ)⁻¹ ^ m := by
  have hgeo : Summable fun i : ℕ => (2 : ℝ)⁻¹ ^ (m + 1) * (2 : ℝ)⁻¹ ^ i :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h2 : (1 - (2 : ℝ)⁻¹)⁻¹ = 2 := by norm_num
  calc ∑' i, luTerm f g (i + m) ≤ ∑' i : ℕ, (2 : ℝ)⁻¹ ^ (m + 1) * (2 : ℝ)⁻¹ ^ i :=
        Summable.tsum_le_tsum (fun i => (luTerm_le f g _).trans_eq (by ring))
          ((summable_nat_add_iff m).2 (summable_luTerm f g)) hgeo
    _ = (2 : ℝ)⁻¹ ^ m := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num), h2, pow_succ]
        ring

/-- Paths within `η` on `[0, K + 1]` are within `η + 2 ^ (-(K + 1))` in the local uniform distance. -/
theorem localUniformDist_le_add_of_forall_le (f g : ℝ≥0 → ℂ) (K : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ t : ℝ≥0, t ≤ ((K + 1 : ℕ) : ℝ≥0) → ‖f t - g t‖ ≤ η) :
    localUniformDist f g ≤ η + (2 : ℝ)⁻¹ ^ (K + 1) := by
  have hterm : ∀ i ∈ Finset.range (K + 1), luTerm f g i ≤ (2 : ℝ)⁻¹ ^ (i + 1) * η := by
    intro i hi
    have hi' : i + 1 ≤ K + 1 := by
      have := Finset.mem_range.1 hi
      omega
    have hsup : (⨆ t : Icc (0 : ℝ≥0) ((i + 1 : ℕ) : ℝ≥0), ENNReal.ofReal ‖f t - g t‖) ≤
        ENNReal.ofReal η :=
      iSup_le fun t => ENNReal.ofReal_le_ofReal (h t (t.2.2.trans (Nat.cast_le.2 hi')))
    unfold luTerm
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hmin := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((min_le_right (1 : ℝ≥0∞) _).trans hsup)
    rwa [ENNReal.toReal_ofReal hη] at hmin
  have hgeo : ∑ i ∈ Finset.range (K + 1), (2 : ℝ)⁻¹ ^ (i + 1) ≤ 1 := by
    have h2 := sum_geometric_two_le (K + 1)
    calc ∑ i ∈ Finset.range (K + 1), (2 : ℝ)⁻¹ ^ (i + 1)
        = (2 : ℝ)⁻¹ * ∑ i ∈ Finset.range (K + 1), (2 : ℝ)⁻¹ ^ i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ (2 : ℝ)⁻¹ * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa [one_div] using h2
      _ = 1 := by norm_num
  have hhead : ∑ i ∈ Finset.range (K + 1), luTerm f g i ≤ η :=
    calc ∑ i ∈ Finset.range (K + 1), luTerm f g i
        ≤ ∑ i ∈ Finset.range (K + 1), (2 : ℝ)⁻¹ ^ (i + 1) * η := Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range (K + 1), (2 : ℝ)⁻¹ ^ (i + 1)) * η := by rw [Finset.sum_mul]
      _ ≤ 1 * η := mul_le_mul_of_nonneg_right hgeo hη
      _ = η := one_mul η
  rw [localUniformDist_eq_tsum_luTerm, ← (summable_luTerm f g).sum_add_tsum_nat_add (K + 1)]
  exact add_le_add hhead (tsum_luTerm_add_le f g (K + 1))

/-- Uniform convergence on every compact time interval `[0, K]` implies convergence in the local uniform distance. -/
theorem tendsto_localUniformDist_of_forall_le {ι : Type*} {l : Filter ι} (f : ι → ℝ≥0 → ℂ) (g : ℝ≥0 → ℂ)
    (h : ∀ (K : ℕ) (η : ℝ), 0 < η → ∀ᶠ i in l, ∀ t : ℝ≥0, t ≤ (K : ℝ≥0) → ‖f i t - g t‖ ≤ η) :
    Tendsto (fun i => localUniformDist (f i) g) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hpow : (2 : ℝ)⁻¹ ^ (K + 1) ≤ (2 : ℝ)⁻¹ ^ K :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ K)
  filter_upwards [h (K + 1) (ε / 2) (half_pos hε)] with i hi
  have hle := localUniformDist_le_add_of_forall_le (f i) g K (half_pos hε).le hi
  have hnn : 0 ≤ localUniformDist (f i) g := localUniformDist_nonneg (f i) g
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-- **Uniform convergence of cutoff inverses for an arbitrary cutoff sequence.** If the cutoffs `c n` eventually exceed every
bounded time, then `cutInv (F n) (c n)` converges uniformly on compact levels to `clockInverse G`. -/
theorem cutInv_tendsto_uniform_of_cutoff {F : ℕ → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ} (hG : IsTimeChangeClock G)
    (hF : ∀ n, StrictMono (F n)) (c : ℕ → ℝ≥0) (hc : ∀ T : ℝ≥0, ∀ᶠ n in atTop, T ≤ c n)
    (hconv : ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t ≤ T, |F n t - G t| < η)
    (U : ℝ≥0) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ u ≤ U,
      |((cutInv (F n) (c n) u : ℝ≥0) : ℝ) - ((clockInverse G u : ℝ≥0) : ℝ)| < η := by
  -- a level `s₀` where the limit clock exceeds `U + 1`
  obtain ⟨s₀, hs₀⟩ := (hG.tendsto_atTop.eventually_gt_atTop ((U : ℝ) + 1)).exists
  -- eventually the clocks exceed `U` at their own cutoff
  have hbig : ∀ᶠ n : ℕ in atTop, (U : ℝ) < F n (c n) := by
    filter_upwards [hconv s₀ 1 one_pos, hc s₀] with n hn hsn
    have h1 := abs_lt.1 (hn s₀ le_rfl)
    have h2 : F n s₀ ≤ F n (c n) := (hF n).monotone hsn
    linarith [h1.1]
  have hunb : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ≥0, u ≤ U → ∃ s : ℝ≥0, (u : ℝ) < F n s := by
    filter_upwards [hbig] with n hn u hu
    exact ⟨c n, lt_of_le_of_lt (by exact_mod_cast hu) hn⟩
  filter_upwards [clockInverse_tendsto_uniform hG hF U hunb hconv η hη, hbig] with n hn hb u hu
  have hu' : (u : ℝ) < F n (c n) := lt_of_le_of_lt (by exact_mod_cast hu) hb
  rw [cutInv_eq_clockInverse (hF n) hu']
  exact hn u hu

/-- **Cutoff approximate paths converge in the local uniform distance.** If the approximate clocks `F n` are strictly
increasing and converge to a time change clock `G` uniformly on compact time intervals, and the cutoffs `c n` tend to
infinity, then for every continuous path `b` and every time scale `m`, the paths `t ↦ b (cutInv (F n) (c n) (m t))`
converge to `t ↦ b (clockInverse G (m t))` in the local uniform distance. -/
theorem cutoffPath_tendsto_localUniformDist {G : ℝ≥0 → ℝ} (hG : IsTimeChangeClock G)
    {F : ℕ → ℝ≥0 → ℝ} (hF : ∀ n, StrictMono (F n)) (c : ℕ → ℝ≥0) (hc : ∀ T : ℝ≥0, ∀ᶠ n in atTop, T ≤ c n)
    (hconv : ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t ≤ T, |F n t - G t| < η)
    (b : ContinuousPath ℂ) (m : ℝ≥0) :
    Tendsto (fun n : ℕ => localUniformDist (fun t => b (cutInv (F n) (c n) (m * t)))
      (fun t => b (clockInverse G (m * t)))) atTop (𝓝 0) := by
  refine tendsto_localUniformDist_of_forall_le _ _ fun K η hη => ?_
  set U : ℝ≥0 := m * (K : ℝ≥0) with hU
  set S : ℝ≥0 := clockInverse G U with hS
  have hunif : UniformContinuousOn (fun s : ℝ≥0 => b s) (Icc 0 (S + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous b.continuous.continuousOn
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.1 hunif η hη
  have hmin : 0 < min δ 1 := lt_min hδpos one_pos
  filter_upwards [cutInv_tendsto_uniform_of_cutoff hG hF c hc hconv U (min δ 1) hmin] with n hn t ht
  have hu : m * t ≤ U := mul_le_mul_of_nonneg_left ht (by positivity)
  have hyS : clockInverse G (m * t) ≤ S := (IsTimeChangeClock.strictMono_clockInverse hG).monotone hu
  have hi : |((cutInv (F n) (c n) (m * t) : ℝ≥0) : ℝ) - ((clockInverse G (m * t) : ℝ≥0) : ℝ)| <
      min δ 1 :=
    hn (m * t) hu
  have hdist : dist (cutInv (F n) (c n) (m * t)) (clockInverse G (m * t)) < δ := by
    rw [NNReal.dist_eq]
    exact lt_of_lt_of_le hi (min_le_left _ _)
  have hyR : ((clockInverse G (m * t) : ℝ≥0) : ℝ) ≤ (S : ℝ) := NNReal.coe_le_coe.2 hyS
  have hxle : ((cutInv (F n) (c n) (m * t) : ℝ≥0) : ℝ) ≤ ((S + 1 : ℝ≥0) : ℝ) := by
    have h1 := (abs_lt.1 hi).2
    push_cast
    linarith [min_le_right δ 1]
  have hmemx : cutInv (F n) (c n) (m * t) ∈ Icc (0 : ℝ≥0) (S + 1) :=
    ⟨by simp, NNReal.coe_le_coe.1 hxle⟩
  have hmemy : clockInverse G (m * t) ∈ Icc (0 : ℝ≥0) (S + 1) :=
    ⟨by simp, le_trans hyS le_self_add⟩
  have hb := hδ _ hmemx _ hmemy hdist
  rw [← dist_eq_norm]
  exact hb.le

end MatedCRT
