import MatedCRT.FirstPass.Derived.EmbeddedExitTimeInterp

/-!
# Convergence of lower medians

The normalisation of Berestycki-Gwynne (proof of Lemma 7.18 and the end of Section 7): the annealed median of
the exit time of the rescaled walk is `1`, hence the median of the exit time of the subsequential limit is
`1`.  Two elementary facts are needed.

* `tendsto_medianOf_of_tendsto_cdf`: if distribution functions `G_n` converge to `G` on a dense set of times
  and `G` crosses `1/2` strictly to the right of its lower median (the exit-time law of the limit has full
  support near its median), then the lower medians converge: `medianOf G_n → medianOf G`.
* `tendsto_div_one_of_abs_sub_le_one`: if `|a - b| ≤ 1` and `a → ∞`, then `b / a → 1`; with the comparison
  `|m_ε - m_ε^{interp}| ≤ 1` of `EmbeddedExitTimeInterp` this shows that the median of the interpolated exit
  time and the step median `m_ε` have ratio tending to `1` (`MatedCRTEnv.tendsto_mεInterp_div_mε`).
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace MatedCRT

private theorem medianOf_nonneg_aux (cdf : ℝ → ℝ≥0∞) : 0 ≤ medianOf cdf :=
  Real.sInf_nonneg fun _ hx => hx.1

/-- **Stability of the lower median.** Let `G_n` be monotone distribution functions converging to `G` at the
points of a dense set `D`, and suppose `G` is strictly above `1/2` to the right of its lower median. Then
`medianOf G_n → medianOf G`. -/
theorem tendsto_medianOf_of_tendsto_cdf {ι : Type*} {l : Filter ι} {G : ℝ → ℝ≥0∞} {Gn : ι → ℝ → ℝ≥0∞}
    (hmono : ∀ i, Monotone (Gn i)) {D : Set ℝ} (hD : Dense D)
    (hconv : ∀ s ∈ D, Tendsto (fun i => Gn i s) l (𝓝 (G s)))
    (hstrict : ∀ s, medianOf G < s → (1 / 2 : ℝ≥0∞) < G s) :
    Tendsto (fun i => medianOf (Gn i)) l (𝓝 (medianOf G)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hm0 : 0 ≤ medianOf G := medianOf_nonneg_aux G
  obtain ⟨s2, hs2D, hs2⟩ := hD.exists_mem_open (isOpen_Ioo (a := medianOf G) (b := medianOf G + ε))
    ⟨medianOf G + ε / 2, by constructor <;> linarith⟩
  have hup : ∀ᶠ i in l, (1 / 2 : ℝ≥0∞) < Gn i s2 :=
    (hconv s2 hs2D).eventually (lt_mem_nhds (hstrict s2 hs2.1))
  have hs20 : 0 ≤ s2 := by linarith [hs2.1]
  have hle : ∀ᶠ i in l, medianOf (Gn i) ≤ s2 := by
    filter_upwards [hup] with i hi
    exact medianOf_le_of_half_le hs20 hi.le
  rcases le_or_gt ε (medianOf G) with hεm | hεm
  · obtain ⟨s1, hs1D, hs1⟩ := hD.exists_mem_open
      (isOpen_Ioo (a := medianOf G - ε) (b := medianOf G))
      ⟨medianOf G - ε / 2, by constructor <;> linarith⟩
    have hs10 : 0 ≤ s1 := by linarith [hs1.1]
    have hG1 : G s1 < 1 / 2 := by
      by_contra h
      have := medianOf_le_of_half_le hs10 (not_lt.1 h)
      linarith [hs1.2]
    have hlow : ∀ᶠ i in l, Gn i s1 < 1 / 2 :=
      (hconv s1 hs1D).eventually (gt_mem_nhds hG1)
    filter_upwards [hup, hle, hlow] with i hi hi2 hi3
    have h1 : s1 ≤ medianOf (Gn i) :=
      le_medianOf_of_lt_half (hmono i) hi3 ⟨s2, hs20, hi.le⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hs1.1, hs2.2]
  · filter_upwards [hle] with i hi2
    have h0 : 0 ≤ medianOf (Gn i) := medianOf_nonneg_aux _
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hs2.2]

/-- If `|a - b| ≤ 1` (eventually) and `a → ∞`, then `b / a → 1`. -/
theorem tendsto_div_one_of_abs_sub_le_one {ι : Type*} {l : Filter ι} {a b : ι → ℝ}
    (hab : ∀ᶠ i in l, |a i - b i| ≤ 1) (ha : Tendsto a l atTop) :
    Tendsto (fun i => b i / a i) l (𝓝 1) := by
  have h1 : Tendsto (fun i => (a i)⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp ha
  have h2 : Tendsto (fun i => (b i - a i) / a i) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [hab, ha.eventually_gt_atTop 0] with i hi hpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_eq_mul_inv]
    have h3 : |b i - a i| ≤ 1 := by rwa [abs_sub_comm]
    calc |b i - a i| * (a i)⁻¹ ≤ 1 * (a i)⁻¹ :=
          mul_le_mul_of_nonneg_right h3 (inv_nonneg.2 hpos.le)
      _ = (a i)⁻¹ := one_mul _
  have h4 := h2.const_add 1
  rw [add_zero] at h4
  refine h4.congr' ?_
  filter_upwards [ha.eventually_gt_atTop 0] with i hpos
  rw [one_add_div hpos.ne']
  congr 1
  ring

namespace MatedCRTEnv

/-- **The interpolated median and the step median have ratio tending to `1`** along every filter on which
`m_ε → ∞` (with `m_ε ≥ c ε⁻¹`, as for `ε → 0+`). -/
theorem tendsto_mεInterp_div_mε {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {l : Filter ℝ}
    (hinf : Tendsto (fun ε => S.mε ε) l atTop) :
    Tendsto (fun ε => S.mεInterp ε / S.mε ε) l (𝓝 1) := by
  refine tendsto_div_one_of_abs_sub_le_one ?_ hinf
  filter_upwards [hinf.eventually_gt_atTop 0] with ε hε
  exact S.abs_mε_sub_mεInterp_le_one ε hε

end MatedCRTEnv

end MatedCRT
