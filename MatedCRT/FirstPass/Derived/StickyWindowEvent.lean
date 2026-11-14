import MatedCRT.FirstPass.Derived.StickyWindowKernel

/-!
# No sticking of the interpolated quenched walk laws: the event bound

The estimate behind the last claim of Proposition 6.1 of Berestycki-Gwynne: from the window event of
Proposition 6.14 (`NoStickingEvent.limLimSmall_noSticking`: with `q > 0` and `ψ(δ) = o(δ^p)` for every `p > 0`, the
simple random walk violates the window event at threshold `δ` and windows of `2 ⌊ε⁻¹ δ^q⌋` steps with
probability at most `ψ(δ)`, from every vertex whose cell meets `B(0, ρ)`, outside a `LimLimSmall` event), we get
that, outside a `LimLimSmall` event, the interpolated walk laws `P̃^ε(ω)(z)` give mass at most `ψ(δ')` to the paths
that nearly stand still on a window.  The bound is uniform over all starting points `z`.

The speed `m_ε` of the walk enters only through `hmε`: `ε m_ε ≥ c₀ > 0` for small `ε` (the lower bound on the
embedded walk's speed), so that the windows of `2 ⌊ε⁻¹ δ^q⌋` steps fit in a time window of length `a` once
`δ^q ≤ c₀ a / 2`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal
open MatedCRT.FirstPass.Derived MatedCRT.StickyWindowKernel

namespace MatedCRT
namespace StickyWindowEvent

variable {Ω : Type} [MeasurableSpace Ω]

/-- A function with `δ⁻¹ ψ(δ) → 0` as `δ → 0⁺` eventually satisfies `ψ(δ) < δ`. -/
theorem eventually_lt_self_of_tendsto {ψ : ℝ → ℝ}
    (h : Tendsto (fun δ : ℝ => δ ^ (-(1 : ℝ)) * ψ δ) (𝓝[>] 0) (𝓝 0)) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ψ δ < δ := by
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ (-(1 : ℝ)) * ψ δ < 1 :=
    h.eventually (gt_mem_nhds one_pos)
  filter_upwards [h1, self_mem_nhdsWithin] with δ hδ hδ0
  have hδ0' : 0 < δ := hδ0
  rw [Real.rpow_neg_one] at hδ
  calc ψ δ = δ * (δ⁻¹ * ψ δ) := by field_simp
    _ < δ * 1 := mul_lt_mul_of_pos_left hδ hδ0'
    _ = δ := mul_one δ

/-- **No sticking, event form.**  Let `ψ`, `q` be as in `NoStickingEvent.limLimSmall_noSticking` and assume that the
failure events `F δ ε` of its conclusion are `LimLimSmall`.  Assume `ε m_ε ≥ c₀ > 0` for small `ε`.  Then for every
`r > 0`, `θ > 0`, every set `K` of starting points and `a > 0`, there are `δ > 0` and `ε₀ > 0` such that for
`ε < ε₀` the probability that some `P̃^ε(ω)(z)`, `z ∈ K`, gives mass more than `r` to the sticky window set
`stickyWindowSet ρ δ a T` is at most `θ`. -/
theorem interpWalkLaw_stickyWindowSet_small {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) (η' : Ω → C(ℝ, ℂ)) (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ρ : ℝ} {q : ℝ}
    (hq : 0 < q) {ψ : ℝ → ℝ}
    (hψ : (∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ δ) ∧
      ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ δ) (𝓝[>] 0) (𝓝 0))
    (hLL : LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ),
          srwLaw (S.mult ε ω) x
            {X | ¬ ∀ j : ℕ, ((j + ⌊ε⁻¹ * δ ^ q⌋₊ : ℕ) : ℕ∞) ≤
                vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X →
              ∃ i₁ i₂ : ℕ, j ≤ i₁ ∧ i₁ ≤ i₂ ∧ i₂ < j + 2 * ⌊ε⁻¹ * δ ^ q⌋₊ ∧
                δ ≤ ‖vertexPoint ε (S.η ω) (X i₂) - vertexPoint ε (S.η ω) (X i₁)‖} ≤
            ENNReal.ofReal (ψ δ)}))
    (hmε : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → c₀ ≤ ε * S.mε ε)
    {a : ℝ≥0} (ha : 0 < a) (T : ℝ≥0) (hmeas : ∀ δ : ℝ, MeasurableSet (stickyWindowSet ρ δ a T))
    (K : Set ℂ) (r : ℝ≥0) (hr : 0 < r) (θ : ℝ) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      S.P {ω | (r : ℝ≥0∞) < ⨆ z : K, ((interpWalkLaw S η' ε ω z : ProbabilityMeasure (ContinuousPath ℂ)) :
        Measure (ContinuousPath ℂ)) (stickyWindowSet ρ δ a T)} ≤ ENNReal.ofReal θ := by
  obtain ⟨c₀, hc₀, ε₁, hε₁, hc⟩ := hmε
  obtain ⟨δ₀, hδ₀, hF⟩ := hLL θ hθ
  have hqlim : Tendsto (fun δ : ℝ => δ ^ q) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const (0 : ℝ) q (Or.inr hq.le)).tendsto
    rw [Real.zero_rpow hq.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hca : 0 < c₀ * (a : ℝ) / 2 := by
    have : (0 : ℝ) < a := by exact_mod_cast ha
    positivity
  have e1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ψ δ < δ := eventually_lt_self_of_tendsto (hψ.2 1 one_pos)
  have e2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ q < c₀ * a / 2 := hqlim.eventually (gt_mem_nhds hca)
  have e3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < (r : ℝ) :=
    (eventually_lt_nhds (show (0 : ℝ) < r from hr)).filter_mono nhdsWithin_le_nhds
  have e4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < δ₀ := (eventually_lt_nhds hδ₀).filter_mono nhdsWithin_le_nhds
  have e5 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨d, hdψ, hdq, hdr, hdδ, hd0⟩ := (e1.and (e2.and (e3.and (e4.and e5)))).exists
  have hd0' : 0 < d := hd0
  obtain ⟨ε₂, hε₂, hFd⟩ := hF d hd0' hdδ
  refine ⟨d / 2, by positivity, min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hεlt => ?_⟩
  have hε1 : ε < ε₁ := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hε2 : ε < ε₂ := lt_of_lt_of_le hεlt (min_le_right _ _)
  refine le_trans (measure_mono_ae ?_) (hFd ε hε hε2)
  have hcε := hc ε hε hε1
  have hm : 0 < S.mε ε := by
    by_contra hneg
    have : ε * S.mε ε ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le (not_lt.1 hneg)
    linarith
  have hb : 2 * ((⌊ε⁻¹ * d ^ q⌋₊ : ℕ) : ℝ) ≤ S.mε ε * a := by
    have h1 : ((⌊ε⁻¹ * d ^ q⌋₊ : ℕ) : ℝ) ≤ ε⁻¹ * d ^ q :=
      Nat.floor_le (mul_nonneg (inv_nonneg.2 hε.le) (Real.rpow_nonneg hd0'.le q))
    have ha' : (0 : ℝ) ≤ a := a.2
    have hdq' : d ^ q ≤ c₀ * a / 2 := hdq.le
    calc 2 * ((⌊ε⁻¹ * d ^ q⌋₊ : ℕ) : ℝ) ≤ 2 * (ε⁻¹ * (c₀ * a / 2)) := by
          have : ε⁻¹ * d ^ q ≤ ε⁻¹ * (c₀ * a / 2) := mul_le_mul_of_nonneg_left hdq' (inv_nonneg.2 hε.le)
          linarith
      _ = ε⁻¹ * (c₀ * a) := by ring
      _ ≤ ε⁻¹ * ((ε * S.mε ε) * a) := by gcongr
      _ = S.mε ε * a := by field_simp
  have hψr : ENNReal.ofReal (ψ d) < r := by
    have : ψ d < (r : ℝ) := lt_trans hdψ hdr
    calc ENNReal.ofReal (ψ d) < ENNReal.ofReal (r : ℝ) := (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hr)).2 this
      _ = r := ENNReal.ofReal_coe_nnreal
  filter_upwards [hS.ae_interpWeight_good hae hε, hae] with ω hgood hηω hω
  by_contra hnot
  try simp only [Set.mem_ofPred_eq, not_not] at hnot
  have h2 : 2 * (d / 2) = d := by ring
  have hbound : ∀ z : K, ((interpWalkLaw S η' ε ω z : ProbabilityMeasure (ContinuousPath ℂ)) :
      Measure (ContinuousPath ℂ)) (stickyWindowSet ρ (d / 2) a T) ≤ ENNReal.ofReal (ψ d) := by
    intro z
    refine interpWalkLaw_apply_le_of_start S η' hε hgood.1 hgood.2 z (hmeas (d / 2))
      (stickyWindowSet_start ρ (d / 2) a T) ?_
    intro k hk
    rw [hηω] at hk
    have h := walkPathLaw_stickyWindowSet_le S η' hε ω (ρ := ρ) (δ := d / 2) (a := a) (T := T) hm hb
      (hmeas (d / 2)) k
    rw [hηω, h2] at h
    exact h.trans (hnot k hk)
  exact (not_lt.2 ((iSup_le hbound).trans hψr.le)) hω

end StickyWindowEvent
end MatedCRT
