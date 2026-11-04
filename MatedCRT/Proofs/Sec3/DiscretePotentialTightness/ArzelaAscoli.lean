import Mathlib

/-!
# Arzelà-Ascoli for asymptotically equicontinuous sequences

The rescaled functions `ū^ε` of Lemma 3.1 are constant on cells, hence not continuous. They are *asymptotically
equicontinuous* (`IsAsymptoticallyEquicontinuousOn`): for every `k > 0` there is `δ > 0` with
`|F_n(x) - F_n(y)| ≤ k` for `|x - y| ≤ δ` and all large `n` (eq:equicontinuity, line 1023). This file proves the
part of the Arzelà-Ascoli theorem used at lines 1021 and 1086.

* `uniformCauchySeqOn_of_isAsymptoticallyEquicontinuousOn`: convergence on a set `T` that is dense in a compact `K`
  gives uniform Cauchy convergence on `K`.
* `tendstoUniformlyOn_limUnder`: the uniform limit is the pointwise limit.
* `continuousAt_of_isAsymptoticallyEquicontinuousOn`: the pointwise limit is continuous.
* `tendsto_of_forall_approx`: a sequence which, for every `k > 0`, stays within `k` of a convergent sequence
  converges. This is used with the measurable proxies.
-/

namespace MatedCRT.Tightness

open Filter Topology Set Metric

/-- **Asymptotic equicontinuity** of `F_n` on `K`: for every `k > 0` there is `δ > 0` such that for all large `n`,
`|F_n(x) - F_n(y)| ≤ k` whenever `x, y ∈ K` and `|x - y| ≤ δ`. -/
def IsAsymptoticallyEquicontinuousOn (F : ℕ → ℂ → ℝ) (K : Set ℂ) : Prop :=
  ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ → |F n x - F n y| ≤ k

theorem IsAsymptoticallyEquicontinuousOn.mono {F : ℕ → ℂ → ℝ} {K K' : Set ℂ}
    (h : IsAsymptoticallyEquicontinuousOn F K') (hK : K ⊆ K') : IsAsymptoticallyEquicontinuousOn F K := by
  intro k hk
  obtain ⟨δ, hδ, h'⟩ := h k hk
  exact ⟨δ, hδ, h'.mono fun n hn x hx y hy hxy => hn x (hK hx) y (hK hy) hxy⟩

theorem IsAsymptoticallyEquicontinuousOn.comp_strictMono {F : ℕ → ℂ → ℝ} {K : Set ℂ}
    (h : IsAsymptoticallyEquicontinuousOn F K) {Φ : ℕ → ℕ} (hΦ : StrictMono Φ) :
    IsAsymptoticallyEquicontinuousOn (fun k => F (Φ k)) K := by
  intro k hk
  obtain ⟨δ, hδ, h'⟩ := h k hk
  exact ⟨δ, hδ, hΦ.tendsto_atTop.eventually h'⟩

/-- **Uniform Cauchy convergence** on a compact `K` from asymptotic equicontinuity on `K' ⊇ K` and convergence on a
set `T` whose points in `K'` approximate every point of `K`. -/
theorem uniformCauchySeqOn_of_isAsymptoticallyEquicontinuousOn {F : ℕ → ℂ → ℝ} {K K' T : Set ℂ}
    (hK : IsCompact K) (hKK' : K ⊆ K') (hEQ : IsAsymptoticallyEquicontinuousOn F K')
    (hT : ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → ∃ t ∈ T, t ∈ K' ∧ ‖x - t‖ < δ)
    (hconv : ∀ t ∈ T, ∃ l, Tendsto (fun n => F n t) atTop (𝓝 l)) : UniformCauchySeqOn F atTop K := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro r hr
  obtain ⟨δ, hδ, hev⟩ := hEQ (r / 4) (by positivity)
  obtain ⟨c, hcK, hcfin, hcov⟩ := hK.finite_cover_balls (e := δ / 2) (by positivity)
  have hchoice : ∀ x ∈ c, ∃ t ∈ T, t ∈ K' ∧ ‖x - t‖ < δ / 2 :=
    fun x hx => hT x (hcK hx) (δ / 2) (by positivity)
  choose! τ hτT hτK' hτx using hchoice
  choose! L hL using fun x (hx : x ∈ c) => hconv (τ x) (hτT x hx)
  have hev2 : ∀ᶠ n in atTop, ∀ x ∈ c, dist (F n (τ x)) (L x) < r / 8 := by
    refine (Filter.eventually_all_finite hcfin).2 fun x hx => ?_
    exact Metric.tendsto_nhds.1 (hL x hx) (r / 8) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and hev2)
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  obtain ⟨y, hyc, hxy⟩ : ∃ y ∈ c, dist x y < δ / 2 := by simpa using hcov hx
  have hxt : ‖x - τ y‖ ≤ δ := by
    have h1 : ‖x - y‖ < δ / 2 := by rw [← dist_eq_norm]; exact hxy
    have h2 := hτx y hyc
    calc ‖x - τ y‖ = ‖(x - y) + (y - τ y)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - y‖ + ‖y - τ y‖ := norm_add_le _ _
      _ ≤ δ := by linarith
  obtain ⟨hm1, hm2⟩ := hN m hm
  obtain ⟨hn1, hn2⟩ := hN n hn
  have e1 := abs_le.1 (hm1 x (hKK' hx) (τ y) (hτK' y hyc) hxt)
  have e2 := abs_le.1 (hn1 x (hKK' hx) (τ y) (hτK' y hyc) hxt)
  have e3 := hm2 y hyc
  have e4 := hn2 y hyc
  rw [Real.dist_eq] at e3 e4 ⊢
  have e3' := abs_lt.1 e3
  have e4' := abs_lt.1 e4
  rw [abs_lt]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3'.1, e3'.2, e4'.1, e4'.2]

/-- A uniformly Cauchy sequence converges uniformly to its pointwise limit. -/
theorem tendstoUniformlyOn_limUnder {F : ℕ → ℂ → ℝ} {K : Set ℂ} (h : UniformCauchySeqOn F atTop K) :
    TendstoUniformlyOn F (fun x => limUnder atTop fun n => F n x) atTop K :=
  h.tendstoUniformlyOn_of_tendsto fun _ hx => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (h.cauchySeq hx))

/-- The pointwise limit of an asymptotically equicontinuous sequence is continuous. -/
theorem continuousAt_of_isAsymptoticallyEquicontinuousOn {F : ℕ → ℂ → ℝ} {f : ℂ → ℝ} {K : Set ℂ} {x : ℂ}
    (hK : K ∈ 𝓝 x) (hEQ : IsAsymptoticallyEquicontinuousOn F K)
    (hlim : ∀ y ∈ K, Tendsto (fun n => F n y) atTop (𝓝 (f y))) : ContinuousAt f x := by
  rw [Metric.continuousAt_iff]
  intro r hr
  obtain ⟨δ, hδ, hev⟩ := hEQ (r / 2) (by positivity)
  obtain ⟨δ', hδ', hball⟩ := Metric.mem_nhds_iff.1 hK
  refine ⟨min δ δ', lt_min hδ hδ', fun y hy => ?_⟩
  have hyK : y ∈ K := hball (lt_of_lt_of_le hy (min_le_right _ _))
  have hxK : x ∈ K := mem_of_mem_nhds hK
  have hyx : ‖y - x‖ ≤ δ := by
    rw [← dist_eq_norm]
    exact (lt_of_lt_of_le hy (min_le_left _ _)).le
  have hconv : Tendsto (fun n => |F n y - F n x|) atTop (𝓝 |f y - f x|) :=
    (continuous_abs.tendsto _).comp ((hlim y hyK).sub (hlim x hxK))
  have hle : |f y - f x| ≤ r / 2 := le_of_tendsto hconv (hev.mono fun n hn => hn y hyK x hxK hyx)
  rw [Real.dist_eq]
  linarith

/-- A sequence within every `k > 0` of some convergent sequence (eventually) converges. -/
theorem tendsto_of_forall_approx {a : ℕ → ℝ}
    (h : ∀ k : ℝ, 0 < k → ∃ z : ℕ → ℝ, (∃ l, Tendsto z atTop (𝓝 l)) ∧ ∀ᶠ n in atTop, |a n - z n| ≤ k) :
    ∃ l, Tendsto a atTop (𝓝 l) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro r hr
  obtain ⟨z, ⟨l, hl⟩, hz⟩ := h (r / 4) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hz.and (Metric.tendsto_nhds.1 hl (r / 4) (by positivity)))
  refine ⟨N, fun m hm n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN m hm
  obtain ⟨h3, h4⟩ := hN n hn
  rw [Real.dist_eq] at h2 h4 ⊢
  have e1 := abs_le.1 h1
  have e3 := abs_le.1 h3
  have e2 := abs_lt.1 h2
  have e4 := abs_lt.1 h4
  rw [abs_lt]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]

end MatedCRT.Tightness
