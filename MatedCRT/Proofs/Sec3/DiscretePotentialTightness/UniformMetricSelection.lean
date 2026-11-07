import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.MetricCompactSelection
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! # Uniform selection through a bounded metric embedding -/

namespace MatedCRT

open Set Filter Topology MeasureTheory
open scoped UniformConvergence

/-- Encode functions on a set in a bounded uniform-function space. -/
noncomputable def uniformSetEncode {α Y : Type*} [UniformSpace Y]
    (K : Set α) (b : ℝ → Y) (f : α → ℝ) : α →ᵤ Y := by
  classical
  exact UniformFun.ofFun (fun x => if x ∈ K then b (f x) else b 0)

/-- Uniform convergence on a set implies convergence of the encoded functions. -/
theorem uniformSetEncode_tendsto {α Y : Type*} [UniformSpace Y]
    (K : Set α) (b : ℝ → Y) (hb : UniformContinuous b)
    (F : ℕ → α → ℝ) (f : α → ℝ)
    (h : TendstoUniformlyOn F f atTop K) :
    Tendsto (fun n => uniformSetEncode K b (F n)) atTop (𝓝 (uniformSetEncode K b f)) := by
  classical
  apply UniformFun.tendsto_iff_tendstoUniformly.mpr
  intro U hU
  have hh := hb.comp_tendstoUniformlyOn h U hU
  filter_upwards [hh] with n hn x
  by_cases hx : x ∈ K
  · simpa [uniformSetEncode, hx, Function.comp_def] using hn x hx
  · simpa [uniformSetEncode, hx] using (refl_mem_uniformity hU : (b 0, b 0) ∈ U)

/-- Measurable distances between bounded encodings select uniform limits on
    countably many sets, including discontinuous boundary limits. -/
theorem exists_measurable_subsequence_uniform_of_encoded_distances
    {Ω α Y : Type*} [MeasurableSpace Ω] [MetricSpace Y] [BoundedSpace Y]
    (b : ℝ → Y) (hb : UniformContinuous b) (hbi : Function.Injective b)
    (K : ℕ → Set α) (F : Ω → ℕ → ℕ → α → ℝ)
    (hdm : ∀ j n m, Measurable fun ω => dist
      (uniformSetEncode (K j) b (F ω j n)) (uniformSetEncode (K j) b (F ω j m)))
    (P : Ω → ℕ → Prop)
    (hc : ∀ ω j, P ω j → ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : α → ℝ,
        TendstoUniformlyOn (fun n => F ω j (ψ (θ n))) w atTop (K j)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable fun ω => Φ ω k) ∧
      ∀ ω, StrictMono (Φ ω) ∧ ∀ j, P ω j → ∃ w : α → ℝ,
        TendstoUniformlyOn (fun n => F ω j (Φ ω n)) w atTop (K j) := by
  classical
  let G : Ω → ℕ → ℕ → (α →ᵤ Y) := fun ω j n => uniformSetEncode (K j) b (F ω j n)
  have hGc : ∀ ω j, P ω j → ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : α →ᵤ Y,
        Tendsto (fun n => G ω j (ψ (θ n))) atTop (𝓝 w) := by
    intro ω j hP ψ hψ
    obtain ⟨θ, hθ, w, hw⟩ := hc ω j hP ψ hψ
    exact ⟨θ, hθ, uniformSetEncode (K j) b w, uniformSetEncode_tendsto (K j) b hb _ w hw⟩
  obtain ⟨Φ, hΦm, hΦ⟩ := exists_measurable_subsequence_of_conditional_metric_compactness
    G hdm P hGc
  refine ⟨Φ, hΦm, ?_⟩
  intro ω
  refine ⟨(hΦ ω).1, ?_⟩
  intro j hP
  obtain ⟨g, hg⟩ := (hΦ ω).2 j hP
  obtain ⟨θ, hθ, w, hw⟩ := hc ω j hP (Φ ω) (hΦ ω).1
  have hgw : g = uniformSetEncode (K j) b w :=
    tendsto_nhds_unique (hg.comp hθ.tendsto_atTop) (uniformSetEncode_tendsto (K j) b hb _ w hw)
  refine ⟨w, ?_⟩
  apply tendstoUniformlyOn_of_subsequence
  intro ψ hψ
  obtain ⟨ζ, hζ, v, hv⟩ := hc ω j hP (Φ ω ∘ ψ) ((hΦ ω).1.comp hψ)
  have hgv : g = uniformSetEncode (K j) b v :=
    tendsto_nhds_unique (hg.comp (hψ.comp hζ).tendsto_atTop)
      (uniformSetEncode_tendsto (K j) b hb _ v hv)
  have heq : EqOn v w (K j) := by
    intro x hx
    apply hbi
    have h := congrArg (fun g : α →ᵤ Y => UniformFun.toFun g x) (hgv.symm.trans hgw)
    simpa [uniformSetEncode, hx] using h
  exact ⟨ζ, hζ, hv.congr_right heq⟩

/-- The arctangent embeds the real line in a bounded metric space. -/
noncomputable def boundedArctan (x : ℝ) : Icc (-2 : ℝ) 2 :=
  ⟨Real.arctan x, by
    constructor
    · have h := Real.neg_pi_div_two_lt_arctan x
      have hp := Real.pi_lt_four
      linarith
    · have h := Real.arctan_lt_pi_div_two x
      have hp := Real.pi_lt_four
      linarith⟩

theorem boundedArctan_injective : Function.Injective boundedArctan := by
  intro x y h
  have hv : Real.arctan x = Real.arctan y := congrArg (fun z : Icc (-2 : ℝ) 2 => z.val) h
  exact Real.arctan_injective hv

theorem boundedArctan_uniformContinuous : UniformContinuous boundedArctan := by
  have hlip : LipschitzWith 1 Real.arctan := by
    apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan
    intro x
    rw [Real.deriv_arctan]
    have hreal : ‖1 / (1 + x ^ 2)‖ ≤ (1 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (1 + x ^ 2))]
      exact div_le_one₀ (by positivity) |>.2 (by nlinarith [sq_nonneg x])
    exact_mod_cast hreal
  exact hlip.uniformContinuous.subtype_mk _

/-- Arctangent encoding gives measurable uniform selection from measurable
    encoded pairwise distances, without continuity of the limits. -/
theorem exists_measurable_subsequence_uniform_of_arctan_distances
    {Ω α : Type*} [MeasurableSpace Ω]
    (K : ℕ → Set α) (F : Ω → ℕ → ℕ → α → ℝ)
    (hdm : ∀ j n m, Measurable fun ω => dist
      (uniformSetEncode (K j) boundedArctan (F ω j n))
      (uniformSetEncode (K j) boundedArctan (F ω j m)))
    (P : Ω → ℕ → Prop)
    (hc : ∀ ω j, P ω j → ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : α → ℝ,
        TendstoUniformlyOn (fun n => F ω j (ψ (θ n))) w atTop (K j)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable fun ω => Φ ω k) ∧
      ∀ ω, StrictMono (Φ ω) ∧ ∀ j, P ω j → ∃ w : α → ℝ,
        TendstoUniformlyOn (fun n => F ω j (Φ ω n)) w atTop (K j) :=
  exists_measurable_subsequence_uniform_of_encoded_distances boundedArctan
    boundedArctan_uniformContinuous boundedArctan_injective K F hdm P hc

end MatedCRT
