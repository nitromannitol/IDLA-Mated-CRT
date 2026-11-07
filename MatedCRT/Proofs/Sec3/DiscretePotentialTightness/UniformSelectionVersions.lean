import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.UniformMetricSelection
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.MetricSelectionVersions

/-! # Uniform selection using measurable distance versions -/

namespace MatedCRT

open Set Filter Topology MeasureTheory
open scoped UniformConvergence

/-- Measurable versions of encoded distances suffice on each compactness event. -/
theorem exists_measurable_subsequence_uniform_of_distance_versions
    {Ω α Y : Type*} [MeasurableSpace Ω] [MetricSpace Y] [BoundedSpace Y]
    (b : ℝ → Y) (hb : UniformContinuous b) (hbi : Function.Injective b)
    (K : ℕ → Set α) (F : Ω → ℕ → ℕ → α → ℝ)
    (d : ℕ → ℕ → ℕ → Ω → ℝ) (hdm : ∀ j n m, Measurable (d j n m))
    (P : Ω → ℕ → Prop)
    (hd : ∀ ω j, P ω j → ∀ n m, d j n m ω = dist
      (uniformSetEncode (K j) b (F ω j n)) (uniformSetEncode (K j) b (F ω j m)))
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
  obtain ⟨Φ, hΦm, hΦ⟩ := exists_measurable_subsequence_of_conditional_distance_versions
    G d hdm P hd hGc
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

end MatedCRT
