import MatedCRT.FirstPass.Derived.TimeChangeExcessiveInvariant

/-!
# Truncated densities of an invariant measure of the time change

Let `A` be a PCAF of planar Brownian motion with a good clock, `P_u = timeChangeKernel A u` the kernel of the time
change and `μ_A` the Revuz measure.  For a `σ`-finite measure `ν` invariant for the time change, put
`λ = ν + μ_A` and `f = dν/dλ`.  For `c ∈ [0, ∞]` and `b ∈ [0, ∞)` the measure `min (c f, b) λ` is excessive
(`(min (c f, b) λ) P_u` lies below both `c ν` and `b λ`, hence below `min (c f, b) λ`) and finite on a set of
positive Revuz measure, hence invariant (`bind_timeChangeKernel_eq_of_excessive`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess _root_.HarmonicBalls

/-- A measure lying below two measures with densities lies below the measure with the pointwise minimum density. -/
theorem le_withDensity_min {α : Type*} [MeasurableSpace α] {L ρ : Measure α} {g₁ g₂ : α → ℝ≥0∞}
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (h₁ : ρ ≤ L.withDensity g₁) (h₂ : ρ ≤ L.withDensity g₂) :
    ρ ≤ L.withDensity (fun x => min (g₁ x) (g₂ x)) := by
  refine Measure.le_iff.2 fun S hS => ?_
  have hT : MeasurableSet {x | g₁ x ≤ g₂ x} := measurableSet_le hg₁ hg₂
  have hST := hS.inter hT
  have hSd := hS.diff hT
  rw [← measure_inter_add_sdiff S hT, ← measure_inter_add_sdiff (μ := L.withDensity _) S hT]
  gcongr ?_ + ?_
  · calc ρ (S ∩ {x | g₁ x ≤ g₂ x}) ≤ L.withDensity g₁ (S ∩ {x | g₁ x ≤ g₂ x}) := Measure.le_iff'.1 h₁ _
      _ = L.withDensity (fun x => min (g₁ x) (g₂ x)) (S ∩ {x | g₁ x ≤ g₂ x}) := by
        rw [withDensity_apply _ hST, withDensity_apply _ hST]
        exact setLIntegral_congr_fun hST fun x hx => (min_eq_left hx.2).symm
  · calc ρ (S \ {x | g₁ x ≤ g₂ x}) ≤ L.withDensity g₂ (S \ {x | g₁ x ≤ g₂ x}) := Measure.le_iff'.1 h₂ _
      _ = L.withDensity (fun x => min (g₁ x) (g₂ x)) (S \ {x | g₁ x ≤ g₂ x}) := by
        rw [withDensity_apply _ hSd, withDensity_apply _ hSd]
        exact setLIntegral_congr_fun hSd fun x hx => (min_eq_right (le_of_lt (not_le.1 hx.2))).symm

/-- A measure below an invariant measure of the time change is mapped below it. -/
theorem bind_timeChangeKernel_le_of_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {u : ℝ≥0} {κ ρ : Measure ℂ}
    (hκρ : κ ≤ ρ) (hρ : timeChangeKernel A u ∘ₘ ρ = ρ) : timeChangeKernel A u ∘ₘ κ ≤ ρ := by
  refine Measure.le_iff.2 fun S hS => ?_
  calc (timeChangeKernel A u ∘ₘ κ) S = ∫⁻ x, timeChangeKernel A u x S ∂κ :=
        Measure.bind_apply hS (Kernel.aemeasurable _)
    _ ≤ ∫⁻ x, timeChangeKernel A u x S ∂ρ := lintegral_mono' hκρ le_rfl
    _ = (timeChangeKernel A u ∘ₘ ρ) S := (Measure.bind_apply hS (Kernel.aemeasurable _)).symm
    _ = ρ S := by rw [hρ]

/-- Multiples of an invariant measure of the time change are invariant. -/
theorem bind_timeChangeKernel_smul_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ν : Measure ℂ}
    (hν : ∀ u, timeChangeKernel A u ∘ₘ ν = ν) (c : ℝ≥0∞) (u : ℝ≥0) :
    timeChangeKernel A u ∘ₘ (c • ν) = c • ν := by
  ext S hS
  rw [Measure.bind_apply hS (Kernel.aemeasurable _), lintegral_smul_measure, Measure.smul_apply, smul_eq_mul,
    ← Measure.bind_apply hS (Kernel.aemeasurable (timeChangeKernel A u)), hν u, smul_eq_mul]

/-- Sums of invariant measures of the time change are invariant. -/
theorem bind_timeChangeKernel_add_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ν ν' : Measure ℂ}
    (hν : ∀ u, timeChangeKernel A u ∘ₘ ν = ν) (hν' : ∀ u, timeChangeKernel A u ∘ₘ ν' = ν') (u : ℝ≥0) :
    timeChangeKernel A u ∘ₘ (ν + ν') = ν + ν' := by
  ext S hS
  rw [Measure.bind_apply hS (Kernel.aemeasurable _), lintegral_add_measure,
    ← Measure.bind_apply hS (Kernel.aemeasurable (timeChangeKernel A u)),
    ← Measure.bind_apply hS (Kernel.aemeasurable (timeChangeKernel A u)), hν u, hν' u, Measure.add_apply]

/-- **Truncated multiples of the density of an invariant measure are invariant**: for `ν` `σ`-finite and invariant
for the time change, `λ = ν + μ_A`, `f = dν/dλ`, `c ∈ [0, ∞]` and `b ∈ [0, ∞)`, the measure `min (c f, b) λ` is
invariant for the time change. -/
theorem bind_timeChangeKernel_withDensity_min_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {ν : Measure ℂ} [SigmaFinite ν]
    (hν : ∀ u, timeChangeKernel A u ∘ₘ ν = ν) (c : ℝ≥0∞) (b : ℝ≥0) (u : ℝ≥0) :
    timeChangeKernel A u ∘ₘ (ν + revuz planarLaw A).withDensity
        (fun x => min (c * ν.rnDeriv (ν + revuz planarLaw A) x) b) =
      (ν + revuz planarLaw A).withDensity (fun x => min (c * ν.rnDeriv (ν + revuz planarLaw A) x) b) := by
  have : SigmaFinite (revuz planarLaw A) := sigmaFinite_revuz hA hG
  set L := ν + revuz planarLaw A with hL
  have hLsf : SigmaFinite L := by rw [hL]; infer_instance
  set f := ν.rnDeriv L with hf
  have hfm : Measurable f := Measure.measurable_rnDeriv _ _
  have hLinv : ∀ v, timeChangeKernel A v ∘ₘ L = L :=
    bind_timeChangeKernel_add_eq hν (bind_timeChangeKernel_revuz_eq hA hG)
  have hcν : L.withDensity (fun x => c * f x) = c • ν := by
    rw [show (fun x => c * f x) = c • f from rfl, withDensity_smul _ hfm,
      Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl))]
  have hκν : L.withDensity (fun x => min (c * f x) b) ≤ c • ν := by
    rw [← hcν]; exact withDensity_mono (ae_of_all _ fun x => min_le_left _ _)
  have hκL : L.withDensity (fun x => min (c * f x) b) ≤ (b : ℝ≥0∞) • L := by
    rw [← withDensity_const]; exact withDensity_mono (ae_of_all _ fun x => min_le_right _ _)
  have hSF : SigmaFinite (L.withDensity (fun x => min (c * f x) b)) :=
    SigmaFinite.withDensity_of_ne_top' fun x => (lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top).ne
  have hexc : ∀ v, timeChangeKernel A v ∘ₘ L.withDensity (fun x => min (c * f x) b) ≤
      L.withDensity (fun x => min (c * f x) b) := fun v => by
    have h1 : timeChangeKernel A v ∘ₘ L.withDensity (fun x => min (c * f x) b) ≤
        L.withDensity (fun x => c * f x) := by
      rw [hcν]; exact bind_timeChangeKernel_le_of_le hκν (bind_timeChangeKernel_smul_eq hν c v)
    have h2 : timeChangeKernel A v ∘ₘ L.withDensity (fun x => min (c * f x) b) ≤
        L.withDensity (fun _ => (b : ℝ≥0∞)) := by
      rw [withDensity_const]; exact bind_timeChangeKernel_le_of_le hκL (bind_timeChangeKernel_smul_eq hLinv _ v)
    exact le_withDensity_min (measurable_const.mul hfm) measurable_const h1 h2
  obtain ⟨E, hE, hμE, hLE⟩ := exists_measurableSet_revuz_ne_zero_lt_top hA hG L
  have hκE : L.withDensity (fun x => min (c * f x) b) E ≠ ∞ := by
    refine (lt_of_le_of_lt (Measure.le_iff'.1 hκL E) ?_).ne
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hLE
  exact bind_timeChangeKernel_eq_of_excessive hA hG hexc hE hμE hκE u

end MatedCRT
