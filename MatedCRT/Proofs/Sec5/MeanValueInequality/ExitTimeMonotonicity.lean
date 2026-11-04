import MatedCRT.Proofs.Sec5.LLowerBound.GreenMonotonicity
import MatedCRT.Proofs.Infra.Setting

/-!
# Monotonicity of normalized exit time

The normalized exit time grows with a finite domain, by the maximum
principle and the first-step Green-function equations.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- A normalized exit time killed on a finite vertex set is bounded by the
one killed on a larger finite set. -/
theorem normExitTime_mono_of_firstStep {m : ℤ → ℤ → ℕ} {A B : Set ℤ}
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B)
    (hfirstA : ∀ b, ∀ a ∈ A,
      mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    (hfirstB : ∀ b, ∀ a ∈ B,
      mLaplacian m (fun x => greenFn m B x b) a = -(if a = b then 1 else 0))
    (a : ℤ) : normExitTime m A a ≤ normExitTime m B a := by
  let f : ℤ → ℝ := fun x => normExitTime m A x + (-1) * normExitTime m B x
  have hf0 : ∀ x ∉ A, f x ≤ 0 := by
    intro x hx
    simp only [f, normExitTime_eq_zero_of_not_mem m hx, zero_add, neg_one_mul]
    exact neg_nonpos.2 (normExitTime_nonneg _ _ _)
  have hfsub : ∀ x ∈ A, 0 ≤ mLaplacian m f x := by
    intro x hx
    dsimp [f]
    rw [mLaplacian_add_of_locallyFinite hlf, mLaplacian_const_mul,
      normExitTime_laplacian_of_firstStep hlf hA hfirstA x hx,
      normExitTime_laplacian_of_firstStep hlf hB hfirstB x (hAB hx)]
    ring_nf
    exact le_refl 0
  have h := le_zero_of_subharmonic_of_nonpos_off hcons hlf hA hf0 hfsub a
  dsimp [f] at h
  linarith

/-- A bound on the ambient normalized exit time gives the same bound on a
smaller finite domain. The logarithmic potential is controlled on a fixed
larger ball. -/
theorem normExitTime_le_of_ambient_bound {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    {μ : Measure ℂ} {η : ℝ → ℂ} {ε ρ ρ' α C : ℝ} {a : ℤ}
    (hε : 0 < ε) (hC : 0 < C) (hεα : ε ^ α < ρ' - ρ)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hA : A.Finite) (hB : (ballInterior ε η ρ).Finite)
    (hAB : A ⊆ ballInterior ε η ρ)
    (hfirstA : ∀ b, ∀ x ∈ A,
      mLaplacian m (fun y => greenFn m A y b) x = -(if x = b then 1 else 0))
    (hfirstB : ∀ b, ∀ x ∈ ballInterior ε η ρ,
      mLaplacian m (fun y => greenFn m (ballInterior ε η ρ) y b) x = -(if x = b then 1 else 0))
    (hM : largestExitTimeRV μ (ball 0 ρ') < ⊤)
    (hq : ENNReal.ofReal (normExitTime m (ballInterior ε η ρ) a) ≤
      ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV μ (thickening (ε ^ α) (ball 0 ρ))) :
    normExitTime m A a ≤ C * ε⁻¹ * (largestExitTimeRV μ (ball 0 ρ')).toReal := by
  have hsub : thickening (ε ^ α) (ball (0 : ℂ) ρ) ⊆ ball 0 ρ' := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.1 hz
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle z y 0]
  have hCε : 0 ≤ C * ε⁻¹ := mul_nonneg hC.le (inv_nonneg.2 hε.le)
  have hreal : 0 ≤ C * ε⁻¹ * (largestExitTimeRV μ (ball 0 ρ')).toReal :=
    mul_nonneg hCε ENNReal.toReal_nonneg
  have hq' : ENNReal.ofReal (normExitTime m (ballInterior ε η ρ) a) ≤
      ENNReal.ofReal (C * ε⁻¹ * (largestExitTimeRV μ (ball 0 ρ')).toReal) := by
    calc
      _ ≤ ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV μ (thickening (ε ^ α) (ball 0 ρ)) := hq
      _ ≤ ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV μ (ball 0 ρ') :=
        mul_le_mul_right (largestExitTimeRV_mono μ hsub) _
      _ = _ := by rw [ENNReal.ofReal_mul hCε, ENNReal.ofReal_toReal hM.ne]
  exact (normExitTime_mono_of_firstStep hlf hcons hA hB hAB hfirstA hfirstB a).trans
    ((ENNReal.ofReal_le_ofReal_iff hreal).1 hq')

end MatedCRT
