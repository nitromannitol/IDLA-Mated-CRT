import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellIntegral
import MatedCRT.Proofs.IDLA.StrongMarkov
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# The expected exit value of simple random walk is discrete harmonic

For a set `A ⊆ ℤ` from which the walk exits almost surely, and bounded boundary data `g`, the expected exit value
`a ↦ E^a[g(X_{τ_A})]` satisfies the mean value property at every vertex of `A` of positive degree (first-step
analysis; Lawler-Limic, Section 6.2). Together with the Green representation it expresses the solution of the
discrete Dirichlet problem of Lemma 3.5 (Lawler-Limic, Corollary 6.2.4).
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

open WalkPotential

variable {m : ℤ → ℤ → ℕ}

/-- Prepending a site of `A` to a path that exits `A` does not change the exit position. -/
theorem vExitPosition_pathCons {A : Set ℤ} {a : ℤ} (ha : a ∈ A) {y : ℕ → ℤ}
    (hy : vExitTime A y ≠ ⊤) : vExitPosition A (pathCons a y) = vExitPosition A y := by
  unfold vExitPosition
  rw [vExitTime_pathCons ha y]
  induction hk : vExitTime A y using ENat.recTopCoe with
  | top => exact absurd hk hy
  | coe k =>
    rw [← Nat.cast_succ, ENat.toNat_natCast, ENat.toNat_natCast]
    rfl

/-- **First-step analysis** for the exit value. -/
theorem lintegral_exitValue_firstStep {A : Set ℤ}
    (hA : ∀ c ∈ A, ∀ᵐ x ∂srwLaw m c, vExitTime A x ≠ ⊤) {a : ℤ} (ha : a ∈ A) (g : ℤ → ℝ≥0∞) :
    ∫⁻ x, g (vExitPosition A x) ∂srwLaw m a =
      ∫⁻ c, ∫⁻ x, g (vExitPosition A x) ∂srwLaw m c ∂srwStep m a := by
  have hF : Measurable fun x : ℕ → ℤ => g (vExitPosition A x) :=
    (measurable_of_countable g).comp (measurable_vExitPosition A)
  rw [lintegral_srwLaw_eq_pathCons m a hF]
  refine lintegral_congr fun c => lintegral_congr_ae ?_
  by_cases hc : c ∈ A
  · filter_upwards [hA c hc] with y hy
    rw [vExitPosition_pathCons ha hy]
  · filter_upwards [srwLaw_ae_start m c] with y hy
    have hfin : vExitTime A y ≠ ⊤ := by
      rw [vExitTime_eq_zero_of_not_mem (by rw [hy]; exact hc)]
      simp
    rw [vExitPosition_pathCons ha hfin]

/-- **The expected exit value is discrete harmonic** on `A`. -/
theorem mLaplacian_integral_exitValue (hlf : IsLocallyFiniteMult m) {A : Set ℤ}
    (hA : ∀ c ∈ A, ∀ᵐ x ∂srwLaw m c, vExitTime A x ≠ ⊤) {a : ℤ} (ha : a ∈ A) (hdeg : mdeg m a ≠ 0)
    {g : ℤ → ℝ} {C : ℝ} (hg : ∀ b, |g b| ≤ C) :
    mLaplacian m (fun c => ∫ x, g (vExitPosition A x) ∂srwLaw m c) a = 0 := by
  set G : ℤ → ℝ := fun c => ∫ x, g (vExitPosition A x) ∂srwLaw m c with hGdef
  set L : ℤ → ℝ≥0∞ := fun c => ∫⁻ x, ENNReal.ofReal (g (vExitPosition A x) + C) ∂srwLaw m c with hLdef
  have hmeas : Measurable fun x : ℕ → ℤ => g (vExitPosition A x) :=
    (measurable_of_countable g).comp (measurable_vExitPosition A)
  have hrepr : ∀ c, G c = (L c).toReal - C := by
    intro c
    have hint : Integrable (fun x => g (vExitPosition A x)) (srwLaw m c) :=
      Integrable.of_bound hmeas.aestronglyMeasurable C
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hg _)
    have hnn : 0 ≤ᵐ[srwLaw m c] fun x => g (vExitPosition A x) + C :=
      Filter.Eventually.of_forall fun x => by
        have := hg (vExitPosition A x)
        rw [abs_le] at this
        simp only [Pi.zero_apply]
        linarith
    have hconst : ∫ _x, C ∂srwLaw m c = C := by simp
    have key : ENNReal.ofReal (∫ x, (g (vExitPosition A x) + C) ∂srwLaw m c) = L c :=
      ofReal_integral_eq_lintegral_ofReal (hint.add (integrable_const C)) hnn
    show ∫ x, g (vExitPosition A x) ∂srwLaw m c = (L c).toReal - C
    rw [← key, ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn), integral_add hint (integrable_const C),
      hconst]
    ring
  have hLfin : ∀ c, L c ≠ ⊤ := by
    intro c
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (2 * C)) ENNReal.ofReal_ne_top ?_
    calc L c ≤ ∫⁻ _x, ENNReal.ofReal (2 * C) ∂srwLaw m c := lintegral_mono fun x => by
          refine ENNReal.ofReal_le_ofReal ?_
          have := hg (vExitPosition A x)
          rw [abs_le] at this
          linarith
      _ = ENNReal.ofReal (2 * C) := by simp
  have hstep := lintegral_exitValue_firstStep hA ha
    (fun b => ENNReal.ofReal (g b + C))
  obtain ⟨-, hsum⟩ := toReal_lintegral_srwStep hlf hdeg hLfin
  have hLa : (L a).toReal = ((mdeg m a : ℝ))⁻¹ * ∑ c ∈ nbrs hlf a, (m a c : ℝ) * (L c).toReal := by
    rw [← hsum]
    exact congrArg ENNReal.toReal hstep
  have hd : (mdeg m a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hdeg
  have hmean : G a = 0 + ((mdeg m a : ℝ))⁻¹ * ∑ c ∈ nbrs hlf a, (m a c : ℝ) * G c := by
    have hsplit : ∑ c ∈ nbrs hlf a, (m a c : ℝ) * (L c).toReal =
        ∑ c ∈ nbrs hlf a, (m a c : ℝ) * G c + C * (mdeg m a : ℝ) := by
      rw [mdeg_cast_eq hlf, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hrepr c]
      ring
    have hC : ((mdeg m a : ℝ))⁻¹ * (C * (mdeg m a : ℝ)) = C := by field_simp
    rw [hrepr a, hLa, hsplit, mul_add, hC]
    ring
  have h := (mLaplacian_eq_neg_iff hlf hdeg G 0).2 hmean
  rw [neg_zero] at h
  exact h

end MatedCRT
