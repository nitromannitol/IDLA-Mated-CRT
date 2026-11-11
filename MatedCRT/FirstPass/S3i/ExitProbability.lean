import MatedCRT.FirstPass.S3i.LensDefs
import MatedCRT.Proofs.WalkPotential.Markov
import MatedCRT.Proofs.IDLA.StrongMarkov
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Proofs.IDLA.Measurable
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellIntegral
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExitValue

/-!
# Finite-domain exit probability: the discrete harmonic measure

For a finite set `A` of vertices and a set `B` of vertices, `exitHitProb m A B a` is the probability that simple random
walk from `a` leaves `A` at a vertex of `B` (Armitage-Gardiner: the discrete harmonic measure of `B` seen from `a` in
`A`). The lemmas below prove the parts of plan Lemma 1 that hold for every `A` and `B`:
the values lie in `[0, 1]`, the value is an indicator off `A`, and the function is discrete harmonic on `A`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT
namespace FirstPass36

/-- The number of edges of `a` is finite as soon as `deg(a) ≠ 0` (the degree is a finite sum otherwise `0`). -/
theorem finite_nbrs_of_mdeg_ne_zero {m : ℤ → ℤ → ℕ} {a : ℤ} (h : mdeg m a ≠ 0) :
    {b | m a b ≠ 0}.Finite := by
  by_contra hinf
  exact h (finsum_of_infinite_support hinf)

theorem mdeg_eq_sum_of_finite {m : ℤ → ℤ → ℕ} {a : ℤ} (hfin : {b | m a b ≠ 0}.Finite) :
    mdeg m a = ∑ b ∈ hfin.toFinset, m a b := by
  unfold mdeg
  apply finsum_eq_sum_of_support_subset
  intro b hb
  exact hfin.mem_toFinset.2 hb

theorem edgeMeasure_univ_of_finite {m : ℤ → ℤ → ℕ} {a : ℤ} (hfin : {b | m a b ≠ 0}.Finite) :
    edgeMeasure m a univ = (mdeg m a : ℝ≥0∞) := by
  rw [mdeg_eq_sum_of_finite hfin, Nat.cast_sum]
  unfold edgeMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  have hz : ∀ b ∉ hfin.toFinset, ((m a b : ℝ≥0∞) • Measure.dirac b) univ = 0 := by
    intro b hb
    have : m a b = 0 := by
      by_contra h
      exact hb (hfin.mem_toFinset.2 h)
    simp [this]
  rw [tsum_eq_sum hz]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Measure.smul_apply]

/-- The one-step integral against simple random walk, on a vertex of finite degree. -/
theorem lintegral_srwStep_of_finite {m : ℤ → ℤ → ℕ} {a : ℤ} (hfin : {b | m a b ≠ 0}.Finite)
    (hdeg : mdeg m a ≠ 0) (f : ℤ → ℝ≥0∞) :
    ∫⁻ b, f b ∂srwStep m a = ((mdeg m a : ℝ≥0∞))⁻¹ * ∑ b ∈ hfin.toFinset, (m a b : ℝ≥0∞) * f b := by
  have hu := edgeMeasure_univ_of_finite hfin
  have hcond : edgeMeasure m a univ ≠ 0 ∧ edgeMeasure m a univ ≠ ⊤ := by
    rw [hu]
    exact ⟨by exact_mod_cast hdeg, ENNReal.natCast_ne_top _⟩
  unfold srwStep
  split_ifs
  rw [ProbabilityTheory.cond, Measure.restrict_univ, lintegral_smul_measure, hu]
  congr 1
  unfold edgeMeasure
  rw [lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  refine tsum_eq_sum fun b hb => ?_
  have : m a b = 0 := by
    by_contra h
    exact hb (hfin.mem_toFinset.2 h)
  simp [this]

/-- The exit-hit probability is a probability: `0 ≤ ω_A(a, B) ≤ 1`. -/
theorem exitHitProb_nonneg_le_one (m : ℤ → ℤ → ℕ) (A B : Set ℤ) (a : ℤ) :
    0 ≤ exitHitProb m A B a ∧ exitHitProb m A B a ≤ 1 := by
  unfold exitHitProb
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h := prob_le_one (μ := srwLaw m a) (s := {x | vExitTime A x < ⊤ ∧ vExitPosition A x ∈ B})
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top h

open Classical in
/-- Off `A` the walk exits at time `0`, so the exit-hit probability is the indicator of `B`. -/
theorem exitHitProb_of_not_mem (m : ℤ → ℤ → ℕ) {A B : Set ℤ} {a : ℤ} (ha : a ∉ A) :
    exitHitProb m A B a = if a ∈ B then 1 else 0 := by
  unfold exitHitProb
  by_cases hB : a ∈ B
  · have hae : {x | vExitTime A x < ⊤ ∧ vExitPosition A x ∈ B} =ᵐ[srwLaw m a] univ := by
      filter_upwards [srwLaw_ae_start m a] with x hx
      have hτ : vExitTime A x = 0 := vExitTime_eq_zero (by rw [hx]; exact ha)
      have hpos : vExitPosition A x = a := by
        unfold vExitPosition
        rw [hτ]
        simp [hx]
      simp [hτ, hpos, hB]
    rw [measure_congr hae]
    simp [hB]
  · have hae : {x | vExitTime A x < ⊤ ∧ vExitPosition A x ∈ B} =ᵐ[srwLaw m a] (∅ : Set (ℕ → ℤ)) := by
      filter_upwards [srwLaw_ae_start m a] with x hx
      have hτ : vExitTime A x = 0 := vExitTime_eq_zero (by rw [hx]; exact ha)
      have hpos : vExitPosition A x = a := by
        unfold vExitPosition
        rw [hτ]
        simp [hx]
      simp [hτ, hpos, hB]
    rw [measure_congr hae]
    simp [hB]

/-- **Discrete harmonicity of the exit-hit probability.** For `a ∈ A` with `FiniteExitData m A`, the exit-hit probability
`ω_A(·, B)` satisfies `Δ ω_A(·, B) (a) = 0` (first-step analysis at time one). -/
theorem exitHitProb_mLaplacian_eq_zero (m : ℤ → ℤ → ℕ) {A B : Set ℤ} (hA : FiniteExitData m A) {a : ℤ}
    (ha : a ∈ A) : mLaplacian m (exitHitProb m A B) a = 0 := by
  have hdeg : 0 < mdeg m a := hA.2.1 a ha
  have hfin : {b | m a b ≠ 0}.Finite := finite_nbrs_of_mdeg_ne_zero hdeg.ne'
  set E : Set (ℕ → ℤ) := {x | vExitTime A x < ⊤ ∧ vExitPosition A x ∈ B} with hEdef
  have hEm : MeasurableSet E := by
    have h1 : MeasurableSet {x : ℕ → ℤ | vExitTime A x < ⊤} := by
      have : {x : ℕ → ℤ | vExitTime A x < ⊤} = vExitTime A ⁻¹' {⊤}ᶜ := by
        ext x; simp [lt_top_iff_ne_top]
      rw [this]
      exact (measurable_vExitTime A) (measurableSet_singleton ⊤).compl
    have h2 : MeasurableSet {x : ℕ → ℤ | vExitPosition A x ∈ B} :=
      measurable_vExitPosition A (Set.to_countable B).measurableSet
    exact h1.inter h2
  -- the exit event is invariant under prepending the site `a ∈ A`
  have hkey : ∀ x : ℕ → ℤ, (vExitTime A (pathCons a x) < ⊤ ∧ vExitPosition A (pathCons a x) ∈ B) ↔
      (vExitTime A x < ⊤ ∧ vExitPosition A x ∈ B) := by
    intro x
    rw [MatedCRT.vExitTime_pathCons ha x]
    by_cases hx : vExitTime A x = ⊤
    · simp [hx]
    · rw [MatedCRT.vExitPosition_pathCons ha hx]
      have : vExitTime A x + 1 < ⊤ ↔ vExitTime A x < ⊤ := by
        simp [lt_top_iff_ne_top, hx]
      simp only [this]
  have hpre : pathCons a ⁻¹' E = E := by
    ext x
    exact hkey x
  -- first-step decomposition of the exit probability
  have hfirst : srwLaw m a E = ∫⁻ b, srwLaw m b E ∂srwStep m a := by
    rw [srwLaw_apply_eq_lintegral m a hEm, hpre]
  have hp : srwLaw m a E = ((mdeg m a : ℝ≥0∞))⁻¹ * ∑ b ∈ hfin.toFinset, (m a b : ℝ≥0∞) * srwLaw m b E := by
    rw [hfirst, lintegral_srwStep_of_finite hfin hdeg.ne']
  -- real form of the first-step identity
  have hF : ∀ b, exitHitProb m A B b = (srwLaw m b E).toReal := fun b => rfl
  have hmr : (mdeg m a : ℝ) ≠ 0 := by exact_mod_cast hdeg.ne'
  have hsumm : (mdeg m a : ℝ) = ∑ b ∈ hfin.toFinset, (m a b : ℝ) := by
    rw [mdeg_eq_sum_of_finite hfin]; push_cast; rfl
  have h1 := congrArg ENNReal.toReal hp
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_sum (fun b _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _))] at h1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h1
  have h2 : exitHitProb m A B a = (mdeg m a : ℝ)⁻¹ * ∑ b ∈ hfin.toFinset, (m a b : ℝ) * exitHitProb m A B b := by
    simpa only [hF] using h1
  have hreal : ∑ b ∈ hfin.toFinset, (m a b : ℝ) * exitHitProb m A B b = (mdeg m a : ℝ) * exitHitProb m A B a := by
    rw [h2, ← mul_assoc, mul_inv_cancel₀ hmr, one_mul]
  -- the finite-support sum for the discrete Laplacian
  have hsub : (Function.support fun b => (m a b : ℝ) * (exitHitProb m A B b - exitHitProb m A B a)) ⊆
      ↑hfin.toFinset := by
    intro b hb
    rw [Function.mem_support] at hb
    have hne : (m a b : ℝ) ≠ 0 := left_ne_zero_of_mul hb
    exact Finset.mem_coe.2 (hfin.mem_toFinset.2 (by exact_mod_cast hne))
  have hsum0 : ∑ b ∈ hfin.toFinset, (m a b : ℝ) * (exitHitProb m A B b - exitHitProb m A B a) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hreal, ← hsumm, sub_self]
  unfold mLaplacian
  rw [finsum_eq_sum_of_support_subset _ hsub, hsum0, mul_zero]

end FirstPass36
end MatedCRT
