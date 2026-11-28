import LatticeProb.Prob.CorrelatedBMConeTimes
import LatticeProb.Prob.CorrelatedBMRationalDescent

-- Adapted from Lattice-Probability (LatticeProb/Prob/CorrelatedBMWhitening.lean and
-- LatticeProb/Prob/CorrelatedBMRecenter.lean).

/-!
# Gram–Schmidt coordinates of the correlated Brownian pair

For `0 < γ < 2` let `ρ = lrCov γ 0 1 = -cos (π γ² / 4) ∈ (-1, 1)` and `σ = √(1 - ρ²)`.  The map
`gramSchmidtAt γ q` sends a path `(L, R)` to the pair of increments after the time `q`
`u ↦ (R (q + u) - R q, ((L (q + u) - L q) - ρ (R (q + u) - R q)) / σ)`.
It has `R` as its first coordinate (which the sum and difference whitening of
`LatticeProb.CorrelatedBM.whitenAt` does not), and the image of the law of the `γ`-correlated pair is
the law of the uncorrelated pair, `γ = √2`: two independent two-sided standard Brownian motions.
This is the decomposition `R = v · Z`, `L = u · Z` of the pair as projections of a planar Brownian
motion `Z` (written answer `notes/mq-rigD2-shimura-answer.md`, opening paragraph; with the roles of the
two coordinates exchanged), used on the middle third of Shimura's Lemma 2 (M. Shimura, *Meandering
points of two-dimensional Brownian motion*, Kodai Math. J. 11 (1988), Lemma 2, (3.5), p. 172; answer §1).

## Main results

* `lrCov_mem_Ioo`: `ρ ∈ (-1, 1)`.
* `gramSchmidtAt`, `continuous_gramSchmidtAt`, `lrCoord_gramSchmidtAt`.
* `isCorrelatedBM2_map_gramSchmidtAt`: `IsCorrelatedBM2 γ μ → IsCorrelatedBM2 (√2) (μ.map (gramSchmidtAt γ q))`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal
open MatedCRTHarmonic.MatedCRT LatticeProb.CorrelatedBM

namespace MatedCRT.PeanosphereTriplePoints

/-- The coefficient of the `L` increment in the coordinate `i` of the Gram–Schmidt pair. -/
noncomputable def gsCoefL (γ : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then 0 else 1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2)

/-- The coefficient of the `R` increment in the coordinate `i` of the Gram–Schmidt pair. -/
noncomputable def gsCoefR (γ : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then 1 else -lrCov γ 0 1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2)

/-- **Gram–Schmidt coordinates after time `q`**: the increments after `q` of `R` and of
`(L - ρ R) / σ`, with `ρ = lrCov γ 0 1` and `σ = √(1 - ρ²)`. -/
noncomputable def gramSchmidtAt (γ q : ℝ) : Path2 → Path2 := fun ω =>
  ⟨fun u => ((ω (q + u)).2 - (ω q).2,
    (((ω (q + u)).1 - (ω q).1) - lrCov γ 0 1 * ((ω (q + u)).2 - (ω q).2)) /
      Real.sqrt (1 - lrCov γ 0 1 ^ 2)), by fun_prop⟩

/-- The value of the Gram–Schmidt path at time `u`. -/
theorem gramSchmidtAt_apply (γ q u : ℝ) (ω : Path2) :
    gramSchmidtAt γ q ω u = ((ω (q + u)).2 - (ω q).2,
      (((ω (q + u)).1 - (ω q).1) - lrCov γ 0 1 * ((ω (q + u)).2 - (ω q).2)) /
        Real.sqrt (1 - lrCov γ 0 1 ^ 2)) :=
  rfl

/-- The Gram–Schmidt map is continuous for the compact-open topology on `Path2`. -/
theorem continuous_gramSchmidtAt (γ q : ℝ) : Continuous (gramSchmidtAt γ q) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  show Continuous fun p : Path2 × ℝ =>
    (((p.1 (q + p.2)).2 - (p.1 q).2,
      (((p.1 (q + p.2)).1 - (p.1 q).1) - lrCov γ 0 1 * ((p.1 (q + p.2)).2 - (p.1 q).2)) /
        Real.sqrt (1 - lrCov γ 0 1 ^ 2)) : ℝ × ℝ)
  fun_prop

/-- The coordinates of the Gram–Schmidt path are combinations of the increments after `q`. -/
theorem lrCoord_gramSchmidtAt (γ q u : ℝ) (i : Fin 2) (ω : Path2) :
    lrCoord i u (gramSchmidtAt γ q ω) =
      coneComb (gsCoefL γ i) (gsCoefR γ i) (q + u) q ω := by
  fin_cases i
  · simp [lrCoord, gramSchmidtAt, gsCoefL, gsCoefR, coneComb, coneIncr]
  · simp [lrCoord, gramSchmidtAt, gsCoefL, gsCoefR, coneComb, coneIncr]
    ring

/-- For `0 < γ < 2` the correlation `-cos (π γ² / 4)` lies strictly between `-1` and `1`. -/
theorem lrCov_mem_Ioo {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    -1 < lrCov γ 0 1 ∧ lrCov γ 0 1 < 1 := by
  have hθ0 : 0 < Real.pi * γ ^ 2 / 4 := by
    have := mul_pos Real.pi_pos (pow_pos hγ0 2)
    linarith
  have hθπ : Real.pi * γ ^ 2 / 4 < Real.pi := by
    have hγ4 : γ ^ 2 < 4 := by nlinarith [mul_pos hγ0 (sub_pos.2 hγ2)]
    nlinarith [mul_pos Real.pi_pos (sub_pos.2 hγ4)]
  have hcos1 : Real.cos (Real.pi * γ ^ 2 / 4) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
    rwa [Real.cos_zero] at h
  have hcosm1 : -1 < Real.cos (Real.pi * γ ^ 2 / 4) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
    rwa [Real.cos_pi] at h
  have hρ : lrCov γ 0 1 = -Real.cos (Real.pi * γ ^ 2 / 4) := rfl
  rw [hρ]
  constructor <;> linarith

/-- **The Gram–Schmidt pair of a correlated Brownian pair is an uncorrelated one.**  For
`γ ∈ (0, 2)` and a deterministic time `q`, the image of the law of the `γ`-correlated pair under
`gramSchmidtAt γ q` is the `√2`-correlated (independent coordinates) Brownian law. -/
theorem isCorrelatedBM2_map_gramSchmidtAt {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (q : ℝ)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    IsCorrelatedBM2 (Real.sqrt 2) (μ.map (gramSchmidtAt γ q)) := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hΦ : Measurable (gramSchmidtAt γ q) := (continuous_gramSchmidtAt γ q).measurable
  have hm : ∀ i t, Measurable (lrCoord i t) := by
    intro i t
    unfold lrCoord
    split_ifs
    · exact measurable_fst.comp (ContinuousMap.measurable_eval t)
    · exact measurable_snd.comp (ContinuousMap.measurable_eval t)
  obtain ⟨hρlo, hρhi⟩ := lrCov_mem_Ioo hγ0 hγ2
  have hpos : 0 < 1 - lrCov γ 0 1 ^ 2 := by nlinarith
  have hσsq : Real.sqrt (1 - lrCov γ 0 1 ^ 2) * Real.sqrt (1 - lrCov γ 0 1 ^ 2) =
      1 - lrCov γ 0 1 ^ 2 := Real.mul_self_sqrt hpos.le
  have hσ : 0 < Real.sqrt (1 - lrCov γ 0 1 ^ 2) := Real.sqrt_pos.2 hpos
  have hcos : Real.cos (Real.pi * Real.sqrt 2 ^ 2 / 4) = 0 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), show Real.pi * 2 / 4 = Real.pi / 2 by ring,
      Real.cos_pi_div_two]
  have hL0 : gsCoefL γ 0 = 0 := by simp [gsCoefL]
  have hL1 : gsCoefL γ 1 = 1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2) := by simp [gsCoefL]
  have hR0 : gsCoefR γ 0 = 1 := by simp [gsCoefR]
  have hR1 : gsCoefR γ 1 = -lrCov γ 0 1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2) := by simp [gsCoefR]
  have h00 : lrCov (Real.sqrt 2) 0 0 = 1 := rfl
  have h11 : lrCov (Real.sqrt 2) 1 1 = 1 := rfl
  have h01 : lrCov (Real.sqrt 2) 0 1 = -Real.cos (Real.pi * Real.sqrt 2 ^ 2 / 4) := rfl
  have h10 : lrCov (Real.sqrt 2) 1 0 = -Real.cos (Real.pi * Real.sqrt 2 ^ 2 / 4) := rfl
  have hscalar : ∀ i j : Fin 2, gsCoefL γ i * gsCoefL γ j + gsCoefR γ i * gsCoefR γ j +
      (gsCoefL γ i * gsCoefR γ j + gsCoefR γ i * gsCoefL γ j) * lrCov γ 0 1 =
      lrCov (Real.sqrt 2) i j := by
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · rw [h00, hL0, hR0]
      ring
    · rw [h01, hcos, hL0, hL1, hR0, hR1]
      ring
    · rw [h10, hcos, hL0, hL1, hR0, hR1]
      ring
    · rw [h11, hL1, hR1]
      rw [show 1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2) * (1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2)) +
        -lrCov γ 0 1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2) *
          (-lrCov γ 0 1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2)) +
        (1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2) *
            (-lrCov γ 0 1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2)) +
          -lrCov γ 0 1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2) *
            (1 / Real.sqrt (1 - lrCov γ 0 1 ^ 2))) * lrCov γ 0 1 =
        (1 - lrCov γ 0 1 ^ 2) / (Real.sqrt (1 - lrCov γ 0 1 ^ 2) *
          Real.sqrt (1 - lrCov γ 0 1 ^ 2)) by ring, hσsq]
      exact div_self hpos.ne'
  have hG : IsGaussianProcess
      (fun (p : Fin 2 × ℝ) ω => lrCoord p.1 p.2 (gramSchmidtAt γ q ω)) μ := by
    apply LatticeProb.GaussIndep.isGaussianProcess_of_mem_span hμ.isGaussianProcess
    intro p
    have hfun : (fun ω => lrCoord p.1 p.2 (gramSchmidtAt γ q ω)) =
        coneComb (gsCoefL γ p.1) (gsCoefR γ p.1) (q + p.2) q :=
      funext (lrCoord_gramSchmidtAt γ q p.2 p.1)
    rw [hfun]
    exact coneComb_mem_span _ _ _ _
  have hgm : ∀ I : Finset (Fin 2 × ℝ),
      Measurable fun ω : Path2 => I.restrict (fun p : Fin 2 × ℝ => lrCoord p.1 p.2 ω) :=
    fun I => measurable_pi_iff.2 fun j => hm j.1.1 j.1.2
  have hL2 : ∀ (k : Fin 2) (t : ℝ), MemLp (lrCoord k t) 2 μ := fun k t =>
    (hμ.isGaussianProcess.hasGaussianLaw_eval (k, t)).memLp_two
  refine
    { isProbabilityMeasure := (Measure.isProbabilityMeasure_map_iff hΦ.aemeasurable).2 inferInstance
      isGaussianProcess := ⟨fun I => ⟨(hgm I).aemeasurable, ?_⟩⟩
      integral_eq_zero := fun i t => ?_
      covariance_eq := fun i j s t => ?_ }
  · rw [Measure.map_map (hgm I) hΦ]
    exact (hG.hasGaussianLaw I).isGaussian_map
  · rw [integral_map hΦ.aemeasurable (hm i t).aestronglyMeasurable]
    simp_rw [lrCoord_gramSchmidtAt]
    have hint : ∀ (k : Fin 2) (t : ℝ), Integrable (lrCoord k t) μ := fun k t =>
      (hL2 k t).integrable (by norm_num)
    have i0 : Integrable (fun ω => gsCoefL γ i * (lrCoord 0 (q + t) ω - lrCoord 0 q ω)) μ :=
      ((hint 0 _).sub (hint 0 q)).const_mul _
    have i1 : Integrable (fun ω => gsCoefR γ i * (lrCoord 1 (q + t) ω - lrCoord 1 q ω)) μ :=
      ((hint 1 _).sub (hint 1 q)).const_mul _
    simp only [coneComb, coneIncr]
    rw [integral_add i0 i1, integral_const_mul, integral_const_mul,
      integral_sub (hint 0 _) (hint 0 q), integral_sub (hint 1 _) (hint 1 q),
      hμ.integral_eq_zero 0 (q + t), hμ.integral_eq_zero 0 q,
      hμ.integral_eq_zero 1 (q + t), hμ.integral_eq_zero 1 q]
    ring
  · rw [covariance_map_fun (hm i s).aestronglyMeasurable (hm j t).aestronglyMeasurable
      hΦ.aemeasurable]
    simp_rw [lrCoord_gramSchmidtAt]
    rw [cov_coneComb hμ, hscalar i j, twoSidedMin_eq_abs]
    congr 1
    rw [show q + s - q = s by ring, show q + t - q = t by ring,
      show q + s - (q + t) = s - t by ring]

end MatedCRT.PeanosphereTriplePoints
