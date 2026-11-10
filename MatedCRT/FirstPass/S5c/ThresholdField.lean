import MatedCRT.FirstPass.S5c.B1bThreshold
import MatedCRT.FirstPass.S5c.ThresholdBorel

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), measure layer, steps (2e) and (2f)): the threshold field

Frozen input: only through the hypothesis `hF1 : FrozenUniversalMeasurabilityOfAnalytic` (Frozen/S1c.lean:40).
Let `g : Ω → Measure ℂ` be measurable for a sub-σ-algebra `m ≤ mΩ` (the field σ-algebra) with `μ ω = g ω` almost surely.

* (2f) `lintegralMoment φs ν` is the moment vector `(∫ φs k dν)_k`, written as a difference of two lintegrals so that it is
  defined for every measure. `ω ↦ lintegralMoment φs (g ω)` is `m`-measurable (`measurable_lintegralMoment`, the argument of
  `aemeasurable_integral_of_measurable_version`, TestIntegralAE.lean). On a measure finite on the closed ball it is the vector
  of test integrals (`lintegralMoment_eq_integral`).
* (2e) For real `c`, `c < leastSupersolution (μ ω) R 0 u p` iff `c < q` and the moment vector lies outside the analytic set
  `S q` of supersolution moments, for some rational `q` (`lt_leastSupersolution_iff_moments`, B1bThreshold.lean:47). The sets
  `S q` are universally measurable by `hF1`. Then `threshold_borel_ae` (M2) gives a Borel set `T` with `{c < v} = Y⁻¹ T` a.s.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology HarmonicBalls
open MatedCRT

/-- The moment vector `(∫ φs k dν)_k` of a measure `ν` on `ℂ`, as a difference of two lintegrals (defined for every measure). -/
noncomputable def lintegralMoment (φs : ℕ → ℂ → ℝ) (ν : Measure ℂ) : ℕ → ℝ :=
  fun k => (∫⁻ x, ENNReal.ofReal (φs k x) ∂ν).toReal - (∫⁻ x, ENNReal.ofReal (-φs k x) ∂ν).toReal

/-- **(2f)** The lintegral moment vector of an `m`-measurable family of measures is `m`-measurable. -/
theorem measurable_lintegralMoment {Ω : Type*} {m : MeasurableSpace Ω} {g : Ω → Measure ℂ}
    (hg : Measurable[m] g) (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, Continuous (φs k)) :
    Measurable[m] (fun ω => lintegralMoment φs (g ω)) := by
  refine measurable_pi_iff.2 fun k => ?_
  have h1 : Measurable[m] (fun ω => ∫⁻ x, ENNReal.ofReal (φs k x) ∂(g ω)) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp (hφs k).measurable)).comp hg
  have h2 : Measurable[m] (fun ω => ∫⁻ x, ENNReal.ofReal (-φs k x) ∂(g ω)) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp (hφs k).measurable.neg)).comp hg
  exact (ENNReal.measurable_toReal.comp h1).sub (ENNReal.measurable_toReal.comp h2)

/-- The lintegral decomposition of a test integral against a measure finite on the closed ball of radius `R`. -/
theorem lintegralMoment_eq_integral {ν : Measure ℂ} {R : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    (hsupp : tsupport φ ⊆ closedBall (0 : ℂ) R) (hloc : ν (closedBall (0 : ℂ) R) < ⊤) :
    ∫ x, φ x ∂ν = (∫⁻ x, ENNReal.ofReal (φ x) ∂ν).toReal - (∫⁻ x, ENNReal.ofReal (-φ x) ∂ν).toReal := by
  have hsub : Function.support φ ⊆ closedBall (0 : ℂ) R := (subset_tsupport φ).trans hsupp
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hφ.continuousOn
  have hbound : ∀ᵐ x ∂(ν.restrict (closedBall (0 : ℂ) R)), ‖φ x‖ ≤ C :=
    (ae_restrict_mem measurableSet_closedBall).mono fun x hx => hC x hx
  have hint : Integrable φ ν :=
    (integrableOn_iff_integrable_of_support_subset hsub).1
      (Measure.integrableOn_of_bounded hloc.ne hφ.aestronglyMeasurable hbound)
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint

/-- **Threshold field** (steps (2e) and (2f) of the measure layer of Lemma 5.3). Let `g` be `m`-measurable with `μ ω = g ω`
almost surely and `μ ω` finite on the closed ball of radius `R` almost surely. Then for every real `c` there is a Borel set
`T` of moment vectors with `{c < leastSupersolution (μ ω) R 0 u p} = {ω | lintegralMoment φs (g ω) ∈ T}` almost surely. -/
theorem threshold_field_borel {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    {P : @Measure Ω mΩ} [IsProbabilityMeasure P] (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    {μ g : Ω → Measure ℂ} {R u : ℝ} (hR : 0 ≤ R) (hu : 0 < u)
    (hg : Measurable[m] g) (hμg : ∀ᵐ ω ∂P, μ ω = g ω)
    (hμ : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x)
    {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) R)
    (hbdd : ∀ᵐ ω ∂P, BddBelow ((fun w : ℂ → ℝ => w p) '' supersolutions (μ ω) R 0 u))
    (c : ℝ) :
    ∃ T : Set (ℕ → ℝ), MeasurableSet T ∧
      ∀ᵐ ω ∂P, (c < leastSupersolution (μ ω) R 0 u p ↔ lintegralMoment φs (g ω) ∈ T) := by
  have hcont : ∀ k, Continuous (φs k) := fun k =>
    (contDiff_two_of_isTestFunction (hφs k).1).continuous
  have hsupp : ∀ k, tsupport (φs k) ⊆ closedBall (0 : ℂ) R := fun k =>
    (hφs k).1.2.2.trans ball_subset_closedBall
  have hY : Measurable[m] (fun ω => lintegralMoment φs (g ω)) :=
    measurable_lintegralMoment hg φs hcont
  have hmom : ∀ᵐ ω ∂P, lintegralMoment φs (g ω) = fun k => ∫ x, φs k x ∂(μ ω) := by
    filter_upwards [hμg, hμ] with ω hωg hωloc
    funext k
    rw [← hωg]
    exact (lintegralMoment_eq_integral (hcont k) (hsupp k) hωloc).symm
  have hS : ∀ q : ℚ, ∀ Q : Measure (ℕ → ℝ), IsFiniteMeasure Q →
      NullMeasurableSet (Prod.fst '' supersolutionPairs hR φs u (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ)) Q :=
    fun q Q hQ => hF1 (ℕ → ℝ) Q hQ _
      (analyticSet_supersolutionMoments hR (fun k => (hφs k).1) u _ ⟨p, hp⟩ (q : ℝ))
  have hid : ∀ᵐ ω ∂P, ∀ c' : ℝ, c' < leastSupersolution (μ ω) R 0 u p ↔
      ∃ q : ℚ, c' < (q : ℝ) ∧ lintegralMoment φs (g ω) ∉
        Prod.fst '' supersolutionPairs hR φs u (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ) := by
    filter_upwards [hmom, hμ, hbdd] with ω hωm hωloc hωb
    intro c'
    rw [hωm]
    exact lt_leastSupersolution_iff_moments hR hωloc hu φs hφs hdense hG c' hp hωb
  obtain ⟨T, hT, hTω⟩ := threshold_borel_ae hm hY
    (S := fun q : ℚ => Prod.fst '' supersolutionPairs hR φs u (greenFunction (ball (0 : ℂ) R) 0) ⟨p, hp⟩ (q : ℝ))
    hS (v := fun ω => leastSupersolution (μ ω) R 0 u p) hid c
  exact ⟨T, hT, hTω⟩

end MatedCRT.S5c
