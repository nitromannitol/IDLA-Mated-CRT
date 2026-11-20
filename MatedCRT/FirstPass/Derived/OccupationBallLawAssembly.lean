import MatedCRT.FirstPass.Derived.OccupationBallLawLintegral

/-!
# Total mass of the occupation integrals of the limiting clock

A tail-truncation interchange lemma (general: a sequence of nonnegative extended real functions whose
integrals over an exhausting family of measurable sets converge, with exterior contributions
uniformly small, has convergent total integrals), and its application to the occupation integrals of
the approximating Liouville clocks:
`∫ dz E_z[∫ f d occupationMeasure of the limiting clock] = ∫ ofReal f dμ` for the vague limit `μ` of
the approximants.
-/

open MeasureTheory MarkovProcess Set Filter Topology Metric
open HarmonicBalls (lqgClockApprox IsLQGClock planarBrownianMotion)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **Tail-truncation interchange.**  If `a k → ainf` in the sense that the integrals over every
member of an exhausting increasing family `S R` of measurable sets converge, and the integrals of
`a k` over the complement of `S R` are at most `T R → 0` uniformly in `k`, then the total integrals
converge. -/
theorem tendsto_lintegral_of_tendsto_setLIntegral_of_tail {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a : ℕ → X → ℝ≥0∞} {ainf : X → ℝ≥0∞} (hinf : Measurable ainf)
    {S : ℝ → Set X} (hS : ∀ R, MeasurableSet (S R)) (hmono : Monotone S)
    (hcover : ∀ x, ∃ R, x ∈ S R) {T : ℝ → ℝ≥0∞} (hT : Tendsto T atTop (𝓝 0))
    (hconv : ∀ R, Tendsto (fun k => ∫⁻ x in S R, a k x ∂μ) atTop (𝓝 (∫⁻ x in S R, ainf x ∂μ)))
    (htail : ∀ R k, ∫⁻ x in (S R)ᶜ, a k x ∂μ ≤ T R) :
    Tendsto (fun k => ∫⁻ x, a k x ∂μ) atTop (𝓝 (∫⁻ x, ainf x ∂μ)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · have hw : ∫⁻ x, ainf x ∂μ = ⨆ n : ℕ, ∫⁻ x in S n, ainf x ∂μ := by
      have h1 : ∀ n : ℕ, ∫⁻ x in S n, ainf x ∂μ = ∫⁻ x, (S n).indicator ainf x ∂μ := fun n =>
        (lintegral_indicator (hS _) _).symm
      simp_rw [h1]
      rw [← lintegral_iSup (fun n => hinf.indicator (hS _))
        (fun m n hmn x => indicator_le_indicator_of_subset (hmono (Nat.cast_le.mpr hmn : (m : ℝ) ≤ n))
          (fun _ => zero_le) x)]
      refine lintegral_congr fun x => ?_
      obtain ⟨R, hR⟩ := hcover x
      obtain ⟨n, hn⟩ := exists_nat_ge R
      exact le_antisymm (le_iSup_of_le n (by simp [indicator_of_mem (hmono hn hR)]))
        (iSup_le fun m => indicator_le_self' (fun _ _ => zero_le) x)
    rw [hw]
    refine iSup_le fun n => ?_
    calc ∫⁻ x in S n, ainf x ∂μ = liminf (fun k => ∫⁻ x in S n, a k x ∂μ) atTop :=
          ((hconv n).liminf_eq).symm
      _ ≤ liminf (fun k => ∫⁻ x, a k x ∂μ) atTop :=
          liminf_le_liminf (Eventually.of_forall fun k => setLIntegral_le_lintegral _ _)
  · have hR : ∀ R, limsup (fun k => ∫⁻ x, a k x ∂μ) atTop ≤ ∫⁻ x, ainf x ∂μ + T R := fun R => by
      calc limsup (fun k => ∫⁻ x, a k x ∂μ) atTop
          ≤ limsup (fun k => ∫⁻ x in S R, a k x ∂μ + T R) atTop :=
            limsup_le_limsup (Eventually.of_forall fun k => by
              rw [← lintegral_add_compl (a k) (hS R)]
              exact add_le_add le_rfl (htail R k))
        _ = ∫⁻ x in S R, ainf x ∂μ + T R := ((hconv R).add_const (T R)).limsup_eq
        _ ≤ ∫⁻ x, ainf x ∂μ + T R := add_le_add (setLIntegral_le_lintegral _ _) le_rfl
    simpa using ge_of_tendsto' (tendsto_const_nhds.add hT) hR

/-- **Total mass of the occupation integrals of the limiting clock.**  Under the hypotheses of the
disc convergence, with `μ` a vague limit of the dyadic approximants,
`∫ dz E_z[∫ f d occupationMeasure of the limiting clock] = ∫ ofReal f dμ`. -/
theorem lintegral_lintegral_ofReal_integral_occupationMeasure_eq {γ : ℝ} {hE : ℝ → ℂ → ℝ}
    {μ : Measure ℂ} (hμ : LatticeProb.LQG.IsLQGLimit γ hE μ)
    (hcont : ∀ k : ℕ, Continuous (hE (HarmonicBalls.dyadicScale k)))
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : ∀ z, IsLQGClock planarBrownianMotion γ hE z F)
    {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hG : IsPCAF planarLaw G)
    (hGF : ∀ z, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = F b t)
    {n β C : ℝ} (hβ : 0 < β) (hC0 : 0 < C)
    (hball : ∀ z : ℂ, ‖z‖ ≤ n + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
      LatticeProb.LQG.lqgApprox γ hE (LatticeProb.LQG.dyadicScale k) (ball z r) ≤
        ENNReal.ofReal (C * r ^ β))
    {f : ℂ → ℝ} (hf : Continuous f) {K : ℝ} (hfK : ∀ x, 0 ≤ f x ∧ f x ≤ K)
    (hfn : ∀ x : ℂ, n < ‖x‖ → f x = 0) :
    ∫⁻ z, ∫⁻ b, ENNReal.ofReal (∫ x, f x ∂occupationMeasure (fun t => G t b) b) ∂planarLaw z =
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  obtain ⟨Φ, hΦ, hver, -, -⟩ :=
    exists_measurable_tendsto_integral_ballLaw_lqgClock hcont hF hG hGF hβ hC0 hball hf hfK hfn 0
  obtain ⟨T, hT, hTb⟩ := exists_tendsto_setLIntegral_compl_ball_windowOcc_le hcont hball
    hf.measurable hfK hfn
  have hinf : Measurable fun z : ℂ => ∫⁻ b,
      ENNReal.ofReal (∫ x, f x ∂occupationMeasure (fun t => G t b) b) ∂planarLaw z := by
    have e : (fun z : ℂ => ∫⁻ b, ENNReal.ofReal (∫ x, f x ∂occupationMeasure (fun t => G t b) b)
        ∂planarLaw z) = fun z => ∫⁻ b, ENNReal.ofReal (Φ b) ∂planarLaw z :=
      funext fun z => lintegral_congr_ae (Filter.EventuallyEq.fun_comp (hver z) ENNReal.ofReal)
    rw [e]
    exact (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hΦ)).comp
      measurable_planarLaw
  have h1 := tendsto_lintegral_of_tendsto_setLIntegral_of_tail (μ := volume)
    (a := fun (k : ℕ) (z : ℂ) => ∫⁻ b, windowOcc (weightedApproxDensity γ hE f k) b ∂planarLaw z)
    hinf (S := fun R : ℝ => ball (0 : ℂ) R) (fun R => measurableSet_ball)
    (fun R R' h => ball_subset_ball h)
    (fun z => ⟨‖z‖ + 1, by simp⟩) hT
    (fun R => tendsto_setLIntegral_ball_windowOcc_lqgClock hcont hF hG hGF hβ hC0 hball hf hfK hfn R)
    hTb
  have h2 := tendsto_lintegral_weightedApproxDensity hμ hcont hball hf hfK hfn
  have e3 : ∀ k : ℕ, ∫⁻ z, ∫⁻ b, windowOcc (weightedApproxDensity γ hE f k) b ∂planarLaw z =
      ∫⁻ x, weightedApproxDensity γ hE f k x := fun k =>
    lintegral_lintegral_windowOcc_planarLaw
      (measurable_weightedApproxDensity hf.measurable (hcont k).measurable)
  simp only [e3] at h1
  exact tendsto_nhds_unique h1 h2

/-- The occupation measure of a clock along a path is a finite measure. -/
theorem isFiniteMeasure_occupationMeasure (a : ℝ≥0 → ℝ≥0) (ω : ContinuousPath ℂ) :
    IsFiniteMeasure (occupationMeasure a ω) := by
  unfold occupationMeasure
  have : IsFiniteMeasure ((stieltjesOfNNReal a).measure.restrict (Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  infer_instance

/-- **The Revuz measure of the limiting clock against `ofReal f`.**  Under the hypotheses of the disc
convergence, `∫ ofReal f d(revuz planarLaw G) = ∫ ofReal f dμ` for continuous `0 ≤ f` with compact
support, `μ` a vague limit of the dyadic approximants. -/
theorem lintegral_ofReal_revuz_eq_of_lqgClock {γ : ℝ} {hE : ℝ → ℂ → ℝ}
    {μ : Measure ℂ} (hμ : LatticeProb.LQG.IsLQGLimit γ hE μ)
    (hcont : ∀ k : ℕ, Continuous (hE (HarmonicBalls.dyadicScale k)))
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : ∀ z, IsLQGClock planarBrownianMotion γ hE z F)
    {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hG : IsPCAF planarLaw G)
    (hGF : ∀ z, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = F b t)
    {n β C : ℝ} (hβ : 0 < β) (hC0 : 0 < C)
    (hball : ∀ z : ℂ, ‖z‖ ≤ n + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
      LatticeProb.LQG.lqgApprox γ hE (LatticeProb.LQG.dyadicScale k) (ball z r) ≤
        ENNReal.ofReal (C * r ^ β))
    {f : ℂ → ℝ} (hf : Continuous f) {K : ℝ} (hfK : ∀ x, 0 ≤ f x ∧ f x ≤ K)
    (hfn : ∀ x : ℂ, n < ‖x‖ → f x = 0) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂revuz planarLaw G = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hfK x).1
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) n) fun x hx =>
      hfn x (by simpa [mem_closedBall_zero_iff] using hx)
  have hfm : Measurable fun x => ENNReal.ofReal (f x) := ENNReal.measurable_ofReal.comp hf.measurable
  rw [lintegral_revuz_of_isPCAF measurable_planarLaw hG (g := fun x => ENNReal.ofReal (f x)) hfm,
    ← lintegral_lintegral_ofReal_integral_occupationMeasure_eq hμ hcont hF hG hGF hβ hC0 hball hf
      hfK hfn]
  refine lintegral_congr fun z => lintegral_congr fun b => ?_
  have := isFiniteMeasure_occupationMeasure (fun t => G t b) b
  rw [ofReal_integral_eq_lintegral_ofReal (hf.integrable_of_hasCompactSupport hfc)
    (ae_of_all _ hf0), lintegral_occupationMeasure _ _ hfm]

end MatedCRT.FirstPass.Derived
