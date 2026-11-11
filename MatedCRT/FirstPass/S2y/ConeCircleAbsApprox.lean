import MatedCRT.FirstPass.S2y.ConeCircleAverage
import HarmonicBalls.FirstPass.S11u
import HarmonicBalls.Proofs.Sec8.CircleDensityContinuousLimit
import HarmonicBalls.Proofs.Sec8.CirclePairingCovariance
import MatedCRT.Proofs.Sec1.EnvironmentScaling.LateralCircleMeasurability
import MatedCRT.Proofs.Sec1.EnvironmentScaling.IntegrableReferenceObservables
import MatedCRT.Proofs.Measurability.ConePairing

/-!
# Absolute approximation of cone circle averages

Proof of the absolute approximation `hAbs` of `coneCircleAverageLocalityStep_of_absApprox`
(MatedCRT/FirstPass/S2y/ConeCircleAverage.lean:52). For `closedBall x ε ⊆ U`, the circle average `h_ε(x)` of a cone
is the limit in probability of pairings with test functions supported in `U`:

* the test functions are the normalized annular circle densities `unitCircleDensity s δ x` (mollified uniform measures
  on `∂B_s(x)`, Duplantier-Sheffield Section 3.1), with `s < ε` close to `ε` and `s ≠ |x|` (so that the circle avoids `0`);
* for the whole-plane GFF the variance of `hC(φ) - hcirc(s, x)` is bounded by the Armitage-Gardiner-type estimate
  `abs_unitCircleDensity_covariance_combination` (Harmonic-Balls, S11u), which tends to `0` with the width;
* the radial part `y ↦ h_{|y|}(0)` is a.s. continuous on the circle, hence the annular averages converge a.s.
  (`circleDensity_integral_tendsto_circleAverage`, after a continuous extension by clamping `|y|`);
* the lateral parts have the law of the lateral part of a whole-plane GFF (`lateralArray_law_of_isQuantumCone`),
  which transfers the convergence in probability;
* a diagonal choice over the radii `s_m → ε` gives the sequence.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

section Diagonal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Convergence in measure is preserved by sums (union bound). -/
theorem tendstoInMeasure_add_of_tendsto [IsFiniteMeasure P] {f f' : ℕ → Ω → ℝ} {g g' : Ω → ℝ}
    (hf : TendstoInMeasure P f atTop g) (hf' : TendstoInMeasure P f' atTop g') :
    TendstoInMeasure P (fun n ω => f n ω + f' n ω) atTop (fun ω => g ω + g' ω) := by
  rw [tendstoInMeasure_iff_dist] at hf hf' ⊢
  intro δ hδ
  have hsplit : ∀ n, P {ω | δ ≤ dist (f n ω + f' n ω) (g ω + g' ω)} ≤
      P {ω | δ / 2 ≤ dist (f n ω) (g ω)} + P {ω | δ / 2 ≤ dist (f' n ω) (g' ω)} := by
    intro n
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω hω
    have hω' : δ ≤ dist (f n ω + f' n ω) (g ω + g' ω) := hω
    have h1 : dist (f n ω + f' n ω) (g ω + g' ω) ≤ dist (f n ω) (g ω) + dist (f' n ω) (g' ω) :=
      dist_add_add_le _ _ _ _
    rcases le_or_gt (δ / 2) (dist (f n ω) (g ω)) with h | h
    · exact Or.inl (show δ / 2 ≤ dist (f n ω) (g ω) from h)
    · refine Or.inr ?_
      show δ / 2 ≤ dist (f' n ω) (g' ω)
      by_contra h'
      have h'' : dist (f' n ω) (g' ω) < δ / 2 := lt_of_not_ge h'
      linarith
  have hlim : Tendsto (fun n => P {ω | δ / 2 ≤ dist (f n ω) (g ω)} +
      P {ω | δ / 2 ≤ dist (f' n ω) (g' ω)}) atTop (𝓝 0) := by
    have h := (hf (δ / 2) (by positivity)).add (hf' (δ / 2) (by positivity))
    rwa [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hsplit

/-- Diagonal selection: if each row converges in measure, a single diagonal sequence converges in measure to the
limit of the row limits. -/
theorem tendstoInMeasure_diagonal [IsFiniteMeasure P] {F : ℕ → ℕ → Ω → ℝ} {G : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hF : ∀ m, TendstoInMeasure P (F m) atTop (G m)) (hG : TendstoInMeasure P G atTop Y) :
    ∃ k : ℕ → ℕ, TendstoInMeasure P (fun m => F m (k m)) atTop Y := by
  have hF' : ∀ m, ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤ dist (F m n ω) (G m ω)}) atTop (𝓝 0) :=
    fun m δ hδ => tendstoInMeasure_iff_dist.1 (hF m) δ hδ
  have hG' : ∀ δ : ℝ, 0 < δ → Tendsto (fun m => P {ω | δ ≤ dist (G m ω) (Y ω)}) atTop (𝓝 0) :=
    fun δ hδ => tendstoInMeasure_iff_dist.1 hG δ hδ
  have hK : ∀ m : ℕ, ∃ K : ℕ, ∀ n ≥ K,
      P {ω | 1 / ((m : ℝ) + 1) ≤ dist (F m n ω) (G m ω)} ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hlt := (tendsto_order.1 (hF' m _ hpos)).2 (ENNReal.ofReal (1 / ((m : ℝ) + 1)))
      (ENNReal.ofReal_pos.2 hpos)
    obtain ⟨K, hK⟩ := eventually_atTop.1 hlt
    exact ⟨K, fun n hn => (hK n hn).le⟩
  choose k hk using hK
  refine ⟨k, tendstoInMeasure_iff_dist.2 fun δ hδ => ?_⟩
  have hA : Tendsto (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    have h : Tendsto (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) atTop
        (𝓝 (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [ENNReal.ofReal_zero] at h
  have hsum := hA.add (hG' (δ / 2) (by positivity))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
    (ge_mem_nhds (show (0 : ℝ) < δ / 2 by positivity))] with m hm
  have hsub : {ω | δ ≤ dist (F m (k m) ω) (Y ω)} ⊆
      {ω | 1 / ((m : ℝ) + 1) ≤ dist (F m (k m) ω) (G m ω)} ∪ {ω | δ / 2 ≤ dist (G m ω) (Y ω)} := by
    intro ω hω
    have hω' : δ ≤ dist (F m (k m) ω) (Y ω) := hω
    have h1 := dist_triangle (F m (k m) ω) (G m ω) (Y ω)
    rcases le_or_gt (1 / ((m : ℝ) + 1)) (dist (F m (k m) ω) (G m ω)) with h | h
    · exact Or.inl (show 1 / ((m : ℝ) + 1) ≤ dist (F m (k m) ω) (G m ω) from h)
    · refine Or.inr ?_
      show δ / 2 ≤ dist (G m ω) (Y ω)
      by_contra h'
      have h'' : dist (G m ω) (Y ω) < δ / 2 := lt_of_not_ge h'
      linarith
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (hk m (k m) le_rfl) le_rfl))

end Diagonal

/-! ## Annular test densities and the reference (whole-plane GFF) estimate -/

/-- The `n`-th width of the annular density of radius `s` (Harmonic-Balls `circleDensityWidth`) is at most `s` times the
annulus width `η₀/(n+1)`. -/
theorem circleDensityWidth_le_annulus (s η₀ : ℝ) (n : ℕ) :
    circleDensityWidth s η₀ n ≤ s * (η₀ / ((n : ℝ) + 1)) := by
  unfold circleDensityWidth
  rw [mul_div_assoc]

/-- The `n`-th annular unit circle density of radius `s` centred at `x`: the mollified uniform measure on
`∂B_s(x)` of Duplantier-Sheffield (Section 3.1), with annulus width `η₀/(n+1)`. -/
noncomputable def annulusDensity {s η₀ : ℝ} (hs : 0 < s) (hη : 0 < η₀) (x : ℂ) (n : ℕ) : ℂ → ℝ :=
  unitCircleDensity s (circleDensityWidth s η₀ n) (circleDensityWidth_pos hs hη n) x

theorem isTestFunction_annulusDensity {O : Set ℂ} {s η₀ : ℝ} (hs : 0 < s) (hη : 0 < η₀) (x : ℂ) (n : ℕ)
    (hO : {y : ℂ | |‖y - x‖ - s| ≤ η₀ / ((n : ℝ) + 1)} ⊆ O) :
    IsTestFunction O (annulusDensity hs hη x n) := by
  unfold annulusDensity
  refine ⟨ContDiff.mul contDiff_const (circleDensity_contDiff _ _ _ _),
    unitCircleDensity_hasCompactSupport hs.le _ x, ?_⟩
  exact (tsupport_unitCircleDensity_subset hs (circleDensityWidth_pos hs hη n)
    (circleDensityWidth_le_annulus s η₀ n) x).trans hO

/-- **Reference estimate.** For a whole-plane GFF, the annular pairings `hC'(annulusDensity)` converge in probability
to the circle average `hcirc'(s, x)`: the variance of the difference is at most `2 (log (s+η) - log (s-η))` with
`η = η₀/(n+1) → 0` (Harmonic-Balls, `abs_unitCircleDensity_covariance_combination`). -/
theorem reference_annulus_tendstoInMeasure {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P' hC' hcirc') {s η₀ : ℝ} (hs : 0 < s) (hη : 0 < η₀) (hηs : η₀ < s) (x : ℂ) :
    TendstoInMeasure P' (fun n ω => hC' ω (annulusDensity hs hη x n) - hcirc' ω s x) atTop (fun _ => 0) := by
  have hφ : ∀ n, IsTestFunction univ (annulusDensity hs hη x n) := fun n =>
    isTestFunction_annulusDensity hs hη x n (subset_univ _)
  have hηn : ∀ n : ℕ, η₀ / ((n : ℝ) + 1) < s := fun n => by
    have hn : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg
    have h1 : η₀ / ((n : ℝ) + 1) ≤ η₀ := div_le_self hη.le (by linarith)
    linarith
  have hB : Tendsto (fun n : ℕ => 2 * (Real.log (s + η₀ / ((n : ℝ) + 1)) -
      Real.log (s - η₀ / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have hηt : Tendsto (fun n : ℕ => η₀ / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul η₀
      rw [mul_zero] at h
      exact h.congr fun n => by ring
    have hc : ContinuousAt (fun t : ℝ => 2 * (Real.log (s + t) - Real.log (s - t))) 0 := by
      refine ContinuousAt.mul continuousAt_const (ContinuousAt.sub ?_ ?_)
      · exact ContinuousAt.log (continuousAt_const.add continuousAt_id)
          (show s + 0 ≠ 0 by rw [add_zero]; exact hs.ne')
      · exact ContinuousAt.log (continuousAt_const.sub continuousAt_id)
          (show s - 0 ≠ 0 by rw [sub_zero]; exact hs.ne')
    have h2 : 2 * (Real.log (s + 0) - Real.log (s - 0)) = 0 := by
      rw [add_zero, sub_zero, sub_self, mul_zero]
    have h := hc.tendsto.comp hηt
    rw [h2] at h
    exact h
  refine tendstoInMeasure_of_centered_variance_tendsto_zero P' _ (fun _ => 0) ?_ ?_ ?_
  · intro n
    simp only [sub_zero]
    have hp2 : MemLp (fun ω => hC' ω (annulusDensity hs hη x n)) 2 P' :=
      (h.isGaussianProcess.hasGaussianLaw_eval
        (⟨.pairing (annulusDensity hs hη x n), hφ n⟩ : GFFObservable.Admissible)).memLp (by simp)
    have hz2 : MemLp (fun ω => hcirc' ω s x) 2 P' := (h.hasGaussianLaw_circle hs x).memLp (by simp)
    exact hp2.sub hz2
  · intro n
    simp only [sub_zero]
    have hadm : GFFObservable.IsAdmissible (.pairing (annulusDensity hs hη x n)) := hφ n
    have h1 : ∫ ω, hC' ω (annulusDensity hs hη x n) ∂P' = 0 := h.integral_eq_zero _ hadm
    have h2 : ∫ ω, hcirc' ω s x ∂P' = 0 := h.integral_eq_zero (.circle s x) hs
    have hp2 : MemLp (fun ω => hC' ω (annulusDensity hs hη x n)) 2 P' :=
      (h.isGaussianProcess.hasGaussianLaw_eval
        (⟨.pairing (annulusDensity hs hη x n), hφ n⟩ : GFFObservable.Admissible)).memLp (by simp)
    have hz2 : MemLp (fun ω => hcirc' ω s x) 2 P' := (h.hasGaussianLaw_circle hs x).memLp (by simp)
    rw [integral_sub (hp2.integrable one_le_two) (hz2.integrable one_le_two), h1, h2, sub_zero]
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB
      (fun n => ProbabilityTheory.variance_nonneg _ _) (fun n => ?_)
    simp only [sub_zero]
    rw [variance_pairing_sub_circle_eq h hs x _ (hφ n)]
    exact (le_abs_self _).trans (abs_unitCircleDensity_covariance_combination hs
      (circleDensityWidth_pos hs hη n) (hηn n) (circleDensityWidth_le_annulus s η₀ n) x)

/-! ## The radial part: pathwise convergence of the annular averages -/

/-- **Radial convergence.** Let `g` be continuous on `(0, ∞)` (the radial part `t ↦ h_t(0)`), and let the circle
`∂B_s(x)` avoid the origin, `2η₀ ≤ | |x| - s |`. Then the annular averages of `y ↦ g |y|` converge to the circle average
of `y ↦ g |y|` over `∂B_s(x)`. The proof clamps `|y|` to a compact interval, so that the integrand is a continuous
function (Harmonic-Balls `circleDensity_integral_tendsto_circleAverage`). -/
theorem tendsto_annulusDensity_integral_radial {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {s η₀ : ℝ}
    (hs : 0 < s) (hη : 0 < η₀) {x : ℂ} (hd : 2 * η₀ ≤ |‖x‖ - s|) :
    Tendsto (fun n => ∫ y, annulusDensity hs hη x n y * g ‖y‖) atTop
      (𝓝 (Real.circleAverage (fun y => g ‖y‖) x s)) := by
  have hdpos : 0 < |‖x‖ - s| := by linarith
  have hdle : |‖x‖ - s| ≤ ‖x‖ + s := by
    rw [abs_le]; constructor <;> linarith [norm_nonneg x]
  have ht1pos : 0 < |‖x‖ - s| / 2 := by linarith
  have ht12 : |‖x‖ - s| / 2 ≤ ‖x‖ + s + η₀ + 1 := by
    linarith [norm_nonneg x]
  have hgI : ContinuousOn g (Icc (|‖x‖ - s| / 2) (‖x‖ + s + η₀ + 1)) :=
    hg.mono fun t ht => lt_of_lt_of_le ht1pos ht.1
  have hGc : Continuous fun y : ℂ => g (max (|‖x‖ - s| / 2) (min (‖x‖ + s + η₀ + 1) ‖y‖)) :=
    hgI.comp_continuous (continuous_const.max (continuous_const.min continuous_norm))
      fun y => ⟨le_max_left _ _, max_le ht12 (min_le_left _ _)⟩
  have key : ∀ η : ℝ, η ≤ η₀ → ∀ y : ℂ, |‖y - x‖ - s| ≤ η →
      g (max (|‖x‖ - s| / 2) (min (‖x‖ + s + η₀ + 1) ‖y‖)) = g ‖y‖ := by
    intro η hηη₀ y hy
    have hyx := abs_le.1 hy
    have hA : |‖x‖ - ‖x - y‖| ≤ ‖y‖ := by
      have := abs_norm_sub_norm_le x (x - y)
      simpa using this
    have hB : |‖x‖ - s| ≤ |‖x‖ - ‖x - y‖| + |‖x - y‖ - s| := abs_sub_le _ _ _
    have hC : ‖x - y‖ = ‖y - x‖ := norm_sub_rev _ _
    rw [hC] at hA hB
    have hlow : |‖x‖ - s| / 2 ≤ ‖y‖ := by linarith
    have hup : ‖y‖ ≤ ‖x‖ + s + η₀ + 1 := by
      have := norm_sub_norm_le y x
      linarith [hyx.2]
    rw [min_eq_right hup, max_eq_right hlow]
  have hint : ∀ n : ℕ, ∫ y, annulusDensity hs hη x n y * g ‖y‖ =
      ∫ y, annulusDensity hs hη x n y *
        g (max (|‖x‖ - s| / 2) (min (‖x‖ + s + η₀ + 1) ‖y‖)) := by
    intro n
    congr 1
    funext y
    by_cases hy : y ∈ tsupport (annulusDensity hs hη x n)
    · have hsub := tsupport_unitCircleDensity_subset hs (circleDensityWidth_pos hs hη n)
        (circleDensityWidth_le_annulus s η₀ n) x hy
      have hn : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg
      rw [key _ (div_le_self hη.le (by linarith)) y hsub]
    · rw [image_eq_zero_of_notMem_tsupport hy]
      simp
  have hav : Real.circleAverage (fun y => g (max (|‖x‖ - s| / 2) (min (‖x‖ + s + η₀ + 1) ‖y‖))) x s =
      Real.circleAverage (fun y => g ‖y‖) x s := by
    apply Real.circleAverage_congr_sphere
    intro y hy
    rw [abs_of_pos hs, mem_sphere, dist_eq_norm] at hy
    have hy' : |‖y - x‖ - s| ≤ 0 := by rw [hy]; simp
    exact key 0 (by linarith) y hy'
  have hlim := circleDensity_integral_tendsto_circleAverage hs hη x hGc
  rw [hav] at hlim
  have hfun : (fun n => ∫ y, annulusDensity hs hη x n y * g ‖y‖) =
      fun n => ∫ y, annulusDensity hs hη x n y *
        g (max (|‖x‖ - s| / 2) (min (‖x‖ + s + η₀ + 1) ‖y‖)) := funext hint
  rw [hfun]
  exact hlim

section Radial

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## Transfer of differences and the radial part -/

/-- Negation preserves convergence in measure. -/
theorem tendstoInMeasure_neg [IsFiniteMeasure P] {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (h : TendstoInMeasure P f atTop g) : TendstoInMeasure P (fun n ω => -f n ω) atTop (fun ω => -g ω) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro δ hδ
  simpa only [dist_neg_neg] using h δ hδ

/-- Convergence in measure of a difference to `0` gives convergence in measure to the limit. -/
theorem tendstoInMeasure_of_sub_zero [IsFiniteMeasure P] {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (h : TendstoInMeasure P (fun n ω => f n ω - g ω) atTop (fun _ => 0)) :
    TendstoInMeasure P f atTop g := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro δ hδ
  simpa only [Real.dist_eq, sub_zero] using h δ hδ

/-- **Radial part.** For a cone (or a whole-plane GFF) the difference between the circle average of the radial part
`y ↦ h_{|y|}(0)` over `∂B_s(x)` and its annular averages tends to `0` in measure, when the circle avoids the origin. -/
theorem tendstoInMeasure_radial [IsFiniteMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hmp : ∀ φ, IsTestFunction univ φ → Measurable fun ω => hC ω φ)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    {s η₀ : ℝ} (hs : 0 < s) (hη : 0 < η₀) {x : ℂ} (hd : 2 * η₀ ≤ |‖x‖ - s|) :
    TendstoInMeasure P (fun n ω => Real.circleAverage (fun y => hcirc ω ‖y‖ 0) x s -
      ∫ y, annulusDensity hs hη x n y * hcirc ω ‖y‖ 0) atTop (fun _ => 0) := by
  have hφ : ∀ n, IsTestFunction univ (annulusDensity hs hη x n) := fun n =>
    isTestFunction_annulusDensity hs hη x n (subset_univ _)
  have hLc := CirclePairing.aemeasurable_lateralProcess hmp hmc hcont
  have hLe : ∀ o : GFFObservable.Admissible,
      AEMeasurable (fun ω => lateralEval (hC ω) (hcirc ω) o.1) P :=
    fun o => (measurable_pi_apply o).comp_aemeasurable hLc
  have hmeas : ∀ n, AEStronglyMeasurable (fun ω => Real.circleAverage (fun y => hcirc ω ‖y‖ 0) x s -
      ∫ y, annulusDensity hs hη x n y * hcirc ω ‖y‖ 0) P := by
    intro n
    have hAE : AEMeasurable (fun ω => (hcirc ω s x - lateralEval (hC ω) (hcirc ω) (GFFObservable.circle s x)) -
        (hC ω (annulusDensity hs hη x n) -
          lateralEval (hC ω) (hcirc ω) (GFFObservable.pairing (annulusDensity hs hη x n)))) P :=
      ((hmc s x hs).aemeasurable.sub (hLe ⟨GFFObservable.circle s x, hs⟩)).sub
        ((hmp _ (hφ n)).aemeasurable.sub (hLe ⟨GFFObservable.pairing _, hφ n⟩))
    exact (hAE.congr (Eventually.of_forall fun ω => by simp only [lateralEval]; ring)).aestronglyMeasurable
  refine tendstoInMeasure_of_tendsto_ae hmeas ?_
  filter_upwards [hcont] with ω hω
  have hg : ContinuousOn (fun t : ℝ => hcirc ω t 0) (Ioi 0) :=
    hω.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨ht, mem_univ _⟩
  have hlim := tendsto_annulusDensity_integral_radial hg hs hη hd
  have h := (tendsto_const_nhds (x := Real.circleAverage (fun y => hcirc ω ‖y‖ 0) x s)).sub hlim
  simp only [sub_self] at h
  exact h

/-- **Reference lateral differences.** For a whole-plane GFF, the lateral annular pairings converge in probability to
the lateral circle average: the lateral difference is the pairing difference minus the radial difference. -/
theorem lateral_diff_tendsto_reference {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P' hC' hcirc') {s η₀ : ℝ} (hs : 0 < s) (hη : 0 < η₀) (hηs : η₀ < s) {x : ℂ}
    (hd : 2 * η₀ ≤ |‖x‖ - s|) :
    TendstoInMeasure P' (fun n ω => lateralEval (hC' ω) (hcirc' ω) (GFFObservable.pairing (annulusDensity hs hη x n)) -
      lateralEval (hC' ω) (hcirc' ω) (GFFObservable.circle s x)) atTop (fun _ => 0) := by
  have h1 := reference_annulus_tendstoInMeasure h hs hη hηs x
  have h2 := tendstoInMeasure_radial h.measurable_pairing h.measurable_circle h.ae_continuousOn_circle hs hη hd
  have h3 := tendstoInMeasure_add_of_tendsto h1 h2
  have heq : (fun n ω => lateralEval (hC' ω) (hcirc' ω) (GFFObservable.pairing (annulusDensity hs hη x n)) -
      lateralEval (hC' ω) (hcirc' ω) (GFFObservable.circle s x)) =
      fun n ω => (hC' ω (annulusDensity hs hη x n) - hcirc' ω s x) +
        (Real.circleAverage (fun y => hcirc' ω ‖y‖ 0) x s -
          ∫ y, annulusDensity hs hη x n y * hcirc' ω ‖y‖ 0) :=
    funext fun n => funext fun ω => by simp only [lateralEval]; ring
  rw [heq]
  simpa only [add_zero] using h3

end Radial

/-! ## Lateral transfer from the whole-plane GFF to the cone -/

section Transfer

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- The observables `j ↦ pairing (ψ (j/2))` (even `j`) and `j ↦ circle s x` (odd `j`), as one sequence. -/
noncomputable def pairCircleObs {ψ : ℕ → ℂ → ℝ} (hψ : ∀ n, IsTestFunction univ (ψ n)) {s : ℝ} (hs : 0 < s)
    (x : ℂ) : ℕ → GFFObservable.Admissible := fun j =>
  if j % 2 = 0 then ⟨GFFObservable.pairing (ψ (j / 2)), hψ (j / 2)⟩ else ⟨GFFObservable.circle s x, hs⟩

theorem pairCircleObs_even {ψ : ℕ → ℂ → ℝ} (hψ : ∀ n, IsTestFunction univ (ψ n)) {s : ℝ} (hs : 0 < s) (x : ℂ)
    (n : ℕ) : pairCircleObs hψ hs x (2 * n) = ⟨GFFObservable.pairing (ψ n), hψ n⟩ := by
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  unfold pairCircleObs
  simp only [h1, ↓reduceIte]
  apply Subtype.ext
  simp only [h2]

theorem pairCircleObs_odd {ψ : ℕ → ℂ → ℝ} (hψ : ∀ n, IsTestFunction univ (ψ n)) {s : ℝ} (hs : 0 < s) (x : ℂ)
    (n : ℕ) : pairCircleObs hψ hs x (2 * n + 1) = ⟨GFFObservable.circle s x, hs⟩ := by
  have h1 : ¬ (2 * n + 1) % 2 = 0 := by omega
  unfold pairCircleObs
  simp only [h1, ↓reduceIte]
  rfl

/-- The event `{|L(ψ_n) - L(s,x)| ≥ δ}` is the preimage of an event of the array of lateral observables. -/
theorem lateral_preimage_eq {Ω₀ : Type*} [MeasurableSpace Ω₀] (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ)
    (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) {ψ : ℕ → ℂ → ℝ} (hψ : ∀ n, IsTestFunction univ (ψ n)) {s : ℝ} (hs : 0 < s)
    (x : ℂ) (δ : ℝ) (n : ℕ) :
    {ω | δ ≤ |lateralEval (hC₀ ω) (hcirc₀ ω) (GFFObservable.pairing (ψ n)) -
        lateralEval (hC₀ ω) (hcirc₀ ω) (GFFObservable.circle s x)|} =
      (fun ω (j : ℕ) => lateralProcess (hC₀ ω) (hcirc₀ ω) (pairCircleObs hψ hs x j)) ⁻¹'
        {f : ℕ → ℝ | δ ≤ |f (2 * n) - f (2 * n + 1)|} := by
  ext ω
  change δ ≤ |_| ↔ δ ≤ |lateralProcess (hC₀ ω) (hcirc₀ ω) (pairCircleObs hψ hs x (2 * n)) -
    lateralProcess (hC₀ ω) (hcirc₀ ω) (pairCircleObs hψ hs x (2 * n + 1))|
  rw [pairCircleObs_even, pairCircleObs_odd]
  exact Iff.rfl

/-- **Lateral transfer.** For a cone, the lateral differences `L(ψ_n) - L(s,x)` converge in measure to `0`, as soon as
they do for every whole-plane GFF: the array of lateral observables has the same law under `P` and under the reference
GFF of `IsQuantumCone.lateral_law` (`lateralArray_law_of_isQuantumCone`). -/
theorem lateral_diff_tendsto_cone {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hQ : IsQuantumCone γ P hC hcirc) (ψ : ℕ → ℂ → ℝ) (hψ : ∀ n, IsTestFunction univ (ψ n)) {s : ℝ} (hs : 0 < s)
    (x : ℂ)
    (href : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω'), IsProbabilityMeasure P' →
      ∀ (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ), IsWholePlaneGFF P' hC' hcirc' →
        TendstoInMeasure P' (fun n ω => lateralEval (hC' ω) (hcirc' ω) (GFFObservable.pairing (ψ n)) -
          lateralEval (hC' ω) (hcirc' ω) (GFFObservable.circle s x)) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => lateralEval (hC ω) (hcirc ω) (GFFObservable.pairing (ψ n)) -
      lateralEval (hC ω) (hcirc ω) (GFFObservable.circle s x)) atTop (fun _ => 0) := by
  obtain ⟨Ω', _, P', hC', hcirc', hP', hGFF, hlaw⟩ :=
    MatedCRT.Sec1.lateralArray_law_of_isQuantumCone hQ (pairCircleObs hψ hs x)
  have hΦ : Measurable (fun (f : GFFObservable.Admissible → ℝ) (j : ℕ) => f (pairCircleObs hψ hs x j)) :=
    Measurable.of_eval fun j => measurable_pi_apply (pairCircleObs hψ hs x j)
  have hA : AEMeasurable (fun ω (j : ℕ) => lateralProcess (hC ω) (hcirc ω) (pairCircleObs hψ hs x j)) P :=
    hΦ.comp_aemeasurable (MatedCRT.Sec1.aemeasurable_lateralProcess_of_isQuantumCone hQ)
  have hA' : AEMeasurable (fun ω' (j : ℕ) => lateralProcess (hC' ω') (hcirc' ω') (pairCircleObs hψ hs x j)) P' :=
    hΦ.comp_aemeasurable
      (CirclePairing.aemeasurable_lateralProcess hGFF.measurable_pairing hGFF.measurable_circle
        hGFF.ae_continuousOn_circle)
  have hE : ∀ (δ : ℝ) (n : ℕ), MeasurableSet {f : ℕ → ℝ | δ ≤ |f (2 * n) - f (2 * n + 1)|} := fun δ n =>
    measurableSet_le measurable_const
      (continuous_abs.measurable.comp ((measurable_pi_apply (2 * n)).sub (measurable_pi_apply (2 * n + 1))))
  have hprob : ∀ (δ : ℝ) (n : ℕ),
      P {ω | δ ≤ |lateralEval (hC ω) (hcirc ω) (GFFObservable.pairing (ψ n)) -
        lateralEval (hC ω) (hcirc ω) (GFFObservable.circle s x)|} =
      P' {ω' | δ ≤ |lateralEval (hC' ω') (hcirc' ω') (GFFObservable.pairing (ψ n)) -
        lateralEval (hC' ω') (hcirc' ω') (GFFObservable.circle s x)|} := by
    intro δ n
    calc P {ω | δ ≤ |lateralEval (hC ω) (hcirc ω) (GFFObservable.pairing (ψ n)) -
          lateralEval (hC ω) (hcirc ω) (GFFObservable.circle s x)|}
        = P ((fun ω (j : ℕ) => lateralProcess (hC ω) (hcirc ω) (pairCircleObs hψ hs x j)) ⁻¹'
            {f : ℕ → ℝ | δ ≤ |f (2 * n) - f (2 * n + 1)|}) :=
          congrArg P (lateral_preimage_eq hC hcirc hψ hs x δ n)
      _ = P.map (fun ω (j : ℕ) => lateralProcess (hC ω) (hcirc ω) (pairCircleObs hψ hs x j))
            {f : ℕ → ℝ | δ ≤ |f (2 * n) - f (2 * n + 1)|} :=
          (Measure.map_apply_of_aemeasurable hA (hE δ n)).symm
      _ = P'.map (fun ω' (j : ℕ) => lateralProcess (hC' ω') (hcirc' ω') (pairCircleObs hψ hs x j))
            {f : ℕ → ℝ | δ ≤ |f (2 * n) - f (2 * n + 1)|} := by rw [hlaw]
      _ = P' ((fun ω' (j : ℕ) => lateralProcess (hC' ω') (hcirc' ω') (pairCircleObs hψ hs x j)) ⁻¹'
            {f : ℕ → ℝ | δ ≤ |f (2 * n) - f (2 * n + 1)|}) :=
          Measure.map_apply_of_aemeasurable hA' (hE δ n)
      _ = P' {ω' | δ ≤ |lateralEval (hC' ω') (hcirc' ω') (GFFObservable.pairing (ψ n)) -
            lateralEval (hC' ω') (hcirc' ω') (GFFObservable.circle s x)|} :=
          (congrArg P' (lateral_preimage_eq hC' hcirc' hψ hs x δ n)).symm
  have href' := href Ω' P' hP' hC' hcirc' hGFF
  rw [tendstoInMeasure_iff_dist]
  intro δ hδ
  have hlim := (tendstoInMeasure_iff_dist.1 href') δ hδ
  have key : ∀ n, P {ω | δ ≤ dist (lateralEval (hC ω) (hcirc ω) (GFFObservable.pairing (ψ n)) -
        lateralEval (hC ω) (hcirc ω) (GFFObservable.circle s x)) 0} =
      P' {ω' | δ ≤ dist (lateralEval (hC' ω') (hcirc' ω') (GFFObservable.pairing (ψ n)) -
        lateralEval (hC' ω') (hcirc' ω') (GFFObservable.circle s x)) 0} := by
    intro n
    simp only [dist_zero_right, Real.norm_eq_abs]
    exact hprob δ n
  exact Tendsto.congr (fun n => (key n).symm) hlim

end Transfer

/-! ## The fixed-radius approximation and the absolute approximation hAbs -/

section Final

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Fixed radius.** For a cone and a radius `s` with `2η₀ ≤ | |x| - s |`, the annular pairings converge in measure
to the circle average `hcirc(s, x)`. -/
theorem annulus_tendsto_cone {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hQ : IsQuantumCone γ P hC hcirc) [IsProbabilityMeasure P] {s η₀ : ℝ} (hs : 0 < s) (hη : 0 < η₀)
    (hηs : η₀ < s) {x : ℂ} (hd : 2 * η₀ ≤ |‖x‖ - s|) :
    TendstoInMeasure P (fun n ω => hC ω (annulusDensity hs hη x n)) atTop (fun ω => hcirc ω s x) := by
  have hφ : ∀ n, IsTestFunction univ (annulusDensity hs hη x n) := fun n =>
    isTestFunction_annulusDensity hs hη x n (subset_univ _)
  have hL := lateral_diff_tendsto_cone hQ (fun n => annulusDensity hs hη x n) hφ hs x
    (fun Ω' _ P' hP' hC' hcirc' hGFF => lateral_diff_tendsto_reference hGFF hs hη hηs hd)
  have hR := tendstoInMeasure_radial hQ.measurable_pairing hQ.measurable_circle hQ.ae_continuousOn_circle hs hη hd
  have hsum := tendstoInMeasure_add_of_tendsto hL (tendstoInMeasure_neg hR)
  refine tendstoInMeasure_of_sub_zero ?_
  show TendstoInMeasure P (fun n ω => hC ω (annulusDensity hs hη x n) - hcirc ω s x) atTop (fun _ => 0)
  have heq : (fun n ω => hC ω (annulusDensity hs hη x n) - hcirc ω s x) =
      fun n ω => (lateralEval (hC ω) (hcirc ω) (GFFObservable.pairing (annulusDensity hs hη x n)) -
        lateralEval (hC ω) (hcirc ω) (GFFObservable.circle s x)) +
        -(Real.circleAverage (fun y => hcirc ω ‖y‖ 0) x s -
          ∫ y, annulusDensity hs hη x n y * hcirc ω ‖y‖ 0) :=
    funext fun n => funext fun ω => by simp only [lateralEval]; ring
  rw [heq]
  simpa only [add_zero, neg_zero] using hsum

/-- **The absolute approximation `hAbs`** of `coneCircleAverageLocalityStep_of_absApprox`
(MatedCRT/FirstPass/S2y/ConeCircleAverage.lean:52): for every cone field and every open `U ⊇ closedBall x ε`, the circle
average `h_ε(x)` is the limit in probability of pairings with test functions supported in `U`. -/
theorem hAbs_proved : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
    ∀ U : Set ℂ, IsOpen U → ∀ (ε : ℝ) (x : ℂ), 0 < ε → closedBall x ε ⊆ U →
      ∃ ψ : ℕ → ℂ → ℝ, (∀ n, IsTestFunction U (ψ n)) ∧
        TendstoInMeasure P (fun n ω => hC ω (ψ n)) atTop (fun ω => hcirc ω ε x) := by
  intro γ _ _ Ω _ P hC hcirc hP hQ U _ ε x hε hsub
  -- radii `s_m ↑ ε` avoiding `‖x‖` (the circle `∂B_s(x)` then avoids the origin)
  have hsel : ∀ m : ℕ, ∃ s : ℝ, max (ε - 1 / ((m : ℝ) + 1)) (ε / 2) < s ∧ s < ε ∧ s ≠ ‖x‖ := by
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hlt : max (ε - 1 / ((m : ℝ) + 1)) (ε / 2) < ε :=
      max_lt (by linarith) (by linarith)
    obtain ⟨s, hs⟩ := ((Set.Ioo_infinite hlt).sdiff (Set.finite_singleton ‖x‖)).nonempty
    exact ⟨s, hs.1.1, hs.1.2, fun h => hs.2 (Set.mem_singleton_iff.2 h)⟩
  choose sm hsm1 hsm2 hsm3 using hsel
  have hsmpos : ∀ m, 0 < sm m := fun m => by
    have h := le_max_right (ε - 1 / ((m : ℝ) + 1)) (ε / 2)
    linarith [hsm1 m]
  have hη_ex : ∀ m, ∃ η : ℝ, 0 < η ∧ η ≤ (ε - sm m) / 2 ∧ η ≤ sm m / 2 ∧ 2 * η ≤ |‖x‖ - sm m| := by
    intro m
    have hd : 0 < |‖x‖ - sm m| := abs_pos.2 (sub_ne_zero.2 (hsm3 m).symm)
    refine ⟨min (min ((ε - sm m) / 2) (sm m / 2)) (|‖x‖ - sm m| / 2), ?_, ?_, ?_, ?_⟩
    · exact lt_min (lt_min (by linarith [hsm2 m]) (by linarith [hsmpos m])) (by linarith)
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · have := min_le_right (min ((ε - sm m) / 2) (sm m / 2)) (|‖x‖ - sm m| / 2)
      linarith
  choose ηm hηpos hηle1 hηle2 hηle3 using hη_ex
  -- test functions supported in `U`
  have hψtest : ∀ m n, IsTestFunction U (annulusDensity (hsmpos m) (hηpos m) x n) := by
    intro m n
    refine isTestFunction_annulusDensity (hsmpos m) (hηpos m) x n (fun y hy => hsub ?_)
    have hy' : |‖y - x‖ - sm m| ≤ ηm m := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg
      have : ηm m / ((n : ℝ) + 1) ≤ ηm m := div_le_self (hηpos m).le (by linarith)
      exact le_trans hy this
    have h2 := (abs_le.1 hy').2
    rw [mem_closedBall, dist_eq_norm]
    linarith [hηle1 m, hsm2 m]
  -- the approximants at fixed radius
  have hfix : ∀ m, TendstoInMeasure P (fun n ω => hC ω (annulusDensity (hsmpos m) (hηpos m) x n)) atTop
      (fun ω => hcirc ω (sm m) x) := fun m =>
    annulus_tendsto_cone hQ (hsmpos m) (hηpos m) (by linarith [hηle2 m, hsmpos m]) (hηle3 m)
  -- the radii converge to `ε`, and the circle averages converge almost surely
  have tsm : Tendsto sm atTop (𝓝 ε) := by
    have hlow : Tendsto (fun m : ℕ => ε - 1 / ((m : ℝ) + 1)) atTop (𝓝 ε) := by
      have := (tendsto_const_nhds (x := ε)).sub tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [sub_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
      (Eventually.of_forall fun m => ?_) (Eventually.of_forall fun m => (hsm2 m).le)
    exact (le_max_left _ _).trans (hsm1 m).le
  have hG : TendstoInMeasure P (fun m ω => hcirc ω (sm m) x) atTop (fun ω => hcirc ω ε x) := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun m => (hQ.measurable_circle (sm m) x (hsmpos m)).aestronglyMeasurable) ?_
    filter_upwards [hQ.ae_continuousOn_circle] with ω hω
    have hlim : Tendsto (fun m => ((sm m, x) : ℝ × ℂ)) atTop (𝓝[Ioi 0 ×ˢ univ] (ε, x)) :=
      tendsto_nhdsWithin_iff.2 ⟨tsm.prodMk_nhds tendsto_const_nhds,
        Eventually.of_forall fun m => ⟨hsmpos m, mem_univ _⟩⟩
    exact (hω (ε, x) ⟨hε, mem_univ _⟩).tendsto.comp hlim
  -- diagonal selection over the radii
  obtain ⟨k, hk⟩ := tendstoInMeasure_diagonal hfix hG
  exact ⟨fun m => annulusDensity (hsmpos m) (hηpos m) x (k m), fun m => hψtest m (k m), hk⟩

/-- **The cone circle average locality step**, proved without the hypothesis `hAbs`
(`coneCircleAverageLocalityStep_of_absApprox` applied to `hAbs_proved`). -/
theorem coneCircleAverageLocalityStep_proved : ConeCircleAverageLocalityStep :=
  coneCircleAverageLocalityStep_of_absApprox hAbs_proved

end Final

end MatedCRT
