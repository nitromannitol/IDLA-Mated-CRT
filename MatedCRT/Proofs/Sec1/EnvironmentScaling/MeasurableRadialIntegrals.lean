import MatedCRT.Proofs.Sec1.EnvironmentScaling.RadialLocalIntegrability
import Mathlib.MeasureTheory.Function.Floor

/-!
# Measurable radial integrals (env-steps.tex:247-252)

Second component of the radial-integral argument for the lateral observables
`ℓ(φ) = h_C(φ) - ∫ φ(z) a(|z|,0) dz` (env-steps.tex:128-135).  For a radial family
`X r ω` (the value of the radial path at radius `r = |z|`), the test integral
`ω ↦ ∫ z, φ z * X ‖z‖ ω` is measurable.

* Compact-annulus slice: Riemann sums on the concentric annuli
  `{r_k ≤ |z| < r_{k+1}}` of a uniform partition of `[a, b)`.  Each Riemann sum is a
  finite linear combination of radial evaluations `X r_k` with deterministic coefficients
  `∫_{cell k} φ`, so it is measurable.  The sums converge on the almost-sure set where
  `r ↦ X r ω` is continuous on `[a, b]`.
* Truncation at zero: the integral over the ball `B(0, b)` is the limit of the annulus
  integrals over `[b/(k+2), b)`, dominated by `M C (1 + |log ‖z‖|)`, which is integrable on
  the ball by `integrableOn_one_add_abs_log_norm_closedBall`.

Names follow Armitage-Gardiner (annuli, Riemann sums of potential theory) and
Duplantier-Sheffield (radial parts of the lateral GFF).
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT.Sec1

/-- The half-open annulus `{a ≤ |z| < b}` in `ℂ`. -/
noncomputable def radialAnnulus (a b : ℝ) : Set ℂ := {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ < b}

/-- The `k`-th cell of the uniform partition of `radialAnnulus a b` into `m` concentric
annuli of mesh `(b - a) / m`: the points with `⌊(|z| - a) / ((b - a) / m)⌋₊ = k`. -/
noncomputable def radialCell (a b : ℝ) (m k : ℕ) : Set ℂ :=
  {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ < b ∧ ⌊(‖z‖ - a) / ((b - a) / m)⌋₊ = k}

/-- The grid step: the radial function `g` evaluated at the left endpoint of the cell
containing `z`.  Its values are the finitely many radial evaluations of a Riemann sum. -/
noncomputable def radialGridStep (g : ℝ → ℝ) (a b : ℝ) (m : ℕ) (z : ℂ) : ℝ :=
  g (a + (⌊(‖z‖ - a) / ((b - a) / m)⌋₊ : ℝ) * ((b - a) / m))

lemma measurableSet_radialAnnulus (a b : ℝ) : MeasurableSet (radialAnnulus a b) :=
  (measurableSet_le measurable_const continuous_norm.measurable).inter
    (measurableSet_lt continuous_norm.measurable measurable_const)

lemma measurableSet_radialCell (a b : ℝ) (m k : ℕ) : MeasurableSet (radialCell a b m k) := by
  have hx : Measurable fun z : ℂ => (‖z‖ - a) / ((b - a) / m) :=
    ((continuous_norm.sub continuous_const).div_const _).measurable
  have hfl : Measurable fun z : ℂ => ⌊(‖z‖ - a) / ((b - a) / m)⌋₊ :=
    Nat.measurable_floor.comp hx
  exact (measurableSet_le measurable_const continuous_norm.measurable).inter
    ((measurableSet_lt continuous_norm.measurable measurable_const).inter
      (hfl (measurableSet_singleton k)))

lemma radialCell_subset (a b : ℝ) (m k : ℕ) : radialCell a b m k ⊆ radialAnnulus a b :=
  fun _ hz => ⟨hz.1, hz.2.1⟩

lemma pairwise_disjoint_radialCell (a b : ℝ) (m : ℕ) :
    Set.Pairwise (↑(Finset.range m)) fun i j : ℕ => Disjoint (radialCell a b m i) (radialCell a b m j) := by
  intro i _ j _ hij
  show Disjoint (radialCell a b m i) (radialCell a b m j)
  exact Set.disjoint_left.2 fun z hi hj => hij (hi.2.2.symm.trans hj.2.2)

lemma mesh_pos {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m) : 0 < (b - a) / m :=
  div_pos (by linarith) (by exact_mod_cast hm)

/-- The floor index of a point of the annulus is a valid cell index. -/
lemma floor_grid_lt {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m) {z : ℂ}
    (h1 : a ≤ ‖z‖) (h2 : ‖z‖ < b) :
    ⌊(‖z‖ - a) / ((b - a) / m)⌋₊ < m := by
  have hh := mesh_pos hab hm
  have hx0 : 0 ≤ (‖z‖ - a) / ((b - a) / m) := div_nonneg (by linarith) hh.le
  refine (Nat.floor_lt hx0).2 ?_
  rw [div_lt_iff₀ hh]
  have hmh : (m : ℝ) * ((b - a) / m) = b - a := by
    field_simp
  nlinarith

/-- The radial annulus is the finite union of the cells of its uniform partition. -/
lemma radialAnnulus_eq_biUnion {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m) :
    radialAnnulus a b = ⋃ k ∈ Finset.range m, radialCell a b m k := by
  ext z
  constructor
  · intro hz
    have h1 : a ≤ ‖z‖ := hz.1
    have h2 : ‖z‖ < b := hz.2
    exact Set.mem_biUnion (Finset.mem_range.2 (floor_grid_lt hab hm h1 h2))
      ⟨h1, h2, rfl⟩
  · intro hz
    obtain ⟨k, -, hk⟩ := Set.mem_iUnion₂.1 hz
    exact ⟨hk.1, hk.2.1⟩

/-- Grid estimate: a point `z` of the cell with index `⌊x⌋₊` lies within one mesh of the
grid point `a + k * h`. -/
lemma abs_norm_sub_grid_le {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m) {z : ℂ}
    (h1 : a ≤ ‖z‖) :
    |‖z‖ - (a + (⌊(‖z‖ - a) / ((b - a) / m)⌋₊ : ℝ) * ((b - a) / m))| ≤ (b - a) / m := by
  set h := (b - a) / (m : ℝ) with hh_def
  have hh : 0 < h := mesh_pos hab hm
  set x := (‖z‖ - a) / h with hx_def
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hh.le
  have hxz : ‖z‖ - a = x * h := by
    rw [hx_def]
    field_simp
  have hk1 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  have hk2 : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  have e1 : ((⌊x⌋₊ : ℕ) : ℝ) * h ≤ x * h := mul_le_mul_of_nonneg_right hk1 hh.le
  have e2 : x * h < (((⌊x⌋₊ : ℕ) : ℝ) + 1) * h := mul_lt_mul_of_pos_right hk2 hh
  rw [abs_le]
  constructor <;> nlinarith

/-- Grid points of the cell index lie in the closed interval `[a, b]`. -/
lemma grid_point_mem {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m) {z : ℂ}
    (h1 : a ≤ ‖z‖) (h2 : ‖z‖ < b) :
    a + (⌊(‖z‖ - a) / ((b - a) / m)⌋₊ : ℝ) * ((b - a) / m) ∈ Icc a b := by
  have hh := mesh_pos hab hm
  have hlt := floor_grid_lt hab hm h1 h2
  have hkm : ((⌊(‖z‖ - a) / ((b - a) / m)⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hlt.le
  have hmh : (m : ℝ) * ((b - a) / m) = b - a := by
    field_simp
  have hk0 : (0 : ℝ) ≤ ((⌊(‖z‖ - a) / ((b - a) / m)⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor
  · nlinarith [mul_nonneg hk0 hh.le]
  · nlinarith [mul_le_mul_of_nonneg_right hkm hh.le]

lemma radialGridStep_eq_on_cell (g : ℝ → ℝ) {a b : ℝ} {m k : ℕ} {z : ℂ}
    (hz : z ∈ radialCell a b m k) :
    radialGridStep g a b m z = g (a + (k : ℝ) * ((b - a) / m)) := by
  unfold radialGridStep
  rw [hz.2.2]

lemma measurable_radialGridStep (g : ℝ → ℝ) (a b : ℝ) (m : ℕ) :
    Measurable (radialGridStep g a b m) := by
  have hx : Measurable fun z : ℂ => (‖z‖ - a) / ((b - a) / m) :=
    ((continuous_norm.sub continuous_const).div_const _).measurable
  exact (measurable_from_nat (f := fun k : ℕ => g (a + (k : ℝ) * ((b - a) / m)))).comp
    (Nat.measurable_floor.comp hx)

lemma measure_radialAnnulus_lt_top (a b : ℝ) : volume (radialAnnulus a b) < ⊤ :=
  (measure_mono (fun _ hz => mem_closedBall_zero_iff.2 hz.2.le)).trans_lt
    measure_closedBall_lt_top

/-- A bounded measurable integrand is integrable on the radial annulus. -/
lemma integrableOn_radialAnnulus_of_bound {F : ℂ → ℝ} {a b M : ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (radialAnnulus a b)))
    (hbd : ∀ z ∈ radialAnnulus a b, ‖F z‖ ≤ M) :
    IntegrableOn F (radialAnnulus a b) := by
  have hfin : (volume.restrict (radialAnnulus a b)) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (measure_radialAnnulus_lt_top a b).ne
  have key : IntegrableOn F univ (volume.restrict (radialAnnulus a b)) := by
    refine Measure.integrableOn_of_bounded (M := M) hfin hF ?_
    rw [Measure.restrict_univ]
    exact ae_restrict_of_forall_mem (measurableSet_radialAnnulus a b) hbd
  exact integrableOn_univ.1 key

/-- Deterministic Riemann approximation on a compact annulus.  For `g` continuous on `[a, b]`
and `φ` continuous, the Riemann sums `∑_{k<m} g(r_k) ∫_{cell k} φ` with
`r_k = a + k (b - a)/m` converge to `∫_{a ≤ |z| < b} φ(z) g(|z|) dz`. -/
theorem tendsto_radialRiemann {a b : ℝ} (hab : a < b) (φ : ℂ → ℝ) (hφ : Continuous φ)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b)) :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m,
        g (a + (k : ℝ) * ((b - a) / (m : ℝ))) * ∫ z in radialCell a b m k, φ z)
      atTop (𝓝 (∫ z in radialAnnulus a b, φ z * g ‖z‖)) := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) b).exists_bound_of_continuousOn
    hφ.continuousOn
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hg
  have hM0 : 0 ≤ max M₀ 0 := le_max_right _ _
  have hφM : ∀ z ∈ closedBall (0 : ℂ) b, ‖φ z‖ ≤ max M₀ 0 :=
    fun z hz => (hM₀ z hz).trans (le_max_left _ _)
  have hgn : ContinuousOn (fun z : ℂ => g ‖z‖) (radialAnnulus a b) :=
    hg.comp continuous_norm.continuousOn fun z hz => ⟨hz.1, hz.2.le⟩
  have hIint : IntegrableOn (fun z : ℂ => φ z * g ‖z‖) (radialAnnulus a b) := by
    refine integrableOn_radialAnnulus_of_bound (M := max M₀ 0 * K) ?_ ?_
    · exact (hφ.continuousOn.mul hgn).aestronglyMeasurable (measurableSet_radialAnnulus a b)
    · intro z hz
      rw [norm_mul]
      exact mul_le_mul (hφM z (mem_closedBall_zero_iff.2 hz.2.le))
        (hK _ ⟨hz.1, hz.2.le⟩) (norm_nonneg _) hM0
  have hstepInt : ∀ m : ℕ, 0 < m →
      IntegrableOn (fun z : ℂ => φ z * radialGridStep g a b m z) (radialAnnulus a b) := by
    intro m hm
    refine integrableOn_radialAnnulus_of_bound (M := max M₀ 0 * K) ?_ ?_
    · exact (hφ.measurable.mul (measurable_radialGridStep g a b m)).aestronglyMeasurable
    · intro z hz
      rw [norm_mul]
      exact mul_le_mul (hφM z (mem_closedBall_zero_iff.2 hz.2.le))
        (hK _ (grid_point_mem hab hm hz.1 hz.2)) (norm_nonneg _) hM0
  -- Riemann sums are the integrals of the grid step function (partition into cells).
  have hsum : ∀ m : ℕ, 0 < m →
      ∫ z in radialAnnulus a b, φ z * radialGridStep g a b m z =
        ∑ k ∈ Finset.range m, g (a + (k : ℝ) * ((b - a) / (m : ℝ))) *
          ∫ z in radialCell a b m k, φ z := by
    intro m hm
    rw [radialAnnulus_eq_biUnion hab hm,
      integral_biUnion_finset (Finset.range m) (fun k _ => measurableSet_radialCell a b m k)
        (pairwise_disjoint_radialCell a b m)
        (fun k _ => (hstepInt m hm).mono_set (radialCell_subset a b m k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hcell : ∫ z in radialCell a b m k, φ z * radialGridStep g a b m z =
        ∫ z in radialCell a b m k, φ z * g (a + (k : ℝ) * ((b - a) / (m : ℝ))) :=
      setIntegral_congr_fun (measurableSet_radialCell a b m k) fun z hz => by
        rw [radialGridStep_eq_on_cell g hz]
    rw [hcell, integral_mul_const]
    ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, hηeq⟩ : ∃ η : ℝ, 0 < η ∧
      η * (max M₀ 0 * volume.real (radialAnnulus a b) + 1) = ε :=
    ⟨ε / (max M₀ 0 * volume.real (radialAnnulus a b) + 1),
      div_pos hε (add_pos_of_nonneg_of_pos (mul_nonneg hM0 measureReal_nonneg) one_pos),
      div_mul_cancel₀ _
        (add_pos_of_nonneg_of_pos (mul_nonneg hM0 measureReal_nonneg) one_pos).ne'⟩
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) η hη
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N + 1, fun m hm => ?_⟩
  have hmpos : 0 < m := by omega
  have hmR : (N : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : N < m)
  have hmR0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hh_lt : (b - a) / (m : ℝ) < δ := by
    rw [div_lt_iff₀ hmR0]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  have hpt : ∀ z ∈ radialAnnulus a b,
      ‖φ z * g ‖z‖ - φ z * radialGridStep g a b m z‖ ≤ max M₀ 0 * η := by
    intro z hz
    have hzb : z ∈ closedBall (0 : ℂ) b := mem_closedBall_zero_iff.2 hz.2.le
    have hgap : ‖g ‖z‖ - radialGridStep g a b m z‖ ≤ η := by
      rw [Real.norm_eq_abs]
      have hdist : dist ‖z‖ (a + (⌊(‖z‖ - a) / ((b - a) / (m : ℝ))⌋₊ : ℝ) *
          ((b - a) / (m : ℝ))) < δ := by
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (abs_norm_sub_grid_le hab hmpos hz.1) hh_lt
      have := hδ' ‖z‖ ⟨hz.1, hz.2.le⟩ _ (grid_point_mem hab hmpos hz.1 hz.2) hdist
      rw [Real.dist_eq] at this
      exact this.le
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (hφM z hzb) hgap (norm_nonneg _) hM0
  have hdiff : (∫ z in radialAnnulus a b, φ z * g ‖z‖) -
      (∫ z in radialAnnulus a b, φ z * radialGridStep g a b m z)
      = ∫ z in radialAnnulus a b, (φ z * g ‖z‖ - φ z * radialGridStep g a b m z) :=
    (integral_sub hIint (hstepInt m hmpos)).symm
  rw [← hsum m hmpos, Real.dist_eq, abs_sub_comm, hdiff, ← Real.norm_eq_abs]
  refine lt_of_le_of_lt
    (norm_setIntegral_le_of_norm_le_const (measure_radialAnnulus_lt_top a b) hpt) ?_
  have hkey : max M₀ 0 * η * volume.real (radialAnnulus a b) + η = ε := by
    linear_combination hηeq
  linarith

/-- Compact-annulus slice, almost surely.  If the radial evaluations `ω ↦ X r ω` are
measurable and `r ↦ X r ω` is continuous on `[a, b]` for almost every `ω`, then
`ω ↦ ∫_{a ≤ |z| < b} φ(z) X(|z|)(ω) dz` is a.e. measurable: it is the almost-sure limit of the
measurable Riemann sums `∑_{k<m} X(r_k)(ω) ∫_{cell k} φ`, each a finite combination of
countably many radial evaluations (env-steps.tex:251-252). -/
theorem aemeasurable_radialAnnulus_test_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ → Ω → ℝ) (hXm : ∀ r : ℝ, Measurable fun ω => X r ω)
    {a b : ℝ} (hab : a < b) (φ : ℂ → ℝ) (hφ : Continuous φ)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun r => X r ω) (Icc a b)) :
    AEMeasurable (fun ω => ∫ z in radialAnnulus a b, φ z * X ‖z‖ ω) P := by
  refine aemeasurable_of_tendsto_metrizable_ae (f := fun (m : ℕ) (ω : Ω) =>
    ∑ k ∈ Finset.range m, X (a + (k : ℝ) * ((b - a) / (m : ℝ))) ω *
      ∫ z in radialCell a b m k, φ z) atTop (fun m => ?_) ?_
  · exact (Finset.measurable_sum _ fun k _ => (hXm _).mul_const _).aemeasurable
  · filter_upwards [hXc] with ω hω
    exact tendsto_radialRiemann hab φ hφ (fun r => X r ω) hω

/-- Truncation at zero (deterministic).  If `g` is continuous on `(0, b]` with the logarithmic
bound `|g r| ≤ C (1 + |log r|)` there, then the annulus integrals over `[b/(k+2), b)` converge
to the integral over the ball `B(0, b)`, by dominated convergence with the integrable majorant
`M C (1 + |log ‖z‖|)` on the ball (`integrableOn_one_add_abs_log_norm_closedBall`). -/
theorem tendsto_radialBallTruncation {b : ℝ} (hb : 0 < b) (φ : ℂ → ℝ) (hφ : Continuous φ)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Ioc 0 b)) (C : ℝ)
    (hC : ∀ r : ℝ, 0 < r → r ≤ b → |g r| ≤ C * (1 + |Real.log r|)) :
    Tendsto (fun k : ℕ => ∫ z in radialAnnulus (b / ((k : ℝ) + 2)) b, φ z * g ‖z‖) atTop
      (𝓝 (∫ z in ball (0 : ℂ) b, φ z * g ‖z‖)) := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) b).exists_bound_of_continuousOn
    hφ.continuousOn
  have hM0 : 0 ≤ max M₀ 0 := le_max_right _ _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hφM : ∀ z ∈ closedBall (0 : ℂ) b, ‖φ z‖ ≤ max M₀ 0 :=
    fun z hz => (hM₀ z hz).trans (le_max_left _ _)
  have hεpos : ∀ k : ℕ, 0 < b / ((k : ℝ) + 2) := fun k => div_pos hb (by positivity)
  have hεtop : Tendsto (fun k : ℕ => b / ((k : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have hgn : ∀ k : ℕ, ContinuousOn (fun z : ℂ => g ‖z‖) (radialAnnulus (b / ((k : ℝ) + 2)) b) :=
    fun k => hg.comp continuous_norm.continuousOn fun z hz =>
      ⟨lt_of_lt_of_le (hεpos k) hz.1, hz.2.le⟩
  have hmajor : IntegrableOn (fun z : ℂ => (max M₀ 0 * max C 0) * (1 + |Real.log ‖z‖|))
      (ball (0 : ℂ) b) :=
    Integrable.const_mul
      ((integrableOn_one_add_abs_log_norm_closedBall b).mono_set ball_subset_closedBall) _
  have hbound_int : Integrable ((ball (0 : ℂ) b).indicator
      (fun z : ℂ => (max M₀ 0 * max C 0) * (1 + |Real.log ‖z‖|))) :=
    IntegrableOn.integrable_indicator hmajor measurableSet_ball
  have hFmeas : ∀ k : ℕ, AEStronglyMeasurable
      ((radialAnnulus (b / ((k : ℝ) + 2)) b).indicator (fun z : ℂ => φ z * g ‖z‖)) volume := by
    intro k
    refine (aestronglyMeasurable_indicator_iff (measurableSet_radialAnnulus _ _)).2 ?_
    exact (hφ.continuousOn.mul (hgn k)).aestronglyMeasurable (measurableSet_radialAnnulus _ _)
  have hbd : ∀ (k : ℕ) (z : ℂ), ‖(radialAnnulus (b / ((k : ℝ) + 2)) b).indicator
      (fun z : ℂ => φ z * g ‖z‖) z‖ ≤ (ball (0 : ℂ) b).indicator
      (fun z : ℂ => (max M₀ 0 * max C 0) * (1 + |Real.log ‖z‖|)) z := by
    intro k z
    by_cases hz : z ∈ radialAnnulus (b / ((k : ℝ) + 2)) b
    · have hzb : z ∈ ball (0 : ℂ) b := mem_ball_zero_iff.2 hz.2
      rw [indicator_of_mem hz, indicator_of_mem hzb, norm_mul, mul_assoc]
      have hr0 : 0 < ‖z‖ := lt_of_lt_of_le (hεpos k) hz.1
      have hgz : ‖g ‖z‖‖ ≤ max C 0 * (1 + |Real.log ‖z‖|) := by
        rw [Real.norm_eq_abs]
        exact (hC ‖z‖ hr0 hz.2.le).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      exact mul_le_mul (hφM z (mem_closedBall_zero_iff.2 hz.2.le)) hgz (norm_nonneg _) hM0
    · rw [indicator_of_notMem hz, norm_zero]
      exact indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hM0 hC0) (by positivity)) z
  have hlim : ∀ z : ℂ, z ≠ 0 → Tendsto (fun k : ℕ =>
      (radialAnnulus (b / ((k : ℝ) + 2)) b).indicator (fun z : ℂ => φ z * g ‖z‖) z) atTop
      (𝓝 ((ball (0 : ℂ) b).indicator (fun z : ℂ => φ z * g ‖z‖) z)) := by
    intro z hz0
    have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    by_cases hzb : ‖z‖ < b
    · have hev : ∀ᶠ k : ℕ in atTop, b / ((k : ℝ) + 2) < ‖z‖ :=
        (tendsto_order.1 hεtop).2 ‖z‖ hpos
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with k hk
      rw [indicator_of_mem (mem_ball_zero_iff.2 hzb),
        indicator_of_mem (show z ∈ radialAnnulus (b / ((k : ℝ) + 2)) b from ⟨hk.le, hzb⟩)]
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
      dsimp only
      rw [indicator_of_notMem (fun h : z ∈ ball (0 : ℂ) b => hzb (mem_ball_zero_iff.1 h)),
        indicator_of_notMem (fun h : z ∈ radialAnnulus (b / ((k : ℝ) + 2)) b => hzb h.2)]
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun z : ℂ => (ball (0 : ℂ) b).indicator
      (fun z : ℂ => (max M₀ 0 * max C 0) * (1 + |Real.log ‖z‖|)) z)
    (F := fun (k : ℕ) (z : ℂ) =>
      (radialAnnulus (b / ((k : ℝ) + 2)) b).indicator (fun z : ℂ => φ z * g ‖z‖) z)
    (f := fun z : ℂ => (ball (0 : ℂ) b).indicator (fun z : ℂ => φ z * g ‖z‖) z)
    (fun k => hFmeas k) hbound_int (fun k => ae_of_all _ (hbd k)) (hae.mono fun z hz => hlim z hz)
  have e1 : ∀ k : ℕ, ∫ z, (radialAnnulus (b / ((k : ℝ) + 2)) b).indicator
      (fun z : ℂ => φ z * g ‖z‖) z = ∫ z in radialAnnulus (b / ((k : ℝ) + 2)) b, φ z * g ‖z‖ :=
    fun k => integral_indicator (measurableSet_radialAnnulus _ _)
  have e2 : ∫ z, (ball (0 : ℂ) b).indicator (fun z : ℂ => φ z * g ‖z‖) z
      = ∫ z in ball (0 : ℂ) b, φ z * g ‖z‖ := integral_indicator measurableSet_ball
  simp only [e1, e2] at hDCT
  exact hDCT

/-- Truncation at zero, almost surely.  If `r ↦ X r ω` is continuous on `(0, b]` and satisfies the
logarithmic bound `|X r ω| ≤ C_ω (1 + |log r|)` for almost every `ω`, then
`ω ↦ ∫_{B(0,b)} φ(z) X(|z|)(ω) dz` is a.e. measurable: it is the almost-sure limit of the
compact-annulus integrals over `[b/(k+2), b)`, which are measurable by
`aemeasurable_radialAnnulus_test_integral`. -/
theorem aemeasurable_ball_test_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (hXm : ∀ r : ℝ, Measurable fun ω => X r ω) {b : ℝ} (hb : 0 < b)
    (φ : ℂ → ℝ) (hφ : Continuous φ)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun r => X r ω) (Ioc 0 b))
    (hlog : ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ b → |X r ω| ≤ C * (1 + |Real.log r|)) :
    AEMeasurable (fun ω => ∫ z in ball (0 : ℂ) b, φ z * X ‖z‖ ω) P := by
  have hεpos : ∀ k : ℕ, 0 < b / ((k : ℝ) + 2) := fun k => div_pos hb (by positivity)
  have hεlt : ∀ k : ℕ, b / ((k : ℝ) + 2) < b := fun k =>
    div_lt_self hb (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  have hXc' : ∀ k : ℕ, ∀ᵐ ω ∂P, ContinuousOn (fun r => X r ω) (Icc (b / ((k : ℝ) + 2)) b) :=
    fun k => by
      filter_upwards [hXc] with ω hω
      exact hω.mono fun x hx => ⟨lt_of_lt_of_le (hεpos k) hx.1, hx.2⟩
  refine aemeasurable_of_tendsto_metrizable_ae (f := fun (k : ℕ) (ω : Ω) =>
    ∫ z in radialAnnulus (b / ((k : ℝ) + 2)) b, φ z * X ‖z‖ ω) atTop (fun k => ?_) ?_
  · exact aemeasurable_radialAnnulus_test_integral P X hXm (hεlt k) φ hφ (hXc' k)
  · filter_upwards [hXc, hlog] with ω hωc hωl
    obtain ⟨C, hC⟩ := hωl
    exact tendsto_radialBallTruncation hb φ hφ (fun r => X r ω) hωc C hC

/-- Radial path, test integral over a ball of radius `b ≤ 1` near the origin
(env-steps.tex:243-252, with `t = -log|z|`).  Given measurable radial evaluations `B t`, a.s.
continuity of `t ↦ B t ω`, and a.s. sublinear growth `B t ω / t → 0` (the inward branch),
the test integral `ω ↦ ∫_{B(0,b)} φ(z) B(-log|z|)(ω) dz` is a.e. measurable.  The sublinear
growth is a premise here (it is the Gaussian and Borel–Cantelli step of the paper); the
measurability of the integral is derived. -/
theorem aemeasurable_ball_radialPath {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ → Ω → ℝ) (hBm : ∀ t : ℝ, Measurable fun ω => B t ω)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (φ : ℂ → ℝ) (hφ : Continuous φ)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t : ℝ => B t ω)
    (hsub : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => B t ω / t) atTop (𝓝 0)) :
    AEMeasurable (fun ω => ∫ z in ball (0 : ℂ) b, φ z * B (-Real.log ‖z‖) ω) P := by
  have hlogc : ContinuousOn (fun r : ℝ => -Real.log r) (Ioc 0 b) :=
    (Real.continuousOn_log.mono fun r (hr : r ∈ Ioc 0 b) =>
      Set.mem_compl_singleton_iff.2 hr.1.ne').neg
  refine aemeasurable_ball_test_integral P (fun r ω => B (-Real.log r) ω)
    (fun r => hBm (-Real.log r)) hb φ hφ ?_ ?_
  · filter_upwards [hcont] with ω hω
    exact hω.comp_continuousOn hlogc
  · filter_upwards [hcont, hsub] with ω hωc hωs
    obtain ⟨C, -, hC⟩ := exists_abs_le_mul_one_add_of_sublinear hωc hωs
    refine ⟨C, fun r hr0 hr1 => ?_⟩
    have hlogr : Real.log r ≤ 0 := Real.log_nonpos hr0.le (hr1.trans hb1)
    have ht : 0 ≤ -Real.log r := by linarith
    show |B (-Real.log r) ω| ≤ C * (1 + |Real.log r|)
    rw [abs_of_nonpos hlogr]
    exact hC (-Real.log r) ht

/-- Radial path, test integral over a compact annulus `{a ≤ |z| < b}` with `0 < a`
(env-steps.tex:243-252).  Measurable radial evaluations and a.s. continuity of `t ↦ B t ω`
suffice; no growth premise is needed on a compact annulus. -/
theorem aemeasurable_radialAnnulus_radialPath {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ → Ω → ℝ) (hBm : ∀ t : ℝ, Measurable fun ω => B t ω)
    {a b : ℝ} (hab : a < b) (ha : 0 < a) (φ : ℂ → ℝ) (hφ : Continuous φ)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t : ℝ => B t ω) :
    AEMeasurable (fun ω => ∫ z in radialAnnulus a b, φ z * B (-Real.log ‖z‖) ω) P := by
  have hlogc : ContinuousOn (fun r : ℝ => -Real.log r) (Icc a b) :=
    (Real.continuousOn_log.mono fun r (hr : r ∈ Icc a b) =>
      Set.mem_compl_singleton_iff.2 (lt_of_lt_of_le ha hr.1).ne').neg
  refine aemeasurable_radialAnnulus_test_integral P (fun r ω => B (-Real.log r) ω)
    (fun r => hBm (-Real.log r)) hab φ hφ ?_
  filter_upwards [hcont] with ω hω
  exact hω.comp_continuousOn hlogc

end MatedCRT.Sec1
