import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceSteps
import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceLocalPath
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaApprox
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaGood
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.ConeLaw
import LatticeProb.LQG.AreaCurveMassMeasurable

/-!
# Local reconstruction of the area measure of a cone on an annulus

For `0 < δ` and `M` let `V = {δ < |z| < M}` (`offsetOuterAnnulus δ M`) and `δ₀ = δ / 2`. The thickening
`thickOpen V δ₀` lies in `{δ / 2 < |z| < M + δ / 2}`. On this set the radial function `z ↦ A_{-log |z|}` of a cone
field `coneField X A` is read off two paths: for `t ≥ 0` the path `A_t` and for `t < 0` the path
`s ↦ A_{-s} + Q s`. The field `reconField γ δ M (L, I, O) = L + ofFunC (reconProfile …)` is built from a lateral
part `L` and two paths `I, O` with the dyadic regularization `regPath` (jointly measurable in the paths for the
product σ-algebra), so that it is a measurable function of `(L, I, O)`.

The area measure of the field restricted to `V` is obtained as a measurable function of the field by the locality of
the LQG area measure (Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011);
Gwynne–Miller–Sheffield, arXiv:1705.11161, §2.3.1): the dyadic approximations `lqgAreaApprox γ h k` at scales below the
thickening width depend only on `h` on the thickening, and the vague limit is decoded by the measurable
decoder `vagueLimitOrZero` of Lattice-Probability applied to the approximations cut off by a continuous partition
of unity `∑ₙ ψₙ = 1_V` with compactly supported `ψₙ ≤ 1_V`, then summed over `n`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT

/-! ### The partition of unity of the annulus -/

/-- The continuous exhaustion `min 1 (max 0 (n d(z, Vᶜ) - 1))` of `1_V`. -/
noncomputable def annulusCutoff (V : Set ℂ) (n : ℕ) (z : ℂ) : ℝ :=
  min 1 (max 0 ((n : ℝ) * infDist z Vᶜ - 1))

/-- The partition of unity `ψₙ = cutoff (n+1) - cutoff n`. -/
noncomputable def annulusPOU (V : Set ℂ) (n : ℕ) (z : ℂ) : ℝ :=
  annulusCutoff V (n + 1) z - annulusCutoff V n z

theorem continuous_annulusCutoff (V : Set ℂ) (n : ℕ) : Continuous (annulusCutoff V n) := by
  unfold annulusCutoff
  fun_prop

theorem annulusCutoff_nonneg (V : Set ℂ) (n : ℕ) (z : ℂ) : 0 ≤ annulusCutoff V n z := by
  unfold annulusCutoff
  exact le_min zero_le_one (le_max_left _ _)

theorem annulusCutoff_le_one (V : Set ℂ) (n : ℕ) (z : ℂ) : annulusCutoff V n z ≤ 1 :=
  min_le_left _ _

theorem annulusCutoff_mono (V : Set ℂ) (z : ℂ) : Monotone fun n => annulusCutoff V n z := by
  refine monotone_nat_of_le_succ fun n => ?_
  unfold annulusCutoff
  have hd : 0 ≤ infDist z Vᶜ := infDist_nonneg
  refine min_le_min_left _ (max_le_max_left _ ?_)
  push_cast
  nlinarith

theorem annulusCutoff_zero (V : Set ℂ) (z : ℂ) : annulusCutoff V 0 z = 0 := by
  simp [annulusCutoff]

theorem annulusCutoff_of_notMem {V : Set ℂ} {z : ℂ} (hz : z ∉ V) (n : ℕ) : annulusCutoff V n z = 0 := by
  have : infDist z Vᶜ = 0 := infDist_zero_of_mem (by simpa using hz)
  simp [annulusCutoff, this]

theorem annulusPOU_nonneg (V : Set ℂ) (n : ℕ) (z : ℂ) : 0 ≤ annulusPOU V n z :=
  sub_nonneg.2 (annulusCutoff_mono V z (Nat.le_succ n))

theorem annulusPOU_le_one (V : Set ℂ) (n : ℕ) (z : ℂ) : annulusPOU V n z ≤ 1 := by
  unfold annulusPOU
  linarith [annulusCutoff_le_one V (n + 1) z, annulusCutoff_nonneg V n z]

theorem continuous_annulusPOU (V : Set ℂ) (n : ℕ) : Continuous (annulusPOU V n) :=
  (continuous_annulusCutoff V (n + 1)).sub (continuous_annulusCutoff V n)

theorem annulusPOU_of_notMem {V : Set ℂ} {z : ℂ} (hz : z ∉ V) (n : ℕ) : annulusPOU V n z = 0 := by
  simp [annulusPOU, annulusCutoff_of_notMem hz]

theorem nonempty_compl_of_isBounded {V : Set ℂ} (hVb : Bornology.IsBounded V) : (Vᶜ).Nonempty := by
  obtain ⟨R, hR⟩ := hVb.subset_closedBall (0 : ℂ)
  refine ⟨((|R| + 1 : ℝ) : ℂ), fun h => ?_⟩
  have := mem_closedBall_zero_iff.1 (hR h)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
  linarith [le_abs_self R]

theorem tsum_ofReal_annulusPOU {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (z : ℂ) :
    ∑' n, ENNReal.ofReal (annulusPOU V n z) = V.indicator 1 z := by
  by_cases hz : z ∈ V
  · rw [Set.indicator_of_mem hz, Pi.one_apply]
    have hne : (Vᶜ).Nonempty := nonempty_compl_of_isBounded hVb
    have hd : 0 < infDist z Vᶜ :=
      ((isClosed_compl_iff.2 hV).notMem_iff_infDist_pos hne).1 (by simpa using hz)
    obtain ⟨N, hN⟩ := exists_nat_ge (2 / infDist z Vᶜ)
    rw [ENNReal.tsum_eq_iSup_nat]
    have hsum : ∀ m, ∑ n ∈ Finset.range m, ENNReal.ofReal (annulusPOU V n z) =
        ENNReal.ofReal (annulusCutoff V m z) := by
      intro m
      rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => annulusPOU_nonneg V n z)]
      congr 1
      simp only [annulusPOU]
      rw [Finset.sum_range_sub (fun n => annulusCutoff V n z), annulusCutoff_zero, sub_zero]
    simp_rw [hsum]
    refine le_antisymm (iSup_le fun m => ENNReal.ofReal_le_one.2 (annulusCutoff_le_one V m z)) ?_
    refine le_iSup_of_le N ?_
    have h1 : annulusCutoff V N z = 1 := by
      have : 2 ≤ (N : ℝ) * infDist z Vᶜ := by
        have := (div_le_iff₀ hd).1 hN
        linarith
      simp only [annulusCutoff]
      rw [max_eq_right (by linarith), min_eq_left (by linarith)]
    rw [h1, ENNReal.ofReal_one]
  · rw [Set.indicator_of_notMem hz]
    simp [annulusPOU_of_notMem hz]

/-! ### Vague limits and densities -/

theorem integral_withDensity_ofReal (ν : Measure ℂ) {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (g : ℂ → ℝ) :
    ∫ z, g z ∂(ν.withDensity fun z => ENNReal.ofReal (ψ z)) = ∫ z, ψ z * g z ∂ν := by
  rw [integral_withDensity_eq_integral_toReal_smul hψ.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp [ENNReal.toReal_ofReal (hψ0 _)]

theorem withDensity_ofReal_apply_le (ν : Measure ℂ) {ψ : ℂ → ℝ} (hψ1 : ∀ z, ψ z ≤ 1) {s : Set ℂ}
    (hs : MeasurableSet s) : (ν.withDensity fun z => ENNReal.ofReal (ψ z)) s ≤ ν s := by
  rw [withDensity_apply _ hs]
  calc ∫⁻ z in s, ENNReal.ofReal (ψ z) ∂ν ≤ ∫⁻ _ in s, 1 ∂ν :=
        lintegral_mono fun z => ENNReal.ofReal_le_one.2 (hψ1 z)
    _ = ν s := by simp

/-- Multiplying vaguely convergent measures by a continuous compactly supported density with values in `[0, 1]`
gives vaguely convergent measures. -/
theorem isVagueLimitC_withDensity {μs : ℕ → Measure ℂ} {μ : Measure ℂ} (h : IsVagueLimitC μs μ)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψ0 : ∀ z, 0 ≤ ψ z) (hψ1 : ∀ z, ψ z ≤ 1) :
    IsVagueLimitC (fun k => (μs k).withDensity fun z => ENNReal.ofReal (ψ z))
      (μ.withDensity fun z => ENNReal.ofReal (ψ z)) := by
  refine ⟨fun K hK => (withDensity_ofReal_apply_le μ hψ1 hK.measurableSet).trans_lt (h.1 K hK), ?_⟩
  intro g hg hgc
  simp_rw [integral_withDensity_ofReal _ hψ hψ0]
  exact h.2 (fun z => ψ z * g z) (hψ.mul hg) (hgc.mul_left)

/-! ### The reconstructed field -/

/-- The annulus `{δ / 2 < |z| < M + δ / 2}`, which contains the `δ / 2`-thickening of `{δ < |z| < M}`. -/
def thickAnnulus (δ M : ℝ) : Set ℂ := {z | δ / 2 < ‖z‖ ∧ ‖z‖ < M + δ / 2}

theorem measurableSet_thickAnnulus (δ M : ℝ) : MeasurableSet (thickAnnulus δ M) :=
  (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)

/-- The open annulus `{δ < |z| < M}` as an open set. -/
def annulusOpen (δ M : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨offsetOuterAnnulus δ M, isOpen_ball.sdiff isClosed_closedBall⟩

theorem isBounded_offsetOuterAnnulus (δ M : ℝ) : Bornology.IsBounded (offsetOuterAnnulus δ M) :=
  (Metric.isBounded_ball (x := (0 : ℂ)) (r := M)).subset Set.sdiff_subset

theorem thickOpen_subset_thickAnnulus (δ M : ℝ) :
    ((MatedCRTHarmonic.GMS4c.thickOpen (annulusOpen δ M) (δ / 2) : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆
      thickAnnulus δ M := by
  intro z hz
  obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.1 hz
  have hy' : y ∈ offsetOuterAnnulus δ M := hy
  obtain ⟨hy1, hy2⟩ := hy'
  rw [mem_ball_zero_iff] at hy1
  rw [mem_closedBall_zero_iff, not_le] at hy2
  have h1 := abs_norm_sub_norm_le z y
  rw [← dist_eq_norm] at h1
  have h2 := abs_le.1 h1
  exact ⟨by linarith [h2.1, hzy], by linarith [h2.2, hzy]⟩

/-- The radial value at `t`, read from the regularized paths: `p.1` for `t ≥ 0`, and `p.2 (-t) + Q t` for `t < 0`. -/
noncomputable def reconRadial (γ : ℝ) (p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) (t : ℝ) : ℝ :=
  if 0 ≤ t then regPath p.1 t.toNNReal else regPath p.2 (-t).toNNReal + lqgQ γ * t

/-- The radial profile `z ↦ A_{-log |z|}` on the annulus `thickAnnulus δ M`, zero elsewhere. -/
noncomputable def reconProfile (γ δ M : ℝ) (p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) (z : ℂ) : ℝ :=
  (thickAnnulus δ M).indicator (fun z : ℂ => reconRadial γ p (-Real.log ‖z‖)) z

/-- The field reconstructed from a lateral part and two paths: lateral part plus the radial profile. -/
noncomputable def reconField (γ δ M : ℝ) (x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) : LQGMetric.DistC :=
  x.1 + MoTPort.ofFunC (reconProfile γ δ M x.2)

theorem measurable_reconRadial (γ : ℝ) :
    Measurable fun q : ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℝ => reconRadial γ q.1 q.2 := by
  unfold reconRadial
  refine Measurable.ite (measurableSet_le measurable_const measurable_snd) ?_ ?_
  · exact measurable_regPath.comp
      ((measurable_fst.comp measurable_fst).prodMk (measurable_real_toNNReal.comp measurable_snd))
  · exact (measurable_regPath.comp
      ((measurable_snd.comp measurable_fst).prodMk (measurable_real_toNNReal.comp measurable_snd.neg))).add
      (measurable_snd.const_mul _)

theorem measurable_reconProfile (γ δ M : ℝ) :
    Measurable fun q : ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℂ => reconProfile γ δ M q.1 q.2 := by
  have e : (fun q : ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℂ => reconProfile γ δ M q.1 q.2) =
      {q : ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℂ | q.2 ∈ thickAnnulus δ M}.indicator
        fun q => reconRadial γ q.1 (-Real.log ‖q.2‖) := by
    funext q
    by_cases hq : q.2 ∈ thickAnnulus δ M
    · have hq' : q ∈ {q : ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℂ | q.2 ∈ thickAnnulus δ M} := hq
      rw [Set.indicator_of_mem hq']
      simp only [reconProfile, Set.indicator_of_mem hq]
    · have hq' : q ∉ {q : ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℂ | q.2 ∈ thickAnnulus δ M} := hq
      rw [Set.indicator_of_notMem hq']
      simp only [reconProfile, Set.indicator_of_notMem hq]
  rw [e]
  refine Measurable.indicator ?_ (measurable_snd (measurableSet_thickAnnulus δ M))
  exact (measurable_reconRadial γ).comp
    (measurable_fst.prodMk (Real.measurable_log.comp (measurable_norm.comp measurable_snd)).neg)

theorem measurable_reconField (γ δ M : ℝ) : Measurable (reconField γ δ M) := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  have e : (fun x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => reconField γ δ M x φ) = fun x =>
      x.1 φ + MoTPort.ofFunC (reconProfile γ δ M x.2) φ := by
    funext x
    simp only [reconField, add_apply]
  have h1 : Measurable fun x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => x.1 φ :=
    (LQGMetric.measurable_distOn_apply φ).comp measurable_fst
  have hF : Measurable fun p : (LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℂ =>
      reconProfile γ δ M p.1.2 p.2 :=
    (measurable_reconProfile γ δ M).comp
      (f := fun p : (LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℂ => (p.1.2, p.2))
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have h2 : Measurable fun x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
      MoTPort.ofFunC (reconProfile γ δ M x.2) φ :=
    MoTPort.ConeMeas2.measurable_ofFunC_apply
      (F := fun (x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) z => reconProfile γ δ M x.2 z) hF φ
  rw [e]
  exact h1.add h2

/-! ### The cut-off area approximations and their decoded limit -/

/-- The density of the `n`-th cut-off area approximation of the reconstructed field at the dyadic scale `2^{-k}`. -/
noncomputable def reconDensity (γ δ M : ℝ) (n k : ℕ) (x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ))
    (z : ℂ) : ℝ :=
  annulusPOU (offsetOuterAnnulus δ M) n z *
    (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * LQGMetric.circleAvg (reconField γ δ M x) (dyadicScale k) z))

theorem reconDensity_nonneg (γ δ M : ℝ) (n k : ℕ) (x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) (z : ℂ) :
    0 ≤ reconDensity γ δ M n k x z :=
  mul_nonneg (annulusPOU_nonneg _ n z) (mul_nonneg (Real.rpow_nonneg (by
    unfold dyadicScale; positivity) _) (Real.exp_pos _).le)

theorem measurable_reconDensity (γ δ M : ℝ) (n k : ℕ) :
    Measurable fun q : (LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℂ => reconDensity γ δ M n k q.1 q.2 := by
  have h1 : Measurable fun q : (LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℂ =>
      LQGMetric.circleAvg (reconField γ δ M q.1) (dyadicScale k) q.2 :=
    LQGMetric.measurable_circleAvg.comp (f := fun q : (LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℂ =>
      (reconField γ δ M q.1, dyadicScale k, q.2))
      (((measurable_reconField γ δ M).comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  exact ((continuous_annulusPOU _ n).measurable.comp measurable_snd).mul
    (measurable_const.mul (Real.measurable_exp.comp (h1.const_mul γ)))

/-- The `n`-th cut-off area approximation of the reconstructed field at the dyadic scale `2^{-k}`. -/
noncomputable def reconApprox (γ δ M : ℝ) (n k : ℕ) (x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) :
    Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (reconDensity γ δ M n k x z)

open Classical in
/-- `reconApprox` when it has finite total mass, and zero otherwise. -/
noncomputable def reconApproxFin (γ δ M : ℝ) (n k : ℕ) (x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) :
    Measure ℂ :=
  if reconApprox γ δ M n k x univ < ⊤ then reconApprox γ δ M n k x else 0

open Classical in
/-- The reconstructed area measure on `{δ < |z| < M}`: the sum over `n` of the decoded vague limits of the
cut-off approximations. -/
noncomputable def reconMeasure (γ δ M : ℝ) (x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) : Measure ℂ :=
  Measure.sum fun n => LatticeProb.VagueLimit.vagueLimitOrZero fun k => reconApproxFin γ δ M n k x

instance isFiniteMeasureOnCompacts_reconApproxFin (γ δ M : ℝ) (n k : ℕ)
    (x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) : IsFiniteMeasureOnCompacts (reconApproxFin γ δ M n k x) := by
  unfold reconApproxFin
  split_ifs with h
  · have : IsFiniteMeasure (reconApprox γ δ M n k x) := ⟨h⟩
    infer_instance
  · infer_instance

theorem measurable_mass_reconApprox (γ δ M : ℝ) (n k : ℕ) :
    Measurable fun x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => reconApprox γ δ M n k x univ := by
  simp_rw [reconApprox, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact Measurable.lintegral_prod_right'
    (f := fun q : (LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × ℂ =>
      ENNReal.ofReal (reconDensity γ δ M n k q.1 q.2))
    (ENNReal.measurable_ofReal.comp (measurable_reconDensity γ δ M n k))

theorem measurable_integral_reconApproxFin (γ δ M : ℝ) (n k : ℕ) {f : ℂ → ℝ} (hf : Continuous f) :
    Measurable fun x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => ∫ z, f z ∂(reconApproxFin γ δ M n k x) := by
  classical
  have e : (fun x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => ∫ z, f z ∂(reconApproxFin γ δ M n k x)) =
      fun x => if reconApprox γ δ M n k x univ < ⊤ then ∫ z, f z ∂(reconApprox γ δ M n k x) else 0 := by
    funext x
    unfold reconApproxFin
    split_ifs <;> simp
  rw [e]
  refine Measurable.ite (measurableSet_lt (measurable_mass_reconApprox γ δ M n k) measurable_const) ?_
    measurable_const
  exact LatticeProb.LQG.measurable_integral_withDensity_ofReal_uncurry_param
    (d := fun x z => reconDensity γ δ M n k x z) (measurable_reconDensity γ δ M n k)
    (reconDensity_nonneg γ δ M n k) (f := fun _ z => f z) (hf.measurable.comp measurable_snd)

/-- **Measurability of the decoded area measure.** -/
theorem measurable_reconMeasure (γ δ M : ℝ) : Measurable (reconMeasure γ δ M) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [reconMeasure, Measure.sum_apply _ hs]
  refine Measurable.tsum fun n => ?_
  have hm := LatticeProb.VagueLimit.measurable_vagueLimitOrZero
    (m := fun k x => reconApproxFin γ δ M n k x) (fun k x => inferInstance)
    (fun k f hf _ => measurable_integral_reconApproxFin γ δ M n k hf)
  exact (Measure.measurable_coe hs).comp hm

/-! ### Identification of the decoded measure -/

/-- The circle averages at a point of `V` at a radius below `δ` only depend on the field on the
`δ`-thickening of `V`. -/
theorem circleAvg_eq_of_restrictTo_eq {V : TopologicalSpace.Opens ℂ} {δ ρ : ℝ} (hρ : 0 < ρ) (hρδ : ρ < δ)
    {h h' : LQGMetric.DistC}
    (hloc : LQGMetric.restrictTo (MatedCRTHarmonic.GMS4c.thickOpen V δ) h =
      LQGMetric.restrictTo (MatedCRTHarmonic.GMS4c.thickOpen V δ) h') {z : ℂ} (hz : z ∈ V) :
    LQGMetric.circleAvg h ρ z = LQGMetric.circleAvg h' ρ z := by
  have hball := MatedCRTHarmonic.GMS4c.closedBall_subset_thickOpen hρδ hz
  have key : ∀ g : LQGMetric.DistC, MatedCRTHarmonic.GMS4c.localCircleProcess
      (MatedCRTHarmonic.GMS4c.thickOpen V δ) (LQGMetric.restrictTo (MatedCRTHarmonic.GMS4c.thickOpen V δ) g)
      ρ z = LQGMetric.circleAvg g ρ z := by
    intro g
    have := congrFun (congrFun (MatedCRTHarmonic.GMS4c.localCircleProcess_restrictTo
      (MatedCRTHarmonic.GMS4c.thickOpen V δ) g) ρ) z
    simpa [MatedCRTHarmonic.MatedCRT.restrictCircles, hρ, hball] using this
  rw [← key h, ← key h', hloc]

theorem withDensity_reconApprox {γ δ M : ℝ} (n k : ℕ) (x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ))
    {h : LQGMetric.DistC}
    (hcirc : ∀ z ∈ offsetOuterAnnulus δ M,
      LQGMetric.circleAvg (reconField γ δ M x) (dyadicScale k) z =
        LQGMetric.circleAvg h (dyadicScale k) z) :
    reconApprox γ δ M n k x =
      (lqgAreaApprox γ h k).withDensity fun z => ENNReal.ofReal (annulusPOU (offsetOuterAnnulus δ M) n z) := by
  have hm : Measurable fun z : ℂ => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * LQGMetric.circleAvg h (dyadicScale k) z)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      ((LQGMetric.measurable_circleAvg.comp (f := fun z : ℂ => (h, dyadicScale k, z))
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).const_mul γ)))
  have hψ : Measurable fun z : ℂ => ENNReal.ofReal (annulusPOU (offsetOuterAnnulus δ M) n z) :=
    ENNReal.measurable_ofReal.comp (continuous_annulusPOU _ n).measurable
  unfold lqgAreaApprox
  rw [← withDensity_mul _ hm hψ]
  unfold reconApprox
  congr 1
  funext z
  simp only [Pi.mul_apply, reconDensity]
  by_cases hz : z ∈ offsetOuterAnnulus δ M
  · rw [hcirc z hz, ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by
      unfold dyadicScale; positivity) _) (Real.exp_pos _).le), mul_comm]
  · simp [annulusPOU_of_notMem hz]

/-- **The decoded measure.** If the dyadic area approximations of `h` converge vaguely to `μ`, are finite on
`closure V`, and the reconstructed field has the same circle averages as `h` on `V` at all fine scales, then the
decoded measure of the reconstructed field is `μ.restrict V`. -/
theorem reconMeasure_eq {γ δ M : ℝ} {x : LQGMetric.DistC × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)} {h : LQGMetric.DistC}
    {μ : Measure ℂ} (hμ : IsVagueLimitC (lqgAreaApprox γ h) μ)
    (hfin : ∀ᶠ k : ℕ in atTop, lqgAreaApprox γ h k (closure (offsetOuterAnnulus δ M)) < ⊤)
    (hcirc : ∀ᶠ k : ℕ in atTop, ∀ z ∈ offsetOuterAnnulus δ M,
      LQGMetric.circleAvg (reconField γ δ M x) (dyadicScale k) z =
        LQGMetric.circleAvg h (dyadicScale k) z) :
    reconMeasure γ δ M x = μ.restrict (offsetOuterAnnulus δ M) := by
  classical
  set V := offsetOuterAnnulus δ M with hV
  have hVo : IsOpen V := isOpen_ball.sdiff isClosed_closedBall
  have hVb : Bornology.IsBounded V := isBounded_offsetOuterAnnulus δ M
  have step : ∀ n, LatticeProb.VagueLimit.vagueLimitOrZero (fun k => reconApproxFin γ δ M n k x) =
      μ.withDensity fun z => ENNReal.ofReal (annulusPOU V n z) := by
    intro n
    set ψ := annulusPOU V n with hψdef
    have hlim := isVagueLimitC_withDensity hμ (continuous_annulusPOU V n) (annulusPOU_nonneg V n)
      (annulusPOU_le_one V n)
    have hev : ∀ᶠ k : ℕ in atTop, reconApproxFin γ δ M n k x =
        (lqgAreaApprox γ h k).withDensity fun z => ENNReal.ofReal (ψ z) := by
      filter_upwards [hfin, hcirc] with k hk hc
      have hE := withDensity_reconApprox (δ := δ) (M := M) n k x hc
      have hlt : reconApprox γ δ M n k x univ < ⊤ := by
        rw [hE, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        calc ∫⁻ z, ENNReal.ofReal (ψ z) ∂lqgAreaApprox γ h k
            ≤ ∫⁻ z, (V.indicator (1 : ℂ → ℝ≥0∞)) z ∂lqgAreaApprox γ h k := by
              refine lintegral_mono fun z => ?_
              by_cases hz : z ∈ V
              · simp only [Set.indicator_of_mem hz, Pi.one_apply]
                exact ENNReal.ofReal_le_one.2 (annulusPOU_le_one V n z)
              · simp [Set.indicator_of_notMem hz, annulusPOU_of_notMem hz, hψdef]
          _ = lqgAreaApprox γ h k V := lintegral_indicator_one hVo.measurableSet
          _ < ⊤ := lt_of_le_of_lt (measure_mono subset_closure) hk
      simp only [reconApproxFin, hlt, ↓reduceIte]
      exact hE
    have hlim' : IsVagueLimitC (fun k => reconApproxFin γ δ M n k x)
        (μ.withDensity fun z => ENNReal.ofReal (ψ z)) := by
      refine ⟨hlim.1, fun g hg hgc => (hlim.2 g hg hgc).congr' ?_⟩
      filter_upwards [hev] with k hk
      rw [hk]
    have hex : ∃ ν, LatticeProb.VagueLimit.IsVagueLimit (fun k => reconApproxFin γ δ M n k x) ν :=
      ⟨_, hlim'⟩
    have h2 := LatticeProb.VagueLimit.isVagueLimit_vagueLimitOrZero hex
    have : IsFiniteMeasureOnCompacts (LatticeProb.VagueLimit.vagueLimitOrZero
        (fun k => reconApproxFin γ δ M n k x)) := inferInstance
    have : IsFiniteMeasureOnCompacts (μ.withDensity fun z => ENNReal.ofReal (ψ z)) := ⟨hlim'.1⟩
    refine Measure.ext_of_integral_eq_on_compactlySupported fun g => ?_
    exact tendsto_nhds_unique (h2.2 g g.continuous g.hasCompactSupport)
      (hlim'.2 g g.continuous g.hasCompactSupport)
  unfold reconMeasure
  simp_rw [step]
  rw [← withDensity_tsum (μ := μ) (f := fun n z => ENNReal.ofReal (annulusPOU V n z))
    (fun n => ENNReal.measurable_ofReal.comp (continuous_annulusPOU V n).measurable)]
  have : (∑' n, fun z => ENNReal.ofReal (annulusPOU V n z)) = V.indicator 1 := by
    funext z
    rw [ENNReal.tsum_apply]
    exact tsum_ofReal_annulusPOU hVo hVb z
  rw [this, withDensity_indicator_one hVo.measurableSet]

end MatedCRT
