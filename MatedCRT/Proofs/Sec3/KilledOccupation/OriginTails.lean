import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec8.InteriorRadialIndependence
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleGaussianMoment
import HarmonicBalls.FirstPass.S11x.CircleVariance
import HarmonicBalls.Proofs.Sec11.SingularCompactNull

/-!
# Regularized origin tails (Appendix B, `lem:occ-tails`)

Printed statement: `paper/appendix-occupation-C16.tex:296-310`, the same claim in the corrected draft as
`paper/idla_mated_crt-corrected.tex:4815-4826` (`lem:tails`, with `p` and `κ` as printed there).
Printed proof: `paper/appendix-occupation-C16.tex:311-368`.

Field. `hc ω r z` are the circle averages of a whole-plane GFF `h^ℂ` (`HarmonicBalls.IsWholePlaneGFF`). The cone field
is `h = h^ℂ − γ log|·|` (eq:gff, `paper/idla_mated_crt-corrected.tex:443`), with circle averages
`h_ε(x) = HarmonicBalls.fieldCircleAverage γ (hc ω) ε x`.

Proof structure. The only input is `IsWholePlaneGFF`; no joint measurability of the field is assumed.
* Pathwise change of variables (eq:occ-regweight, eq:occ-scale): with `N = hc ω R 0` and `R = 2s` on the annulus,
  `R = 8ε` on the core, the weighted mass is `e^{γN} ∫ ρ e^{γ(h_ε(x) − N)} dx` (`weightedMass_eq`).
* Gaussian input (eq:occ-field, eq:occ-var): for `‖w‖ + ε ≤ R`, `N` is independent of `hc ε w − N`, because the
  covariance vanishes (`indepFun_shift`, Mathlib `IsGaussianProcess.indepFun_of_covariance_eq_zero`), and
  `E e^{t(hc ε w − N)} = e^{t²(log R − log ε)/2}` (`lintegral_exp_shift`).
* Dyadic discretization of the field integral over countably many cells, Fatou's lemma and dominated convergence
  on the a.e. continuous circle process (`moment_bound`), and Jensen's inequality for `p ∈ (0,1]`
  (`lintegral_rpow_le_rpow_lintegral`).
* Annulus estimate (printed `:335-346`, `annulus_estimate`) and core estimate (printed `:347-358`, `core_estimate`),
  then the dyadic summation (printed `:359-368`) in `origin_tail_moment`.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MatedCRT.KilledOccupation

/-- The annulus `A_s = {s/2 ≤ |x| < s}` (printed `A_s = {s/2 < |x| ≤ s}`, up to a Lebesgue-null set). -/
def annulus (s : ℝ) : Set ℂ := {x : ℂ | s / 2 ≤ ‖x‖ ∧ ‖x‖ < s}

/-- The regularized LQG density `μ_ε(dx) = ε^{γ²/2} e^{γ h_ε(x)} dx` at `x` (printed `:296`), with circle averages
`hc` of the whole-plane GFF and `h_ε(x) = HarmonicBalls.fieldCircleAverage γ hc ε x`. -/
def regDensity (γ ε : ℝ) (hc : ℝ → ℂ → ℝ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * HarmonicBalls.fieldCircleAverage γ hc ε x))

/-- The weighted mass `∫_S (1 + log(1/|x|)) μ_ε(dx)` of the printed lemma. -/
def weightedMass (γ ε : ℝ) (hc : ℝ → ℂ → ℝ) (S : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ x in S, ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) * regDensity γ ε hc x

lemma measurableSet_annulus (s : ℝ) : MeasurableSet (annulus s) :=
  (measurableSet_le measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)

lemma ball_eq_union_annulus {r : ℝ} (hr : 0 < r) :
    ball (0 : ℂ) r = ball (0 : ℂ) (r / 2) ∪ annulus r := by
  ext x
  simp only [mem_ball, dist_zero_right, mem_union, annulus, Set.mem_ofPred_eq]
  constructor
  · intro h
    by_cases h2 : r / 2 ≤ ‖x‖
    · exact Or.inr ⟨h2, h⟩
    · exact Or.inl (not_le.mp h2)
  · rintro (h | h)
    · linarith
    · linarith [h.2]

lemma disjoint_ball_annulus {r : ℝ} : Disjoint (ball (0 : ℂ) (r / 2)) (annulus r) := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [mem_ball, dist_zero_right] at hx
  exact absurd hy.1 (not_le.mpr hx)

lemma weightedMass_ball_split (γ ε : ℝ) (hc : ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r) :
    weightedMass γ ε hc (ball 0 r) =
      weightedMass γ ε hc (ball 0 (r / 2)) + weightedMass γ ε hc (annulus r) := by
  unfold weightedMass
  rw [ball_eq_union_annulus hr, lintegral_union (measurableSet_annulus r) disjoint_ball_annulus]

/-- Dyadic decomposition: `B_a` is `B_{a 2^{-J}}` together with the annuli `A_{a 2^{-j}}`, `j < J`. -/
lemma weightedMass_dyadic (γ ε a : ℝ) (hc : ℝ → ℂ → ℝ) (ha : 0 < a) (J : ℕ) :
    weightedMass γ ε hc (ball 0 a) =
      weightedMass γ ε hc (ball 0 (a * (1 / 2) ^ J)) +
        ∑ j ∈ Finset.range J, weightedMass γ ε hc (annulus (a * (1 / 2) ^ j)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hr : 0 < a * (1 / 2) ^ J := by positivity
    have h := weightedMass_ball_split γ ε hc hr
    have e : a * (1 / 2) ^ J / 2 = a * (1 / 2) ^ (J + 1) := by rw [pow_succ]; ring
    rw [e] at h
    rw [ih, h, Finset.sum_range_succ]
    ring

/-- Subadditivity of `x ↦ x^p` for `0 < p ≤ 1` over a finite sum. -/
lemma rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (x : ι → ℝ≥0∞) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, x i) ^ p ≤ ∑ i ∈ s, x i ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hp0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1).trans (add_le_add le_rfl ih)

/-- Sum of nonnegative bounds over a dyadic partition: the finite sum plus one more term is bounded by the
`tsum`. -/
lemma sum_ofReal_le_ofReal_tsum (J : ℕ) (u : ℕ → ℝ) (hu : ∀ j, 0 ≤ u j) (hs : Summable u) :
    (∑ j ∈ Finset.range J, ENNReal.ofReal (u j)) + ENNReal.ofReal (u J) ≤ ENNReal.ofReal (∑' j, u j) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hu j), ← ENNReal.ofReal_add
    (Finset.sum_nonneg (fun j _ => hu j)) (hu J)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.sum_range_succ]
  exact hs.sum_le_tsum _ (fun j _ => hu j)


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Exponential moment of a centred Gaussian variable: `E e^{tX} = e^{t² Var X / 2}` (lintegral form). -/
lemma lintegral_ofReal_exp_gaussian {X : Ω → ℝ} (hXm : Measurable X) (hX : HasGaussianLaw X P)
    (hm : ∫ ω, X ω ∂P = 0) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂P = ENNReal.ofReal (Real.exp (t ^ 2 * Var[X; P] / 2)) := by
  have hmap := hX.map_eq_gaussianReal
  rw [hm] at hmap
  have hvar : (Var[X; P].toNNReal : ℝ) = Var[X; P] := Real.coe_toNNReal _ (variance_nonneg _ _)
  have h1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂P
      = ∫⁻ x, ENNReal.ofReal (Real.exp (t * x)) ∂(P.map X) :=
    (lintegral_map (f := fun x => ENNReal.ofReal (Real.exp (t * x))) (by fun_prop) hXm).symm
  rw [h1, hmap]
  have hint := integrable_exp_mul_gaussianReal (μ := 0) (v := Var[X; P].toNNReal) t
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  congr 1
  have hmgf := congrFun (mgf_id_gaussianReal (μ := 0) (v := Var[X; P].toNNReal)) t
  simp only [mgf, id, zero_mul, zero_add, hvar] at hmgf
  rw [hmgf]
  congr 1
  ring

/-- Covariance of the circle average of radius `ε` centred at `w` with the circle average of radius `R` at `0`,
when the first circle lies in the disk of radius `R`. Uses `circleAverage_wholePlaneCov_inside`. -/
lemma cov_circle_zero {hC : Ω → (ℂ → ℝ) → ℝ} {hc : Ω → ℝ → ℂ → ℝ} (h : HarmonicBalls.IsWholePlaneGFF P hC hc)
    {R ε : ℝ} {w : ℂ} (hR : 0 < R) (hR1 : R ≤ 1) (hε : 0 < ε) (hw : ‖w‖ + ε ≤ R) :
    cov[fun ω => hc ω ε w, fun ω => hc ω R 0; P] = -Real.log R := by
  refine Eq.trans (h.covariance_eq (.circle ε w) (.circle R 0) hε hR) ?_
  show Real.circleAverage (fun x => Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) 0 R) w ε = _
  rw [Real.circleAverage_congr_sphere (f₂ := fun _ => -Real.log R) ?_, Real.circleAverage_const]
  intro x hx
  have hxw : ‖x - w‖ = ε := by
    rw [mem_sphere, dist_eq_norm] at hx
    simpa [abs_of_pos hε] using hx
  have hxR : ‖x‖ ≤ R := by
    have := norm_le_norm_add_norm_sub' x w
    linarith
  exact HarmonicBalls.circleAverage_wholePlaneCov_inside hR hR1 hxR

lemma var_circle {hC : Ω → (ℂ → ℝ) → ℝ} {hc : Ω → ℝ → ℂ → ℝ} (h : HarmonicBalls.IsWholePlaneGFF P hC hc)
    {ε : ℝ} {w : ℂ} (hε : 0 < ε) (hw : ‖w‖ + ε ≤ 1) :
    Var[fun ω => hc ω ε w; P] = -Real.log ε := by
  rw [← covariance_self (h.measurable_circle ε w hε).aemeasurable]
  refine Eq.trans (h.covariance_eq (.circle ε w) (.circle ε w) hε hε) ?_
  apply HarmonicBalls.wholePlaneGFFCov_circle_self_eq hε w
  intro x hx
  have hxw : ‖x - w‖ = ε := by
    rw [mem_sphere, dist_eq_norm] at hx
    simpa [abs_of_pos hε] using hx
  have := norm_le_norm_add_norm_sub' x w
  linarith

lemma var_zero {hC : Ω → (ℂ → ℝ) → ℝ} {hc : Ω → ℝ → ℂ → ℝ} (h : HarmonicBalls.IsWholePlaneGFF P hC hc)
    {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    Var[fun ω => hc ω R 0; P] = -Real.log R := by
  rw [← covariance_self (h.measurable_circle R 0 hR).aemeasurable]
  refine Eq.trans (h.covariance_eq (.circle R 0) (.circle R 0) hR hR) ?_
  exact HarmonicBalls.wholePlaneGFFCov_circle_zero_of_le_one hR hR1

lemma memLp_circle {hC : Ω → (ℂ → ℝ) → ℝ} {hc : Ω → ℝ → ℂ → ℝ} (h : HarmonicBalls.IsWholePlaneGFF P hC hc)
    {r : ℝ} (z : ℂ) (hr : 0 < r) : MemLp (fun ω => hc ω r z) 2 P :=
  (h.isGaussianProcess.hasGaussianLaw_eval ⟨.circle r z, hr⟩).memLp_two

lemma hasGaussianLaw_shift {hC : Ω → (ℂ → ℝ) → ℝ} {hc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hc) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (w : ℂ) :
    HasGaussianLaw (fun ω => hc ω ε w - hc ω R 0) P :=
  h.isGaussianProcess.hasGaussianLaw_fun_sub (s := ⟨.circle ε w, hε⟩) (t := ⟨.circle R 0, hR⟩)

/-- The circle average at `0` of radius `R` together with the shifted circle averages `hc ε (c k) - hc R 0`
form a Gaussian process (linear combinations of observables). -/
lemma isGaussianProcess_shift {hC : Ω → (ℂ → ℝ) → ℝ} {hc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hc) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) {ι : Type*} (c : ι → ℂ) :
    IsGaussianProcess (Sum.elim (fun (_ : Unit) (ω : Ω) => hc ω R 0)
      (fun (k : ι) (ω : Ω) => hc ω ε (c k) - hc ω R 0)) P := by
  classical
  refine h.isGaussianProcess.of_isGaussianProcess ?_
  rintro (u | k)
  · exact ⟨{⟨.circle R 0, hR⟩}, ContinuousLinearMap.proj ⟨⟨.circle R 0, hR⟩, Finset.mem_singleton_self _⟩,
      fun ω => rfl⟩
  · refine ⟨{⟨.circle ε (c k), hε⟩, ⟨.circle R 0, hR⟩},
      ContinuousLinearMap.proj ⟨⟨.circle ε (c k), hε⟩, Finset.mem_insert_self _ _⟩ -
        ContinuousLinearMap.proj ⟨⟨.circle R 0, hR⟩, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩,
      fun ω => rfl⟩

/-- Independence of `hc R 0` from the shifted circle averages (zero covariance, jointly Gaussian). -/
lemma indepFun_shift {hC : Ω → (ℂ → ℝ) → ℝ} {hc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hc) [IsProbabilityMeasure P] {R ε : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hε : 0 < ε)
    {ι : Type*} (c : ι → ℂ) (hc' : ∀ k, ‖c k‖ + ε ≤ R) :
    IndepFun (fun ω (_ : Unit) => hc ω R 0) (fun ω (k : ι) => hc ω ε (c k) - hc ω R 0) P := by
  have hG := isGaussianProcess_shift h hR hε c
  refine hG.indepFun_of_covariance_eq_zero ?_ ?_ ?_
  · intro s
    exact (h.measurable_circle R 0 hR).aemeasurable
  · intro k
    exact ((h.measurable_circle ε (c k) hε).sub (h.measurable_circle R 0 hR)).aemeasurable
  · intro s k
    have hN : MemLp (fun ω => hc ω R 0) 2 P := memLp_circle h 0 hR
    have hX : MemLp (fun ω => hc ω ε (c k)) 2 P := memLp_circle h (c k) hε
    rw [covariance_fun_sub_right hN hX hN, covariance_comm, cov_circle_zero h hR hR1 hε (hc' k),
      covariance_self (h.measurable_circle R 0 hR).aemeasurable, var_zero h hR hR1]
    ring

/-- Variance of the shifted circle average: `Var (hc ε w - hc R 0) = log R - log ε`. -/
lemma var_shift {hC : Ω → (ℂ → ℝ) → ℝ} {hc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hc) [IsProbabilityMeasure P] {R ε : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hε : 0 < ε)
    {w : ℂ} (hw : ‖w‖ + ε ≤ R) :
    Var[fun ω => hc ω ε w - hc ω R 0; P] = Real.log R - Real.log ε := by
  have hN : MemLp (fun ω => hc ω R 0) 2 P := memLp_circle h 0 hR
  have hX : MemLp (fun ω => hc ω ε w) 2 P := memLp_circle h w hε
  have hZ : MemLp (fun ω => hc ω ε w - hc ω R 0) 2 P := (hasGaussianLaw_shift h hR hε w).memLp_two
  have hmeas : AEMeasurable (fun ω => hc ω ε w - hc ω R 0) P :=
    ((h.measurable_circle ε w hε).sub (h.measurable_circle R 0 hR)).aemeasurable
  rw [← covariance_self hmeas, covariance_fun_sub_left hX hN hZ, covariance_fun_sub_right hX hX hN,
    covariance_fun_sub_right hN hX hN, covariance_comm (X := fun ω => hc ω R 0),
    cov_circle_zero h hR hR1 hε hw, covariance_self (h.measurable_circle R 0 hR).aemeasurable,
    var_zero h hR hR1, covariance_self (h.measurable_circle ε w hε).aemeasurable, var_circle h hε (by linarith)]
  ring

/-- `E exp(γ (hc ε w - hc R 0)) = exp(γ² (log R - log ε) / 2)`. -/
lemma lintegral_exp_shift {hC : Ω → (ℂ → ℝ) → ℝ} {hc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hc) [IsProbabilityMeasure P] {R ε : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hε : 0 < ε) {w : ℂ} (hw : ‖w‖ + ε ≤ R) (γ : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * (hc ω ε w - hc ω R 0))) ∂P
      = ENNReal.ofReal (Real.exp (γ ^ 2 * (Real.log R - Real.log ε) / 2)) := by
  have hGL := hasGaussianLaw_shift h hR hε w
  have hm : ∫ ω, (hc ω ε w - hc ω R 0) ∂P = 0 := by
    have hN : MemLp (fun ω => hc ω R 0) 2 P := memLp_circle h 0 hR
    have hX : MemLp (fun ω => hc ω ε w) 2 P := memLp_circle h w hε
    rw [integral_sub (hX.integrable one_le_two) (hN.integrable one_le_two)]
    have h0 : ∫ ω, hc ω ε w ∂P = 0 := h.integral_eq_zero (.circle ε w) hε
    have h1 : ∫ ω, hc ω R 0 ∂P = 0 := h.integral_eq_zero (.circle R 0) hR
    rw [h0, h1, sub_zero]
  have := lintegral_ofReal_exp_gaussian (X := fun ω => hc ω ε w - hc ω R 0)
    ((h.measurable_circle ε w hε).sub (h.measurable_circle R 0 hR)) hGL hm γ
  rw [this, var_shift h hR hR1 hε hw]


/-- Dyadic cell index of a point of the plane at level `n`. -/
noncomputable def cellIdx (n : ℕ) (x : ℂ) : ℤ × ℤ := (⌊x.re * 2 ^ n⌋, ⌊x.im * 2 ^ n⌋)

/-- Centre of the dyadic cell `k` at level `n`. -/
noncomputable def cellPt (n : ℕ) (k : ℤ × ℤ) : ℂ := ⟨(k.1 : ℝ) / 2 ^ n, (k.2 : ℝ) / 2 ^ n⟩

lemma measurable_cellIdx (n : ℕ) : Measurable (cellIdx n) := by
  unfold cellIdx
  exact (Int.measurable_floor.comp (Complex.measurable_re.mul_const _)).prodMk
    (Int.measurable_floor.comp (Complex.measurable_im.mul_const _))

lemma abs_sub_floor_div (n : ℕ) (t : ℝ) :
    |t - (⌊t * 2 ^ n⌋ : ℝ) / 2 ^ n| ≤ 1 / 2 ^ n := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hf := Int.floor_le (t * 2 ^ n)
  have hf' := Int.lt_floor_add_one (t * 2 ^ n)
  have e : t - (⌊t * 2 ^ n⌋ : ℝ) / 2 ^ n = (t * 2 ^ n - ⌊t * 2 ^ n⌋) / 2 ^ n := by
    field_simp
  rw [e, abs_le]
  constructor
  · have h0 : (0 : ℝ) ≤ (t * 2 ^ n - ⌊t * 2 ^ n⌋) / 2 ^ n := div_nonneg (by linarith) hpos.le
    have h2 : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
    linarith
  · have h1 : t * 2 ^ n - ⌊t * 2 ^ n⌋ ≤ 1 := by linarith
    have := div_le_div_of_nonneg_right h1 hpos.le
    linarith

lemma norm_sub_cellPt_le (n : ℕ) (x : ℂ) : ‖x - cellPt n (cellIdx n x)‖ ≤ 2 / 2 ^ n := by
  have hre := abs_sub_floor_div n x.re
  have him := abs_sub_floor_div n x.im
  have hn := Complex.norm_le_abs_re_add_abs_im (x - cellPt n (cellIdx n x))
  have e1 : (x - cellPt n (cellIdx n x)).re = x.re - (⌊x.re * 2 ^ n⌋ : ℝ) / 2 ^ n := by
    simp [cellPt, cellIdx]
  have e2 : (x - cellPt n (cellIdx n x)).im = x.im - (⌊x.im * 2 ^ n⌋ : ℝ) / 2 ^ n := by
    simp [cellPt, cellIdx]
  rw [e1, e2] at hn
  have : (2 : ℝ) / 2 ^ n = 1 / 2 ^ n + 1 / 2 ^ n := by ring
  linarith

/-- The cell decomposition of a lower Lebesgue integral over a measurable set. -/
lemma lintegral_mul_cellIdx (n : ℕ) {S : Set ℂ} (hS : MeasurableSet S) {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    (G : ℤ × ℤ → ℝ≥0∞) :
    ∫⁻ x in S, f x * G (cellIdx n x) = ∑' k : ℤ × ℤ, G k * ∫⁻ x in S ∩ cellIdx n ⁻¹' {k}, f x := by
  have hcell := measurable_cellIdx n
  have hdisj : Pairwise (Function.onFun Disjoint fun k : ℤ × ℤ => S ∩ cellIdx n ⁻¹' {k}) := by
    intro k l hkl
    refine Set.disjoint_left.2 fun x hx hy => hkl ?_
    have h1 : cellIdx n x = k := hx.2
    have h2 : cellIdx n x = l := hy.2
    exact h1.symm.trans h2
  have hunion : S = ⋃ k : ℤ × ℤ, S ∩ cellIdx n ⁻¹' {k} := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun hx => ⟨cellIdx n x, hx, rfl⟩, fun ⟨_, hx, _⟩ => hx⟩
  conv_lhs => rw [hunion]
  rw [lintegral_iUnion (fun k => hS.inter (hcell (measurableSet_singleton k))) hdisj]
  congr 1
  funext k
  have hsk : MeasurableSet (S ∩ cellIdx n ⁻¹' {k}) := hS.inter (hcell (measurableSet_singleton k))
  rw [setLIntegral_congr_fun hsk (fun x hx => by rw [show cellIdx n x = k from hx.2]),
    lintegral_mul_const _ hf, mul_comm]

/-- Pointwise tangent-line bound for `v ↦ v ^ p`, `0 < p ≤ 1`, at a level `a ∈ (0, ∞)`. -/
lemma rpow_le_tangent {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {a : ℝ≥0∞} (ha0 : a ≠ 0) (ha_top : a ≠ ⊤)
    (v : ℝ≥0∞) :
    v ^ p ≤ a ^ p * (ENNReal.ofReal p * (v * a⁻¹) + ENNReal.ofReal (1 - p)) := by
  by_cases hv : v = ⊤
  · have hinv : a⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ha_top
    have hap : a ^ p ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) ha_top).ne'
    have hp : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
    rw [hv, ENNReal.top_rpow_of_pos hp0]
    simp [ENNReal.top_mul hinv, ENNReal.mul_top hp, ENNReal.mul_top hap]
  · have hx : v * a⁻¹ ≠ ⊤ := ENNReal.mul_ne_top hv (ENNReal.inv_ne_top.2 ha0)
    set x : ℝ := (v * a⁻¹).toReal with hxdef
    have hvx : v * a⁻¹ = ENNReal.ofReal x := (ENNReal.ofReal_toReal hx).symm
    have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
    have hva : v = a * (v * a⁻¹) := by
      calc v = v * (a * a⁻¹) := by rw [ENNReal.mul_inv_cancel ha0 ha_top, mul_one]
        _ = a * (v * a⁻¹) := by ring
    have hbern : x ^ p ≤ p * x + (1 - p) := by
      have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := p) (w₂ := 1 - p) (p₁ := x)
        (p₂ := 1) hp0.le (by linarith) hx0 zero_le_one (by ring)
      simpa using h
    calc v ^ p = a ^ p * (v * a⁻¹) ^ p := by rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← hva]
      _ = a ^ p * ENNReal.ofReal (x ^ p) := by
          rw [hvx, ENNReal.ofReal_rpow_of_nonneg hx0 hp0.le]
      _ ≤ a ^ p * (ENNReal.ofReal p * (v * a⁻¹) + ENNReal.ofReal (1 - p)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hvx, ← ENNReal.ofReal_mul hp0.le, ← ENNReal.ofReal_add (by positivity) (by linarith)]
          exact ENNReal.ofReal_le_ofReal hbern

/-- Jensen's inequality for `p ∈ (0, 1]` in the form `E[V^p] ≤ (E V)^p` on a probability space. -/
lemma lintegral_rpow_le_rpow_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : Ω → ℝ≥0∞} (hV : Measurable V) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∫⁻ ω, V ω ^ p ∂μ ≤ (∫⁻ ω, V ω ∂μ) ^ p := by
  rcases eq_or_ne (∫⁻ ω, V ω ∂μ) ⊤ with ha_top | ha_top
  · rw [ha_top, ENNReal.top_rpow_of_pos hp0]; exact le_top
  rcases eq_or_ne (∫⁻ ω, V ω ∂μ) 0 with ha0 | ha0
  · have hae : ∀ᵐ ω ∂μ, V ω = 0 := (lintegral_eq_zero_iff' hV.aemeasurable).1 ha0
    have hae' : ∀ᵐ ω ∂μ, V ω ^ p = 0 := hae.mono fun ω hω => by simp [hω, ENNReal.zero_rpow_of_pos hp0]
    rw [ha0, ENNReal.zero_rpow_of_pos hp0, lintegral_congr_ae hae']
    simp
  generalize ha : ∫⁻ ω, V ω ∂μ = a at *
  have hint : ∫⁻ ω, V ω * a⁻¹ ∂μ = 1 := by
    rw [lintegral_mul_const _ hV, ha, ENNReal.mul_inv_cancel ha0 ha_top]
  have hs : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
    rw [← ENNReal.ofReal_add hp0.le (by linarith)]; simp
  calc ∫⁻ ω, V ω ^ p ∂μ
      ≤ ∫⁻ ω, a ^ p * (ENNReal.ofReal p * (V ω * a⁻¹) + ENNReal.ofReal (1 - p)) ∂μ :=
        lintegral_mono fun ω => rpow_le_tangent hp0 hp1 ha0 ha_top (V ω)
    _ = a ^ p * (ENNReal.ofReal p * (∫⁻ ω, V ω * a⁻¹ ∂μ) + ENNReal.ofReal (1 - p)) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ha_top),
          lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ = a ^ p := by rw [hint, mul_one, hs, mul_one]


/-- Deterministic weight `ρ(x) = ε^{γ²/2} (1 + log(1/|x|)) (|x| ∨ ε)^{-γ²}`. -/
noncomputable def rho (γ ε : ℝ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * ((1 + Real.log (1 / ‖x‖)) * max ε ‖x‖ ^ (-(γ ^ 2))))

lemma measurable_rho (γ ε : ℝ) : Measurable (rho γ ε) := by
  unfold rho
  apply Measurable.ennreal_ofReal
  apply Measurable.mul measurable_const
  apply Measurable.mul
  · exact measurable_const.add (Real.measurable_log.comp (measurable_const.div measurable_norm))
  · exact (measurable_const.max measurable_norm).pow_const _

lemma fieldCircleAverage_eq (hc : ℝ → ℂ → ℝ) (γ ε : ℝ) (hε : 0 < ε) (x : ℂ) :
    HarmonicBalls.fieldCircleAverage γ hc ε x = hc ε x - γ * Real.log (max ε ‖x‖) := by
  unfold HarmonicBalls.fieldCircleAverage
  rw [HarmonicBalls.circleAverage_log_norm_eq_log_max hε x]

/-- Pathwise identity for the weighted mass: `∫_S (1+log 1/|x|) μ_ε(dx) = e^{γN} ∫_S ρ e^{γ(h_ε(x)-N)} dx`. -/
lemma weightedMass_eq (hc : ℝ → ℂ → ℝ) (γ ε N : ℝ) (hε : 0 < ε) {S : Set ℂ} (hSm : MeasurableSet S)
    (hS : ∀ x ∈ S, ‖x‖ ≤ 1) :
    weightedMass γ ε hc S = ENNReal.ofReal (Real.exp (γ * N)) *
      ∫⁻ x in S, rho γ ε x * ENNReal.ofReal (Real.exp (γ * (hc ε x - N))) := by
  unfold weightedMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hSm fun x hx => ?_
  have hm : 0 < max ε ‖x‖ := lt_max_of_lt_left hε
  have hL : 0 ≤ 1 + Real.log (1 / ‖x‖) := by
    rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
    · rw [← h0]; simp
    · have : 0 ≤ Real.log (1 / ‖x‖) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith [hS x hx])
      linarith
  have hA : 0 ≤ ε ^ (γ ^ 2 / 2) * ((1 + Real.log (1 / ‖x‖)) * max ε ‖x‖ ^ (-(γ ^ 2))) :=
    mul_nonneg (Real.rpow_nonneg hε.le _) (mul_nonneg hL (Real.rpow_nonneg hm.le _))
  have e1 : Real.exp (γ * (hc ε x - γ * Real.log (max ε ‖x‖)))
      = Real.exp (γ * hc ε x) * max ε ‖x‖ ^ (-(γ ^ 2)) := by
    rw [Real.rpow_def_of_pos hm, ← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (γ * hc ε x) = Real.exp (γ * N) * Real.exp (γ * (hc ε x - N)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold regDensity rho
  rw [fieldCircleAverage_eq hc γ ε hε x]
  rw [← ENNReal.ofReal_mul hL, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (Real.exp_pos (γ * N)).le]
  congr 1
  rw [e1, e2]
  ring


lemma lintegral_exp_zero {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc)
    [IsProbabilityMeasure P] {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * hcirc ω R 0)) ∂P
      = ENNReal.ofReal (Real.exp (t ^ 2 * (-Real.log R) / 2)) := by
  have hGL : HasGaussianLaw (fun ω => hcirc ω R 0) P := (h.isGaussianProcess.hasGaussianLaw_eval ⟨.circle R 0, hR⟩)
  have h1 : ∫ ω, hcirc ω R 0 ∂P = 0 := h.integral_eq_zero (.circle R 0) hR
  rw [lintegral_ofReal_exp_gaussian (h.measurable_circle R 0 hR) hGL h1 t, var_zero h hR hR1]

/-- Admissible dyadic cells: centres whose closed `ε`-disk lies in `closedBall 0 R`. -/
def cellOK (R ε : ℝ) (n : ℕ) (k : ℤ × ℤ) : Prop := ‖cellPt n k‖ + ε ≤ R

noncomputable def cellMass (γ ε : ℝ) (S : Set ℂ) (n : ℕ) (k : ℤ × ℤ) : ℝ≥0∞ :=
  ∫⁻ x in S ∩ cellIdx n ⁻¹' {k}, rho γ ε x

lemma cellMass_eq_zero {γ ε R : ℝ} {S : Set ℂ} {n : ℕ} (hR : 0 < R) (hS : ∀ x ∈ S, ‖x‖ ≤ R / 2)
    (hn : 2 / 2 ^ n ≤ R / 8) (hεR : ε ≤ R / 8) {k : ℤ × ℤ} (hk : ¬ cellOK R ε n k) :
    cellMass γ ε S n k = 0 := by
  have hempty : S ∩ cellIdx n ⁻¹' {k} = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxS, hxk⟩
    apply hk
    have hxk' : cellIdx n x = k := hxk
    have h1 := norm_sub_cellPt_le n x
    rw [hxk'] at h1
    rw [norm_sub_rev] at h1
    have h3 := norm_le_norm_add_norm_sub' (cellPt n k) x
    unfold cellOK
    linarith [hS x hxS]
  simp [cellMass, hempty]

lemma measurable_exp_shift {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (γ : ℝ) (w : ℂ) :
    Measurable (fun ω => ENNReal.ofReal (Real.exp (γ * (hcirc ω ε w - hcirc ω R 0)))) :=
  ((((h.measurable_circle ε w hε).sub (h.measurable_circle R 0 hR)).const_mul γ).exp).ennreal_ofReal

/-- The discrete (dyadic) approximation `V_n(ω)` of `∫_S ρ e^{γ(h_ε(x)-N)} dx`. -/
noncomputable def Vn (γ ε R : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (S : Set ℂ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ∑' k : {k : ℤ × ℤ // cellOK R ε n k}, cellMass γ ε S n k.1 *
    ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt n k.1) - hcirc ω R 0)))

lemma tsum_cellMass_eq {γ ε R : ℝ} {S : Set ℂ} {n : ℕ} (hR : 0 < R) (hS : ∀ x ∈ S, ‖x‖ ≤ R / 2)
    (hn : 2 / 2 ^ n ≤ R / 8) (hεR : ε ≤ R / 8) (f : ℤ × ℤ → ℝ≥0∞) :
    ∑' k : {k : ℤ × ℤ // cellOK R ε n k}, f k.1 * cellMass γ ε S n k.1
      = ∑' k : ℤ × ℤ, f k * cellMass γ ε S n k := by
  rw [← tsum_subtype_eq_of_support_subset (f := fun k => f k * cellMass γ ε S n k)]
  · rfl
  · intro k hk
    by_contra hnot
    apply hk
    simp [cellMass_eq_zero hR hS hn hεR hnot]


lemma measurable_Vn {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (γ : ℝ) (S : Set ℂ) (n : ℕ) :
    Measurable (Vn γ ε R hcirc S n) :=
  Measurable.tsum fun k => measurable_const.mul (measurable_exp_shift h hR hε γ (cellPt n k.1))

lemma tsum_cellMass_eq_lintegral {γ ε : ℝ} {S : Set ℂ} (hSm : MeasurableSet S) (n : ℕ) :
    ∑' k : ℤ × ℤ, cellMass γ ε S n k = ∫⁻ x in S, rho γ ε x := by
  have := lintegral_mul_cellIdx n hSm (measurable_rho γ ε) (fun _ => (1 : ℝ≥0∞))
  simp only [mul_one, one_mul] at this
  exact this.symm

/-- `E V_n = (∫_S ρ) e^{γ²(log R - log ε)/2}` (dyadic approximation, unbiased). -/
lemma lintegral_Vn {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc)
    [IsProbabilityMeasure P] {R ε : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hε : 0 < ε) (γ : ℝ) {S : Set ℂ}
    (hSm : MeasurableSet S) {n : ℕ} (hS : ∀ x ∈ S, ‖x‖ ≤ R / 2) (hn : 2 / 2 ^ n ≤ R / 8) (hεR : ε ≤ R / 8) :
    ∫⁻ ω, Vn γ ε R hcirc S n ω ∂P
      = (∫⁻ x in S, rho γ ε x) * ENNReal.ofReal (Real.exp (γ ^ 2 * (Real.log R - Real.log ε) / 2)) := by
  have hterm : ∀ k : {k : ℤ × ℤ // cellOK R ε n k},
      ∫⁻ ω, cellMass γ ε S n k.1 * ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt n k.1) - hcirc ω R 0))) ∂P
        = cellMass γ ε S n k.1 * ENNReal.ofReal (Real.exp (γ ^ 2 * (Real.log R - Real.log ε) / 2)) := by
    intro k
    rw [lintegral_const_mul _ (measurable_exp_shift h hR hε γ _), lintegral_exp_shift h hR hR1 hε k.2 γ]
  unfold Vn
  have hm : ∀ k : {k : ℤ × ℤ // cellOK R ε n k}, Measurable (fun ω => cellMass γ ε S n k.1 *
      ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt n k.1) - hcirc ω R 0)))) :=
    fun k => measurable_const.mul (measurable_exp_shift h hR hε γ (cellPt n k.1))
  refine (lintegral_tsum fun k => (hm k).aemeasurable).trans ?_
  rw [tsum_congr hterm, ENNReal.tsum_mul_right]
  congr 1
  have hsub := tsum_cellMass_eq (γ := γ) (ε := ε) (f := fun _ => (1 : ℝ≥0∞)) hR hS hn hεR
  simp only [one_mul] at hsub
  rw [hsub, tsum_cellMass_eq_lintegral hSm n]

/-- Independence of `e^{pγ N}` and `V_n^p`, from the Gaussian independence of `N` and the shifted field. -/
lemma lintegral_mul_Vn_pow {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P] {R ε : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hε : 0 < ε) (γ p : ℝ) (S : Set ℂ) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)) * Vn γ ε R hcirc S n ω ^ p ∂P
      = (∫⁻ ω, ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)) ∂P) * ∫⁻ ω, Vn γ ε R hcirc S n ω ^ p ∂P := by
  have hind := indepFun_shift h hR hR1 hε (fun k : {k : ℤ × ℤ // cellOK R ε n k} => cellPt n k.1) (fun k => k.2)
  let φ : (Unit → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (p * γ * y ()))
  let ψ : ({k : ℤ × ℤ // cellOK R ε n k} → ℝ) → ℝ≥0∞ := fun y =>
    (∑' k : {k : ℤ × ℤ // cellOK R ε n k}, cellMass γ ε S n k.1 * ENNReal.ofReal (Real.exp (γ * y k))) ^ p
  have hφ : Measurable φ := by unfold φ; fun_prop
  have hψ : Measurable ψ := by
    unfold ψ
    apply Measurable.pow_const
    apply Measurable.tsum
    intro k
    exact measurable_const.mul (by fun_prop)
  have hcomp := hind.comp hφ hψ
  have hmf : Measurable (fun ω => ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0))) :=
    ((((h.measurable_circle R 0 hR).const_mul _).exp).ennreal_ofReal)
  have hmg : Measurable (fun ω => Vn γ ε R hcirc S n ω ^ p) :=
    (measurable_Vn h hR hε γ S n).pow_const p
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (f := fun ω => ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)))
    (g := fun ω => Vn γ ε R hcirc S n ω ^ p) hmf.aemeasurable hmg.aemeasurable hcomp


/-- The dyadic approximation as a lower integral over `S`. -/
lemma Vn_eq_lintegral {hcirc : Ω → ℝ → ℂ → ℝ} {R ε : ℝ} (hR : 0 < R)
    (γ : ℝ) {S : Set ℂ} (hSm : MeasurableSet S) {n : ℕ} (hS : ∀ x ∈ S, ‖x‖ ≤ R / 2)
    (hn : 2 / 2 ^ n ≤ R / 8) (hεR : ε ≤ R / 8) (ω : Ω) :
    Vn γ ε R hcirc S n ω = ∫⁻ x in S, rho γ ε x *
      ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt n (cellIdx n x)) - hcirc ω R 0))) := by
  have h1 := lintegral_mul_cellIdx n hSm (measurable_rho γ ε)
    (fun k => ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt n k) - hcirc ω R 0))))
  have e := tsum_cellMass_eq (γ := γ) (ε := ε)
    (f := fun k => ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt n k) - hcirc ω R 0)))) hR hS hn hεR
  calc Vn γ ε R hcirc S n ω
      = ∑' k : {k : ℤ × ℤ // cellOK R ε n k},
          ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt n k.1) - hcirc ω R 0))) * cellMass γ ε S n k.1 :=
        tsum_congr fun k => mul_comm _ _
    _ = ∑' k : ℤ × ℤ, ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt n k) - hcirc ω R 0))) *
          cellMass γ ε S n k := e
    _ = ∫⁻ x in S, rho γ ε x *
          ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt n (cellIdx n x)) - hcirc ω R 0))) := h1.symm

lemma tendsto_cellPt (x : ℂ) (n0 : ℕ) :
    Filter.Tendsto (fun m : ℕ => cellPt (n0 + m) (cellIdx (n0 + m) x)) Filter.atTop (nhds x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun m : ℕ => (2 : ℝ) / 2 ^ (n0 + m)) Filter.atTop (nhds 0) := by
    apply tendsto_const_nhds.div_atTop
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (Filter.tendsto_atTop_mono (fun m => Nat.le_add_left m n0) Filter.tendsto_id)
  exact squeeze_zero (fun m => norm_nonneg _) (fun m => by rw [norm_sub_rev]; exact norm_sub_cellPt_le (n0 + m) x) hlim


/-- Dominated convergence for the dyadic approximation at a good `ω`. -/
lemma tendsto_Vn {hcirc : Ω → ℝ → ℂ → ℝ}
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hεR : ε ≤ R / 8) (γ : ℝ) {S : Set ℂ} (hSm : MeasurableSet S)
    (hS : ∀ x ∈ S, ‖x‖ ≤ R / 2) (hfin : ∫⁻ x in S, rho γ ε x ≠ ⊤) (n0 : ℕ) (hn0 : 2 / (2:ℝ) ^ n0 ≤ R / 8)
    (ω : Ω) (hω : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) :
    Filter.Tendsto (fun m : ℕ => Vn γ ε R hcirc S (n0 + m) ω) Filter.atTop
      (nhds (∫⁻ x in S, rho γ ε x * ENNReal.ofReal (Real.exp (γ * (hcirc ω ε x - hcirc ω R 0))))) := by
  have hcont : Continuous (fun y : ℂ => hcirc ω ε y) := by
    have : ContinuousOn (fun y : ℂ => hcirc ω ε y) Set.univ := by
      have hmap : Set.MapsTo (fun y : ℂ => ((ε, y) : ℝ × ℂ)) Set.univ (Set.Ioi 0 ×ˢ Set.univ) :=
        fun y _ => ⟨hε, Set.mem_univ _⟩
      exact hω.comp (continuousOn_const.prodMk continuousOn_id) hmap
    exact continuousOn_univ.1 this
  have hn : ∀ m : ℕ, 2 / (2:ℝ) ^ (n0 + m) ≤ R / 8 := fun m =>
    le_trans (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right n0 m))) hn0
  set N := hcirc ω R 0 with hN
  -- continuity bound of the exponential on the closed disk
  have hcontE : ContinuousOn (fun y : ℂ => Real.exp (γ * (hcirc ω ε y - N))) (Metric.closedBall 0 R) :=
    (Real.continuous_exp.comp (continuous_const.mul (hcont.sub continuous_const))).continuousOn
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hcontE
  have hmeasF : ∀ m : ℕ, Measurable (fun x : ℂ => rho γ ε x *
      ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt (n0 + m) (cellIdx (n0 + m) x)) - N)))) := by
    intro m
    have hG : Measurable (fun k : ℤ × ℤ => ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt (n0 + m) k) - N)))) :=
      measurable_of_countable _
    exact (measurable_rho γ ε).mul (hG.comp (measurable_cellIdx (n0 + m)))
  have hlim : ∀ x : ℂ, Filter.Tendsto (fun m : ℕ => rho γ ε x *
      ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt (n0 + m) (cellIdx (n0 + m) x)) - N))))
      Filter.atTop (nhds (rho γ ε x * ENNReal.ofReal (Real.exp (γ * (hcirc ω ε x - N))))) := by
    intro x
    have hc2 : Continuous (fun y : ℂ => ENNReal.ofReal (Real.exp (γ * (hcirc ω ε y - N)))) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul (hcont.sub continuous_const)))
    exact ENNReal.Tendsto.const_mul ((hc2.tendsto x).comp (tendsto_cellPt x n0)) (Or.inr ENNReal.ofReal_ne_top)
  have hVm : ∀ m : ℕ, Vn γ ε R hcirc S (n0 + m) ω = ∫⁻ x in S, rho γ ε x *
      ENNReal.ofReal (Real.exp (γ * (hcirc ω ε (cellPt (n0 + m) (cellIdx (n0 + m) x)) - hcirc ω R 0))) := fun m =>
    Vn_eq_lintegral hR γ hSm hS (hn m) hεR ω
  simp only [hVm]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence (fun x => rho γ ε x * ENNReal.ofReal C)
    (fun m => hmeasF m) ?_ ?_ ?_
  · intro m
    refine ae_restrict_of_forall_mem hSm fun x hx => ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply ENNReal.ofReal_le_ofReal
    have hmem : cellPt (n0 + m) (cellIdx (n0 + m) x) ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 := norm_sub_cellPt_le (n0 + m) x
      have h2 := norm_le_norm_add_norm_sub' (cellPt (n0 + m) (cellIdx (n0 + m) x)) x
      rw [norm_sub_rev] at h1
      linarith [hS x hx, hn m]
    have := hC _ hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] at this
    exact this
  · rw [lintegral_mul_const _ (measurable_rho γ ε)]
    exact ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top
  · exact ae_restrict_of_forall_mem hSm fun x _ => hlim x


/-- Moment bound for the weighted mass on a set `S ⊆ closedBall 0 (R/2)` (`R ≤ 1`, `ε ≤ R/8`, `∫_S ρ < ∞`):
`E[(∫_S (1+log 1/|x|) μ_ε(dx))^p] ≤ e^{p²γ²(-log R)/2} (∫_S ρ e^{γ(h_ε - N)})^p` style bound. -/
lemma moment_bound {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P] {R ε : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hε : 0 < ε) (hεR : ε ≤ R / 8) (γ p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {S : Set ℂ} (hSm : MeasurableSet S) (hS : ∀ x ∈ S, ‖x‖ ≤ R / 2) (hfin : ∫⁻ x in S, rho γ ε x ≠ ⊤) :
    ∫⁻ ω, weightedMass γ ε (hcirc ω) S ^ p ∂P
      ≤ ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * (-Real.log R) / 2)) *
        ((∫⁻ x in S, rho γ ε x) * ENNReal.ofReal (Real.exp (γ ^ 2 * (Real.log R - Real.log ε) / 2))) ^ p := by
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, 2 / (2:ℝ) ^ n0 ≤ R / 8 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (16 / R) (by norm_num : (1:ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hR] at hn
    nlinarith
  have hn : ∀ m : ℕ, 2 / (2:ℝ) ^ (n0 + m) ≤ R / 8 := fun m =>
    le_trans (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right n0 m))) hn0
  set B := ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * (-Real.log R) / 2)) *
        ((∫⁻ x in S, rho γ ε x) * ENNReal.ofReal (Real.exp (γ ^ 2 * (Real.log R - Real.log ε) / 2))) ^ p with hB
  have hseq : ∀ m : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)) *
      Vn γ ε R hcirc S (n0 + m) ω ^ p ∂P ≤ B := by
    intro m
    rw [lintegral_mul_Vn_pow h hR hR1 hε γ p S (n0 + m), lintegral_exp_zero h hR hR1 (p * γ)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∫⁻ ω, Vn γ ε R hcirc S (n0 + m) ω ^ p ∂P
        ≤ (∫⁻ ω, Vn γ ε R hcirc S (n0 + m) ω ∂P) ^ p :=
          lintegral_rpow_le_rpow_lintegral (measurable_Vn h hR hε γ S (n0 + m)) hp0 hp1
      _ = _ := by rw [lintegral_Vn h hR hR1 hε γ hSm hS (hn m) hεR]
  have hpt : ∀ ω : Ω, weightedMass γ ε (hcirc ω) S ^ p =
      ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)) *
        (∫⁻ x in S, rho γ ε x * ENNReal.ofReal (Real.exp (γ * (hcirc ω ε x - hcirc ω R 0)))) ^ p := by
    intro ω
    rw [weightedMass_eq (hcirc ω) γ ε (hcirc ω R 0) hε hSm (fun x hx => le_trans (hS x hx) (by linarith)),
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp0.le]
    have e : Real.exp (γ * hcirc ω R 0) ^ p = Real.exp (p * γ * hcirc ω R 0) := by
      rw [← Real.exp_mul]
      ring_nf
    rw [e]
  have hmeasΦ : ∀ m : ℕ, Measurable (fun ω => ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)) *
      Vn γ ε R hcirc S (n0 + m) ω ^ p) := fun m =>
    ((((h.measurable_circle R 0 hR).const_mul _).exp).ennreal_ofReal).mul
      ((measurable_Vn h hR hε γ S (n0 + m)).pow_const p)
  have hae : ∀ᵐ ω ∂P, weightedMass γ ε (hcirc ω) S ^ p = Filter.liminf
      (fun m : ℕ => ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)) * Vn γ ε R hcirc S (n0 + m) ω ^ p)
      Filter.atTop := by
    filter_upwards [h.ae_continuousOn_circle] with ω hω
    rw [hpt ω]
    refine (Filter.Tendsto.liminf_eq ?_).symm
    have hV := tendsto_Vn (hcirc := hcirc) hR hε hεR γ hSm hS hfin n0 hn0 ω hω
    have hp : Filter.Tendsto (fun m : ℕ => Vn γ ε R hcirc S (n0 + m) ω ^ p) Filter.atTop
        (nhds ((∫⁻ x in S, rho γ ε x * ENNReal.ofReal (Real.exp (γ * (hcirc ω ε x - hcirc ω R 0)))) ^ p)) :=
      ((ENNReal.continuous_rpow_const).tendsto _).comp hV
    exact ENNReal.Tendsto.const_mul hp (Or.inr ENNReal.ofReal_ne_top)
  rw [lintegral_congr_ae hae]
  calc ∫⁻ ω, Filter.liminf (fun m : ℕ => ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)) *
        Vn γ ε R hcirc S (n0 + m) ω ^ p) Filter.atTop ∂P
      ≤ Filter.liminf (fun m : ℕ => ∫⁻ ω, ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)) *
          Vn γ ε R hcirc S (n0 + m) ω ^ p ∂P) Filter.atTop :=
        lintegral_liminf_le hmeasΦ
    _ ≤ B := (Filter.liminf_le_liminf (Filter.Eventually.of_forall hseq)).trans_eq (Filter.liminf_const B)


/-- Real weight `w(x) = (1 + log(1/|x|)) (|x| ∨ ε)^{-γ²}`. -/
noncomputable def wgt (γ ε : ℝ) (x : ℂ) : ℝ := (1 + Real.log (1 / ‖x‖)) * max ε ‖x‖ ^ (-(γ ^ 2))

lemma rho_eq_wgt (γ ε : ℝ) (x : ℂ) : rho γ ε x = ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * wgt γ ε x) := rfl

lemma rho_mul_K {γ ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) {x : ℂ} (hw : 0 ≤ wgt γ ε x) :
    rho γ ε x * ENNReal.ofReal (Real.exp (γ ^ 2 * (Real.log R - Real.log ε) / 2))
      = ENNReal.ofReal (R ^ (γ ^ 2 / 2) * wgt γ ε x) := by
  rw [rho_eq_wgt, ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hε.le _) hw)]
  congr 1
  have e : ε ^ (γ ^ 2 / 2) * Real.exp (γ ^ 2 * (Real.log R - Real.log ε) / 2) = R ^ (γ ^ 2 / 2) := by
    rw [Real.rpow_def_of_pos hε, Real.rpow_def_of_pos hR, ← Real.exp_add]
    congr 1
    ring
  calc ε ^ (γ ^ 2 / 2) * wgt γ ε x * Real.exp (γ ^ 2 * (Real.log R - Real.log ε) / 2)
      = (ε ^ (γ ^ 2 / 2) * Real.exp (γ ^ 2 * (Real.log R - Real.log ε) / 2)) * wgt γ ε x := by ring
    _ = R ^ (γ ^ 2 / 2) * wgt γ ε x := by rw [e]

lemma log_inv_le_of_lt_one {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    Real.log (1 / t) ≤ 2 * t ^ (-(1 / 2 : ℝ)) := by
  rcases eq_or_lt_of_le ht with h0 | h0
  · subst h0
    simp
  · have hu : 1 ≤ (1 / t) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by rw [le_div_iff₀ h0]; linarith) (by norm_num)
    have hlog : Real.log ((1 / t) ^ (1 / 2 : ℝ)) = (1 / 2) * Real.log (1 / t) := by
      rw [Real.log_rpow (by positivity)]
    have hpow : t ^ (-(1 / 2 : ℝ)) = (1 / t) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_neg ht, one_div t, Real.inv_rpow ht]
    rw [hpow]
    have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (1 / t) ^ (1 / 2 : ℝ))
    linarith

lemma integrableOn_log_inv_ball : IntegrableOn (fun y : ℂ => Real.log (1 / ‖y‖)) (Metric.ball (0 : ℂ) 1) := by
  refine integrableOn_ball_of_norm_le_rpow (μ := (MeasureTheory.volume : Measure ℂ)) (f := fun y : ℂ => Real.log (1 / ‖y‖)) (C := 2) (α := 1 / 2) (r := 1) ?_ ?_ ?_ ?_
  · simp
  · norm_num
  · refine ae_restrict_of_forall_mem measurableSet_ball fun y hy => ?_
    have hy1 : ‖y‖ < 1 := by simpa using hy
    have hnn : 0 ≤ ‖y‖ := norm_nonneg y
    rcases eq_or_lt_of_le hnn with h0 | h0
    · rw [← h0]; simp
    · have hb := log_inv_le_of_lt_one hnn hy1
      have hpos : 0 ≤ Real.log (1 / ‖y‖) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg hpos]
      exact hb
  · exact (Real.measurable_log.comp (measurable_const.div measurable_norm)).aestronglyMeasurable

lemma K1_lt_top : ∫⁻ y in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (Real.log (1 / ‖y‖)) < ⊤ :=
  integrableOn_log_inv_ball.lintegral_lt_top


/-- Scaling of the logarithmic integral on balls: `∫_{B_c} log(c/|x|) dx = c² ∫_{B_1} log(1/|y|) dy`. -/
lemma lintegral_ball_log_scale {c : ℝ} (hc : 0 < c) :
    ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (Real.log (c / ‖x‖))
      = ENNReal.ofReal (c ^ 2) * ∫⁻ y in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (Real.log (1 / ‖y‖)) := by
  set H : ℂ → ENNReal := (Metric.ball (0 : ℂ) c).indicator
    (fun x => ENNReal.ofReal (Real.log (c / ‖x‖))) with hH
  have hHm : Measurable H :=
    (Measurable.ennreal_ofReal (Real.measurable_log.comp (measurable_const.div measurable_norm))).indicator
      measurableSet_ball
  have hmap := MeasureTheory.Measure.map_addHaar_smul (MeasureTheory.volume : MeasureTheory.Measure ℂ)
    (r := c) hc.ne'
  rw [Complex.finrank_real_complex] at hmap
  have key : ∫⁻ x, H x ∂(MeasureTheory.Measure.map (fun y : ℂ => c • y) MeasureTheory.volume)
      = ∫⁻ y, H (c • y) := lintegral_map hHm (measurable_const_smul c)
  rw [hmap, lintegral_smul_measure] at key
  have hRHS : ∀ y : ℂ, H (c • y) = (Metric.ball (0 : ℂ) 1).indicator
      (fun y : ℂ => ENNReal.ofReal (Real.log (1 / ‖y‖))) y := by
    intro y
    by_cases hy : y ∈ Metric.ball (0 : ℂ) 1
    · have hcy : c • y ∈ Metric.ball (0 : ℂ) c := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        rw [mem_ball_zero_iff] at hy
        nlinarith
      rw [hH, Set.indicator_of_mem hcy, Set.indicator_of_mem hy]
      congr 2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      rcases eq_or_ne ‖y‖ 0 with h0 | h0
      · simp [h0]
      · field_simp
    · have hcy : c • y ∉ Metric.ball (0 : ℂ) c := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        rw [mem_ball_zero_iff] at hy
        intro h
        have : c * ‖y‖ < c := h
        apply hy
        nlinarith
      rw [hH, Set.indicator_of_notMem hcy, Set.indicator_of_notMem hy]
  have hK : ∫⁻ y, H (c • y) = ∫⁻ y in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (Real.log (1 / ‖y‖)) := by
    simp_rw [hRHS]
    exact lintegral_indicator measurableSet_ball _
  have hX : ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (Real.log (c / ‖x‖)) = ∫⁻ x, H x := by
    rw [hH, lintegral_indicator measurableSet_ball]
  have h1 : ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (|(c ^ 2)⁻¹|) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_nonneg (by positivity), mul_inv_cancel₀ (by positivity),
      ENNReal.ofReal_one]
  rw [hX, ← hK, ← key, smul_eq_mul, ← mul_assoc, h1, one_mul]


/-- The disk integral of `1 + log(1/|x|)`: `∫_{B_c} (1+log 1/|x|) ≤ |B_c| (1+log 1/c) + c² ∫_{B_1} log(1/|y|)`. -/
lemma lintegral_one_add_log_ball {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (1 + Real.log (1 / ‖x‖))
      ≤ ENNReal.ofReal (1 + Real.log (1 / c)) * MeasureTheory.volume (Metric.ball (0 : ℂ) c)
        + ENNReal.ofReal (c ^ 2) * ∫⁻ y in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (Real.log (1 / ‖y‖)) := by
  have hL : 0 ≤ Real.log (1 / c) := Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith)
  have hpt : ∀ x ∈ Metric.ball (0 : ℂ) c, ENNReal.ofReal (1 + Real.log (1 / ‖x‖))
      ≤ ENNReal.ofReal (1 + Real.log (1 / c)) + ENNReal.ofReal (Real.log (c / ‖x‖)) := by
    intro x hx
    have hx' : ‖x‖ < c := by simpa using hx
    have hnn := norm_nonneg x
    rcases eq_or_lt_of_le hnn with h0 | h0
    · rw [← h0]
      simp only [div_zero, Real.log_zero, add_zero]
      exact le_trans (ENNReal.ofReal_le_ofReal (by linarith)) le_self_add
    · have hlog : Real.log (1 / ‖x‖) = Real.log (1 / c) + Real.log (c / ‖x‖) := by
        rw [Real.log_div (by norm_num) h0.ne', Real.log_div (by norm_num) hc.ne',
          Real.log_div hc.ne' h0.ne']
        simp only [Real.log_one]
        ring
      have hpos : 0 ≤ Real.log (c / ‖x‖) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
      rw [← ENNReal.ofReal_add (by linarith) hpos]
      apply ENNReal.ofReal_le_ofReal
      linarith
  calc ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (1 + Real.log (1 / ‖x‖))
      ≤ ∫⁻ x in Metric.ball (0 : ℂ) c, (ENNReal.ofReal (1 + Real.log (1 / c))
          + ENNReal.ofReal (Real.log (c / ‖x‖))) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = ENNReal.ofReal (1 + Real.log (1 / c)) * MeasureTheory.volume (Metric.ball (0 : ℂ) c)
          + ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (Real.log (c / ‖x‖)) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const]
    _ = _ := by rw [lintegral_ball_log_scale hc]

/-- Real weight `wgt` on the disk, with the ε-regularized insertion bounded by `ε^{-γ²}`. -/
lemma lintegral_wgt_ball {γ ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (wgt γ ε x)
      ≤ ENNReal.ofReal (ε ^ (-(γ ^ 2))) * (ENNReal.ofReal (1 + Real.log (1 / c)) * MeasureTheory.volume (Metric.ball (0 : ℂ) c)
        + ENNReal.ofReal (c ^ 2) * ∫⁻ y in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (Real.log (1 / ‖y‖))) := by
  have hpt : ∀ x ∈ Metric.ball (0 : ℂ) c, ENNReal.ofReal (wgt γ ε x)
      ≤ ENNReal.ofReal (ε ^ (-(γ ^ 2))) * ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) := by
    intro x hx
    have hx' : ‖x‖ < c := by simpa using hx
    have hnn := norm_nonneg x
    have hL : 0 ≤ 1 + Real.log (1 / ‖x‖) := by
      rcases eq_or_lt_of_le hnn with h0 | h0
      · rw [← h0]; simp
      · have : 0 ≤ Real.log (1 / ‖x‖) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
        linarith
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
    apply ENNReal.ofReal_le_ofReal
    unfold wgt
    have hm : ε ^ (-(γ ^ 2)) ≥ max ε ‖x‖ ^ (-(γ ^ 2)) :=
      Real.rpow_le_rpow_of_nonpos hε (le_max_left _ _) (by nlinarith [sq_nonneg γ])
    have hm0 : 0 ≤ max ε ‖x‖ ^ (-(γ ^ 2)) := Real.rpow_nonneg (lt_max_of_lt_left hε).le _
    nlinarith
  calc ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (wgt γ ε x)
      ≤ ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (ε ^ (-(γ ^ 2))) * ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = ENNReal.ofReal (ε ^ (-(γ ^ 2))) * ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_one_add_log_ball hc hc1) (by positivity)


lemma wgt_nonneg {γ ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : ‖x‖ ≤ 1) : 0 ≤ wgt γ ε x := by
  unfold wgt
  apply mul_nonneg _ (Real.rpow_nonneg (lt_max_of_lt_left hε).le _)
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
  · rw [← h0]; simp
  · have : 0 ≤ Real.log (1 / ‖x‖) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
    linarith

lemma lintegral_wgt_annulus {γ ε s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 < ε) (hεs : ε ≤ s / 4) :
    ∫⁻ x in annulus s, ENNReal.ofReal (wgt γ ε x)
      ≤ ENNReal.ofReal ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) * MeasureTheory.volume (Metric.ball (0 : ℂ) s) := by
  have hlog2 : 0 ≤ Real.log (2 / s) := Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith)
  have hB0 : 0 ≤ (1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  have hpt : ∀ x ∈ annulus s, ENNReal.ofReal (wgt γ ε x)
      ≤ ENNReal.ofReal ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) := by
    rintro x ⟨hx1, hx2⟩
    apply ENNReal.ofReal_le_ofReal
    unfold wgt
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hx1
    have hmax : max ε ‖x‖ = ‖x‖ := max_eq_right (by linarith)
    rw [hmax]
    have hA : ‖x‖ ^ (-(γ ^ 2)) ≤ (2 / s) ^ (γ ^ 2) := by
      have h1 : (s / 2) ^ (-(γ ^ 2)) ≥ ‖x‖ ^ (-(γ ^ 2)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hx1 (by nlinarith [sq_nonneg γ])
      have h2 : (s / 2) ^ (-(γ ^ 2)) = (2 / s) ^ (γ ^ 2) := by
        rw [Real.rpow_neg (by positivity), show (2 / s) = (s / 2)⁻¹ by field_simp,
          Real.inv_rpow (by positivity)]
      linarith
    have hLe : 1 + Real.log (1 / ‖x‖) ≤ 1 + Real.log (2 / s) := by
      have : Real.log (1 / ‖x‖) ≤ Real.log (2 / s) :=
        Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hxpos hs]; linarith [hx1])
      linarith
    exact mul_le_mul hLe hA (Real.rpow_nonneg hxpos.le _) (by linarith)
  calc ∫⁻ x in annulus s, ENNReal.ofReal (wgt γ ε x)
      ≤ ∫⁻ x in annulus s, ENNReal.ofReal ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) :=
        setLIntegral_mono' (measurableSet_annulus s) hpt
    _ = ENNReal.ofReal ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) * MeasureTheory.volume (annulus s) :=
        setLIntegral_const _ _
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply MeasureTheory.measure_mono
        intro x hx
        exact mem_ball_zero_iff.2 hx.2

lemma rho_ne_top_ball {γ ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∫⁻ x in Metric.ball (0 : ℂ) c, rho γ ε x ≠ ⊤ := by
  have hpt : ∀ x ∈ Metric.ball (0 : ℂ) c, rho γ ε x
      ≤ ENNReal.ofReal (ε ^ (γ ^ 2 / 2)) * ENNReal.ofReal (wgt γ ε x) := by
    intro x hx
    have hx' : ‖x‖ ≤ 1 := by simp at hx; linarith
    rw [rho_eq_wgt, ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
  have hbr : ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (wgt γ ε x)
      ≤ ENNReal.ofReal (ε ^ (-(γ ^ 2))) * (ENNReal.ofReal (1 + Real.log (1 / c)) *
        MeasureTheory.volume (Metric.ball (0 : ℂ) c) + ENNReal.ofReal (c ^ 2) *
        ∫⁻ y in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (Real.log (1 / ‖y‖))) :=
    lintegral_wgt_ball hε hc hc1
  have hbracket : ENNReal.ofReal (1 + Real.log (1 / c)) * MeasureTheory.volume (Metric.ball (0 : ℂ) c) +
      ENNReal.ofReal (c ^ 2) * ∫⁻ y in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (Real.log (1 / ‖y‖)) ≠ ⊤ :=
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top K1_lt_top⟩).ne
  have hle : ∫⁻ x in Metric.ball (0 : ℂ) c, rho γ ε x
      ≤ ENNReal.ofReal (ε ^ (γ ^ 2 / 2)) * (ENNReal.ofReal (ε ^ (-(γ ^ 2))) * (ENNReal.ofReal (1 + Real.log (1 / c)) *
        MeasureTheory.volume (Metric.ball (0 : ℂ) c) + ENNReal.ofReal (c ^ 2) *
        ∫⁻ y in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (Real.log (1 / ‖y‖)))) := by
    calc ∫⁻ x in Metric.ball (0 : ℂ) c, rho γ ε x
        ≤ ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (ε ^ (γ ^ 2 / 2)) * ENNReal.ofReal (wgt γ ε x) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (ε ^ (γ ^ 2 / 2)) * ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (wgt γ ε x) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul_of_nonneg_left hbr (by positivity)
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbracket)) hle

/-- The rescaled identity for the moment bound on a set. -/
lemma rhoK_set {γ ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) {S : Set ℂ} (hSm : MeasurableSet S)
    (hS : ∀ x ∈ S, ‖x‖ ≤ 1) :
    (∫⁻ x in S, rho γ ε x) * ENNReal.ofReal (Real.exp (γ ^ 2 * (Real.log R - Real.log ε) / 2))
      = ENNReal.ofReal (R ^ (γ ^ 2 / 2)) * ∫⁻ x in S, ENNReal.ofReal (wgt γ ε x) := by
  rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ x in S, rho γ ε x * ENNReal.ofReal (Real.exp (γ ^ 2 * (Real.log R - Real.log ε) / 2))
      = ∫⁻ x in S, ENNReal.ofReal (R ^ (γ ^ 2 / 2)) * ENNReal.ofReal (wgt γ ε x) :=
        setLIntegral_congr_fun hSm fun x hx => by
          rw [rho_mul_K hε hR (wgt_nonneg hε (hS x hx)), ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    _ = ENNReal.ofReal (R ^ (γ ^ 2 / 2)) * ∫⁻ x in S, ENNReal.ofReal (wgt γ ε x) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top


/-- Real exponent algebra for the annulus: `e^{-(pγ)² log(2s)/2} (Y_s)^p ≤ C s^κ (1+log 1/s)^p`. -/
lemma annulus_real_bound (γ p : ℝ) (hp0 : 0 < p) (V : ℝ) (hV : 0 ≤ V) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 →
      Real.exp ((p * γ) ^ 2 * (-Real.log (2 * s)) / 2)
        * ((2 * s) ^ (γ ^ 2 / 2) * ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) * (s ^ 2 * V)) ^ p
        ≤ C * s ^ ((2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2) * (1 + Real.log (1 / s)) ^ p := by
  refine ⟨2 ^ (-((p * γ) ^ 2) / 2) * (2 ^ (γ ^ 2 / 2) * 2 ^ (γ ^ 2) * (1 + Real.log 2) * V) ^ p, fun s hs hs1 => ?_⟩
  set L := Real.log (1 / s) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith)
  have hlog2 : Real.log (2 / s) = Real.log 2 + L := by
    rw [Real.log_div (by norm_num) hs.ne', hLdef, Real.log_div (by norm_num) hs.ne', Real.log_one]
    ring
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- the rpow identity for the power of `s`
  have hsp : s ^ (γ ^ 2 / 2) * s ^ (-(γ ^ 2)) * s ^ (2 : ℝ) = s ^ (2 - γ ^ 2 / 2) := by
    rw [← Real.rpow_add hs, ← Real.rpow_add hs]
    congr 1
    ring
  have e1 : (2 * s) ^ (γ ^ 2 / 2) = 2 ^ (γ ^ 2 / 2) * s ^ (γ ^ 2 / 2) := Real.mul_rpow (by norm_num) hs.le
  have e2 : (2 / s) ^ (γ ^ 2) = 2 ^ (γ ^ 2) * s ^ (-(γ ^ 2)) := by
    rw [Real.div_rpow (by norm_num) hs.le, Real.rpow_neg hs.le, div_eq_mul_inv]
  have hY : (2 * s) ^ (γ ^ 2 / 2) * ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) * (s ^ 2 * V)
      = (2 ^ (γ ^ 2 / 2) * 2 ^ (γ ^ 2) * V * (1 + Real.log (2 / s))) * s ^ (2 - γ ^ 2 / 2) := by
    rw [e1, e2, ← hsp, Real.rpow_two]
    ring
  have hYle : (2 ^ (γ ^ 2 / 2) * 2 ^ (γ ^ 2) * V * (1 + Real.log (2 / s))) ≤
      (2 ^ (γ ^ 2 / 2) * 2 ^ (γ ^ 2) * (1 + Real.log 2) * V) * (1 + L) := by
    rw [hlog2]
    have h2 : 0 ≤ 2 ^ (γ ^ 2 / 2) * 2 ^ (γ ^ 2) * V := by positivity
    nlinarith [mul_nonneg hl2 hL0, mul_nonneg h2 hL0]
  have hL1 : 0 ≤ 1 + L := by linarith
  have hlog2' : 0 ≤ 1 + Real.log (2 / s) := by
    rw [hlog2]
    linarith
  have hK0 : 0 ≤ 2 ^ (γ ^ 2 / 2) * 2 ^ (γ ^ 2) * V * (1 + Real.log (2 / s)) :=
    mul_nonneg (by positivity) hlog2'
  have hD : 0 ≤ 2 ^ (γ ^ 2 / 2) * 2 ^ (γ ^ 2) * (1 + Real.log 2) * V :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by linarith)) hV
  have hpow : ((2 * s) ^ (γ ^ 2 / 2) * ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) * (s ^ 2 * V)) ^ p
      ≤ ((2 ^ (γ ^ 2 / 2) * 2 ^ (γ ^ 2) * (1 + Real.log 2) * V) * (1 + L)) ^ p * s ^ ((2 - γ ^ 2 / 2) * p) := by
    rw [hY, Real.mul_rpow hK0 (Real.rpow_nonneg hs.le _), ← Real.rpow_mul hs.le]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hK0 hYle hp0.le) (by positivity)
  have eexp : Real.exp ((p * γ) ^ 2 * (-Real.log (2 * s)) / 2) = (2 * s) ^ (-((p * γ) ^ 2) / 2) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  have hs_eq : s ^ (-((p * γ) ^ 2) / 2) * s ^ ((2 - γ ^ 2 / 2) * p) = s ^ ((2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  rw [eexp, Real.mul_rpow (by norm_num) hs.le]
  calc 2 ^ (-((p * γ) ^ 2) / 2) * s ^ (-((p * γ) ^ 2) / 2) *
        ((2 * s) ^ (γ ^ 2 / 2) * ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) * (s ^ 2 * V)) ^ p
      ≤ 2 ^ (-((p * γ) ^ 2) / 2) * s ^ (-((p * γ) ^ 2) / 2) *
        (((2 ^ (γ ^ 2 / 2) * 2 ^ (γ ^ 2) * (1 + Real.log 2) * V) * (1 + L)) ^ p * s ^ ((2 - γ ^ 2 / 2) * p)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 ^ (-((p * γ) ^ 2) / 2) * (2 ^ (γ ^ 2 / 2) * 2 ^ (γ ^ 2) * (1 + Real.log 2) * V) ^ p) *
        s ^ ((2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2) * (1 + L) ^ p := by
        rw [← hs_eq, Real.mul_rpow hD hL1]
        ring


/-- Real exponent algebra for the core: `e^{-(pγ)² log(8ε)/2} (Y_c)^p ≤ C c^κ (1+log 1/c)^p`. -/
lemma core_real_bound (γ p : ℝ) (hp0 : 0 < p) (Kr : ℝ) (hK : 0 ≤ Kr) :
    ∃ C : ℝ, ∀ c ε : ℝ, 0 < c → 0 < ε → c ≤ 1 → c ≤ 4 * ε →
      Real.exp ((p * γ) ^ 2 * (-Real.log (8 * ε)) / 2)
        * ((8 * ε) ^ (γ ^ 2 / 2) * ε ^ (-(γ ^ 2)) * (c ^ 2 * (1 + Real.log (1 / c))) * Kr) ^ p
        ≤ C * c ^ ((2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2) * (1 + Real.log (1 / c)) ^ p := by
  set a : ℝ := (p * γ) ^ 2 / 2 + γ ^ 2 * p / 2 with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  refine ⟨8 ^ (-((p * γ) ^ 2) / 2) * (8 ^ (γ ^ 2 / 2) * Kr) ^ p * 4 ^ a, fun c ε hc hε hc1 hc4 => ?_⟩
  have hLnn : 0 ≤ Real.log (1 / c) := Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith)
  set L : ℝ := 1 + Real.log (1 / c) with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  set κ : ℝ := (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2 with hκ
  have hκa : κ + a = 2 * p := by rw [hκ, ha]; ring
  have hsplit : (8 * ε) ^ (γ ^ 2 / 2) * ε ^ (-(γ ^ 2)) = 8 ^ (γ ^ 2 / 2) * ε ^ (-(γ ^ 2 / 2)) := by
    rw [Real.mul_rpow (by norm_num) hε.le, mul_assoc, ← Real.rpow_add hε]
    congr 2
    ring
  have hY : (8 * ε) ^ (γ ^ 2 / 2) * ε ^ (-(γ ^ 2)) * (c ^ 2 * L) * Kr
      = (8 ^ (γ ^ 2 / 2) * Kr) * ε ^ (-(γ ^ 2 / 2)) * (c ^ 2 * L) := by
    rw [mul_right_comm _ (c ^ 2 * L), hsplit]
    ring
  have hexp : Real.exp ((p * γ) ^ 2 * (-Real.log (8 * ε)) / 2)
      = 8 ^ (-((p * γ) ^ 2) / 2) * ε ^ (-((p * γ) ^ 2) / 2) := by
    rw [← Real.mul_rpow (by norm_num) hε.le, Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  have hX : 0 ≤ 8 ^ (γ ^ 2 / 2) * Kr := mul_nonneg (by positivity) hK
  have hY' : 0 ≤ ε ^ (-(γ ^ 2 / 2)) := by positivity
  have hZ : 0 ≤ c ^ 2 * L := mul_nonneg (by positivity) hL0
  have hc2 : (c ^ 2) ^ p = c ^ (2 * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num
  have hpow : ((8 ^ (γ ^ 2 / 2) * Kr) * ε ^ (-(γ ^ 2 / 2)) * (c ^ 2 * L)) ^ p
      = (8 ^ (γ ^ 2 / 2) * Kr) ^ p * ε ^ (-(γ ^ 2 / 2) * p) * (c ^ (2 * p) * L ^ p) := by
    rw [Real.mul_rpow (mul_nonneg hX hY') hZ, Real.mul_rpow hX hY', ← Real.rpow_mul hε.le,
      Real.mul_rpow (by positivity) hL0, hc2]
  have key : ε ^ (-a) * c ^ (2 * p) ≤ 4 ^ a * c ^ κ := by
    have hce : c / ε ≤ 4 := by rw [div_le_iff₀ hε]; linarith
    have h1 : (c / ε) ^ a ≤ 4 ^ a := Real.rpow_le_rpow (by positivity) hce ha0
    have h2 : (c / ε) ^ a = c ^ a * ε ^ (-a) := by
      rw [Real.div_rpow hc.le hε.le, Real.rpow_neg hε.le, div_eq_mul_inv]
    have h3 : c ^ (2 * p) = c ^ κ * c ^ a := by rw [← Real.rpow_add hc, hκa]
    calc ε ^ (-a) * c ^ (2 * p) = c ^ κ * (c ^ a * ε ^ (-a)) := by rw [h3]; ring
      _ = c ^ κ * (c / ε) ^ a := by rw [h2]
      _ ≤ c ^ κ * 4 ^ a := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 ^ a * c ^ κ := by ring
  rw [hY, hexp, hpow]
  have hE : 8 ^ (-((p * γ) ^ 2) / 2) * ε ^ (-((p * γ) ^ 2) / 2) * ((8 ^ (γ ^ 2 / 2) * Kr) ^ p * ε ^ (-(γ ^ 2 / 2) * p) * (c ^ (2 * p) * L ^ p))
      = 8 ^ (-((p * γ) ^ 2) / 2) * (8 ^ (γ ^ 2 / 2) * Kr) ^ p * (ε ^ (-a) * c ^ (2 * p)) * L ^ p := by
    rw [show -a = -((p * γ) ^ 2) / 2 + -(γ ^ 2 / 2) * p by rw [ha]; ring, Real.rpow_add hε]
    ring
  rw [hE]
  calc 8 ^ (-((p * γ) ^ 2) / 2) * (8 ^ (γ ^ 2 / 2) * Kr) ^ p * (ε ^ (-a) * c ^ (2 * p)) * L ^ p
      ≤ 8 ^ (-((p * γ) ^ 2) / 2) * (8 ^ (γ ^ 2 / 2) * Kr) ^ p * (4 ^ a * c ^ κ) * L ^ p := by
        gcongr
    _ = 8 ^ (-((p * γ) ^ 2) / 2) * (8 ^ (γ ^ 2 / 2) * Kr) ^ p * 4 ^ a * c ^ κ * L ^ p := by ring


lemma volume_ball_eq_scale (s : ℝ) (hs : 0 ≤ s) :
    MeasureTheory.volume (Metric.ball (0 : ℂ) s) = ENNReal.ofReal (s ^ 2) * MeasureTheory.volume (Metric.ball (0 : ℂ) 1) := by
  rw [MeasureTheory.Measure.addHaar_ball _ (0 : ℂ) hs, Complex.finrank_real_complex]

lemma annulus_estimate {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P] {γ p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ C : ℝ, ∀ s ε : ℝ, 0 < s → s ≤ 1 / 8 → 0 < ε → 4 * ε ≤ s →
      ∫⁻ ω, weightedMass γ ε (hcirc ω) (annulus s) ^ p ∂P
        ≤ ENNReal.ofReal (C * s ^ ((2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2) * (1 + Real.log (1 / s)) ^ p) := by
  set V1r : ℝ := (MeasureTheory.volume (Metric.ball (0 : ℂ) 1)).toReal with hV1r
  have hV1 : MeasureTheory.volume (Metric.ball (0 : ℂ) 1) = ENNReal.ofReal V1r :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  obtain ⟨C₀, hC₀⟩ := annulus_real_bound γ p hp0 V1r ENNReal.toReal_nonneg
  refine ⟨C₀, fun s ε hs hs8 hε h4 => ?_⟩
  have hs1 : s ≤ 1 := by linarith
  have hεs : ε ≤ s / 4 := by linarith
  have hR : (0 : ℝ) < 2 * s := by positivity
  have hR1 : 2 * s ≤ 1 := by linarith
  have hεR : ε ≤ 2 * s / 8 := by linarith
  have hS : ∀ x ∈ annulus s, ‖x‖ ≤ 2 * s / 2 := fun x hx => by have := hx.2; linarith
  have hfin : ∫⁻ x in annulus s, rho γ ε x ≠ ⊤ :=
    ne_top_of_le_ne_top (rho_ne_top_ball hε hs hs1)
      (MeasureTheory.lintegral_mono_set (fun x hx => mem_ball_zero_iff.2 hx.2))
  have hmom := moment_bound h hR hR1 hε hεR γ p hp0 hp1 (measurableSet_annulus s) hS hfin
  have hrhoK := rhoK_set (γ := γ) (R := 2 * s) hε hR (measurableSet_annulus s)
    (fun x hx => le_trans (hS x hx) (by linarith))
  have hwb := lintegral_wgt_annulus (γ := γ) hs hs1 hε hεs
  rw [volume_ball_eq_scale s hs.le, hV1] at hwb
  have hlog2 : 0 ≤ Real.log (2 / s) := Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith)
  have hB : 0 ≤ (1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  have hYle : (∫⁻ x in annulus s, rho γ ε x) * ENNReal.ofReal (Real.exp (γ ^ 2 * (Real.log (2 * s) - Real.log ε) / 2))
      ≤ ENNReal.ofReal ((2 * s) ^ (γ ^ 2 / 2) * ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) * (s ^ 2 * V1r)) := by
    rw [hrhoK]
    calc ENNReal.ofReal ((2 * s) ^ (γ ^ 2 / 2)) * ∫⁻ x in annulus s, ENNReal.ofReal (wgt γ ε x)
        ≤ ENNReal.ofReal ((2 * s) ^ (γ ^ 2 / 2)) *
          (ENNReal.ofReal ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) *
            (ENNReal.ofReal (s ^ 2) * ENNReal.ofReal V1r)) :=
          mul_le_mul_of_nonneg_left hwb (by positivity)
      _ = ENNReal.ofReal ((2 * s) ^ (γ ^ 2 / 2) * ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) * (s ^ 2 * V1r)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hB,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hY0 : 0 ≤ (2 * s) ^ (γ ^ 2 / 2) * ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) * (s ^ 2 * V1r) :=
    mul_nonneg (mul_nonneg (by positivity) hB) (by positivity)
  calc ∫⁻ ω, weightedMass γ ε (hcirc ω) (annulus s) ^ p ∂P
      ≤ ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * (-Real.log (2 * s)) / 2)) *
        ((∫⁻ x in annulus s, rho γ ε x) *
          ENNReal.ofReal (Real.exp (γ ^ 2 * (Real.log (2 * s) - Real.log ε) / 2))) ^ p := hmom
    _ ≤ ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * (-Real.log (2 * s)) / 2)) *
        (ENNReal.ofReal ((2 * s) ^ (γ ^ 2 / 2) * ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) * (s ^ 2 * V1r))) ^ p :=
        mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hYle hp0.le) (by positivity)
    _ = ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * (-Real.log (2 * s)) / 2) *
        ((2 * s) ^ (γ ^ 2 / 2) * ((1 + Real.log (2 / s)) * (2 / s) ^ (γ ^ 2)) * (s ^ 2 * V1r)) ^ p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hY0 hp0.le, ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (C₀ * s ^ ((2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2) * (1 + Real.log (1 / s)) ^ p) :=
        ENNReal.ofReal_le_ofReal (hC₀ s hs hs1)


lemma core_estimate {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P] {γ p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ C : ℝ, ∀ c ε : ℝ, 0 < c → 0 < ε → ε ≤ 1 / 8 → c ≤ 4 * ε →
      ∫⁻ ω, weightedMass γ ε (hcirc ω) (Metric.ball (0 : ℂ) c) ^ p ∂P
        ≤ ENNReal.ofReal (C * c ^ ((2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2) * (1 + Real.log (1 / c)) ^ p) := by
  set K1 : ENNReal := ∫⁻ y in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (Real.log (1 / ‖y‖)) with hK1
  set Kc : ENNReal := MeasureTheory.volume (Metric.ball (0 : ℂ) 1) + K1 with hKc
  have hKcne : Kc ≠ ⊤ := (ENNReal.add_lt_top.2 ⟨measure_ball_lt_top, K1_lt_top⟩).ne
  set Kr : ℝ := Kc.toReal with hKr
  have hKr0 : 0 ≤ Kr := ENNReal.toReal_nonneg
  have hKc' : Kc = ENNReal.ofReal Kr := (ENNReal.ofReal_toReal hKcne).symm
  obtain ⟨C₀, hC₀⟩ := core_real_bound γ p hp0 Kr hKr0
  refine ⟨C₀, fun c ε hc hε hε8 hc4 => ?_⟩
  have hc1 : c ≤ 1 := by linarith
  have hR : (0 : ℝ) < 8 * ε := by positivity
  have hR1 : 8 * ε ≤ 1 := by linarith
  have hεR : ε ≤ 8 * ε / 8 := by linarith
  have hS : ∀ x ∈ Metric.ball (0 : ℂ) c, ‖x‖ ≤ 8 * ε / 2 := fun x hx => by
    have : ‖x‖ < c := mem_ball_zero_iff.1 hx
    linarith
  have hfin := rho_ne_top_ball (γ := γ) hε hc hc1
  have hmom := moment_bound h hR hR1 hε hεR γ p hp0 hp1 measurableSet_ball hS hfin
  have hrhoK := rhoK_set (γ := γ) (R := 8 * ε) hε hR measurableSet_ball
    (fun x hx => by have : ‖x‖ < c := mem_ball_zero_iff.1 hx
                    linarith)
  have hwb := lintegral_wgt_ball (γ := γ) hε hc hc1
  rw [volume_ball_eq_scale c hc.le] at hwb
  have hLnn : 0 ≤ Real.log (1 / c) := Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith)
  have hbr : ENNReal.ofReal (1 + Real.log (1 / c)) * (ENNReal.ofReal (c ^ 2) * MeasureTheory.volume (Metric.ball (0 : ℂ) 1))
      + ENNReal.ofReal (c ^ 2) * K1 ≤ ENNReal.ofReal (c ^ 2 * (1 + Real.log (1 / c))) * Kc := by
    have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (1 + Real.log (1 / c)) :=
      ENNReal.one_le_ofReal.2 (by linarith)
    have h2 : ENNReal.ofReal (c ^ 2) * K1 ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (1 + Real.log (1 / c)) * K1 := by
      calc ENNReal.ofReal (c ^ 2) * K1 = ENNReal.ofReal (c ^ 2) * 1 * K1 := by ring
        _ ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (1 + Real.log (1 / c)) * K1 := by gcongr
    calc ENNReal.ofReal (1 + Real.log (1 / c)) * (ENNReal.ofReal (c ^ 2) * MeasureTheory.volume (Metric.ball (0 : ℂ) 1))
          + ENNReal.ofReal (c ^ 2) * K1
        ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (1 + Real.log (1 / c)) * MeasureTheory.volume (Metric.ball (0 : ℂ) 1)
          + ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (1 + Real.log (1 / c)) * K1 := by
          rw [show ENNReal.ofReal (1 + Real.log (1 / c)) * (ENNReal.ofReal (c ^ 2) * MeasureTheory.volume (Metric.ball (0 : ℂ) 1))
              = ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (1 + Real.log (1 / c)) * MeasureTheory.volume (Metric.ball (0 : ℂ) 1) by ring]
          exact add_le_add le_rfl h2
      _ = ENNReal.ofReal (c ^ 2 * (1 + Real.log (1 / c))) * Kc := by
          rw [hKc, ENNReal.ofReal_mul (sq_nonneg c)]
          ring
  have hY : ENNReal.ofReal ((8 * ε) ^ (γ ^ 2 / 2)) * ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (wgt γ ε x)
      ≤ ENNReal.ofReal ((8 * ε) ^ (γ ^ 2 / 2) * ε ^ (-(γ ^ 2)) * (c ^ 2 * (1 + Real.log (1 / c))) * Kr) := by
    calc ENNReal.ofReal ((8 * ε) ^ (γ ^ 2 / 2)) * ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (wgt γ ε x)
        ≤ ENNReal.ofReal ((8 * ε) ^ (γ ^ 2 / 2)) * (ENNReal.ofReal (ε ^ (-(γ ^ 2))) *
            (ENNReal.ofReal (c ^ 2 * (1 + Real.log (1 / c))) * Kc)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hwb.trans (mul_le_mul_of_nonneg_left hbr (by positivity))
      _ = ENNReal.ofReal ((8 * ε) ^ (γ ^ 2 / 2) * ε ^ (-(γ ^ 2)) * (c ^ 2 * (1 + Real.log (1 / c))) * Kr) := by
          rw [hKc', ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hY0 : 0 ≤ (8 * ε) ^ (γ ^ 2 / 2) * ε ^ (-(γ ^ 2)) * (c ^ 2 * (1 + Real.log (1 / c))) * Kr :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (mul_nonneg (by positivity) (by linarith))) hKr0
  have hrhoKc := hrhoK
  calc ∫⁻ ω, weightedMass γ ε (hcirc ω) (Metric.ball (0 : ℂ) c) ^ p ∂P
      ≤ ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * (-Real.log (8 * ε)) / 2)) *
        ((∫⁻ x in Metric.ball (0 : ℂ) c, rho γ ε x) *
          ENNReal.ofReal (Real.exp (γ ^ 2 * (Real.log (8 * ε) - Real.log ε) / 2))) ^ p := hmom
    _ = ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * (-Real.log (8 * ε)) / 2)) *
        (ENNReal.ofReal ((8 * ε) ^ (γ ^ 2 / 2)) * ∫⁻ x in Metric.ball (0 : ℂ) c, ENNReal.ofReal (wgt γ ε x)) ^ p := by
        rw [hrhoKc]
    _ ≤ ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * (-Real.log (8 * ε)) / 2)) *
        (ENNReal.ofReal ((8 * ε) ^ (γ ^ 2 / 2) * ε ^ (-(γ ^ 2)) * (c ^ 2 * (1 + Real.log (1 / c))) * Kr)) ^ p :=
        mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hY hp0.le) (by positivity)
    _ = ENNReal.ofReal (Real.exp ((p * γ) ^ 2 * (-Real.log (8 * ε)) / 2) *
        ((8 * ε) ^ (γ ^ 2 / 2) * ε ^ (-(γ ^ 2)) * (c ^ 2 * (1 + Real.log (1 / c))) * Kr) ^ p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hY0 hp0.le, ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (C₀ * c ^ ((2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2) * (1 + Real.log (1 / c)) ^ p) :=
        ENNReal.ofReal_le_ofReal (hC₀ c ε hc hε hc1 hc4)


/-- The weighted mass power is a.e. measurable (a.e. equal to a limit of measurable dyadic approximations). -/
lemma aemeasurable_weightedMass_pow {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P] {R ε : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hε : 0 < ε) (hεR : ε ≤ R / 8) (γ p : ℝ) (hp0 : 0 < p) (_hp1 : p ≤ 1)
    {S : Set ℂ} (hSm : MeasurableSet S) (hS : ∀ x ∈ S, ‖x‖ ≤ R / 2) (hfin : ∫⁻ x in S, rho γ ε x ≠ ⊤) :
    AEMeasurable (fun ω => weightedMass γ ε (hcirc ω) S ^ p) P := by
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, 2 / (2:ℝ) ^ n0 ≤ R / 8 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (16 / R) (by norm_num : (1:ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hR] at hn
    nlinarith
  have hn : ∀ m : ℕ, 2 / (2:ℝ) ^ (n0 + m) ≤ R / 8 := fun m =>
    le_trans (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right n0 m))) hn0
  have hpt : ∀ ω : Ω, weightedMass γ ε (hcirc ω) S ^ p =
      ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)) *
        (∫⁻ x in S, rho γ ε x * ENNReal.ofReal (Real.exp (γ * (hcirc ω ε x - hcirc ω R 0)))) ^ p := by
    intro ω
    rw [weightedMass_eq (hcirc ω) γ ε (hcirc ω R 0) hε hSm (fun x hx => le_trans (hS x hx) (by linarith)),
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp0.le]
    have e : Real.exp (γ * hcirc ω R 0) ^ p = Real.exp (p * γ * hcirc ω R 0) := by
      rw [← Real.exp_mul]
      ring_nf
    rw [e]
  have hmeasΦ : ∀ m : ℕ, Measurable (fun ω => ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)) *
      Vn γ ε R hcirc S (n0 + m) ω ^ p) := fun m =>
    ((((h.measurable_circle R 0 hR).const_mul _).exp).ennreal_ofReal).mul
      ((measurable_Vn h hR hε γ S (n0 + m)).pow_const p)
  have hae : ∀ᵐ ω ∂P, weightedMass γ ε (hcirc ω) S ^ p = Filter.liminf
      (fun m : ℕ => ENNReal.ofReal (Real.exp (p * γ * hcirc ω R 0)) * Vn γ ε R hcirc S (n0 + m) ω ^ p)
      Filter.atTop := by
    filter_upwards [h.ae_continuousOn_circle] with ω hω
    rw [hpt ω]
    refine (Filter.Tendsto.liminf_eq ?_).symm
    have hV := tendsto_Vn (hcirc := hcirc) hR hε hεR γ hSm hS hfin n0 hn0 ω hω
    have hp : Filter.Tendsto (fun m : ℕ => Vn γ ε R hcirc S (n0 + m) ω ^ p) Filter.atTop
        (nhds ((∫⁻ x in S, rho γ ε x * ENNReal.ofReal (Real.exp (γ * (hcirc ω ε x - hcirc ω R 0)))) ^ p)) :=
      ((ENNReal.continuous_rpow_const).tendsto _).comp hV
    exact ENNReal.Tendsto.const_mul hp (Or.inr ENNReal.ofReal_ne_top)
  exact ((Measurable.liminf hmeasΦ).aemeasurable).congr (hae.mono fun ω hω => hω.symm)

lemma aemeasurable_annulus {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P] {γ p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {s ε : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 8) (hε : 0 < ε) (h4 : 4 * ε ≤ s) :
    AEMeasurable (fun ω => weightedMass γ ε (hcirc ω) (annulus s) ^ p) P := by
  have hs1' : s ≤ 1 := by linarith
  exact aemeasurable_weightedMass_pow h (R := 2 * s) (by positivity) (by linarith) hε (by linarith) γ p hp0 hp1
    (measurableSet_annulus s) (fun x hx => by have := hx.2; linarith)
    (ne_top_of_le_ne_top (rho_ne_top_ball hε hs hs1')
      (MeasureTheory.lintegral_mono_set (fun x hx => mem_ball_zero_iff.2 hx.2)))

lemma aemeasurable_core {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P] {γ p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) (hc4 : c ≤ 4 * ε) :
    AEMeasurable (fun ω => weightedMass γ ε (hcirc ω) (Metric.ball (0 : ℂ) c) ^ p) P :=
  aemeasurable_weightedMass_pow h (R := 8 * ε) (by positivity) (by linarith) hε (by linarith) γ p hp0 hp1
    measurableSet_ball (fun x hx => by have := mem_ball_zero_iff.1 hx; linarith)
    (rho_ne_top_ball (γ := γ) hε hc (by linarith))

/-- Regularized origin tails (`lem:occ-tails`): `E[(∫_{B_a} (1+log(1/|x|)) μ_ε(dx))^p] ≤ C a^κ (1+log(1/a))^p`
uniformly in small `ε`, for `0 < p < min{1, 4/γ²−1}` and `κ = (2−γ²/2)p − γ²p²/2 > 0`. -/
theorem origin_tail_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hc : Ω → ℝ → ℂ → ℝ) (hGFF : HarmonicBalls.IsWholePlaneGFF P hC hc)
    {γ p κ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hp0 : 0 < p) (hp1 : p < min 1 (4 / γ ^ 2 - 1))
    (hκ : κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2) :
    ∃ C : ℝ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Ioo 0 a₀, ∀ ε ∈ Ioo 0 a₀,
      ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 a) ^ p ∂P ≤
        ENNReal.ofReal (C * a ^ κ * (1 + Real.log (1 / a)) ^ p) := by
  -- `hGFF` and `hγ2` only fix the setting of the statement; the estimates enter through the binders
  have _ := hGFF
  have _ := hγ2
  have hp1le : p ≤ 1 := le_of_lt (lt_of_lt_of_le hp1 (min_le_left _ _))
  obtain ⟨C₁, hC₁⟩ := annulus_estimate hGFF hp0 hp1le
  rw [← hκ] at hC₁
  obtain ⟨C₂, hC₂⟩ := core_estimate hGFF hp0 hp1le
  rw [← hκ] at hC₂
  have hp1' : p ≤ 1 := le_of_lt (lt_of_lt_of_le hp1 (min_le_left _ _))
  have hp2 : p < 4 / γ ^ 2 - 1 := lt_of_lt_of_le hp1 (min_le_right _ _)
  have hg2 : 0 < γ ^ 2 := by positivity
  have h4 : γ ^ 2 * (1 + p) < 4 := by
    have h' : p < (4 - γ ^ 2) / γ ^ 2 := by
      rw [show (4 : ℝ) / γ ^ 2 - 1 = (4 - γ ^ 2) / γ ^ 2 by field_simp] at hp2
      exact hp2
    rw [lt_div_iff₀ hg2] at h'
    nlinarith
  have hκpos : 0 < κ := by
    have e : κ = p / 2 * (4 - γ ^ 2 * (1 + p)) := by rw [hκ]; ring
    rw [e]
    exact mul_pos (by linarith) (by linarith)
  set M : ℝ := max (max C₁ C₂) 0 with hM
  have hM1 : C₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : C₂ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  set q : ℝ := (1 / 2 : ℝ) ^ κ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hκpos
  have hK : Summable (fun j : ℕ => q ^ j * (1 + j * Real.log 2)) := by
    have h1 := summable_geometric_of_lt_one hq0 hq1
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_of_nonneg hq0]; exact hq1)
    refine (h1.add (h2.mul_left (Real.log 2))).congr (fun j => ?_)
    simp only [pow_one]
    ring
  refine ⟨M * ∑' j : ℕ, q ^ j * (1 + j * Real.log 2), 1 / 8, by norm_num, ?_⟩
  intro a ha ε hε
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hε0, hε1⟩ := hε
  have ha8 : a ≤ 1 / 8 := ha1.le
  set L : ℝ := Real.log (1 / a) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
  -- the dyadic index at which the radius first falls to `4ε`
  have hex : ∃ J : ℕ, a * (1 / 2) ^ J ≤ 4 * ε := by
    obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show 0 < 4 * ε / a by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
    exact ⟨J, by rw [mul_comm]; exact ((lt_div_iff₀ ha0).1 hJ).le⟩
  classical
  set J := Nat.find hex with hJdef
  have hJ : a * (1 / 2) ^ J ≤ 4 * ε := Nat.find_spec hex
  have hjlt : ∀ j < J, 4 * ε < a * (1 / 2) ^ j := fun j hj => not_le.mp (Nat.find_min hex hj)
  have hrad : ∀ j : ℕ, 0 < a * (1 / 2) ^ j ∧ a * (1 / 2) ^ j ≤ 1 / 8 := by
    intro j
    refine ⟨by positivity, le_trans ?_ ha8⟩
    exact mul_le_of_le_one_right ha0.le (pow_le_one₀ (by norm_num) (by norm_num))
  -- pointwise bound of one dyadic term by the power of `a`
  have key : ∀ j : ℕ, (a * (1 / 2) ^ j) ^ κ * (1 + Real.log (1 / (a * (1 / 2) ^ j))) ^ p ≤
      a ^ κ * (1 + L) ^ p * (q ^ j * (1 + j * Real.log 2)) := by
    intro j
    have h1 : (a * (1 / 2) ^ j) ^ κ = a ^ κ * q ^ j := by
      have hh : ((1 / 2 : ℝ) ^ j) ^ κ = ((1 / 2 : ℝ) ^ κ) ^ j := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]
      rw [Real.mul_rpow ha0.le (by positivity), hh, hq]
    have h2 : Real.log (1 / (a * (1 / 2) ^ j)) = L + j * Real.log 2 := by
      rw [hL, show 1 / (a * (1 / 2) ^ j) = (1 / a) * 2 ^ j by field_simp; rw [← mul_pow]; norm_num,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h3 : (1 + (L + j * Real.log 2)) ^ p ≤ (1 + L) ^ p * (1 + j * Real.log 2) := by
      have hj0 : 0 ≤ (j : ℝ) * Real.log 2 := by positivity
      have hA : 1 + (L + j * Real.log 2) ≤ (1 + L) * (1 + j * Real.log 2) := by nlinarith
      have hB : (1 + j * Real.log 2) ^ p ≤ 1 + j * Real.log 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + j * Real.log 2 by linarith) hp1'
        simpa using this
      calc (1 + (L + j * Real.log 2)) ^ p ≤ ((1 + L) * (1 + j * Real.log 2)) ^ p :=
            Real.rpow_le_rpow (by linarith) hA hp0.le
        _ = (1 + L) ^ p * (1 + j * Real.log 2) ^ p := Real.mul_rpow (by linarith) (by nlinarith)
        _ ≤ (1 + L) ^ p * (1 + j * Real.log 2) := mul_le_mul_of_nonneg_left hB (by positivity)
    rw [h1, h2]
    have hnn : 0 ≤ a ^ κ := by positivity
    calc a ^ κ * q ^ j * (1 + (L + j * Real.log 2)) ^ p
        ≤ a ^ κ * q ^ j * ((1 + L) ^ p * (1 + j * Real.log 2)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = a ^ κ * (1 + L) ^ p * (q ^ j * (1 + j * Real.log 2)) := by ring
  have hlog : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ 1 + Real.log (1 / s) := fun s hs hs1 => by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / s by rw [le_div_iff₀ hs]; linarith)
    linarith
  -- the core radius `c = a 2^{-J}` and the dyadic terms
  set c : ℝ := a * (1 / 2) ^ J with hcdef
  have hc0 : 0 < c := by positivity
  set u : ℕ → ℝ := fun j => M * (a ^ κ * (1 + L) ^ p) * (q ^ j * (1 + j * Real.log 2)) with hu
  have hu0 : ∀ j, 0 ≤ u j := fun j => by
    simp only [hu]
    have hX : 0 ≤ 1 + L := by linarith
    positivity
  have hus : Summable u := hK.mul_left _
  -- core bound
  have hF : ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 c) ^ p ∂P ≤ ENNReal.ofReal (u J) := by
    refine (hC₂ c ε hc0 hε0 hε1.le hJ).trans (ENNReal.ofReal_le_ofReal ?_)
    have hX : 0 ≤ c ^ κ * (1 + Real.log (1 / c)) ^ p :=
      mul_nonneg (Real.rpow_nonneg hc0.le _) (Real.rpow_nonneg (hlog c hc0 (by linarith)) _)
    calc C₂ * c ^ κ * (1 + Real.log (1 / c)) ^ p
        = C₂ * (c ^ κ * (1 + Real.log (1 / c)) ^ p) := by ring
      _ ≤ M * (c ^ κ * (1 + Real.log (1 / c)) ^ p) := mul_le_mul_of_nonneg_right hM2 hX
      _ ≤ M * (a ^ κ * (1 + L) ^ p * (q ^ J * (1 + J * Real.log 2))) :=
          mul_le_mul_of_nonneg_left (key J) hM0
      _ = u J := by simp only [hu]; ring
  -- annulus bounds
  have hG : ∀ j ∈ Finset.range J,
      ∫⁻ ω, weightedMass γ ε (hc ω) (annulus (a * (1 / 2) ^ j)) ^ p ∂P ≤ ENNReal.ofReal (u j) := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.1 hj
    obtain ⟨hs0, hs1⟩ := hrad j
    refine (hC₁ (a * (1 / 2) ^ j) ε hs0 hs1 hε0 (le_of_lt (hjlt j hjJ))).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hX : 0 ≤ (a * (1 / 2) ^ j) ^ κ * (1 + Real.log (1 / (a * (1 / 2) ^ j))) ^ p :=
      mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg (hlog _ hs0 (by linarith)) _)
    calc C₁ * (a * (1 / 2) ^ j) ^ κ * (1 + Real.log (1 / (a * (1 / 2) ^ j))) ^ p
        = C₁ * ((a * (1 / 2) ^ j) ^ κ * (1 + Real.log (1 / (a * (1 / 2) ^ j))) ^ p) := by ring
      _ ≤ M * ((a * (1 / 2) ^ j) ^ κ * (1 + Real.log (1 / (a * (1 / 2) ^ j))) ^ p) :=
          mul_le_mul_of_nonneg_right hM1 hX
      _ ≤ M * (a ^ κ * (1 + L) ^ p * (q ^ j * (1 + j * Real.log 2))) :=
          mul_le_mul_of_nonneg_left (key j) hM0
      _ = u j := by simp only [hu]; ring
  -- expectation of the dyadic decomposition
  have hmeasF : AEMeasurable (fun ω => weightedMass γ ε (hc ω) (ball 0 c) ^ p) P :=
    aemeasurable_core hGFF hp0 hp1le (c := c) (ε := ε) hc0 hε0 hε1.le hJ
  have hmeasG : ∀ j ∈ Finset.range J, AEMeasurable (fun ω => weightedMass γ ε (hc ω) (annulus (a * (1 / 2) ^ j)) ^ p) P :=
    fun j hj => aemeasurable_annulus hGFF hp0 hp1le (hrad j).1 (hrad j).2 hε0 (le_of_lt (hjlt j (Finset.mem_range.1 hj)))
  have hpt : ∀ ω, weightedMass γ ε (hc ω) (ball 0 a) ^ p ≤
      weightedMass γ ε (hc ω) (ball 0 c) ^ p +
        ∑ j ∈ Finset.range J, weightedMass γ ε (hc ω) (annulus (a * (1 / 2) ^ j)) ^ p := by
    intro ω
    rw [weightedMass_dyadic γ ε a (hc ω) ha0 J]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1').trans
      (add_le_add le_rfl (rpow_sum_le_sum_rpow _ _ hp0 hp1'))
  have htsum : ∑' j, u j = M * (a ^ κ * (1 + L) ^ p) * ∑' j : ℕ, q ^ j * (1 + j * Real.log 2) := by
    rw [← tsum_mul_left]
  calc ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 a) ^ p ∂P
      ≤ ∫⁻ ω, (weightedMass γ ε (hc ω) (ball 0 c) ^ p +
          ∑ j ∈ Finset.range J, weightedMass γ ε (hc ω) (annulus (a * (1 / 2) ^ j)) ^ p) ∂P :=
        lintegral_mono hpt
    _ = ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 c) ^ p ∂P +
          ∑ j ∈ Finset.range J, ∫⁻ ω, weightedMass γ ε (hc ω) (annulus (a * (1 / 2) ^ j)) ^ p ∂P := by
        rw [lintegral_add_left' hmeasF, lintegral_finsetSum' _ (fun j hj => hmeasG j hj)]
    _ ≤ (∑ j ∈ Finset.range J, ENNReal.ofReal (u j)) + ENNReal.ofReal (u J) := by
        rw [add_comm]
        exact add_le_add (Finset.sum_le_sum fun j hj => hG j hj) hF
    _ ≤ ENNReal.ofReal (∑' j, u j) := sum_ofReal_le_ofReal_tsum J u hu0 hus
    _ ≤ ENNReal.ofReal ((M * ∑' j : ℕ, q ^ j * (1 + j * Real.log 2)) * a ^ κ * (1 + L) ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        rw [htsum]
        exact le_of_eq (by ring)

end MatedCRT.KilledOccupation
