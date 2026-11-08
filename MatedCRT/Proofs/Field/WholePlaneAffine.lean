import MatedCRT.Proofs.Field.WholePlaneAffineCov
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Covariance

/-!
# The affine transform of a whole-plane GFF is a whole-plane GFF

For `r > 0` and `z ∈ ℂ` the field `h ↦ h(r · + z) - h_r(z)` of a whole-plane GFF `h` (Duplantier-Sheffield 2011,
eq:gff-scaling; Harmonic-Balls `WholePlaneGFFAffineInvariance`, here for real scalings) has pairings
`r^{-2} h(φ^T) - (∫φ) h_r(z)` with `φ^T = φ((· - z)/r)`, and circle averages `h_{rs}(rv + z) - h_r(z)`.
This file proves that these observables are a whole-plane GFF, i.e. `IsWholePlaneGFF` is preserved:

* the family of new observables is a finite affine combination of the old family, hence Gaussian;
* the covariances are the bilinear expansions of the old covariances, and the three identities
  `affine_pp`, `affine_pc`, `affine_cc` (`WholePlaneAffineCov.lean`) identify them with the whole-plane kernel.

The normalization circle `∂B_r(z)` is the common old observable `b` of all new observables.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Set HarmonicBalls

/-- Gaussian closure: a finite affine combination `α_s V(a_s) + β_s V(b_s)` of a Gaussian process `V` is Gaussian. -/
theorem isGaussianProcess_comb {Ω T S : Type*} [MeasurableSpace Ω] {P : Measure Ω} {V : T → Ω → ℝ}
    (hV : IsGaussianProcess V P) (a b : S → T) (α β : S → ℝ) :
    IsGaussianProcess (fun s ω => α s * V (a s) ω + β s * V (b s) ω) P := by
  classical
  refine hV.of_isGaussianProcess fun s => ⟨{a s, b s}, ?_, ?_⟩
  · exact (α s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({a s, b s} : Finset T) => ℝ) ⟨a s, by simp⟩
      + (β s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({a s, b s} : Finset T) => ℝ) ⟨b s, by simp⟩
  · intro ω
    simp [Finset.restrict]

/-- The pullback `φ((· - z)/r)` of a test function is a test function. -/
theorem isTestFunction_affPull {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    IsTestFunction Set.univ (affPull r z φ) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨?_, ?_, subset_univ _⟩
  · exact hφ.1.comp ((contDiff_id.sub contDiff_const).div_const (r : ℂ))
  · exact hφ.2.1.comp_homeomorph
      ((Homeomorph.subRight z).trans (Homeomorph.mulRight₀ (r : ℂ)⁻¹ (inv_ne_zero hr')))

/-- The pairings of the affine transform `h ↦ h(r · + z) - h_r(z)`. -/
noncomputable def affHC {Ω : Type*} (r : ℝ) (z : ℂ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    Ω → (ℂ → ℝ) → ℝ :=
  fun ω φ => (r ^ 2)⁻¹ * hC ω (affPull r z φ) - hcirc ω r z * ∫ x, φ x

/-- The circle averages of the affine transform `h ↦ h(r · + z) - h_r(z)`. -/
noncomputable def affHcirc {Ω : Type*} (r : ℝ) (z : ℂ) (hcirc : Ω → ℝ → ℂ → ℝ) : Ω → ℝ → ℂ → ℝ :=
  fun ω s v => hcirc ω (r * s) ((r : ℂ) * v + z) - hcirc ω r z

/-- The family `o ↦ o.eval (hC ω) (hcirc ω)` of a whole-plane sample. -/
def obsFam {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    GFFObservable.Admissible → Ω → ℝ :=
  fun o ω => o.1.eval (hC ω) (hcirc ω)

/-- The admissible observable of the normalization circle `∂B_r(z)`. -/
def normIdx (r : ℝ) (z : ℂ) (hr : 0 < r) : GFFObservable.Admissible := ⟨.circle r z, hr⟩

/-- The old observable of a new one: pairing `φ` ↦ pairing `φ^T`, circle `(s, v)` ↦ circle `(r s, r v + z)`. -/
noncomputable def affIdx (r : ℝ) (z : ℂ) (hr : 0 < r) : GFFObservable.Admissible → GFFObservable.Admissible
  | ⟨.pairing φ, hφ⟩ => ⟨.pairing (affPull r z φ), isTestFunction_affPull hφ hr z⟩
  | ⟨.circle s v, hs⟩ => ⟨.circle (r * s) ((r : ℂ) * v + z), mul_pos hr hs⟩

/-- The coefficient of the old observable `o` in the new one. -/
noncomputable def affCoef (r : ℝ) : GFFObservable.Admissible → ℝ
  | ⟨.pairing _, _⟩ => (r ^ 2)⁻¹
  | ⟨.circle _ _, _⟩ => 1

/-- The coefficient of the normalization circle in the new observable. -/
noncomputable def affShift : GFFObservable.Admissible → ℝ
  | ⟨.pairing φ, _⟩ => -∫ x, φ x
  | ⟨.circle _ _, _⟩ => -1

/-- Each new observable is the affine combination `affCoef · V(old) + affShift · V(normalization)`. -/
theorem obs_affine_eq {Ω : Type*} (r : ℝ) (z : ℂ) (hr : 0 < r) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (o : GFFObservable.Admissible) (ω : Ω) :
    o.1.eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω)
      = affCoef r o * obsFam hC hcirc (affIdx r z hr o) ω
        + affShift o * obsFam hC hcirc (normIdx r z hr) ω := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => simp [obsFam, affHC, affCoef, affShift, affIdx, normIdx, GFFObservable.eval]; ring
  | circle s v => simp [obsFam, affHcirc, affCoef, affShift, affIdx, normIdx, GFFObservable.eval]; ring

/-- Each old observable is in `L²`. -/
theorem memLp_obs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (o : GFFObservable.Admissible) : MemLp (obsFam hC hcirc o) 2 P :=
  (hh.isGaussianProcess.hasGaussianLaw_eval o).memLp_two

/-- The covariance of the whole-plane GFF is symmetric on admissible observables. -/
theorem wGC_symm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {o o' : GFFObservable} (ho : o.IsAdmissible) (ho' : o'.IsAdmissible) :
    wholePlaneGFFCov o o' = wholePlaneGFFCov o' o :=
  ((hh.covariance_eq o o' ho ho').symm.trans (covariance_comm _ _)).trans (hh.covariance_eq o' o ho' ho)

/-- Bilinear expansion of the covariance of two affine combinations of two `L²` variables. -/
theorem cov_comb_four {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X1 X2 Y1 Y2 : Ω → ℝ} (hX1 : MemLp X1 2 P) (hX2 : MemLp X2 2 P) (hY1 : MemLp Y1 2 P) (hY2 : MemLp Y2 2 P)
    (a b c d : ℝ) :
    cov[fun ω => a * X1 ω + b * X2 ω, fun ω => c * Y1 ω + d * Y2 ω; P]
      = a * c * cov[X1, Y1; P] + a * d * cov[X1, Y2; P] + b * c * cov[X2, Y1; P] + b * d * cov[X2, Y2; P] := by
  have e1 : (fun ω => a * X1 ω + b * X2 ω) = (fun ω => a * X1 ω) + (fun ω => b * X2 ω) := rfl
  have e2 : (fun ω => c * Y1 ω + d * Y2 ω) = (fun ω => c * Y1 ω) + (fun ω => d * Y2 ω) := rfl
  have hA := hX1.const_mul a
  have hB := hX2.const_mul b
  have hC := hY1.const_mul c
  have hD := hY2.const_mul d
  rw [e1, e2, covariance_add_left hA hB (hC.add hD), covariance_add_right hA hC hD,
    covariance_add_right hB hC hD]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- The covariance of two new observables, expanded in the old covariances. -/
theorem cov_affine_obs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (o o' : GFFObservable.Admissible) :
    cov[fun ω => o.1.eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω),
        fun ω => o'.1.eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω); P]
      = affCoef r o * affCoef r o' * wholePlaneGFFCov (affIdx r z hr o).1 (affIdx r z hr o').1
        + affCoef r o * affShift o' * wholePlaneGFFCov (affIdx r z hr o).1 (normIdx r z hr).1
        + affShift o * affCoef r o' * wholePlaneGFFCov (normIdx r z hr).1 (affIdx r z hr o').1
        + affShift o * affShift o' * wholePlaneGFFCov (normIdx r z hr).1 (normIdx r z hr).1 := by
  have e : ∀ p : GFFObservable.Admissible,
      (fun ω => p.1.eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω))
        = fun ω => affCoef r p * obsFam hC hcirc (affIdx r z hr p) ω
          + affShift p * obsFam hC hcirc (normIdx r z hr) ω :=
    fun p => funext fun ω => obs_affine_eq r z hr hC hcirc p ω
  have k1 : cov[obsFam hC hcirc (affIdx r z hr o), obsFam hC hcirc (affIdx r z hr o'); P]
      = wholePlaneGFFCov (affIdx r z hr o).1 (affIdx r z hr o').1 :=
    hh.covariance_eq _ _ (affIdx r z hr o).2 (affIdx r z hr o').2
  have k2 : cov[obsFam hC hcirc (affIdx r z hr o), obsFam hC hcirc (normIdx r z hr); P]
      = wholePlaneGFFCov (affIdx r z hr o).1 (normIdx r z hr).1 :=
    hh.covariance_eq _ _ (affIdx r z hr o).2 (normIdx r z hr).2
  have k3 : cov[obsFam hC hcirc (normIdx r z hr), obsFam hC hcirc (affIdx r z hr o'); P]
      = wholePlaneGFFCov (normIdx r z hr).1 (affIdx r z hr o').1 :=
    hh.covariance_eq _ _ (normIdx r z hr).2 (affIdx r z hr o').2
  have k4 : cov[obsFam hC hcirc (normIdx r z hr), obsFam hC hcirc (normIdx r z hr); P]
      = wholePlaneGFFCov (normIdx r z hr).1 (normIdx r z hr).1 :=
    hh.covariance_eq _ _ (normIdx r z hr).2 (normIdx r z hr).2
  rw [e o, e o', cov_comb_four (memLp_obs hh _) (memLp_obs hh _) (memLp_obs hh _) (memLp_obs hh _), k1, k2, k3, k4]

/-! ### The covariance identities of the four types of observables -/

theorem wGC_pp (A B : ℂ → ℝ) :
    wholePlaneGFFCov (.pairing A) (.pairing B)
      = ∫ x, A x * ∫ y, B y * HarmonicBalls.wholePlaneCov x y := rfl

theorem wGC_pN (A : ℂ → ℝ) (r : ℝ) (z : ℂ) :
    wholePlaneGFFCov (.pairing A) (.circle r z) = ∫ x, A x * A0 z r x := rfl

theorem wGC_NN (r : ℝ) (z : ℂ) : wholePlaneGFFCov (.circle r z) (.circle r z) = B0 z r := rfl

theorem wGC_p_circle (A : ℂ → ℝ) (s : ℝ) (w : ℂ) :
    wholePlaneGFFCov (.pairing A) (.circle s w)
      = ∫ x, A x * Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) w s := rfl

theorem wGC_circle_N (r s : ℝ) (z w : ℂ) :
    wholePlaneGFFCov (.circle (r * s) ((r : ℂ) * w + z)) (.circle r z)
      = Real.circleAverage (A0 z r) ((r : ℂ) * w + z) (r * s) := rfl

theorem wGC_cc (s t : ℝ) (w v : ℂ) :
    wholePlaneGFFCov (.circle s w) (.circle t v)
      = Real.circleAverage (fun x => Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) v t) w s := rfl

/-- Pairing with pairing: the new covariance is the whole-plane covariance of the pairings. -/
theorem cov_affine_pp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {φ ψ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ)
    (hψ : IsTestFunction Set.univ ψ) :
    cov[fun ω => (GFFObservable.pairing φ).eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω),
        fun ω => (GFFObservable.pairing ψ).eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω); P]
      = wholePlaneGFFCov (.pairing φ) (.pairing ψ) := by
  refine (cov_affine_obs hh hr z ⟨.pairing φ, hφ⟩ ⟨.pairing ψ, hψ⟩).trans ?_
  rw [wGC_symm hh (normIdx r z hr).2 (affIdx r z hr ⟨.pairing ψ, hψ⟩).2]
  simp only [affCoef, affShift, affIdx, normIdx]
  rw [wGC_pp (affPull r z φ) (affPull r z ψ), wGC_pN (affPull r z φ) r z, wGC_pN (affPull r z ψ) r z,
    wGC_NN r z, wGC_pp φ ψ]
  linear_combination affine_pp hr z hφ hψ

/-- Pairing with circle average: `wholePlaneGFFCov (pairing φ) (circle s w)`. -/
theorem cov_affine_pc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ)
    {s : ℝ} (hs : 0 < s) (w : ℂ) :
    cov[fun ω => (GFFObservable.pairing φ).eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω),
        fun ω => (GFFObservable.circle s w).eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω); P]
      = wholePlaneGFFCov (.pairing φ) (.circle s w) := by
  refine (cov_affine_obs hh hr z ⟨.pairing φ, hφ⟩ ⟨.circle s w, hs⟩).trans ?_
  rw [wGC_symm hh (normIdx r z hr).2 (affIdx r z hr ⟨.circle s w, hs⟩).2]
  simp only [affCoef, affShift, affIdx, normIdx]
  rw [wGC_p_circle (affPull r z φ) (r * s) ((r : ℂ) * w + z), wGC_pN (affPull r z φ) r z,
    wGC_circle_N r s z w, wGC_NN r z, wGC_p_circle φ s w]
  linear_combination affine_pc hr z hφ hs w

/-- Circle average with pairing: by symmetry of the covariance. -/
theorem cov_affine_cp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ)
    {s : ℝ} (hs : 0 < s) (w : ℂ) :
    cov[fun ω => (GFFObservable.circle s w).eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω),
        fun ω => (GFFObservable.pairing φ).eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω); P]
      = wholePlaneGFFCov (.circle s w) (.pairing φ) := by
  rw [covariance_comm _ _, cov_affine_pc hh hr z hφ hs w]
  exact wGC_symm hh (o := GFFObservable.pairing φ) (o' := GFFObservable.circle s w) hφ hs

/-- Circle average with circle average. -/
theorem cov_affine_cc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (w v : ℂ) :
    cov[fun ω => (GFFObservable.circle s w).eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω),
        fun ω => (GFFObservable.circle t v).eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω); P]
      = wholePlaneGFFCov (.circle s w) (.circle t v) := by
  refine (cov_affine_obs hh hr z ⟨.circle s w, hs⟩ ⟨.circle t v, ht⟩).trans ?_
  rw [wGC_symm hh (normIdx r z hr).2 (affIdx r z hr ⟨.circle t v, ht⟩).2]
  simp only [affCoef, affShift, affIdx, normIdx]
  rw [wGC_cc (r * s) (r * t) ((r : ℂ) * w + z) ((r : ℂ) * v + z), wGC_circle_N r s z w,
    wGC_circle_N r t z v, wGC_NN r z, wGC_cc s t w v]
  linear_combination affine_cc hr z hs ht w v

/-- **The affine transform of a whole-plane GFF is a whole-plane GFF.** For `r > 0` and `z ∈ ℂ`, the pairings
`r^{-2} h(φ^T) - (∫φ) h_r(z)` and the circle averages `h_{rs}(r v + z) - h_r(z)` form a whole-plane GFF
(Duplantier-Sheffield 2011, eq:gff-scaling; Harmonic-Balls `WholePlaneGFFAffineInvariance` for real scalings). -/
theorem isWholePlaneGFF_affine {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    IsWholePlaneGFF P (affHC r z hC hcirc) (affHcirc r z hcirc) := by
  refine
    { measurable_pairing := ?_
      measurable_circle := ?_
      isGaussianProcess := ?_
      integral_eq_zero := ?_
      covariance_eq := ?_
      ae_continuousOn_circle := ?_ }
  · intro φ hφ
    exact ((hh.measurable_pairing _ (isTestFunction_affPull hφ hr z)).const_mul _).sub
      ((hh.measurable_circle r z hr).mul_const _)
  · intro s v hs
    exact (hh.measurable_circle (r * s) _ (mul_pos hr hs)).sub (hh.measurable_circle r z hr)
  · have e : (fun (o : GFFObservable.Admissible) ω => o.1.eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω))
        = fun (o : GFFObservable.Admissible) ω => affCoef r o * obsFam hC hcirc (affIdx r z hr o) ω
          + affShift o * obsFam hC hcirc (normIdx r z hr) ω :=
      funext fun o => funext fun ω => obs_affine_eq r z hr hC hcirc o ω
    rw [e]
    exact isGaussianProcess_comb (V := obsFam hC hcirc) hh.isGaussianProcess (affIdx r z hr)
      (fun _ => normIdx r z hr) (affCoef r) affShift
  · intro o ho
    have e : ∀ ω, o.eval (affHC r z hC hcirc ω) (affHcirc r z hcirc ω)
        = affCoef r ⟨o, ho⟩ * obsFam hC hcirc (affIdx r z hr ⟨o, ho⟩) ω
          + affShift ⟨o, ho⟩ * obsFam hC hcirc (normIdx r z hr) ω :=
      fun ω => obs_affine_eq r z hr hC hcirc ⟨o, ho⟩ ω
    have h1 : ∫ ω, obsFam hC hcirc (affIdx r z hr ⟨o, ho⟩) ω ∂P = 0 :=
      hh.integral_eq_zero _ (affIdx r z hr ⟨o, ho⟩).2
    have h2 : ∫ ω, obsFam hC hcirc (normIdx r z hr) ω ∂P = 0 :=
      hh.integral_eq_zero _ (normIdx r z hr).2
    have i1 := (MemLp.integrable one_le_two (memLp_obs hh (affIdx r z hr ⟨o, ho⟩))).const_mul
      (affCoef r ⟨o, ho⟩)
    have i2 := (MemLp.integrable one_le_two (memLp_obs hh (normIdx r z hr))).const_mul (affShift ⟨o, ho⟩)
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_add i1 i2, integral_const_mul,
      integral_const_mul, h1, h2]
    ring
  · intro o o' ho ho'
    cases o with
    | pairing φ =>
      cases o' with
      | pairing ψ => exact cov_affine_pp hh hr z ho ho'
      | circle s w => exact cov_affine_pc hh hr z ho ho' w
    | circle s w =>
      cases o' with
      | pairing ψ => exact cov_affine_cp hh hr z ho' ho w
      | circle t v => exact cov_affine_cc hh hr z ho ho' w v
  · filter_upwards [hh.ae_continuousOn_circle] with ω hω
    have hmap : ContinuousOn (fun p : ℝ × ℂ => (r * p.1, (r : ℂ) * p.2 + z)) (Set.Ioi 0 ×ˢ Set.univ) :=
      (Continuous.prodMk (continuous_const.mul continuous_fst)
        ((continuous_const.mul continuous_snd).add continuous_const)).continuousOn
    have hmaps : Set.MapsTo (fun p : ℝ × ℂ => (r * p.1, (r : ℂ) * p.2 + z)) (Set.Ioi 0 ×ˢ Set.univ)
        (Set.Ioi 0 ×ˢ Set.univ) := fun p hp => ⟨mul_pos hr hp.1, Set.mem_univ _⟩
    exact (hω.comp hmap hmaps).sub continuousOn_const

end MatedCRT.Field

