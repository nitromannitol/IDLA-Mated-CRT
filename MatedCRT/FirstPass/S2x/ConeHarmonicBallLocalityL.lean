import MatedCRT.FirstPass.S2x.ConeHarmonicBallLocality
import HarmonicBalls.Proofs.Potential.GreenLocalVolumeBound
import HarmonicBalls.Steps.Sec3.Basic
import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity
import HarmonicBalls.Proofs.Sec6.DiscGreenMass
import HarmonicBalls.Proofs.Sec5.GeneralDomainGreenQuadrature
import HarmonicBalls.Proofs.Sec5.PuncturePotentialShift
import HarmonicBalls.Proofs.Potential.Fundamental
import HarmonicBalls.Proofs.Sec5.BoundaryRightContinuity

/-!
# Restriction invariance of the obstacle package to `B_1` (ingredients of `hL`, radii `r ≤ 1`)

For measures `μ, μ'` with `μ|_U = μ'|_U` on an open set `U`, the clauses of the harmonic-ball package that involve only
test functions supported in `U` do not change:

* `integrable_test_iff_of_restrict`, `integral_test_eq_of_restrict`: a test function on `U` sees only `μ|_U`;
* `laplacianLE_iff_of_restrict`, `hasLaplacian_iff_of_restrict`: the distributional clauses `Δw ≤ μ`, `Δw = μ⁺ - μ⁻`
  in `U` (Armitage-Gardiner, distributional Laplacian);
* `supersolutions_eq_of_restrict`, `leastSupersolution_eq_of_restrict`, `cluster_eq_of_restrict`: the obstacle problem
  on the disc `B_r` depends only on `μ|_{B_r}` (`S_{B_r;z}(t)`, `v_{B_r;z}(t)`, `Λ_{B_r;z}(t)`, Armitage-Gardiner);
* `hasMeanValueProperty_iff_of_restrict`, `isHarmonicBall_iff_of_restrict`: a set `Λ ⊆ U` is a harmonic ball for `μ`
  iff it is one for `μ'` (`μ(Λ)` and the mean value property see only `μ|_Λ`).

The radii `ρ ≥ 1` of the obstacle characterization are not covered here: they need the outer-domain argument
(notes/fp-gaps/CHATGPT-213-idla-cone-hlim-hL-hM-PRO.md, section 2, step 8).
-/

open MeasureTheory Set Metric
open _root_.HarmonicBalls
open Laplacian

namespace MatedCRT.FirstPass2x.ConeLocality

/-- A test function on `U` equals its indicator on `U`. -/
theorem indicator_eq_of_isTestFunction {U : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) :
    U.indicator φ = φ := by
  funext x
  by_cases hx : x ∈ U
  · exact indicator_of_mem hx φ
  · have hx' : x ∉ tsupport φ := fun h => hx (hφ.2.2 h)
    rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx']

/-- Integrability of a test function on `U` depends only on `μ|_U`. -/
theorem integrable_test_iff_of_restrict {U : Set ℂ} (hU : IsOpen U) {μ μ' : Measure ℂ}
    (h : μ.restrict U = μ'.restrict U) {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) :
    Integrable φ μ ↔ Integrable φ μ' := by
  have key : ∀ m : Measure ℂ, Integrable φ m ↔ Integrable φ (m.restrict U) := fun m => by
    have h1 : Integrable φ m ↔ Integrable (U.indicator φ) m := by
      rw [indicator_eq_of_isTestFunction hφ]
    rw [h1]
    exact integrable_indicator_iff hU.measurableSet
  rw [key μ, key μ', h]

/-- The integral of a test function on `U` depends only on `μ|_U`. -/
theorem integral_test_eq_of_restrict {U : Set ℂ} (hU : IsOpen U) {μ μ' : Measure ℂ}
    (h : μ.restrict U = μ'.restrict U) {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) :
    ∫ x, φ x ∂μ = ∫ x, φ x ∂μ' := by
  have key : ∀ m : Measure ℂ, ∫ x, φ x ∂m = ∫ x in U, φ x ∂m := fun m => by
    rw [← integral_indicator hU.measurableSet, indicator_eq_of_isTestFunction hφ]
  rw [key μ, key μ', h]

/-- `Δw ≤ μ` in `U` depends only on `μ|_U`. -/
theorem laplacianLE_iff_of_restrict {w : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) {μ μ' : Measure ℂ}
    (h : μ.restrict U = μ'.restrict U) : LaplacianLE w μ U ↔ LaplacianLE w μ' U := by
  have key : ∀ m m' : Measure ℂ, m.restrict U = m'.restrict U → LaplacianLE w m U → LaplacianLE w m' U := by
    intro m m' hm hL
    obtain ⟨hloc, hle⟩ := hL
    refine ⟨hloc, fun φ hφ h0 hint => ?_⟩
    have hint' : Integrable φ m := (integrable_test_iff_of_restrict hU hm hφ).2 hint
    have hle' := hle φ hφ h0 hint'
    rwa [integral_test_eq_of_restrict hU hm hφ] at hle'
  exact ⟨key μ μ' h, key μ' μ h.symm⟩

/-- `Δw = μ⁺ - μ⁻` in `U` depends only on `μ⁺|_U` and `μ⁻|_U`. -/
theorem hasLaplacian_iff_of_restrict {w : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) {μp μn μp' μn' : Measure ℂ}
    (hp : μp.restrict U = μp'.restrict U) (hn : μn.restrict U = μn'.restrict U) :
    HasLaplacian w μp μn U ↔ HasLaplacian w μp' μn' U := by
  constructor
  · rintro ⟨hloc, hd⟩
    refine ⟨hloc, fun φ hφ => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hd φ hφ
    refine ⟨(integrable_test_iff_of_restrict hU hp hφ).1 h1, (integrable_test_iff_of_restrict hU hn hφ).1 h2, ?_⟩
    rw [← integral_test_eq_of_restrict hU hp hφ, ← integral_test_eq_of_restrict hU hn hφ]
    exact h3
  · rintro ⟨hloc, hd⟩
    refine ⟨hloc, fun φ hφ => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hd φ hφ
    refine ⟨(integrable_test_iff_of_restrict hU hp.symm hφ).1 h1,
      (integrable_test_iff_of_restrict hU hn.symm hφ).1 h2, ?_⟩
    rw [integral_test_eq_of_restrict hU hp hφ, integral_test_eq_of_restrict hU hn hφ]
    exact h3

/-- `μ|_U = μ'|_U` and `Λ ⊆ U` give `μ|_Λ = μ'|_Λ`. -/
theorem restrict_eq_of_subset {U Λ : Set ℂ} (hΛ : MeasurableSet Λ) (hsub : Λ ⊆ U) {μ μ' : Measure ℂ}
    (h : μ.restrict U = μ'.restrict U) : μ.restrict Λ = μ'.restrict Λ := by
  have key : ∀ m : Measure ℂ, m.restrict Λ = (m.restrict U).restrict Λ := fun m => by
    rw [Measure.restrict_restrict hΛ, inter_eq_left.2 hsub]
  rw [key μ, key μ', h]

/-- The mean value property of a set `Λ ⊆ U` depends only on `μ|_U`. -/
theorem hasMeanValueProperty_iff_of_restrict {U Λ : Set ℂ} (hΛ : MeasurableSet Λ) (hsub : Λ ⊆ U)
    {μ μ' : Measure ℂ} (h : μ.restrict U = μ'.restrict U) (z : ℂ) (f : ℂ → ℝ) :
    HasMeanValueProperty μ Λ z f ↔ HasMeanValueProperty μ' Λ z f := by
  have hΛμ := restrict_eq_of_subset hΛ hsub h
  have hval : μ Λ = μ' Λ := by
    rw [← Measure.restrict_apply_univ, hΛμ, Measure.restrict_apply_univ]
  simp only [HasMeanValueProperty, IntegrableOn, measureReal_def, hval, hΛμ]

/-- A set `Λ ⊆ U` is a harmonic ball for `μ` iff it is one for any `μ'` with `μ|_U = μ'|_U`. -/
theorem isHarmonicBall_iff_of_restrict {U Λ : Set ℂ} (hΛ : IsOpen Λ) (hsub : Λ ⊆ U)
    {μ μ' : Measure ℂ} (h : μ.restrict U = μ'.restrict U) (z : ℂ) :
    IsHarmonicBall μ Λ z ↔ IsHarmonicBall μ' Λ z := by
  have hΛm : MeasurableSet Λ := hΛ.measurableSet
  have hval : μ Λ = μ' Λ := by
    rw [← Measure.restrict_apply_univ, restrict_eq_of_subset hΛm hsub h, Measure.restrict_apply_univ]
  have hmvp : ∀ f : ℂ → ℝ, HasMeanValueProperty μ Λ z f ↔ HasMeanValueProperty μ' Λ z f :=
    fun f => hasMeanValueProperty_iff_of_restrict hΛm hsub h z f
  unfold IsHarmonicBall
  simp only [hval, hmvp]

/-- The set of supersolutions `S_{B_r;z}(t)` depends only on `μ|_{B_r}`. -/
theorem supersolutions_eq_of_restrict {μ μ' : Measure ℂ} {r t : ℝ} {z : ℂ}
    (h : μ.restrict (ball 0 r) = μ'.restrict (ball 0 r)) :
    supersolutions μ r z t = supersolutions μ' r z t := by
  ext w
  simp only [supersolutions, mem_ofPred_eq]
  rw [laplacianLE_iff_of_restrict isOpen_ball h]

/-- The least supersolution `v_{B_r;z}(t)` depends only on `μ|_{B_r}`. -/
theorem leastSupersolution_eq_of_restrict {μ μ' : Measure ℂ} {r t : ℝ} {z : ℂ}
    (h : μ.restrict (ball 0 r) = μ'.restrict (ball 0 r)) :
    leastSupersolution μ r z t = leastSupersolution μ' r z t := by
  funext x
  unfold leastSupersolution
  rw [supersolutions_eq_of_restrict h]

/-- The cluster `Λ_{B_r;z}(t)` depends only on `μ|_{B_r}`. -/
theorem cluster_eq_of_restrict {μ μ' : Measure ℂ} {r t : ℝ} {z : ℂ}
    (h : μ.restrict (ball 0 r) = μ'.restrict (ball 0 r)) :
    cluster μ r z t = cluster μ' r z t := by
  unfold cluster
  rw [leastSupersolution_eq_of_restrict h]

/-- Radii `r ≤ 1`: the restrictions of `ν` and `ν'` to `B_r` agree when they agree on `B_1`. -/
theorem restrict_ball_eq_of_le_one {ν ν' : Measure ℂ} (hres : ν.restrict (ball 0 1) = ν'.restrict (ball 0 1))
    {r : ℝ} (hr : r ≤ 1) : ν.restrict (ball 0 r) = ν'.restrict (ball 0 r) :=
  restrict_eq_of_subset isOpen_ball.measurableSet (ball_subset_ball hr) hres

#print axioms MatedCRT.FirstPass2x.ConeLocality.laplacianLE_iff_of_restrict
#print axioms MatedCRT.FirstPass2x.ConeLocality.hasLaplacian_iff_of_restrict
#print axioms MatedCRT.FirstPass2x.ConeLocality.isHarmonicBall_iff_of_restrict
#print axioms MatedCRT.FirstPass2x.ConeLocality.cluster_eq_of_restrict

/-! ## Part 2: the outer domain `ρ > R` (locality of the obstacle package, step 8 of notes/fp-gaps/CHATGPT-213 section 2)

`discG r x := G_{B_r}(0,x)` (Armitage-Gardiner Green function with pole at the centre). The explicit formula
`discG r x = (2π)⁻¹ log⁺(r/|x|)` (`greenFunction_ball_center_eq_posLog`) gives `discG ρ - discG R = κ` on `B_R \ {0}`
with the constant `κ = (2π)⁻¹ log(ρ/R)`. For `1/2 < R < 1` and `ρ > R`, the least supersolution on `B_ρ` is the explicit
glued function `outerW = v - tκ` on `cl B_R`, `-t G_{B_ρ}(0,·)` outside (`v` the least supersolution on `B_R`). -/

section OuterDomain

open Real

/-- The Green function of the disc `B_r` with pole at its centre `0`, `G_{B_r}(0,·)`. -/
noncomputable def discG (r : ℝ) (x : ℂ) : ℝ := greenFunction (ball (0 : ℂ) r) 0 x

theorem posLog_eq_log_of_one_le {a : ℝ} (ha : 1 ≤ a) : Real.posLog a = Real.log a :=
  max_eq_right (Real.log_nonneg ha)

theorem posLog_eq_zero_of_le_one {a : ℝ} (ha : a ≤ 1) (ha0 : 0 ≤ a) : Real.posLog a = 0 :=
  max_eq_left (Real.log_nonpos ha0 ha)

theorem discG_eq {r : ℝ} (hr : 0 < r) (x : ℂ) :
    discG r x = (2 * π)⁻¹ * Real.posLog (r / ‖x‖) := by
  have h := greenFunction_ball_center_eq_posLog hr 0 x
  simpa [discG, sub_zero] using h

theorem discG_of_le_norm {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : r ≤ ‖x‖) : discG r x = 0 := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le hr hx
  rw [discG_eq hr x, posLog_eq_zero_of_le_one ((div_le_one hn).2 hx) (div_nonneg hr.le hn.le), mul_zero]

theorem discG_shift {R ρ : ℝ} (hR : 0 < R) (hRρ : R < ρ) {x : ℂ} (hx0 : x ≠ 0) (hxR : ‖x‖ ≤ R) :
    discG ρ x = discG R x + (2 * π)⁻¹ * Real.log (ρ / R) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h1 : 1 ≤ R / ‖x‖ := (one_le_div hn).2 hxR
  have h2 : 1 ≤ ρ / ‖x‖ := (one_le_div hn).2 (hxR.trans hRρ.le)
  rw [discG_eq (hR.trans hRρ) x, discG_eq hR x, posLog_eq_log_of_one_le h1,
    posLog_eq_log_of_one_le h2]
  have hsplit : ρ / ‖x‖ = (R / ‖x‖) * (ρ / R) := by
    field_simp
  rw [hsplit, Real.log_mul (div_pos hR hn).ne' (div_pos (hR.trans hRρ) hR).ne']
  ring

theorem continuousOn_discG {r : ℝ} (hr : 0 < r) : ContinuousOn (discG r) {0}ᶜ := by
  have h : ContinuousOn (fun x : ℂ => (2 * π)⁻¹ * Real.posLog (r / ‖x‖)) {0}ᶜ :=
    continuousOn_const.mul (Real.continuous_posLog.comp_continuousOn
      (continuousOn_const.div continuous_norm.continuousOn fun _ hx => norm_ne_zero_iff.2 hx))
  exact h.congr fun x _ => discG_eq hr x

/-- Laplacian of a sum with a multiple of a Green function: `Δ(u + tG) = μ - tδ_z` when `Δu = μ` and `ΔG = -δ_z`. -/
theorem hasLaplacian_add_const_mul_dirac {u G : ℂ → ℝ} {M : Measure ℂ} {U : Set ℂ} {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hu : HasLaplacian u M 0 U) (hG : HasLaplacian G 0 (Measure.dirac z) U) :
    HasLaplacian (fun x => u x + t * G x) M (ENNReal.ofReal t • Measure.dirac z) U := by
  refine ⟨hu.1.add (hG.1.smul t), fun φ hφ => ?_⟩
  obtain ⟨hM, -, hu'⟩ := hu.2 φ hφ
  obtain ⟨-, hD, hG'⟩ := hG.2 φ hφ
  refine ⟨hM, hD.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  have i1 := integrable_mul_laplacian_of_test hu.1 hφ
  have i2 := (integrable_mul_laplacian_of_test hG.1 hφ).const_mul t
  have hfun : (fun x => (u x + t * G x) * Δ φ x) = fun x => u x * Δ φ x + t * (G x * Δ φ x) := by
    funext x; ring
  rw [hfun, integral_add i1 i2, integral_const_mul, hu', hG', integral_smul_measure, integral_dirac,
    integral_zero_measure, ENNReal.toReal_ofReal ht]
  simp only [smul_eq_mul]
  ring

/-- The shift constant `κ = (2π)⁻¹ log(ρ/R)`: `discG ρ - discG R = κ` on `B_R \ {0}`. -/
noncomputable def outerShift (R ρ : ℝ) : ℝ := (2 * π)⁻¹ * Real.log (ρ / R)

/-- The glued candidate of the outer step: `v - tκ` on `cl B_R` and `-t G_{B_ρ}(0,·)` outside `cl B_R`. -/
noncomputable def outerW (v : ℂ → ℝ) (t R ρ : ℝ) (x : ℂ) : ℝ :=
  if ‖x‖ ≤ R then v x - t * outerShift R ρ else -(t * discG ρ x)

theorem continuousOn_outerW {v : ℂ → ℝ} {t R ρ : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hvc : ContinuousOn v (closedBall 0 R)) (hvsph : ∀ x ∈ sphere (0 : ℂ) R, v x = 0) :
    ContinuousOn (outerW v t R ρ) (closedBall 0 ρ) := by
  have hρ : 0 < ρ := hR.trans hRρ
  have h1 : ContinuousOn (outerW v t R ρ) (closedBall 0 R) := by
    have hc : ContinuousOn (fun x => v x - t * outerShift R ρ) (closedBall 0 R) :=
      hvc.sub continuousOn_const
    refine hc.congr fun x hx => ?_
    have hle : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 hx
    simp [outerW, hle]
  have hS : {x : ℂ | R ≤ ‖x‖} ⊆ {0}ᶜ := fun x hx h0 => by
    have h' : R ≤ ‖x‖ := hx
    rw [h0, norm_zero] at h'
    linarith
  have h2 : ContinuousOn (outerW v t R ρ) {x : ℂ | R ≤ ‖x‖} := by
    have hc : ContinuousOn (fun x => -(t * discG ρ x)) {x : ℂ | R ≤ ‖x‖} :=
      (continuousOn_const.mul ((continuousOn_discG hρ).mono hS)).neg
    refine hc.congr fun x hx => ?_
    have hx' : R ≤ ‖x‖ := hx
    rcases le_or_gt ‖x‖ R with hle | hgt
    · have hxR : ‖x‖ = R := le_antisymm hle hx'
      have hsph : x ∈ sphere (0 : ℂ) R := by simpa [mem_sphere_zero_iff_norm] using hxR
      have hx0 : x ≠ 0 := fun h0 => by rw [h0, norm_zero] at hxR; linarith
      have hle' : ‖x‖ ≤ R := hle
      simp only [outerW, hle', ite_true, hvsph x hsph, zero_sub]
      rw [discG_shift hR hRρ hx0 hle', discG_of_le_norm hR hx']
      simp only [outerShift]
      ring
    · have hgt' : ¬ ‖x‖ ≤ R := not_le.2 hgt
      simp only [outerW, hgt', ite_false]
  have hcov : closedBall (0 : ℂ) ρ ⊆ closedBall (0 : ℂ) R ∪ {x : ℂ | R ≤ ‖x‖} := by
    intro x hx
    have hx' : ‖x‖ ≤ ρ := by simpa using hx
    rcases le_total ‖x‖ R with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr h
  exact ((h1.union_of_isClosed h2 isClosed_closedBall (isClosed_le continuous_const continuous_norm)).mono hcov)

end OuterDomain

section OuterDomainLaplacian

/-- Off the pole the least supersolution is above the obstacle `-tG_{B_r}(0,·)` (`bddBelow_supersolutions`). -/
theorem leastSupersolution_ge_obstacle {μ : Measure ℂ} {r t : ℝ} (ht : 0 ≤ t) {x : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) r) (hx0 : x ≠ 0) :
    -(t * discG r x) ≤ leastSupersolution μ r 0 t x := by
  unfold leastSupersolution
  refine le_csInf ⟨(0 : ℂ → ℝ) x, 0, zero_mem_supersolutions_ball (μ := μ) ht, rfl⟩ ?_
  rintro _ ⟨w, hw, rfl⟩
  have h := hw.2.2 x hx hx0
  unfold discG
  linarith

/-- Localization of `LaplacianLE` to a smaller open set, and adding a constant (`∫ Δφ = 0`). -/
theorem laplacianLE_add_const {u : ℂ → ℝ} {μ : Measure ℂ} {U V : Set ℂ} (hUV : U ⊆ V) (c : ℝ)
    (hu : LaplacianLE u μ V) : LaplacianLE (fun x => u x + c) μ U := by
  refine ⟨(hu.1.mono_set hUV).add (locallyIntegrableOn_const c), fun φ hφ hφ0 hμφ => ?_⟩
  have hφV : IsTestFunction V φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hUV⟩
  have h2 := hu.2 φ hφV hφ0 hμφ
  have h0 : ∫ x, Δ φ x = 0 := integral_laplacian_eq_zero (hφ.1.of_le (by norm_num)) hφ.2.1
  have i1 := integrable_mul_laplacian_of_test (hu.1.mono_set hUV) hφ
  have i2 := integrable_mul_laplacian_of_test (locallyIntegrableOn_const c) hφ
  have hfun : (fun x => (u x + c) * Δ φ x) = fun x => u x * Δ φ x + c * Δ φ x := by
    funext x; ring
  rw [hfun, integral_add i1 i2, integral_const_mul, h0, mul_zero, add_zero]
  exact h2

/-- The Laplacian of the glued candidate: `Δ outerW = μ|_Λ` on `B_ρ`, from `Δv = μ|_Λ` on `B_R`, the Green function
pole `ΔG_{B_R} = -δ_0`, the zero extension of `v + tG_{B_R}` (it vanishes on `B_R \ cl B_{1/2}`) and `ΔG_{B_ρ} = -δ_0`. -/
theorem hasLaplacian_outerW {μ : Measure ℂ} {L : Set ℂ} {v : ℂ → ℝ} {t R ρ : ℝ} (ht : 0 ≤ t)
    (hR : 1 / 2 < R) (hRρ : R < ρ) (hLm : MeasurableSet L) (hL : L ⊆ ball (0 : ℂ) (1 / 2))
    (hvlap : HasLaplacian v (μ.restrict L) 0 (ball (0 : ℂ) R))
    (hvann : ∀ x ∈ ball (0 : ℂ) R, 1 / 2 ≤ ‖x‖ → x ≠ 0 → v x = -(t * discG R x))
    (hvsph : ∀ x ∈ sphere (0 : ℂ) R, v x = 0) :
    HasLaplacian (outerW v t R ρ) (μ.restrict L) 0 (ball (0 : ℂ) ρ) := by
  have hR0 : 0 < R := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hGR : HasLaplacian (discG R) 0 (Measure.dirac 0) (ball (0 : ℂ) R) := by
    have h := hasLaplacian_greenFunction_pole (U := ball (0 : ℂ) R) isOpen_ball isBounded_ball
      (mem_ball_self hR0)
    have hfun : (fun x => greenFunction (ball (0 : ℂ) R) x 0) = discG R :=
      funext fun x => Section6.greenFunction_ball_center_comm 0 R x 0
    rw [hfun] at h
    exact h
  have hGρ : HasLaplacian (discG ρ) 0 (Measure.dirac 0) (ball (0 : ℂ) ρ) := by
    have h := hasLaplacian_greenFunction_pole (U := ball (0 : ℂ) ρ) isOpen_ball isBounded_ball
      (mem_ball_self hρ0)
    have hfun : (fun x => greenFunction (ball (0 : ℂ) ρ) x 0) = discG ρ :=
      funext fun x => Section6.greenFunction_ball_center_comm 0 ρ x 0
    rw [hfun] at h
    exact h
  have hF := hasLaplacian_add_const_mul_dirac ht hvlap hGR
  have hKU : closedBall (0 : ℂ) (1 / 2) ⊆ ball (0 : ℂ) R := closedBall_subset_ball hR
  have hα : (μ.restrict L) (closedBall (0 : ℂ) (1 / 2))ᶜ = 0 := by
    have hempty : (closedBall (0 : ℂ) (1 / 2))ᶜ ∩ L = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
      intro hy hyL
      exact hy (ball_subset_closedBall (hL hyL))
    rw [Measure.restrict_apply' hLm, hempty, measure_empty]
  have hβ : (ENNReal.ofReal t • Measure.dirac (0 : ℂ)) (closedBall (0 : ℂ) (1 / 2))ᶜ = 0 := by
    have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) (1 / 2) := mem_closedBall_self (by norm_num)
    simp
  have hext := HasLaplacian.extend_by_zero_of_compact isOpen_ball (isCompact_closedBall 0 (1 / 2)) hKU hF
    (fun x hx hxK => by
      have h12 : 1 / 2 < ‖x‖ := by
        have : ¬ ‖x‖ ≤ 1 / 2 := fun h => hxK (mem_closedBall_zero_iff.2 h)
        exact not_le.1 this
      have hx0 : x ≠ 0 := fun h0 => by rw [h0, norm_zero] at h12; linarith
      rw [hvann x hx h12.le hx0]
      ring)
    hα hβ
  have hũ := hext.mono_domain (subset_univ (ball (0 : ℂ) ρ))
  have hW := HasLaplacian.sub_const_mul ht hũ hGρ
  refine HasLaplacian.congr_ae_volume hW ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with x hx0
  have hx0' : x ≠ 0 := Set.mem_compl_singleton_iff.1 hx0
  rcases le_or_gt ‖x‖ R with hle | hgt
  · simp only [outerW, hle, ite_true]
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hxb : x ∈ ball (0 : ℂ) R := mem_ball_zero_iff.2 hlt
      rw [Set.indicator_of_mem hxb]
      rw [discG_shift hR0 hRρ hx0' hle]
      simp only [outerShift]
      ring
    · have hxs : x ∈ sphere (0 : ℂ) R := mem_sphere_zero_iff_norm.2 heq
      have hxb : x ∉ ball (0 : ℂ) R := fun h => by
        have := mem_ball_zero_iff.1 h
        linarith
      rw [Set.indicator_of_notMem hxb, discG_shift hR0 hRρ hx0' hle, discG_of_le_norm hR0 heq.ge,
        hvsph x hxs]
      simp only [outerShift]
      ring
  · have hxb : x ∉ ball (0 : ℂ) R := fun h => by
      have := mem_ball_zero_iff.1 h
      linarith
    rw [Set.indicator_of_notMem hxb]
    simp only [outerW, not_le.2 hgt, ite_false]
    ring

end OuterDomainLaplacian

section OuterDomainIdentity

/-- Annulus identity: if the cluster at `B_R` has interior `L ⊆ B_{1/2}`, the least supersolution equals the obstacle
`-tG_{B_R}(0,·)` on `B_R \ cl B_{1/2}` (the open set `{x ≠ 0 : -tG < v}` lies in the cluster, hence in `L`). -/
theorem leastSupersolution_eq_neg_of_annulus {μ : Measure ℂ} {L : Set ℂ} {t R : ℝ} (hR : 0 < R) (ht : 0 ≤ t)
    (hLc : L = interior (closure (cluster μ R 0 t))) (hL : L ⊆ ball (0 : ℂ) (1 / 2))
    (hvc : ContinuousOn (leastSupersolution μ R 0 t) (closedBall 0 R)) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) R) (hx0 : x ≠ 0) (hxh : 1 / 2 ≤ ‖x‖) :
    leastSupersolution μ R 0 t x = -(t * discG R x) := by
  have hfc : ContinuousOn (fun y => leastSupersolution μ R 0 t y + t * discG R y)
      (ball (0 : ℂ) R ∩ {0}ᶜ) :=
    (hvc.mono (fun y hy => ball_subset_closedBall hy.1)).add
      (continuousOn_const.mul ((continuousOn_discG hR).mono fun y hy => hy.2))
  have hUo : IsOpen ((ball (0 : ℂ) R ∩ {0}ᶜ) ∩
      (fun y => leastSupersolution μ R 0 t y + t * discG R y) ⁻¹' Set.Ioi 0) :=
    hfc.isOpen_inter_preimage (isOpen_ball.inter isOpen_compl_singleton) isOpen_Ioi
  have hUc : ((ball (0 : ℂ) R ∩ {0}ᶜ) ∩
      (fun y => leastSupersolution μ R 0 t y + t * discG R y) ⁻¹' Set.Ioi 0) ⊆ cluster μ R 0 t := by
    rintro y ⟨⟨hyb, hy0⟩, hpos⟩
    have hpos' : 0 < leastSupersolution μ R 0 t y + t * discG R y := hpos
    refine ⟨hyb, Or.inr ?_⟩
    unfold discG at hpos'
    linarith
  have hUL : ((ball (0 : ℂ) R ∩ {0}ᶜ) ∩
      (fun y => leastSupersolution μ R 0 t y + t * discG R y) ⁻¹' Set.Ioi 0) ⊆ L := by
    rw [hLc]
    exact fun y hy => interior_mono subset_closure (interior_maximal hUc hUo hy)
  have hfx : ¬ (0 < leastSupersolution μ R 0 t x + t * discG R x) := by
    intro hpos
    have hxU : x ∈ ((ball (0 : ℂ) R ∩ {0}ᶜ) ∩
        (fun y => leastSupersolution μ R 0 t y + t * discG R y) ⁻¹' Set.Ioi 0) :=
      ⟨⟨hx, hx0⟩, hpos⟩
    have h1 := hL (hUL hxU)
    rw [mem_ball_zero_iff] at h1
    linarith
  have hlow := leastSupersolution_ge_obstacle (μ := μ) ht (ball_subset_closedBall hx) hx0
  replace hfx := not_lt.1 hfx
  linarith

/-- Lower bound for the outer candidate: every supersolution `u` on `B_ρ` (for a measure `μ'` whose least supersolution on
`B_R` is `v`) lies above `outerW` on `cl B_ρ`. Off the pole this is `u + tκ ∈ S_{B_R}(t)`; at the pole it follows from the
continuity of `u` and `outerW` (no volume growth is needed). -/
theorem outerW_le_of_mem {μ' : Measure ℂ} {v : ℂ → ℝ} {t R ρ : ℝ} (_ht : 0 ≤ t)
    (hR : 1 / 2 < R) (hRρ : R < ρ) (hv' : leastSupersolution μ' R 0 t = v)
    (hvc : ContinuousOn v (closedBall 0 R)) (hvsph : ∀ x ∈ sphere (0 : ℂ) R, v x = 0)
    {u : ℂ → ℝ} (hu : u ∈ supersolutions μ' ρ 0 t) :
    ∀ x ∈ closedBall (0 : ℂ) ρ, outerW v t R ρ x ≤ u x := by
  have hR0 : 0 < R := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hcont := continuousOn_outerW (t := t) hR0 hRρ hvc hvsph
  have hpt : ∀ x ∈ closedBall (0 : ℂ) ρ, x ≠ 0 → outerW v t R ρ x ≤ u x := by
    intro x hxρ hx0
    rcases le_or_gt ‖x‖ R with hle | hgt
    · have hxR : x ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.2 hle
      have hmem : (fun y => u y + t * outerShift R ρ) ∈ supersolutions μ' R 0 t := by
        refine ⟨(hu.1.mono (closedBall_subset_closedBall hRρ.le)).add continuousOn_const, ?_, ?_⟩
        · exact laplacianLE_add_const (ball_subset_ball hRρ.le) _ hu.2.1
        · intro y hy hy0
          have h1 : -t * greenFunction (ball 0 ρ) 0 y ≤ u y :=
            hu.2.2 y (closedBall_subset_closedBall hRρ.le hy) hy0
          have h2 : greenFunction (ball 0 ρ) 0 y = greenFunction (ball 0 R) 0 y + outerShift R ρ :=
            discG_shift hR0 hRρ hy0 (mem_closedBall_zero_iff.1 hy)
          rw [h2] at h1
          linarith
      have hlow : leastSupersolution μ' R 0 t x ≤ u x + t * outerShift R ρ :=
        csInf_le (bddBelow_supersolutions hxR hx0) (Set.mem_image_of_mem (fun w : ℂ → ℝ => w x) hmem)
      rw [hv'] at hlow
      simp only [outerW, hle, ite_true]
      linarith
    · have h1 : -t * greenFunction (ball 0 ρ) 0 x ≤ u x := hu.2.2 x hxρ hx0
      simp only [outerW, not_le.2 hgt, ite_false]
      unfold discG
      linarith
  have hgc : ContinuousOn (fun y => u y - outerW v t R ρ y) (closedBall 0 ρ) := hu.1.sub hcont
  have hC : IsClosed ((closedBall (0 : ℂ) ρ) ∩ (fun y => u y - outerW v t R ρ y) ⁻¹' Set.Ici 0) :=
    hgc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Ici
  have hS : closedBall (0 : ℂ) ρ \ {0} ⊆
      (closedBall (0 : ℂ) ρ) ∩ (fun y => u y - outerW v t R ρ y) ⁻¹' Set.Ici 0 := by
    rintro y ⟨hy, hy0⟩
    refine ⟨hy, ?_⟩
    have := hpt y hy hy0
    show 0 ≤ u y - outerW v t R ρ y
    linarith
  have h0cl : (0 : ℂ) ∈ closure (closedBall (0 : ℂ) ρ \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hm : 0 < min ε ρ / 2 := by
      have := lt_min hε hρ0
      linarith
    refine ⟨((min ε ρ / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hm.le]
      have := min_le_right ε ρ
      linarith
    · intro h
      exact hm.ne' (Complex.ofReal_eq_zero.1 h)
    · rw [dist_zero_left, Complex.norm_real, Real.norm_of_nonneg hm.le]
      have := min_le_left ε ρ
      linarith
  have h0C := closure_minimal hS hC h0cl
  have h0 : 0 ≤ u 0 - outerW v t R ρ 0 := h0C.2
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0]
    linarith
  · exact hpt x hx hx0

/-- The least supersolution on `B_ρ` (`ρ > R`) of a measure `μ'` is the glued candidate `outerW` on `cl B_ρ`, as soon as
`μ'` has the same least supersolution on `B_R` and `Δ(outerW) = μ'|_L` on `B_ρ`. -/
theorem leastSupersolution_eq_outerW {μ' : Measure ℂ} {L : Set ℂ} {v : ℂ → ℝ} {t R ρ : ℝ} (ht : 0 ≤ t)
    (hR : 1 / 2 < R) (hRρ : R < ρ) (hv' : leastSupersolution μ' R 0 t = v)
    (hvc : ContinuousOn v (closedBall 0 R)) (hvsph : ∀ x ∈ sphere (0 : ℂ) R, v x = 0)
    (hvob : ∀ x ∈ closedBall (0 : ℂ) R, x ≠ 0 → -(t * discG R x) ≤ v x)
    (hW : HasLaplacian (outerW v t R ρ) (μ'.restrict L) 0 (ball (0 : ℂ) ρ)) :
    ∀ x ∈ closedBall (0 : ℂ) ρ, leastSupersolution μ' ρ 0 t x = outerW v t R ρ x := by
  have hR0 : 0 < R := by linarith
  have hcont := continuousOn_outerW (t := t) hR0 hRρ hvc hvsph
  have hmem : outerW v t R ρ ∈ supersolutions μ' ρ 0 t := by
    refine ⟨hcont, ⟨hW.1, fun φ hφ hφ0 hμφ => ?_⟩, fun x hxρ hx0 => ?_⟩
    · obtain ⟨-, -, heq⟩ := hW.2 φ hφ
      rw [heq, integral_zero_measure, sub_zero]
      exact setIntegral_le_integral hμφ (Filter.Eventually.of_forall hφ0)
    · have key : -(t * discG ρ x) ≤ outerW v t R ρ x := by
        rcases le_or_gt ‖x‖ R with hle | hgt
        · have hxR : x ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.2 hle
          have hv1 := hvob x hxR hx0
          have hsh := discG_shift hR0 hRρ hx0 hle
          simp only [outerW, hle, ite_true]
          rw [hsh]
          simp only [outerShift]
          linarith
        · simp only [outerW, not_le.2 hgt, ite_false]
          exact le_refl _
      unfold discG at key
      linarith
  have hbdd : ∀ x ∈ closedBall (0 : ℂ) ρ,
      BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ' ρ 0 t) := fun x hx =>
    ⟨outerW v t R ρ x, by
      rintro _ ⟨u, hu, rfl⟩
      exact outerW_le_of_mem ht hR hRρ hv' hvc hvsph hu x hx⟩
  intro x hx
  apply le_antisymm
  · exact csInf_le (hbdd x hx) (Set.mem_image_of_mem (fun w : ℂ → ℝ => w x) hmem)
  · refine le_csInf ⟨outerW v t R ρ x, Set.mem_image_of_mem (fun w : ℂ → ℝ => w x) hmem⟩ ?_
    rintro _ ⟨u, hu, rfl⟩
    exact outerW_le_of_mem ht hR hRρ hv' hvc hvsph hu x hx

end OuterDomainIdentity

section Assembly

/-- The clauses of the obstacle characterization of Theorem 2.3 (lines 518-526) at one radius `ρ` for the set `L = Λ_t`. -/
abbrev ConeObstacleClauses (μ : Measure ℂ) (L : Set ℂ) (t ρ : ℝ) : Prop :=
  L = interior (closure (cluster μ ρ 0 t)) ∧ ContinuousOn (leastSupersolution μ ρ 0 t) (closedBall 0 ρ) ∧
    HasLaplacian (leastSupersolution μ ρ 0 t) (μ.restrict L) 0 (ball 0 ρ) ∧
    ∀ x ∈ sphere (0 : ℂ) ρ, leastSupersolution μ ρ 0 t x = 0

/-- The masses of subsets of `B_1` agree for measures with the same restriction to `B_1`. -/
theorem measure_congr_of_restrict_ball {ν ν' : Measure ℂ}
    (hres : ν.restrict (ball (0 : ℂ) 1) = ν'.restrict (ball (0 : ℂ) 1)) {A : Set ℂ} (hA : MeasurableSet A)
    (hsub : A ⊆ ball (0 : ℂ) 1) : ν A = ν' A := by
  have h := congrArg (fun m : Measure ℂ => m A) hres
  simp only [Measure.restrict_apply hA, Set.inter_eq_left.2 hsub] at h
  exact h

/-- The closure of a subset of `B_{1/2}` lies in `B_1`. -/
theorem closure_subset_ball_one_of_subset_half {A : Set ℂ} (h : A ⊆ ball (0 : ℂ) (1 / 2)) :
    closure A ⊆ ball (0 : ℂ) 1 :=
  (closure_minimal (h.trans ball_subset_closedBall) isClosed_closedBall).trans
    (closedBall_subset_ball (by norm_num))

/-- The cluster depends only on the least supersolution on the closed ball. -/
theorem cluster_congr_of_eqOn {μ μ' : Measure ℂ} {r t : ℝ} {z : ℂ}
    (h : ∀ x ∈ closedBall (0 : ℂ) r, leastSupersolution μ' r z t x = leastSupersolution μ r z t x) :
    cluster μ' r z t = cluster μ r z t := by
  ext x
  unfold cluster
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hP⟩
    exact ⟨hx, by rwa [h x (ball_subset_closedBall hx)] at hP⟩
  · rintro ⟨hx, hP⟩
    exact ⟨hx, by rwa [← h x (ball_subset_closedBall hx)] at hP⟩

/-- Radii `ρ ≤ 1`: the clauses transfer through the restriction to `B_ρ`. -/
theorem coneObstacleClauses_of_le {ν ν' : Measure ℂ}
    (hres : ν.restrict (ball (0 : ℂ) 1) = ν'.restrict (ball (0 : ℂ) 1)) {L : Set ℂ} (hLm : MeasurableSet L)
    (hL1 : L ⊆ ball (0 : ℂ) 1) {t ρ : ℝ} (hρ : ρ ≤ 1) (h : ConeObstacleClauses ν L t ρ) :
    ConeObstacleClauses ν' L t ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hr := restrict_ball_eq_of_le_one hres hρ
  have hlss : leastSupersolution ν ρ 0 t = leastSupersolution ν' ρ 0 t :=
    leastSupersolution_eq_of_restrict (z := 0) hr
  have hcl : cluster ν ρ 0 t = cluster ν' ρ 0 t := cluster_eq_of_restrict (z := 0) hr
  have hLres : ν.restrict L = ν'.restrict L := restrict_eq_of_subset hLm hL1 hres
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hcl]
    exact h1
  · rw [← hlss]
    exact h2
  · rw [← hlss, ← hLres]
    exact h3
  · intro x hx
    rw [← hlss]
    exact h4 x hx

/-- Radii `ρ > 3/4`: the clauses for `ν'` follow from those of `ν` at `R = 3/4` and at `ρ` (the glued candidate). -/
theorem coneObstacleClauses_of_outer {ν ν' : Measure ℂ}
    (hres : ν.restrict (ball (0 : ℂ) 1) = ν'.restrict (ball (0 : ℂ) 1)) {L : Set ℂ} {t ρ : ℝ} (ht : 0 < t)
    (hLm : MeasurableSet L) (hL1 : L ⊆ ball (0 : ℂ) 1)
    (hL : L ⊆ ball (0 : ℂ) (1 / 2)) (hR : ConeObstacleClauses ν L t (3 / 4)) (hρ : 3 / 4 < ρ)
    (hLρ : L = interior (closure (cluster ν ρ 0 t))) :
    ConeObstacleClauses ν' L t ρ := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hR
  have hR34 : (3 : ℝ) / 4 ≤ 1 := by norm_num
  have hv' : leastSupersolution ν' (3 / 4) 0 t = leastSupersolution ν (3 / 4) 0 t :=
    (leastSupersolution_eq_of_restrict (z := 0) (restrict_ball_eq_of_le_one hres hR34)).symm
  have hvob : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 →
      -(t * discG (3 / 4) x) ≤ leastSupersolution ν (3 / 4) 0 t x :=
    fun x hx hx0 => leastSupersolution_ge_obstacle (μ := ν) ht.le hx hx0
  have hann : ∀ x ∈ ball (0 : ℂ) (3 / 4), 1 / 2 ≤ ‖x‖ → x ≠ 0 →
      leastSupersolution ν (3 / 4) 0 t x = -(t * discG (3 / 4) x) :=
    fun x hx h12 hx0 => leastSupersolution_eq_neg_of_annulus (by norm_num) ht.le hc1 hL hc2 hx hx0 h12
  have hW := hasLaplacian_outerW (μ := ν) (L := L) (v := leastSupersolution ν (3 / 4) 0 t) (t := t) (R := 3 / 4)
    (ρ := ρ) ht.le (by norm_num) hρ hLm hL hc3 hann hc4
  have hLres : ν'.restrict L = ν.restrict L := (restrict_eq_of_subset hLm hL1 hres).symm
  have hW' : HasLaplacian (outerW (leastSupersolution ν (3 / 4) 0 t) t (3 / 4) ρ) (ν'.restrict L) 0
      (ball (0 : ℂ) ρ) := by
    rw [hLres]
    exact hW
  have hid' := leastSupersolution_eq_outerW (μ' := ν') (L := L) ht.le (by norm_num) hρ hv' hc2 hc4 hvob hW'
  have hidν := leastSupersolution_eq_outerW (μ' := ν) (L := L) ht.le (by norm_num) hρ rfl hc2 hc4 hvob hW
  have hcl : cluster ν' ρ 0 t = cluster ν ρ 0 t :=
    cluster_congr_of_eqOn (fun x hx => by rw [hid' x hx, hidν x hx])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcl]
    exact hLρ
  · exact (continuousOn_outerW (t := t) (by norm_num) hρ hc2 hc4).congr (fun x hx => hid' x hx)
  · exact hW'.congr_eqOn measurableSet_ball (fun x hx => (hid' x (ball_subset_closedBall hx)).symm)
  · intro x hx
    rw [hid' x (sphere_subset_closedBall hx)]
    have hxn : ‖x‖ = ρ := mem_sphere_zero_iff_norm.1 hx
    have hgt : ¬ ‖x‖ ≤ 3 / 4 := by
      rw [hxn]
      exact not_le.2 hρ
    have hd : discG ρ x = 0 := discG_of_le_norm (by linarith) hxn.ge
    simp only [outerW, hgt, ite_false, hd, mul_zero, neg_zero]

/-- **Restriction invariance of `HasConeHarmonicBallsUpToHalfBall`** (the forward half of `hL`, HB22 Proposition 1.3 in
the form needed here): a family for `ν` (Lemma 2.4) is a family for every `ν'` with the same restriction to `B_1`. The
stopping time and the family `Λ` are unchanged. -/
theorem hasConeHarmonicBallsUpToHalfBall_of_restrict {ν ν' : Measure ℂ}
    (hres : ν.restrict (ball (0 : ℂ) 1) = ν'.restrict (ball (0 : ℂ) 1))
    (h : MatedCRT.HasConeHarmonicBallsUpToHalfBall ν) : MatedCRT.HasConeHarmonicBallsUpToHalfBall ν' := by
  obtain ⟨T, hT, Λ, ⟨hIH, hSHB, hOC⟩, hstop⟩ := h
  have hLo : ∀ t ∈ Set.Ioo 0 T, IsOpen (Λ t) := fun t ht => (hIH t ht).1
  have hLsub : ∀ t ∈ Set.Ioo 0 T, Λ t ⊆ ball (0 : ℂ) (1 / 2) := fun t ht => hstop.1 t ht
  have hL1 : ∀ t ∈ Set.Ioo 0 T, Λ t ⊆ ball (0 : ℂ) 1 := fun t ht =>
    (hLsub t ht).trans (ball_subset_ball (by norm_num))
  have hLm : ∀ t ∈ Set.Ioo 0 T, MeasurableSet (Λ t) := fun t ht => (hLo t ht).measurableSet
  have hmeas : ∀ t ∈ Set.Ioo 0 T, ν' (Λ t) = ENNReal.ofReal t := fun t ht =>
    (measure_congr_of_restrict_ball hres (hLm t ht) (hL1 t ht)).symm.trans (hSHB.measure_eq t ht)
  have hfr : ∀ t ∈ Set.Ioo 0 T, ν' (frontier (Λ t)) = 0 := fun t ht =>
    (measure_congr_of_restrict_ball hres isClosed_frontier.measurableSet
      ((frontier_subset_closure).trans (closure_subset_ball_one_of_subset_half (hLsub t ht)))).symm.trans
      (hSHB.measure_frontier t ht)
  refine ⟨T, hT, Λ, ⟨fun t ht => ?_, { hSHB with measure_eq := hmeas, measure_frontier := hfr }, ?_⟩, hstop⟩
  · exact (isHarmonicBall_iff_of_restrict (hLo t ht) (hL1 t ht) hres 0).1 (hIH t ht)
  · intro t r ht hr hΛr ρ hrρ
    show ConeObstacleClauses ν' (Λ t) t ρ
    by_cases hρ : ρ ≤ 3 / 4
    · exact coneObstacleClauses_of_le hres (hLm t ht) (hL1 t ht) (hρ.trans (by norm_num))
        (hOC t r ht hr hΛr ρ hrρ)
    · have hρ' : 3 / 4 < ρ := not_le.1 hρ
      have hR : ConeObstacleClauses ν (Λ t) t (3 / 4) := hOC t (1 / 2) ht (by norm_num) (hLsub t ht) (3 / 4) (by norm_num)
      exact coneObstacleClauses_of_outer hres ht.1 (hLm t ht) (hL1 t ht) (hLsub t ht) hR hρ'
        (hOC t r ht hr hΛr ρ hrρ).1

/-- The congruence of `HasConeHarmonicBallsUpToHalfBall` under equal restrictions to `B_1`. -/
theorem hasConeHarmonicBallsUpToHalfBall_congr_restrict {ν ν' : Measure ℂ}
    (hres : ν.restrict (ball (0 : ℂ) 1) = ν'.restrict (ball (0 : ℂ) 1)) :
    MatedCRT.HasConeHarmonicBallsUpToHalfBall ν ↔ MatedCRT.HasConeHarmonicBallsUpToHalfBall ν' :=
  ⟨hasConeHarmonicBallsUpToHalfBall_of_restrict hres, hasConeHarmonicBallsUpToHalfBall_of_restrict hres.symm⟩

/-- **`hL` of `coneHarmonicBallLocalityStep_of_locality`** (restriction to `B_1`). -/
theorem coneHarmonicBall_hL :
    ∀ ν ν' : Measure ℂ, ν.restrict (ball 0 1) = ν'.restrict (ball 0 1) →
      (MatedCRT.HasConeHarmonicBallsUpToHalfBall ν ↔ MatedCRT.HasConeHarmonicBallsUpToHalfBall ν') :=
  fun _ _ hres => hasConeHarmonicBallsUpToHalfBall_congr_restrict hres

end Assembly

#print axioms MatedCRT.FirstPass2x.ConeLocality.coneHarmonicBall_hL

end MatedCRT.FirstPass2x.ConeLocality
