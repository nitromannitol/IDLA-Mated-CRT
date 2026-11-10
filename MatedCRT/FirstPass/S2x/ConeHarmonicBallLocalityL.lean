import MatedCRT.FirstPass.S2x.ConeHarmonicBallLocality

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

end MatedCRT.FirstPass2x.ConeLocality
