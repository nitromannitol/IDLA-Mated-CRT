import MatedCRT.FirstPass.S2g.GoodSet
import MatedCRT.FirstPass.Frozen.S2g
import LatticeProb.Analysis.LaplacianCalculus

/-! # All-disks obstacle clause from the radius-3/4 clause (H7)

Deterministic part of `ConeCanonicalHalfBallStep`. For a measure `μ`, a time `t > 0` and `A = Λ_t` (open, containing the
pole `0`, contained in `B_{1/2}`), the least supersolution `W = leastSupersolution μ (3/4) 0 t` at radius `3/4` determines
the least supersolutions at every radius `ρ > r` with `A ⊆ B_r`: the candidate `allDisksCandidate W t ρ` is `W + c` on
`B_{3/4}` (with `c` the constant `t G_{B_{3/4}}(0,·) - t G_{B_ρ}(0,·)`, which is constant by the centre formula
`FrozenGreenBallCentre`) and `-t G_{B_ρ}(0,·)` off `B_{3/4}`. The pole cancels in the centre formula. Least-ness is `certificate_le_supersolution` (GoodSet.lean).

Laplacian identity (`allDisks_integral_identity`): the potential `U = W + t G_{B_{3/4}}(0,·)` (zero off `B_{3/4}`) satisfies
`Δ U = μ|_A - t δ_0` tested against cut-off test functions; the cut-off `χ` equals `1` on `B_{5/8} ⊇ Ā`. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ContDiff

open Classical in
/-- The H7 candidate at radius `ρ` built from `W`: `W + t (2π)⁻¹ log (3/(4ρ))` on `B_{3/4}` and `-t G_{B_ρ}(0,·)` off
`B_{3/4}`. -/
noncomputable def allDisksCandidate (W : ℂ → ℝ) (t ρ : ℝ) : ℂ → ℝ :=
  fun x => if x ∈ ball (0 : ℂ) (3 / 4) then W x + t * ((2 * Real.pi)⁻¹ * Real.log (3 / (4 * ρ)))
    else -t * greenFunction (ball (0 : ℂ) ρ) 0 x

/-- On `B_{3/4} ∩ B_ρ` minus the pole, the candidate is `W + t G_{B_{3/4}}(0,·) - t G_{B_ρ}(0,·)` (pole-free form). -/
theorem allDisksCandidate_eq_of_centre (hC : FrozenGreenBallCentre) {W : ℂ → ℝ} {t ρ : ℝ} (hρ : 0 < ρ)
    {x : ℂ} (hx3 : x ∈ ball (0 : ℂ) (3 / 4)) (hxρ : x ∈ ball (0 : ℂ) ρ) (hx0 : x ≠ 0) :
    allDisksCandidate W t ρ x =
      W x + t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x - t * greenFunction (ball (0 : ℂ) ρ) 0 x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h3 : ‖x‖ < 3 / 4 := mem_ball_zero_iff.mp hx3
  have hr : ‖x‖ < ρ := mem_ball_zero_iff.mp hxρ
  have h1 : (3 / 4 : ℝ) / ‖x‖ ≠ 0 := (div_pos (by norm_num) hn).ne'
  have h2 : ρ / ‖x‖ ≠ 0 := (div_pos hρ hn).ne'
  have hlog : Real.log (3 / (4 * ρ)) = Real.log ((3 / 4 : ℝ) / ‖x‖) - Real.log (ρ / ‖x‖) := by
    rw [← Real.log_div h1 h2]
    congr 1
    field_simp
  unfold allDisksCandidate
  simp only [hx3, ↓reduceIte]
  rw [hC (3 / 4) (by norm_num) x hn h3, hC ρ hρ x hn hr, hlog]
  ring

open Classical in
/-- The potential `U = W + t G_{B_{3/4}}(0,·)` on `B_{3/4}`, extended by `0`. -/
noncomputable def allDisksPotential (W : ℂ → ℝ) (t : ℝ) : ℂ → ℝ :=
  fun x => if x ∈ ball (0 : ℂ) (3 / 4) then W x + t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x else 0

/-- Off the pole, the candidate is the potential minus `t G_{B_ρ}(0,·)` on `B_ρ`. -/
theorem allDisksCandidate_eq_potential (hC : FrozenGreenBallCentre) {W : ℂ → ℝ} {t ρ : ℝ} (hρ : 0 < ρ)
    {x : ℂ} (hxρ : x ∈ ball (0 : ℂ) ρ) (hx0 : x ≠ 0) :
    allDisksCandidate W t ρ x = allDisksPotential W t x - t * greenFunction (ball (0 : ℂ) ρ) 0 x := by
  by_cases h3 : x ∈ ball (0 : ℂ) (3 / 4)
  · rw [allDisksCandidate_eq_of_centre hC hρ h3 hxρ hx0]
    simp only [allDisksPotential, h3, ↓reduceIte]
  · simp only [allDisksCandidate, allDisksPotential, h3, ↓reduceIte]
    ring

/-- The potential vanishes off `A`: on `B_{3/4} \ A` the obstacle is attained (`W = -t G`), and off `B_{3/4}` it is `0`. -/
theorem allDisksPotential_eq_zero_of_not_mem {W : ℂ → ℝ} {t : ℝ} {A : Set ℂ} (hA0 : (0 : ℂ) ∈ A)
    (hlow : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 → -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x ≤ W x)
    (hobs : ∀ x ∈ ball (0 : ℂ) (3 / 4), x ∉ A → W x ≤ -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x)
    {x : ℂ} (hxA : x ∉ A) : allDisksPotential W t x = 0 := by
  by_cases h3 : x ∈ ball (0 : ℂ) (3 / 4)
  · have hx0 : x ≠ 0 := fun h => hxA (h ▸ hA0)
    have h1 := hobs x h3 hxA
    have h2 := hlow x (ball_subset_closedBall h3) hx0
    simp only [allDisksPotential, h3, ↓reduceIte]
    linarith
  · simp only [allDisksPotential, h3, ↓reduceIte]

/-- Laplacian of a function vanishes off the support. -/
theorem laplacian_eq_zero_off_tsupport {φ : ℂ → ℝ} {x : ℂ} (hx : x ∉ tsupport φ) :
    Laplacian.laplacian φ x = 0 :=
  LatticeProb.LaplacianCalculus.laplacian_eq_zero_off_tsupport hx

/-- The test function `φ` on `U` has `Δφ` continuous with compact support in `U`; a locally integrable `w` on `U`
gives `w Δφ` integrable. -/
theorem integrable_mul_laplacian_of_locallyIntegrableOn {U : Set ℂ} {w : ℂ → ℝ} (hw : LocallyIntegrableOn w U)
    {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) :
    Integrable (fun x => w x * Laplacian.laplacian φ x) := by
  have hK : IsCompact (tsupport φ) := hφ.2.1.isCompact
  have hΔ : Continuous (Laplacian.laplacian φ) :=
    continuous_laplacian_of_contDiff (contDiff_two_of_isTestFunction hφ)
  have hsupp : Function.support (fun x => w x * Laplacian.laplacian φ x) ⊆ tsupport φ := by
    intro x hx
    by_contra hxn
    exact hx (by simp [laplacian_eq_zero_off_tsupport hxn])
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  exact (hw.integrableOn_compact_subset hφ.2.2 hK).mul_continuousOn hΔ.continuousOn hK

/-- A smooth cut-off `χ`: `χ = 1` on `B_{5/8}` and `tsupport χ ⊆ B_{3/4}`. -/
theorem exists_cutoff_three_quarters :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ ball (0 : ℂ) (3 / 4) ∧
      ∀ x ∈ closedBall (0 : ℂ) (5 / 8), χ x = 1 := by
  let c : ContDiffBump (0 : ℂ) :=
    { rIn := 5 / 8, rOut := 11 / 16, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  refine ⟨c, c.contDiff, c.hasCompactSupport, ?_, fun x hx => c.one_of_mem_closedBall hx⟩
  rw [c.tsupport_eq]
  exact closedBall_subset_ball (by norm_num)

/-- Second derivatives of a test function are continuous at every point (`ContDiffAt ℝ 2`). -/
theorem contDiffAt_two_of_isTestFunction' {U : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) (x : ℂ) :
    ContDiffAt ℝ 2 φ x :=
  (contDiff_two_of_isTestFunction hφ).contDiffAt

/-- Pointwise: away from the pole, the candidate integrand is `(U - t G_{B_ρ}) Δφ`. -/
theorem allDisksCandidate_mul_laplacian_eq (hC : FrozenGreenBallCentre) {W : ℂ → ℝ} {t ρ : ℝ} (hρ : 0 < ρ)
    {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) ρ) φ) {x : ℂ} (hx0 : x ≠ 0) :
    allDisksCandidate W t ρ x * Laplacian.laplacian φ x =
      allDisksPotential W t x * Laplacian.laplacian φ x
        - t * (greenFunction (ball (0 : ℂ) ρ) 0 x * Laplacian.laplacian φ x) := by
  by_cases hxφ : x ∈ tsupport φ
  · rw [allDisksCandidate_eq_potential hC hρ (hφ.2.2 hxφ) hx0]
    ring
  · rw [laplacian_eq_zero_off_tsupport hxφ]
    ring

/-- The integral identity of the H7 candidate: for every test function `φ` on `B_ρ`, `∫ (candidate) Δφ = ∫ φ d(μ|_A)`.
Proof: split `φ = χφ + (1-χ)φ`; the second piece is killed by the potential (zero off `A`, locally constant near `A`), the
first piece is handled by the hypothesis `HasLaplacian W (μ|_A) 0 B_{3/4}` and the Green identity `ΔG = -δ_0` of `B_{3/4}`;
the `G_{B_ρ}` term is handled by the Green identity of `B_ρ`. -/
theorem allDisks_integral_identity (hC : FrozenGreenBallCentre) (hGB : HarmonicBalls.GreenFunctionBallStmt)
    {μ : Measure ℂ} {W : ℂ → ℝ} {t ρ : ℝ} {A : Set ℂ} (hρ : 0 < ρ)
    (hW : HasLaplacian W (μ.restrict A) 0 (ball (0 : ℂ) (3 / 4)))
    (hlow : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 → -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x ≤ W x)
    (hobs : ∀ x ∈ ball (0 : ℂ) (3 / 4), x ∉ A → W x ≤ -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x)
    (hA : A ⊆ ball (0 : ℂ) (1 / 2)) (hAopen : IsOpen A) (hA0 : (0 : ℂ) ∈ A)
    {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) ρ) φ) :
    ∫ x, allDisksCandidate W t ρ x * Laplacian.laplacian φ x = ∫ x, φ x ∂(μ.restrict A) := by
  obtain ⟨χ, hχs, hχc, hχsupp, hχ1⟩ := exists_cutoff_three_quarters
  set ψ1 : ℂ → ℝ := fun x => χ x * φ x with hψ1def
  set ψ2 : ℂ → ℝ := fun x => (1 - χ x) * φ x with hψ2def
  have hT1 : tsupport ψ1 ⊆ tsupport χ := tsupport_mul_subset_left
  have hT1' : tsupport ψ1 ⊆ tsupport φ := tsupport_mul_subset_right
  have hT2 : tsupport ψ2 ⊆ tsupport φ := tsupport_mul_subset_right
  have hψ1 : IsTestFunction (ball (0 : ℂ) (3 / 4)) ψ1 :=
    ⟨hχs.mul hφ.1, hχc.mul_right, hT1.trans hχsupp⟩
  have hψ1ρ : IsTestFunction (ball (0 : ℂ) ρ) ψ1 :=
    ⟨hχs.mul hφ.1, hχc.mul_right, hT1'.trans hφ.2.2⟩
  have hψ2 : IsTestFunction (ball (0 : ℂ) ρ) ψ2 :=
    ⟨((contDiff_const.sub hχs)).mul hφ.1, hφ.2.1.mul_left, hT2.trans hφ.2.2⟩
  -- splitting of the Laplacian
  have hsum : ∀ x, Laplacian.laplacian φ x = Laplacian.laplacian ψ1 x + Laplacian.laplacian ψ2 x := by
    intro x
    have hfun : φ = ψ1 + ψ2 := by
      funext y
      simp only [hψ1def, hψ2def, Pi.add_apply]
      ring
    conv_lhs => rw [hfun]
    exact ContDiffAt.laplacian_add (contDiffAt_two_of_isTestFunction' hψ1ρ x)
      (contDiffAt_two_of_isTestFunction' hψ2 x)
  -- the second piece has zero Laplacian on A
  have hψ2zero : ∀ x ∈ A, Laplacian.laplacian ψ2 x = 0 := by
    intro x hx
    have hx5 : x ∈ ball (0 : ℂ) (5 / 8) := ball_subset_ball (by norm_num) (hA hx)
    have hev : ψ2 =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_ball.mem_nhds hx5] with y hy
      simp [hψ2def, hχ1 y (ball_subset_closedBall hy)]
    have h := (InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds
    rw [h]
    simp
  have hUzero : ∀ x, allDisksPotential W t x * Laplacian.laplacian ψ2 x = 0 := by
    intro x
    by_cases hxA : x ∈ A
    · rw [hψ2zero x hxA, mul_zero]
    · rw [allDisksPotential_eq_zero_of_not_mem hA0 hlow hobs hxA, zero_mul]
  have hUsplit : ∀ x, allDisksPotential W t x * Laplacian.laplacian φ x
      = allDisksPotential W t x * Laplacian.laplacian ψ1 x := by
    intro x
    rw [hsum x, mul_add, hUzero x, add_zero]
  have hUpsi : ∀ x, allDisksPotential W t x * Laplacian.laplacian ψ1 x
      = W x * Laplacian.laplacian ψ1 x
        + t * (greenFunction (ball (0 : ℂ) (3 / 4)) 0 x * Laplacian.laplacian ψ1 x) := by
    intro x
    by_cases h3 : x ∈ ball (0 : ℂ) (3 / 4)
    · have hU : allDisksPotential W t x = W x + t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x := by
        simp [allDisksPotential, h3]
      rw [hU]
      ring
    · have h0 : Laplacian.laplacian ψ1 x = 0 :=
        laplacian_eq_zero_off_tsupport (fun hx => h3 (hT1.trans hχsupp hx))
      have hU : allDisksPotential W t x = 0 := by simp [allDisksPotential, h3]
      rw [hU, h0]
      ring
  -- Green identities and local integrability
  have hGHL3 := hGB (3 / 4) (by norm_num) 0 (mem_ball_self (by norm_num))
  have hGρHL := hGB ρ hρ 0 (mem_ball_self hρ)
  have hi1 : Integrable (fun x => W x * Laplacian.laplacian ψ1 x) :=
    integrable_mul_laplacian_of_locallyIntegrableOn hW.1 hψ1
  have hi2 : Integrable (fun x => greenFunction (ball (0 : ℂ) (3 / 4)) 0 x * Laplacian.laplacian ψ1 x) :=
    integrable_mul_laplacian_of_locallyIntegrableOn hGHL3.1.1 hψ1
  have hiU : Integrable (fun x => allDisksPotential W t x * Laplacian.laplacian φ x) := by
    have hfun : (fun x => allDisksPotential W t x * Laplacian.laplacian φ x)
        = fun x => W x * Laplacian.laplacian ψ1 x
          + t * (greenFunction (ball (0 : ℂ) (3 / 4)) 0 x * Laplacian.laplacian ψ1 x) := by
      funext x
      rw [hUsplit x, hUpsi x]
    rw [hfun]
    exact hi1.add (hi2.const_mul t)
  have hiG : Integrable (fun x => greenFunction (ball (0 : ℂ) ρ) 0 x * Laplacian.laplacian φ x) :=
    integrable_mul_laplacian_of_locallyIntegrableOn hGρHL.1.1 hφ
  -- the integral of the potential against Δφ
  have hUint : ∫ x, allDisksPotential W t x * Laplacian.laplacian φ x = ∫ x, φ x ∂(μ.restrict A) - t * φ 0 := by
    have hfun : (fun x => allDisksPotential W t x * Laplacian.laplacian φ x)
        = fun x => W x * Laplacian.laplacian ψ1 x
          + t * (greenFunction (ball (0 : ℂ) (3 / 4)) 0 x * Laplacian.laplacian ψ1 x) := by
      funext x
      rw [hUsplit x, hUpsi x]
    have hWI : ∫ x, W x * Laplacian.laplacian ψ1 x = ∫ x, ψ1 x ∂(μ.restrict A) :=
      by simpa using (hW.2 ψ1 hψ1).2.2
    have hGI : ∫ x, greenFunction (ball (0 : ℂ) (3 / 4)) 0 x * Laplacian.laplacian ψ1 x = -φ 0 := by
      have h := (hGHL3.1.2 ψ1 hψ1).2.2
      have hχ0 : χ 0 = 1 := hχ1 0 (mem_closedBall_self (by norm_num))
      simpa [integral_dirac, hψ1def, hχ0] using h
    have hψA : ∫ x, ψ1 x ∂(μ.restrict A) = ∫ x, φ x ∂(μ.restrict A) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_forall_mem hAopen.measurableSet (fun x hx =>
        hχ1 x (ball_subset_closedBall (ball_subset_ball (by norm_num) (hA hx))))] with x hx
      simp [hψ1def, hx]
    rw [hfun, integral_add hi1 (hi2.const_mul t), integral_const_mul, hWI, hGI, hψA]
    ring
  -- the integral against Δφ of the Green function of B_ρ
  have hGρint : ∫ x, greenFunction (ball (0 : ℂ) ρ) 0 x * Laplacian.laplacian φ x = -φ 0 := by
    have h := (hGρHL.1.2 φ hφ).2.2
    simpa [integral_dirac] using h
  -- pointwise identity away from the pole
  have hcongr : (fun x => allDisksCandidate W t ρ x * Laplacian.laplacian φ x) =ᵐ[volume]
      (fun x => allDisksPotential W t x * Laplacian.laplacian φ x
        - t * (greenFunction (ball (0 : ℂ) ρ) 0 x * Laplacian.laplacian φ x)) := by
    have hae : ∀ᵐ x : ℂ ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hae] with x hx0
    exact allDisksCandidate_mul_laplacian_eq hC hρ hφ hx0
  rw [integral_congr_ae hcongr, integral_sub hiU (hiG.const_mul t), integral_const_mul, hUint, hGρint]
  ring

end MatedCRT
