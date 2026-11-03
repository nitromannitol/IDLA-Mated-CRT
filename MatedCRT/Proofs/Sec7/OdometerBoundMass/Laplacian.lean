import MatedCRT.Proofs.Sec7.OdometerBoundMass.StoppedOdometer
import MatedCRT.Proofs.WalkPotential.ExitBeforeHit
import MatedCRT.Proofs.WalkPotential.Comparison

/-!
# The stopped odometer is `w̃^ε_t - φ` everywhere (towards eq:laplacian-of-uteps, line 2962)

Without hypothesis on the map:
* the Green's function `G_A(a, b)` vanishes for `b ∉ A` (no visit to `b` before exiting `A`), hence the obstacle
  `φ = -(t ε⁻¹) g^ε_{B_ρ}(0, ·)` vanishes off `V = V^ε(B_ρ) \ V^ε(∂B_ρ)`;
* off `V^ε(cl(B_ρ))` the obstacle problem does not constrain `w̃^ε_t`, whose infimum is the junk value `0`;
* so `u^ε_t = w̃^ε_t - φ` on all of `ℤ` (`stoppedOdometer_eq_sub`), and `Δ^ε u^ε_t = Δ^ε w̃^ε_t - Δ^ε φ` at every
  vertex of positive degree of a locally finite map (`mLaplacian_stoppedOdometer`).
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

theorem visitsBeforeExit_eq_zero_of_not_mem {A : Set ℤ} {b : ℤ} (hb : b ∉ A) (x : ℕ → ℤ) :
    visitsBeforeExit A b x = 0 := by
  unfold visitsBeforeExit
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  rw [ite_eq_right_iff]
  rintro ⟨hn, hxn⟩
  exact (hb (hxn ▸ lt_vExitTime_iff.1 hn n le_rfl)).elim

/-- `G_A(a, b) = 0` for `b ∉ A` (line 760). -/
theorem greenFn_eq_zero_of_not_mem_right (m : ℤ → ℤ → ℕ) {A : Set ℤ} (a : ℤ) {b : ℤ} (hb : b ∉ A) :
    greenFn m A a b = 0 := by
  unfold greenFn
  simp [visitsBeforeExit_eq_zero_of_not_mem hb]

theorem greenKernel_eq_zero_of_not_mem_right (m : ℤ → ℤ → ℕ) {A : Set ℤ} (a : ℤ) {b : ℤ} (hb : b ∉ A) :
    greenKernel m A a b = 0 := by
  simp [greenKernel, greenFn_eq_zero_of_not_mem_right m a hb]

variable {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ}

theorem ballInterior_subset_cellVertices_closedBall :
    ballInterior ε η ρ ⊆ cellVertices ε η (closedBall 0 ρ) := fun b hb =>
  cellVertices_mono ball_subset_closedBall
    (show b ∈ cellVertices ε η (ball 0 ρ) \ cellVertices ε η (frontier (ball 0 ρ)) from hb).1

theorem matedObstacle_eq_zero_of_not_mem {a : ℤ} (ha : a ∉ ballInterior ε η ρ) : matedObstacle ε η ρ t a = 0 := by
  simp [matedObstacle, greenKernel_eq_zero_of_not_mem_right _ _ ha]

theorem mLaplacian_update_zero (m : ℤ → ℤ → ℕ) {a b : ℤ} (hba : b ≠ a) (v : ℝ) :
    mLaplacian m (Function.update (fun _ => 0) a v) b = ((mdeg m b : ℕ) : ℝ)⁻¹ * ((m b a : ℝ) * v) := by
  unfold mLaplacian
  congr 1
  rw [finsum_eq_single _ a]
  · simp [hba]
  · intro c hc
    simp [hc, hba]

/-- Off `V^ε(cl(B_ρ))`, `w̃^ε_t` is the junk infimum `0` of an unbounded below set. -/
theorem matedLeastSupersolution_eq_zero_of_not_mem (hε : 0 < ε) (ht : 0 < t) {a : ℤ}
    (ha : a ∉ cellVertices ε η (closedBall 0 ρ)) : matedLeastSupersolution ε η ρ t a = 0 := by
  unfold matedLeastSupersolution discreteLeastSupersolution
  apply Real.sInf_of_not_bddBelow
  rintro ⟨β, hβ⟩
  have hK : 0 ≤ |β| + 1 := by positivity
  have hmem : -(|β| + 1) ∈ (fun u : ℤ → ℝ => u a) ''
      {u | (∀ b ∈ ballInterior ε η ρ, mLaplacian (cellMult ε η) u b ≤ ((matedDeg ε η b : ℕ) : ℝ)⁻¹) ∧
        ∀ b ∈ cellVertices ε η (closedBall 0 ρ), matedObstacle ε η ρ t b ≤ u b} := by
    refine ⟨Function.update (fun _ => 0) a (-(|β| + 1)), ⟨fun b hb => ?_, fun b hb => ?_⟩, by simp⟩
    · have hba : b ≠ a := fun h => ha (h ▸ ballInterior_subset_cellVertices_closedBall hb)
      rw [mLaplacian_update_zero _ hba]
      have h2 : 0 ≤ ((mdeg (cellMult ε η) b : ℕ) : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
      have h3 : (cellMult ε η b a : ℝ) * -(|β| + 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
      exact (mul_nonpos_of_nonneg_of_nonpos h2 h3).trans (inv_nonneg.2 (Nat.cast_nonneg _))
    · have hba : b ≠ a := fun h => ha (h ▸ hb)
      rw [Function.update_of_ne hba]
      exact matedObstacle_nonpos hε ht b
  have := hβ hmem
  linarith [neg_abs_le β]

/-- `u^ε_t = w̃^ε_t - φ` on all of `ℤ`, `φ = -(t ε⁻¹) g^ε_{B_ρ}(0, ·)`. -/
theorem stoppedOdometer_eq_sub (hε : 0 < ε) (ht : 0 < t) (a : ℤ) :
    stoppedOdometer ε η ρ t a = matedLeastSupersolution ε η ρ t a - matedObstacle ε η ρ t a := by
  by_cases haW : a ∈ cellVertices ε η (closedBall 0 ρ)
  · simp only [stoppedOdometer, haW, ↓reduceIte]
  · have hV : a ∉ ballInterior ε η ρ := fun h => haW (ballInterior_subset_cellVertices_closedBall h)
    simp only [stoppedOdometer, haW, ↓reduceIte, matedLeastSupersolution_eq_zero_of_not_mem hε ht haW,
      matedObstacle_eq_zero_of_not_mem hV, sub_zero]

/-- `Δ^ε u^ε_t = Δ^ε w̃^ε_t + (t ε⁻¹) Δ^ε g^ε_{B_ρ}(0, ·)` (line 2962) on a locally finite map. -/
theorem mLaplacian_stoppedOdometer (hε : 0 < ε) (ht : 0 < t) (hlf : IsLocallyFiniteMult (cellMult ε η)) (a : ℤ) :
    mLaplacian (cellMult ε η) (stoppedOdometer ε η ρ t) a =
      mLaplacian (cellMult ε η) (matedLeastSupersolution ε η ρ t) a +
        t / ε * mLaplacian (cellMult ε η) (greenKernel (cellMult ε η) (ballInterior ε η ρ) 0) a := by
  have hfun : stoppedOdometer ε η ρ t = fun b => matedLeastSupersolution ε η ρ t b - matedObstacle ε η ρ t b :=
    funext (stoppedOdometer_eq_sub hε ht)
  have hφ : matedObstacle ε η ρ t = fun b => -(t / ε) * greenKernel (cellMult ε η) (ballInterior ε η ρ) 0 b := rfl
  rw [hfun, mLaplacian_eq_div hlf, lapSum_sub hlf, hφ, lapSum_const_mul hlf, mLaplacian_eq_div hlf,
    mLaplacian_eq_div hlf]
  ring

end MatedCRT
