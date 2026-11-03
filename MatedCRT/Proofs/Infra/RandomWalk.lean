import MatedCRT.Defs.RandomWalk

/-!
# Simple random walk: elementary facts

* `srwLaw_ae_start`: the walk starts at its starting point.
* Exit times, Green's functions and expected exit times vanish when the walk starts outside the set.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Classical
open scoped ENNReal

/-- Simple random walk started at `a` is at `a` at time `0`. -/
theorem srwLaw_ae_start (m : ℤ → ℤ → ℕ) (a : ℤ) : ∀ᵐ x ∂srwLaw m a, x 0 = a := by
  have h := Kernel.traj_map_frestrictLe_apply (X := fun _ => ℤ) (κ := srwHistoryKernel m) 0 0 (fun _ => a)
  rw [Kernel.partialTraj_self, Kernel.id_apply] at h
  have h0 : (0 : ℕ) ∈ Finset.Iic 0 := Finset.mem_Iic.2 le_rfl
  have hmeas : MeasurableSet {z : (i : Finset.Iic 0) → ℤ | z ⟨0, h0⟩ ≠ a} :=
    (measurableSet_singleton a).compl.preimage (measurable_pi_apply _)
  rw [ae_iff]
  have hset : {x : ℕ → ℤ | ¬ x 0 = a} = Preorder.frestrictLe 0 ⁻¹' {z | z ⟨0, h0⟩ ≠ a} := by
    ext x; simp [Preorder.frestrictLe]
  have := congrArg (fun μ : Measure ((i : Finset.Iic 0) → ℤ) => μ {z | z ⟨0, h0⟩ ≠ a}) h
  rw [Measure.map_apply (Preorder.measurable_frestrictLe 0) hmeas, Measure.dirac_apply' _ hmeas] at this
  rw [hset]
  unfold srwLaw
  rw [this]
  simp

theorem vExitTime_eq_zero {A : Set ℤ} {x : ℕ → ℤ} (hx : x 0 ∉ A) : vExitTime A x = 0 := by
  unfold vExitTime
  split_ifs with h
  · simp [(Nat.find_eq_zero h).2 hx]
  · exact absurd ⟨0, hx⟩ h

theorem visitsBeforeExit_eq_zero {A : Set ℤ} {x : ℕ → ℤ} (hx : x 0 ∉ A) (b : ℤ) :
    visitsBeforeExit A b x = 0 := by
  unfold visitsBeforeExit
  rw [vExitTime_eq_zero hx]
  simp

theorem greenFn_eq_zero_of_not_mem (m : ℤ → ℤ → ℕ) {A : Set ℤ} {a : ℤ} (ha : a ∉ A) (b : ℤ) :
    greenFn m A a b = 0 := by
  unfold greenFn
  have : ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a = 0 := by
    rw [lintegral_eq_zero_iff']
    · filter_upwards [srwLaw_ae_start m a] with x hx
      exact visitsBeforeExit_eq_zero (hx ▸ ha) b
    · exact aemeasurable_zero.congr (by
        filter_upwards [srwLaw_ae_start m a] with x hx
        exact (visitsBeforeExit_eq_zero (hx ▸ ha) b).symm)
  rw [this, ENNReal.toReal_zero]

theorem greenKernel_eq_zero_of_not_mem (m : ℤ → ℤ → ℕ) {A : Set ℤ} {a : ℤ} (ha : a ∉ A) (b : ℤ) :
    greenKernel m A a b = 0 := by
  simp [greenKernel, greenFn_eq_zero_of_not_mem m ha b]

theorem normExitTime_eq_zero_of_not_mem (m : ℤ → ℤ → ℕ) {A : Set ℤ} {a : ℤ} (ha : a ∉ A) :
    normExitTime m A a = 0 := by
  simp [normExitTime, greenKernel_eq_zero_of_not_mem m ha]

theorem expectedExitTime_eq_zero_of_not_mem (m : ℤ → ℤ → ℕ) {A : Set ℤ} {a : ℤ} (ha : a ∉ A) :
    expectedExitTime m A a = 0 := by
  unfold expectedExitTime
  have hae : (fun x => (vExitTime A x : ℝ≥0∞)) =ᵐ[srwLaw m a] fun _ => 0 := by
    filter_upwards [srwLaw_ae_start m a] with x hx
    rw [vExitTime_eq_zero (hx ▸ ha)]
    simp
  rw [lintegral_congr_ae hae, lintegral_zero]

end MatedCRT
