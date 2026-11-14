import MatedCRT.FirstPass.Derived.AreaCellAbsorbedTrajectory
import MatedCRT.FirstPass.Derived.StoppedDiscreteCoupling
import MatedCRT.FirstPass.Derived.SrwTrajectoryLaw
import LatticeProb.Prob.ProductNoiseTrajectory

/-! # Stopped integer trajectories -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Preorder unitInterval
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

namespace MatedCRT

/-- An absorbed path is unchanged by stopping at its first exit. -/
theorem stoppedPath_eq_self_of_absorbed (D : Set ℤ) (x : ℕ → ℤ)
    (hx : IsAbsorbedPath D x) : stoppedPath D x = x := by
  by_cases ht : vExitTime D x = ⊤
  · exact stoppedPath_of_top ht
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp ht
    have hk' : vExitTime D x = (k : ℕ∞) := hk.symm
    have hout := ((MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec D x k).mp hk').1
    funext n
    by_cases hn : n ≤ k
    · exact stoppedPath_of_le hk' hn
    · have hkn : k ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hn)
      have heq : x n = x k := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
        exact hx.after_exit hout j
      rw [stoppedPath, hk', min_eq_left (by exact_mod_cast hkn), ENat.toNat_natCast]
      exact heq.symm

/-- Stopping the ordinary and absorbed trajectories gives the same law. -/
theorem absorbedSrwKernel_stopped_trajectoryLaw (m : ℤ → ℤ → ℕ)
    (D : Set ℤ) (a : ℤ) :
    (Kernel.trajMeasure (Measure.dirac a)
      (fun n => (absorbedSrwKernel m D).comap
        (fun h : Finset.Iic n → ℤ => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _))).map (stoppedPath D) =
      (srwLaw m a).map (stoppedPath D) := by
  classical
  obtain ⟨P, Q, hP, hQ, hPlaw, hQlaw, hcouple⟩ :=
    LatticeProb.exists_productNoise_trajectories (absorbedSrwKernel m D) (srwKernel m)
      Dᶜ (Set.to_countable Dᶜ).measurableSet (by
        intro x hx
        have hxD : x ∈ D := by simpa using hx
        simp only [absorbedSrwKernel, Kernel.piecewise_apply, hxD, ↓reduceIte]) a
  have heq := stoppedPath_law_eq_of_hitTime_coupling
    (Measure.infinitePi fun _ : ℕ => (volume : Measure I)) P Q hP hQ Dᶜ
    (Filter.Eventually.of_forall hcouple)
  rw [hPlaw, hQlaw] at heq
  simp only [compl_compl] at heq
  rw [srwLaw_eq_trajMeasure]
  clear P Q hP hQ hPlaw hQlaw hcouple
  convert heq using 1
  unfold srwHistoryKernel
  rfl

end MatedCRT
