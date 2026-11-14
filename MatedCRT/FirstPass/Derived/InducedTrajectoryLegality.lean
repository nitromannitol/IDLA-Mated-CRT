import MatedCRT.FirstPass.Derived.SrwAmbientLegality
import MatedCRT.FirstPass.Derived.SrwTrajectoryLaw

/-!
# Legality of induced and ambient random-walk trajectories

The trajectory measures of an induced walk and the ambient walk both follow
ambient graph edges, apart from holding steps.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace MatedCRT

open Classical in
/-- Induced and ambient walk trajectory measures are supported on paths
starting in the inducing set and taking legal ambient graph steps. -/
theorem induced_or_ambient_trajMeasure_ae_legal (m : ℤ → ℤ → ℕ)
    (A : Set ℤ) (a : ℤ) (ha : a ∈ A) (k : Kernel ℤ ℤ) [IsMarkovKernel k]
    (hk : k = srwKernel (fun u v => if u ∈ A ∧ v ∈ A then m u v else 0) ∨
      k = srwKernel m) :
    ∀ᵐ p ∂Kernel.trajMeasure (X := fun _ => ℤ) (Measure.dirac a)
      (fun n => k.comap
        (fun h : Finset.Iic n → ℤ => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _)),
      p 0 ∈ A ∧ ∀ n, p (n + 1) = p n ∨ (adjGraph m).Adj (p n) (p (n + 1)) := by
  classical
  rcases hk with hk | hk
  · subst k
    change ∀ᵐ p ∂Kernel.trajMeasure (X := fun _ => ℤ) (Measure.dirac a)
      (srwHistoryKernel (fun u v => if u ∈ A ∧ v ∈ A then m u v else 0)), _
    rw [← srwLaw_eq_trajMeasure]
    filter_upwards [srwLaw_induced_ae_start_and_ambient_legal m A a] with p hp
    exact ⟨by simpa only [hp.1] using ha, hp.2⟩
  · subst k
    change ∀ᵐ p ∂Kernel.trajMeasure (X := fun _ => ℤ) (Measure.dirac a) (srwHistoryKernel m), _
    rw [← srwLaw_eq_trajMeasure]
    filter_upwards [srwLaw_ae_start_and_ambient_legal m m a (fun _ _ h => h)] with p hp
    exact ⟨by simpa only [hp.1] using ha, hp.2⟩

end MatedCRT
