import MatedCRT.FirstPass.Derived.SrwRelabelStep
import LatticeProb.Bonanno.ReflectedWalk.ApproximatingChain

/-! # Relabelling multigraph random-walk laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory
open scoped ENNReal

/-- A bijective vertex relabelling maps the whole multigraph walk law to the
walk law of the original multiplicity, including the Dirac fallback. -/
theorem srwLaw_map_relabel (m : ℤ → ℤ → ℕ) (e : ℤ ≃ ℤ) (a : ℤ) :
    (srwLaw (fun x y => m (e x) (e y)) a).map (fun ω n => e (ω n)) =
      srwLaw m (e a) := by
  classical
  have hf : Measurable (fun ω : ℕ → ℤ => fun n => e (ω n)) :=
    Measurable.of_eval fun n => measurable_of_countable _ |>.comp (measurable_pi_apply n)
  apply ReflectedWalk.MarkovChain.measure_eq_of_prefix_eq
  intro n
  apply Measure.ext_of_singleton
  intro z
  let x : ℕ → ℤ := extendHistory n z
  have hx : Preorder.frestrictLe n x = z := frestrictLe_extendHistory n z
  rw [← hx, Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton _),
    ← cylinder_eq_preimage, Measure.map_apply hf (measurableSet_cylinder n x),
    Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton _),
    ← cylinder_eq_preimage]
  have he : (fun ω : ℕ → ℤ => fun j => e (ω j)) ⁻¹' {ω | ∀ i ≤ n, ω i = x i} =
      {ω | ∀ i ≤ n, ω i = e.symm (x i)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, e.eq_symm_apply]
  rw [he, srwLaw_cylinder, srwLaw_cylinder]
  have hzero : (e.symm (x 0) = a) ↔ x 0 = e a := e.symm_apply_eq
  rw [if_congr hzero rfl rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simpa only [e.apply_symm_apply] using
    srwStep_singleton_relabel m e (e.symm (x i)) (e.symm (x (i + 1)))

/-- Translating the boundary paths by an integer number of mesh intervals
translates the entire vertex walk by the same integer. -/
theorem srwLaw_bmEdgeCount_timeShift_int (ε : ℝ) (L R : ℝ → ℝ) (k a : ℤ) :
    (srwLaw (bmEdgeCount ε (fun t => L (t + ε * k)) (fun t => R (t + ε * k))) a).map
      (fun ω n => ω n + k) = srwLaw (bmEdgeCount ε L R) (a + k) := by
  let e : ℤ ≃ ℤ := Equiv.addRight k
  have h : bmEdgeCount ε (fun t => L (t + ε * k)) (fun t => R (t + ε * k)) =
      fun x y => bmEdgeCount ε L R (e x) (e y) := by
    funext x y
    exact bmEdgeCount_timeShift_int ε L R k x y
  rw [h]
  exact srwLaw_map_relabel _ e a

end MatedCRT
