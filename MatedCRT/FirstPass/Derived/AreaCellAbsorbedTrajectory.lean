import MatedCRT.FirstPass.Derived.AreaCellStoppedStep
import LatticeProb.Bonanno.BouRabeeGwynne.TrajectoryCoupling

/-! # Absorbed trajectories of curve-cell walks -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory ReflectedGMS.GMS
open BouRabeeGwynne.FiniteConductanceNetwork

open Classical in
/-- The integer walk follows its usual step law on `D` and stays put elsewhere. -/
noncomputable def absorbedSrwKernel (m : ℤ → ℤ → ℕ) (D : Set ℤ) : Kernel ℤ ℤ :=
  Kernel.piecewise (Set.to_countable D).measurableSet (srwKernel m) Kernel.id

instance (m : ℤ → ℤ → ℕ) (D : Set ℤ) : IsMarkovKernel (absorbedSrwKernel m D) := by
  unfold absorbedSrwKernel
  infer_instance

/-- The finite restriction, relabelled by integers, has the absorbed integer
trajectory law. The retained-neighbor condition is needed only at active cells. -/
theorem areaCellConfig_finiteRestriction_trajectoryLaw_map
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε) (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] (A : Set R)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R →
      (areaCellConfig h hε (S.mult ε ω)).c v w = 0)
    (hpos : ∀ v ∈ A, 0 < (LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).totalConductance v)
    (v : R) :
    let e := euclideanCellEquiv h hε
    let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
    let D : Set ℤ := {a | ∃ x ∈ A, e a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
    let N := LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
    (N.trajectoryLaw A hpos v).map (fun p n => f (p n)) =
      Kernel.trajMeasure (Measure.dirac (f v))
        (fun n => (absorbedSrwKernel (S.mult ε ω) D).comap
          (fun x : Finset.Iic n → ℤ => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _)) := by
  classical
  dsimp only
  unfold BouRabeeGwynne.FiniteConductanceNetwork.trajectoryLaw
  apply BouRabeeGwynne.TrajectoryCoupling.map_trajectory_law _ _ _ _
    (fun z : R => (euclideanCellEquiv h hε).symm
      (z : (areaCellConfig h hε (S.mult ε ω)).cells)) (measurable_of_finite _)
  · exact Measure.map_dirac' (measurable_of_finite _) _
  · intro n x
    let u := x ⟨n, Finset.mem_Iic.mpr le_rfl⟩
    have hstep := areaCellConfig_finiteRestriction_stoppedStepPMF_map S ω h hε hlf
      R A hretain hpos ((euclideanCellEquiv h hε).symm (u : (areaCellConfig h hε (S.mult ε ω)).cells)) (by
        rw [Equiv.apply_symm_apply]
        exact u.property)
    have heq : (⟨euclideanCellEquiv h hε ((euclideanCellEquiv h hε).symm (u : (areaCellConfig h hε (S.mult ε ω)).cells)),
        by
        rw [Equiv.apply_symm_apply]
        exact u.property⟩ : R) = u := by
      apply Subtype.ext
      exact Equiv.apply_symm_apply _ _
    rw [heq] at hstep
    change ((LatticeProb.finiteConductanceRestriction _ _ _ _ R).stepPMF A hpos u).toMeasure.map
      (fun z : R => (euclideanCellEquiv h hε).symm (z : (areaCellConfig h hε (S.mult ε ω)).cells)) = _
    rw [PMF.toMeasure_map _ _ (measurable_of_finite _)]
    have hmap := congrArg (fun p => p.map (euclideanCellEquiv h hε).symm) hstep
    simp only [PMF.map_comp, Function.comp_def] at hmap
    by_cases hu : u ∈ A
    · have hd : (euclideanCellEquiv h hε).symm (u : (areaCellConfig h hε (S.mult ε ω)).cells) ∈
          {a : ℤ | ∃ y ∈ A, euclideanCellEquiv h hε a = (y : (areaCellConfig h hε (S.mult ε ω)).cells)} :=
        ⟨u, hu, by simp⟩
      simp only [hu, ↓reduceIte, PMF.map_comp, Function.comp_def, Equiv.symm_apply_apply,
        ] at hmap
      rw [hmap]
      rw [show (fun x : ℤ => x) = id from rfl, PMF.map_id]
      change (srwStep (S.mult ε ω) ((euclideanCellEquiv h hε).symm (u : (areaCellConfig h hε (S.mult ε ω)).cells))).toPMF.toMeasure =
        absorbedSrwKernel (S.mult ε ω) _ ((euclideanCellEquiv h hε).symm (u : (areaCellConfig h hε (S.mult ε ω)).cells))
      simp only [absorbedSrwKernel, Kernel.piecewise_apply]
      split_ifs
      exact Measure.toPMF_toMeasure (srwStep (S.mult ε ω)
        ((euclideanCellEquiv h hε).symm (u : (areaCellConfig h hε (S.mult ε ω)).cells)))
    · have hd : (euclideanCellEquiv h hε).symm (u : (areaCellConfig h hε (S.mult ε ω)).cells) ∉
          {a : ℤ | ∃ y ∈ A, euclideanCellEquiv h hε a = (y : (areaCellConfig h hε (S.mult ε ω)).cells)} := by
        rintro ⟨y, hy, hxy⟩
        have : y = u := Subtype.ext (by simpa using hxy.symm)
        exact hu (this ▸ hy)
      simp only [hu, ↓reduceIte, PMF.pure_map] at hmap
      rw [hmap]
      simp only [Equiv.symm_apply_apply]
      change (PMF.pure ((euclideanCellEquiv h hε).symm (u : (areaCellConfig h hε (S.mult ε ω)).cells))).toMeasure =
        absorbedSrwKernel (S.mult ε ω) _ ((euclideanCellEquiv h hε).symm (u : (areaCellConfig h hε (S.mult ε ω)).cells))
      simp only [absorbedSrwKernel, Kernel.piecewise_apply]
      split_ifs
      simp only [PMF.toMeasure_pure, Kernel.id_apply]

end MatedCRT
