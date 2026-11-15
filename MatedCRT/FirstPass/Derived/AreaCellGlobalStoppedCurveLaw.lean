import MatedCRT.FirstPass.Derived.AreaCellFullStoppedCurveLaw

/-! # Stopped curve laws with a global active set -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory BouRabeeGwynne
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- If the finite region contains every active cell, its stopped polygonal
curve law is the integer walk law stopped on the global active set. -/
theorem areaCellConfig_global_stopped_curveLaw
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε) (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    (B : Set (areaCellConfig h hε (S.mult ε ω)).cells)
    (hcontain : B ⊆ R)
    (hretain : ∀ v : R, (v : (areaCellConfig h hε (S.mult ε ω)).cells) ∈ B →
      ∀ w, w ∉ R → (areaCellConfig h hε (S.mult ε ω)).c v w = 0)
    (hpos : ∀ v : R, (v : (areaCellConfig h hε (S.mult ε ω)).cells) ∈ B →
      0 < (LatticeProb.finiteConductanceRestriction
        (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
          (areaCellConfig h hε (S.mult ε ω)).c v w)
        (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
        (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
        (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).totalConductance v)
    (v : R) {d : ℕ} (pos : (areaCellConfig h hε (S.mult ε ω)).cells → Euc d) :
    let e := euclideanCellEquiv h hε
    let A : Set R := {x | (x : (areaCellConfig h hε (S.mult ε ω)).cells) ∈ B}
    let N := LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
    ((N.trajectoryLaw A hpos v).map (fun p n =>
      (p n : (areaCellConfig h hε (S.mult ε ω)).cells))).map
        (stoppedPolygonalCurve pos B) =
      (srwLaw (S.mult ε ω) (e.symm v.1)).map
        (stoppedPolygonalCurve (pos ∘ e) (e ⁻¹' B)) := by
  classical
  dsimp only
  have heq := areaCellConfig_fullCell_stopped_curveLaw S ω h hε hlf R
    {x : R | (x : (areaCellConfig h hε (S.mult ε ω)).cells) ∈ B}
    hretain hpos v pos B rfl
  dsimp only at heq
  have hset : {a : ℤ | ∃ x : R, x.1 ∈ B ∧ euclideanCellEquiv h hε a = x.1} =
      (euclideanCellEquiv h hε) ⁻¹' B := by
    ext a
    constructor
    · rintro ⟨x, hx, he⟩
      change euclideanCellEquiv h hε a ∈ B
      rw [he]
      exact hx
    · intro ha
      change euclideanCellEquiv h hε a ∈ B at ha
      exact ⟨⟨euclideanCellEquiv h hε a, hcontain ha⟩, ha, rfl⟩
  simp only [Set.mem_ofPred_eq] at heq
  rw [hset] at heq
  exact heq

end MatedCRT
end
