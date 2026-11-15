import MatedCRT.FirstPass.Derived.JointMeshVertex
import MatedCRT.FirstPass.Derived.JointShiftedMeshMultiplicity
import MatedCRT.FirstPass.Derived.ConeUnstoppedWalkFamily

/-! # Selected embedded walk laws jointly in the mesh and time shift -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- A measurable selected walk law for every positive mesh, agreeing with the
paper's selected law on proper surjective curves. -/
theorem exists_measurable_jointMesh_selected_walk_law (m : ℝ≥0) :
    ∃ F : {ε : ℝ // 0 < ε} × ((C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ) →
        Measure C(ℝ≥0, ℂ),
      Measurable F ∧
      ∀ (ε : {ε : ℝ // 0 < ε}) (η : C(ℝ, ℂ)) (w : C(ℝ, ℝ × ℝ)) (x : ℂ),
        Tendsto η (cocompact ℝ) (cocompact ℂ) → Function.Surjective η →
        F (ε, ((η, w), x)) =
          (srwLaw (bmEdgeCount ε.1 (fun t => (w t).1) (fun t => (w t).2))
            (vertexOf ε.1 η x)).map (interpPathCM (vertexPoint ε.1 η) m.coe_nonneg) := by
  obtain ⟨V, hV, hVe⟩ := exists_measurable_jointMesh_vertexOf
  let E := {ε : ℝ // 0 < ε} × ((C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ)
  let v : E → ℤ → ℂ := fun p => vertexPoint p.1.1 p.2.1.1
  let M : E → ℤ → ℤ → ℕ := fun p =>
    bmEdgeCount p.1.1 (fun t => (p.2.1.2 t).1) (fun t => (p.2.1.2 t).2)
  let a : E → ℤ := fun p => V (p.1, p.2.1.1, p.2.2)
  have hv : Measurable v := by
    apply measurable_pi_iff.2
    intro k
    have ht : Continuous (fun p : E => p.1.1 * (k : ℝ)) := by
      dsimp [E]
      fun_prop
    exact (continuous_eval.comp
      (((continuous_fst.comp continuous_fst).comp continuous_snd).prodMk ht)).measurable
  have hM : ∀ j k, Measurable fun p : E => M p j k := by
    intro j k
    have harg : Measurable (fun p : E => (p.2.1.2, p.1, (0 : ℝ))) :=
      (measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_fst.prodMk measurable_const)
    have hm := (measurable_bmEdgeCount_shiftedMesh j k).comp harg
    simpa only [M, Function.comp_def, mul_zero, add_zero] using hm
  have ha : Measurable a := hV.comp (measurable_fst.prodMk
    (((measurable_fst.comp measurable_fst).comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd)))
  let G : E → ℤ → Measure C(ℝ≥0, ℂ) := fun p k =>
    (srwLaw (M p) k).map (interpPathCM (v p) m.coe_nonneg)
  have hG : Measurable G := measurable_pi_iff.2 fun k =>
    measurable_interpPathCM_srwLaw v hv M hM m k
  have hselect : Measurable (fun p : (ℤ → Measure C(ℝ≥0, ℂ)) × ℤ => p.1 p.2) :=
    measurable_from_prod_countable_left (fun k => measurable_pi_apply k)
  refine ⟨fun p => G p (a p), hselect.comp (hG.prodMk ha), ?_⟩
  intro ε η w x hp hs
  simp only [G, a, M, v, hVe ε η x hp hs]

/-- A measurable version jointly in the positive mesh, time shift, curve,
boundary pair and marked point. -/
theorem exists_measurable_jointMesh_shifted_selected_walk_law (m : ℝ≥0) :
    ∃ F : ({ε : ℝ // 0 < ε} × ((C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ)) × ℝ →
        Measure C(ℝ≥0, ℂ),
      Measurable F ∧
      ∀ (ε : {ε : ℝ // 0 < ε}) (η : C(ℝ, ℂ)) (w : C(ℝ, ℝ × ℝ)) (x : ℂ) (τ : ℝ),
        Tendsto η (cocompact ℝ) (cocompact ℂ) → Function.Surjective η →
        F ((ε, ((η, w), x)), τ) =
          (srwLaw (bmEdgeCount ε.1 (fun t => (w (t + τ)).1) (fun t => (w (t + τ)).2))
            (vertexOf ε.1 (fun t => η (t + τ)) x)).map
              (interpPathCM (vertexPoint ε.1 (fun t => η (t + τ))) m.coe_nonneg) := by
  obtain ⟨F, hF, hFe⟩ := exists_measurable_jointMesh_selected_walk_law m
  let shift (τ : ℝ) : C(ℝ, ℝ) := ⟨fun t => t + τ, continuous_id.add continuous_const⟩
  let E := ({ε : ℝ // 0 < ε} × ((C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ)) × ℝ
  let G : E → Measure C(ℝ≥0, ℂ) := fun p =>
    F (p.1.1, ((p.1.2.1.1.comp (shift p.2), p.1.2.1.2.comp (shift p.2)), p.1.2.2))
  have hη : Measurable (fun p : E => p.1.2.1.1.comp (shift p.2)) := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    exact (continuous_eval.comp
      (((((continuous_fst.comp continuous_fst).comp continuous_snd).comp continuous_fst)).prodMk
        (continuous_const.add continuous_snd))).measurable
  have hw : Measurable (fun p : E => p.1.2.1.2.comp (shift p.2)) := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    exact (continuous_eval.comp
      (((((continuous_snd.comp continuous_fst).comp continuous_snd).comp continuous_fst)).prodMk
        (continuous_const.add continuous_snd))).measurable
  refine ⟨G, hF.comp ((measurable_fst.comp measurable_fst).prodMk
    ((hη.prodMk hw).prodMk ((measurable_snd.comp measurable_snd).comp measurable_fst))), ?_⟩
  intro ε η w x τ hp hs
  have hshift : Tendsto (fun t : ℝ => t + τ) (cocompact ℝ) (cocompact ℝ) :=
    (Homeomorph.addRight τ).isClosedEmbedding.tendsto_cocompact
  have hp' : Tendsto (η.comp (shift τ)) (cocompact ℝ) (cocompact ℂ) := hp.comp hshift
  have hs' : Function.Surjective (η.comp (shift τ)) := by
    intro z
    obtain ⟨t, ht⟩ := hs z
    exact ⟨t - τ, by simpa [shift] using ht⟩
  exact hFe ε (η.comp (shift τ)) (w.comp (shift τ)) x hp' hs'

end MatedCRT
