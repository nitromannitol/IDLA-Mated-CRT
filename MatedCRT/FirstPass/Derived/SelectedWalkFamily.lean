import MatedCRT.FirstPass.Derived.ConeUnstoppedWalkFamily
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentVertex

/-! # Measurable selected embedded walk laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- A jointly measurable version of the embedded walk law at the cell containing a
marked point, with equality for continuous proper surjective curves. -/
theorem exists_measurable_selected_walk_law {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0) :
    ∃ F : (C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ → Measure C(ℝ≥0, ℂ),
      Measurable F ∧
      ∀ (η : C(ℝ, ℂ)) (w : C(ℝ, ℝ × ℝ)) (x : ℂ),
        Tendsto η (cocompact ℝ) (cocompact ℂ) → Function.Surjective η →
        F ((η, w), x) =
          (srwLaw (bmEdgeCount ε (fun t => (w t).1) (fun t => (w t).2))
            (vertexOf ε η x)).map (interpPathCM (vertexPoint ε η) m.coe_nonneg) := by
  obtain ⟨V, hV, hVe⟩ := exists_measurable_vertexOf_curve hε
  let F : (C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ → Measure C(ℝ≥0, ℂ) := fun p =>
    (walkVertexFamily ε p.1.1 p.1.2 m (V (p.1.1, p.2))).2
  have hselect : Measurable (fun p :
      ((ℤ → ℂ × Measure C(ℝ≥0, ℂ)) × ℤ) => p.1 p.2) :=
    measurable_from_prod_countable_left (fun k => measurable_pi_apply k)
  have hfamily : Measurable (fun p : (C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ =>
      walkVertexFamily ε p.1.1 p.1.2 m) :=
    (measurable_walkVertexFamily ε m).comp measurable_fst
  have hv : Measurable (fun p : (C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ =>
      V (p.1.1, p.2)) :=
    hV.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  refine ⟨F, measurable_snd.comp (hselect.comp (hfamily.prodMk hv)), ?_⟩
  intro η w x hp hs
  simp only [F, walkVertexFamily, hVe η x hp hs]

end MatedCRT
