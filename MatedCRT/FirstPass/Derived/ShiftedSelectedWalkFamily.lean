import MatedCRT.FirstPass.Derived.SelectedWalkFamily

/-! # Selected embedded walk laws on shifted time grids -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- A measurable version of the embedded walk law at a marked point on a fixed
shifted time grid, agreeing with the selected law for proper surjective curves. -/
theorem exists_measurable_shifted_selected_walk_law {ε : ℝ} (hε : 0 < ε)
    (m : ℝ≥0) (τ : ℝ) :
    ∃ F : (C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ → Measure C(ℝ≥0, ℂ),
      Measurable F ∧
      ∀ (η : C(ℝ, ℂ)) (w : C(ℝ, ℝ × ℝ)) (x : ℂ),
        Tendsto η (cocompact ℝ) (cocompact ℂ) → Function.Surjective η →
        F ((η, w), x) =
          (srwLaw (bmEdgeCount ε (fun t => (w (t + τ)).1) (fun t => (w (t + τ)).2))
            (vertexOf ε (fun t => η (t + τ)) x)).map
              (interpPathCM (vertexPoint ε (fun t => η (t + τ))) m.coe_nonneg) := by
  obtain ⟨F, hF, hFe⟩ := exists_measurable_selected_walk_law hε m
  let shift : C(ℝ, ℝ) := ⟨fun t => t + τ, continuous_id.add continuous_const⟩
  let G : (C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ → Measure C(ℝ≥0, ℂ) :=
    fun p => F (((p.1.1.comp shift), (p.1.2.comp shift)), p.2)
  have hη : Measurable (fun p : (C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ => p.1.1.comp shift) := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    exact (ContinuousMap.measurable_eval (t + τ)).comp (measurable_fst.comp measurable_fst)
  have hw : Measurable (fun p : (C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ => p.1.2.comp shift) := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    exact (ContinuousMap.measurable_eval (t + τ)).comp (measurable_snd.comp measurable_fst)
  refine ⟨G, hF.comp ((hη.prodMk hw).prodMk measurable_snd), ?_⟩
  intro η w x hp hs
  have hshift : Tendsto (fun t : ℝ => t + τ) (cocompact ℝ) (cocompact ℝ) :=
    (Homeomorph.addRight τ).isClosedEmbedding.tendsto_cocompact
  have hp' : Tendsto (η.comp shift) (cocompact ℝ) (cocompact ℂ) := hp.comp hshift
  have hs' : Function.Surjective (η.comp shift) := by
    intro z
    obtain ⟨t, ht⟩ := hs z
    exact ⟨t - τ, by simpa [shift] using ht⟩
  exact hFe (η.comp shift) (w.comp shift) x hp' hs'

end MatedCRT
