import MatedCRT.FirstPass.Derived.ShiftedSelectedWalkFamily

/-! # Selected walk laws jointly measurable in the time shift -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- A measurable version of the selected walk law, jointly in the time shift,
curve, boundary pair and marked point. -/
theorem exists_jointly_measurable_shifted_selected_walk_law {ε : ℝ} (hε : 0 < ε)
    (m : ℝ≥0) :
    ∃ F : ((C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ) × ℝ → Measure C(ℝ≥0, ℂ),
      Measurable F ∧
      ∀ (η : C(ℝ, ℂ)) (w : C(ℝ, ℝ × ℝ)) (x : ℂ) (τ : ℝ),
        Tendsto η (cocompact ℝ) (cocompact ℂ) → Function.Surjective η →
        F (((η, w), x), τ) =
          (srwLaw (bmEdgeCount ε (fun t => (w (t + τ)).1) (fun t => (w (t + τ)).2))
            (vertexOf ε (fun t => η (t + τ)) x)).map
              (interpPathCM (vertexPoint ε (fun t => η (t + τ))) m.coe_nonneg) := by
  obtain ⟨F, hF, hFe⟩ := exists_measurable_selected_walk_law hε m
  let shift (τ : ℝ) : C(ℝ, ℝ) := ⟨fun t => t + τ, continuous_id.add continuous_const⟩
  let G : ((C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ) × ℝ → Measure C(ℝ≥0, ℂ) :=
    fun p => F (((p.1.1.1.comp (shift p.2)), (p.1.1.2.comp (shift p.2))), p.1.2)
  have hη : Measurable (fun p : ((C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ) × ℝ =>
      p.1.1.1.comp (shift p.2)) := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    exact (continuous_eval.comp
      (((continuous_fst.comp continuous_fst).comp continuous_fst).prodMk
        (continuous_const.add continuous_snd))).measurable
  have hw : Measurable (fun p : ((C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ) × ℝ =>
      p.1.1.2.comp (shift p.2)) := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    exact (continuous_eval.comp
      (((continuous_snd.comp continuous_fst).comp continuous_fst).prodMk
        (continuous_const.add continuous_snd))).measurable
  refine ⟨G, hF.comp ((hη.prodMk hw).prodMk (measurable_snd.comp measurable_fst)), ?_⟩
  intro η w x τ hp hs
  have hshift : Tendsto (fun t : ℝ => t + τ) (cocompact ℝ) (cocompact ℝ) :=
    (Homeomorph.addRight τ).isClosedEmbedding.tendsto_cocompact
  have hp' : Tendsto (η.comp (shift τ)) (cocompact ℝ) (cocompact ℂ) := hp.comp hshift
  have hs' : Function.Surjective (η.comp (shift τ)) := by
    intro z
    obtain ⟨t, ht⟩ := hs z
    exact ⟨t - τ, by simpa [shift] using ht⟩
  exact hFe (η.comp (shift τ)) (w.comp (shift τ)) x hp' hs'

end MatedCRT
