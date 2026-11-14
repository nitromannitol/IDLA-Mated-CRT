import MatedCRT.FirstPass.Derived.AreaCellTransition

/-! # Relabelled random-walk step probabilities -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- Relabelling a multigraph step gives the cell transition probabilities. -/
theorem srwStep_toPMF_map_cell_apply
    (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m) (H : CellConfig)
    (e : ℤ ≃ H.cells) (a : ℤ) (hdeg : 0 < mdeg m a)
    (hc : ∀ b, H.c (e a) (e b) = (m a b : ℝ))
    (hpi : H.pi (e a) = (mdeg m a : ℝ)) (B : H.cells) :
    ((srwStep m a).toPMF.map e) B = ENNReal.ofReal (H.transition (e a) B) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (e.symm B)]
  · simp only [Equiv.apply_symm_apply, ↓reduceIte, Measure.toPMF_apply]
    simpa only [Equiv.apply_symm_apply] using
      srwStep_singleton_eq_cell_transition m hlf H e a (e.symm B) hdeg (hc _) hpi
  · intro b hb
    have hne : B ≠ e b := by
      intro he
      apply hb
      exact e.injective (by simpa only [Equiv.apply_symm_apply] using he.symm)
    simp only [hne, ↓reduceIte]

/-- Relabelling the integer walk step gives the mated-CRT cell transition. -/
theorem areaCellConfig_srwStep_toPMF_map_apply {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) {μ : Measure ℂ}
    (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (a : ℤ)
    (B : (areaCellConfig h hε (S.mult ε ω)).cells) :
    ((srwStep (S.mult ε ω) a).toPMF.map (euclideanCellEquiv h hε)) B =
      ENNReal.ofReal ((areaCellConfig h hε (S.mult ε ω)).transition
        (euclideanCellEquiv h hε a) B) :=
  srwStep_toPMF_map_cell_apply (S.mult ε ω) hlf _ _ a
    (S.mult_mdeg_pos hε.le ω hlf a) (areaCellConfig_conductance h hε _ a)
    (areaCellConfig_pi_eq_mdeg S ω h hε hlf a) B

end MatedCRT
