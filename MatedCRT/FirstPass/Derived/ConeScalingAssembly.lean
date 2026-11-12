import MatedCRT.FirstPass.Derived.ConeRadialRescale

/-!
# Assembly of the scale invariance of the quantum cone from the radial invariance

The cone scale radius `R_b` is a function of the radial process, the radial process of the rescaled field is a
measurable function of the radial process of the field (`radialProcess_rescaled_ae`), and the lateral circle
averages at the dilated circles `R_b q_j` are independent of the radial process and have the law of the lateral
circle averages at the circles `q_j` (`map_radial_dilatedLateral_vec`).  If the radial process of the rescaled field
has the law of the radial process of the field (the radial invariance of the quantum cone, a statement about
one-dimensional Brownian motion with drift), then the pair (radial process of the rescaled field, lateral circle
averages at `R_b q_j`) has the same product law as the pair (radial process, lateral circle averages at `q_j`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal Classical

namespace MatedCRT.FirstPass.Derived

/-- The lateral circle averages at the dilated circles `R_b q_j` form an almost surely measurable vector (a limit
of the dyadic discretisations). -/
lemma aemeasurable_dilVec_cone {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) {k : ℕ}
    (q : Fin k → NonsingularCircle) :
    AEMeasurable (fun ω => dilVec q (coneScaleRadius γ (hcirc ω) b)
      (projCircle (lateralProcess (hC ω) (hcirc ω)))) P := by
  have hXm : Measurable fun ω => radialProcess (hcirc ω) :=
    Measurable.prodMk
      (Measurable.of_eval fun t => h.measurable_circle _ _ (Real.exp_pos _))
      (Measurable.of_eval fun s => h.measurable_circle _ _ (Real.exp_pos _))
  have hLae : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    MatedCRT.ConeMeanZeroRestriction.lateralProcessAEMeasurable_holds.1 γ Ω P hC hcirc inferInstance h
  have hYae : AEMeasurable (fun ω => projCircle (lateralProcess (hC ω) (hcirc ω))) P :=
    measurable_projCircle.comp_aemeasurable hLae
  have hρ : Measurable (radScale γ b) := measurable_radScale γ b
  have hk : ∀ n : ℕ, Measurable fun p : RadialPair => ⌈(2 : ℝ) ^ n * radScale γ b p⌉ := fun n =>
    Int.measurable_ceil.comp (measurable_const.mul hρ)
  have hTm : ∀ (n : ℕ) (i : ℤ), Measurable (dilVec q (dyadicRadius n i)) := fun n i => measurable_dilVec q _
  have hVm : ∀ n : ℕ, AEMeasurable (fun ω => dilVec q (dyadicRadius n ⌈(2 : ℝ) ^ n * radScale γ b (radialProcess (hcirc ω))⌉)
      (projCircle (lateralProcess (hC ω) (hcirc ω)))) P := by
    intro n
    have hT2 : Measurable (fun r : ℤ × (NonsingularCircle → ℝ) => dilVec q (dyadicRadius n r.1) r.2) :=
      measurable_from_prod_countable_right (fun i => hTm n i)
    have hΦ : Measurable (fun p : RadialPair × (NonsingularCircle → ℝ) =>
        dilVec q (dyadicRadius n ⌈(2 : ℝ) ^ n * radScale γ b p.1⌉) p.2) :=
      hT2.comp (((hk n).comp measurable_fst).prodMk measurable_snd)
    exact hΦ.comp_aemeasurable (hXm.aemeasurable.prodMk hYae)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => dilVec q (dyadicRadius n ⌈(2 : ℝ) ^ n * radScale γ b (radialProcess (hcirc ω))⌉)
      (projCircle (lateralProcess (hC ω) (hcirc ω)))) atTop
      (𝓝 (dilVec q (coneScaleRadius γ (hcirc ω) b) (projCircle (lateralProcess (hC ω) (hcirc ω))))) := by
    filter_upwards [ae_continuous_lateralCircle_cone h, ae_coneScaleRadius_spec hγ0 hγ2 h b,
      radScale_radialProcess_ae hγ0 hγ2 h b] with ω hcont hspec hrho
    have hR := hspec.1
    have hRn := tendsto_dyadicRadius_ceil hR
    rw [tendsto_pi_nhds]
    intro j
    have h1 := tendsto_dilateTot hR (fun n => dyadicRadius_pos n _) hRn (q j)
    have h2 := (hcont.tendsto _).comp h1
    simp only [hrho, dilVec]
    exact h2
  exact aemeasurable_of_tendsto_metrizable_ae atTop hVm hlim

/-- **The rescaled radial process and the dilated lateral circle averages: product law, given the radial
invariance.** -/
theorem map_radialRescale_dilatedLateral_vec {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) {k : ℕ}
    (q : Fin k → NonsingularCircle)
    (hrad : P.map (fun ω => radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) =
      P.map (fun ω => radialProcess (hcirc ω))) :
    P.map (fun ω => (radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
        dilVec q (coneScaleRadius γ (hcirc ω) b) (projCircle (lateralProcess (hC ω) (hcirc ω))))) =
      (P.map fun ω => radialProcess (hcirc ω)).prod
        (P.map fun ω => fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j)) := by
  have hXm : Measurable fun ω => radialProcess (hcirc ω) :=
    Measurable.prodMk
      (Measurable.of_eval fun t => h.measurable_circle _ _ (Real.exp_pos _))
      (Measurable.of_eval fun s => h.measurable_circle _ _ (Real.exp_pos _))
  have h5b := map_radial_dilatedLateral_vec hγ0 hγ2 h b q
  have hGm := measurable_radialRescale γ b
  have hres := radialProcess_rescaled_ae hγ0 hγ2 h b
  have hae : AEMeasurable (fun ω => (radialProcess (hcirc ω), dilVec q (coneScaleRadius γ (hcirc ω) b)
      (projCircle (lateralProcess (hC ω) (hcirc ω))))) P :=
    hXm.aemeasurable.prodMk (aemeasurable_dilVec_cone hγ0 hγ2 h b q)
  have hmapG : (P.map fun ω => radialProcess (hcirc ω)).map (radialRescale γ b) =
      P.map (fun ω => radialProcess (hcirc ω)) := by
    rw [Measure.map_map hGm hXm, ← hrad]
    refine Measure.map_congr ?_
    filter_upwards [hres] with ω hω
    exact hω.symm
  calc P.map (fun ω => (radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
          dilVec q (coneScaleRadius γ (hcirc ω) b) (projCircle (lateralProcess (hC ω) (hcirc ω)))))
      = P.map (fun ω => (radialRescale γ b (radialProcess (hcirc ω)), dilVec q (coneScaleRadius γ (hcirc ω) b)
          (projCircle (lateralProcess (hC ω) (hcirc ω))))) := by
        refine Measure.map_congr ?_
        filter_upwards [hres] with ω hω
        rw [hω]
    _ = (P.map (fun ω => (radialProcess (hcirc ω), dilVec q (coneScaleRadius γ (hcirc ω) b)
          (projCircle (lateralProcess (hC ω) (hcirc ω)))))).map (Prod.map (radialRescale γ b) id) := by
        exact (AEMeasurable.map_map_of_aemeasurable (hGm.prodMap measurable_id).aemeasurable hae).symm
    _ = ((P.map fun ω => radialProcess (hcirc ω)).prod
          (P.map fun ω => fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j))).map
          (Prod.map (radialRescale γ b) id) := by rw [h5b]
    _ = ((P.map fun ω => radialProcess (hcirc ω)).map (radialRescale γ b)).prod
          ((P.map fun ω => fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j)).map id) :=
        (Measure.map_prod_map _ _ hGm measurable_id).symm
    _ = _ := by rw [hmapG, Measure.map_id]

end MatedCRT.FirstPass.Derived
