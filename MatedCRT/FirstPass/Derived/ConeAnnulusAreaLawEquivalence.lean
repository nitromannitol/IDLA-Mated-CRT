import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceInner

/-!
# The laws of the area measures of the two quantum cones on a bounded annulus

`ConeAnnulusAreaLawEquivalence γ` (`GMS21Lemma33Cone.lean`) from the steps of
`ConeAnnulusAreaLawEquivalenceSteps.lean`. For either cone (`α = γ` or `α = 0`) the outer data on `{δ < |z| < M}` is
almost surely `G` of the curve `e`, the lateral part of the field, the inner radial path and the outer radial window
(`ConeAnnulusLocality`). These four random variables are independent (the curve is independent of the cone data, the
field of the two radial Brownian motions, and these of each other), so the law of the outer data is the image under
`G` of the product of their laws (`map_annulusOuterData_eq_map_prod`). The factors of the two products are pairwise
equal (the curve, the lateral part: `LateralPartLaw`) or mutually absolutely continuous (the inner path:
`ConeInnerPathLaw`; the outer window: `ConeOuterWindowLaw`), hence so are the products and their images
(`coneAnnulusAreaLawEquivalence_of_steps`).

Source: the answer to MQ-sbl-18, section "The field laws on a bounded annulus"; Gwynne–Miller–Sheffield
(arXiv:1705.11161), §2.3.1; Duplantier–Miller–Sheffield (arXiv:1409.7055), Definition 4.10.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.MesoModel.FrozenIdentities (lt_lqgQ lqgQ_pos)

/-- **The law of the outer data as the image of a product law.** If the outer data of the cone
`coneField X (coneRadial γ α B B')` on `{δ < |z| < M}` is almost surely `G` of the curve, `Λ` of the field, the inner
path and `Φ` of the outer Brownian motion, and the curve, the field and the two Brownian motions have the independence
structure of the cone data, then the law of the outer data is the image under `G` of the product of the four laws. -/
theorem map_annulusOuterData_eq_map_prod {γ α δ M T : ℝ}
    {G : C(ℝ, ℂ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → C(ℝ, ℂ) × Measure ℂ} (hG : Measurable G)
    {Λ : Field → Field} (hΛ : Measurable Λ) {Φ : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ)} (hΦ : Measurable Φ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → Field} {B B' : ℝ≥0 → Ω → ℝ} {e : Ω → C(ℝ, ℂ)}
    (hX : Measurable X) (hBm : AEMeasurable (fun ω t => B t ω) P)
    (hB'm : AEMeasurable (fun ω t => B' t ω) P) (he : Measurable e)
    (hie : IndepFun e (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω))) P)
    (hXB : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P)
    (hBB : IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P)
    (hae : ∀ᵐ ω ∂P, annulusOuterData (e ω) (quantumConeArea γ α X B B' ω) δ M =
      G (e ω, Λ (X ω), coneInnerPath α T (fun t => B t ω), Φ (fun t => B' t ω))) :
    P.map (fun ω => annulusOuterData (e ω) (quantumConeArea γ α X B B' ω) δ M) =
      ((P.map e).prod ((P.map fun ω => Λ (X ω)).prod
        ((P.map fun ω => coneInnerPath α T (fun t => B t ω)).prod
          (P.map fun ω => Φ (fun t => B' t ω))))).map G := by
  set I : Ω → ℝ≥0 → ℝ := fun ω => coneInnerPath α T (fun t => B t ω) with hI
  set O : Ω → ℝ≥0 → ℝ := fun ω => Φ (fun t => B' t ω) with hO
  set L : Ω → Field := fun ω => Λ (X ω) with hL
  have hIm : AEMeasurable I P := (measurable_coneInnerPath α T).comp_aemeasurable hBm
  have hOm : AEMeasurable O P := hΦ.comp_aemeasurable hB'm
  have hLm : AEMeasurable L P := (hΛ.comp hX).aemeasurable
  -- independence of the inner path and the outer window
  have hIO : IndepFun I O P :=
    hBB.comp (φ := coneInnerPath α T) (ψ := Φ) (measurable_coneInnerPath α T) hΦ
  -- independence of the lateral part and the radial data
  have hLIO : IndepFun L (fun ω => (I ω, O ω)) P :=
    hXB.comp (φ := Λ) (ψ := fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => (coneInnerPath α T p.1, Φ p.2)) hΛ
      (((measurable_coneInnerPath α T).comp measurable_fst).prodMk (hΦ.comp measurable_snd))
  -- independence of the curve and the cone data
  have heLIO : IndepFun e (fun ω => (L ω, I ω, O ω)) P :=
    hie.comp (φ := id) (ψ := fun p : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
        (Λ p.1, coneInnerPath α T p.2.1, Φ p.2.2)) measurable_id
      ((hΛ.comp measurable_fst).prodMk
        (((measurable_coneInnerPath α T).comp (measurable_fst.comp measurable_snd)).prodMk
          (hΦ.comp (measurable_snd.comp measurable_snd))))
  have hZ : AEMeasurable (fun ω => (e ω, L ω, I ω, O ω)) P :=
    he.aemeasurable.prodMk (hLm.prodMk (hIm.prodMk hOm))
  have hprod : P.map (fun ω => (e ω, L ω, I ω, O ω)) =
      (P.map e).prod ((P.map L).prod ((P.map I).prod (P.map O))) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map he.aemeasurable
        (hLm.prodMk (hIm.prodMk hOm))).1 heLIO,
      (indepFun_iff_map_prod_eq_prod_map_map hLm (hIm.prodMk hOm)).1 hLIO,
      (indepFun_iff_map_prod_eq_prod_map_map hIm hOm).1 hIO]
  rw [Measure.map_congr hae, ← hprod,
    AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hZ]
  rfl

/-- **`ConeAnnulusAreaLawEquivalence` from the steps.** -/
theorem coneAnnulusAreaLawEquivalence_of_steps {γ : ℝ} (h0 : BrownianPathAEMeasurable)
    (h1 : ∀ δ M : ℝ, 0 < δ → δ < M → ConeAnnulusLocality γ δ M) (h2 : ConeInnerPathLaw)
    (h3 : ConeOuterWindowLaw) (h3m : ConeOuterWindowMeasurable) (h4 : LateralPartLaw) :
    ConeAnnulusAreaLawEquivalence γ := by
  intro Ω _ P _ X X₀ B B' B₀ B₀' e hγ hX hX₀ hB hB' hB₀ hB₀' hind hind₀ he hie δ M hδ hδM
  obtain ⟨T, S, G, hT, hS, hG, hloc⟩ := h1 δ M hδ hδM
  obtain ⟨Λ, hΛ, hΛae, hΛlaw⟩ := h4
  have hQγ : 0 < lqgQ γ - γ := sub_pos.2 (lt_lqgQ hγ)
  have hQ0 : 0 < lqgQ γ - 0 := by rw [sub_zero]; exact lqgQ_pos hγ.1
  obtain ⟨Φ₁, hΦ₁, hΦ₁ae⟩ := h3m (lqgQ γ - γ) S hQγ hS
  obtain ⟨Φ₀, hΦ₀, hΦ₀ae⟩ := h3m (lqgQ γ - 0) S hQ0 hS
  -- the independence of the curve from each cone's data
  have hie₁ : IndepFun e (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω))) P :=
    hie.comp (φ := id) (ψ := fun p : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
        (p.1, p.2.1, p.2.2.1)) measurable_id
      (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))))
  have hie₀ : IndepFun e (fun ω => (X₀ ω, (fun t => B₀ t ω), (fun t => B₀' t ω))) P :=
    hie.comp (φ := id) (ψ := fun p : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
        (p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2)) measurable_id
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
        ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
          (measurable_snd.comp measurable_snd)))).prodMk
          (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
            (measurable_snd.comp measurable_snd))))))
  -- the a.s. representations
  have hae₁ : ∀ᵐ ω ∂P, annulusOuterData (e ω) (quantumConeArea γ γ X B B' ω) δ M =
      G (e ω, Λ (X ω), coneInnerPath γ T (fun t => B t ω), Φ₁ (fun t => B' t ω)) := by
    filter_upwards [hloc γ (lt_lqgQ hγ) P X B B' e hX hB hB' hind, hΛae P X hX,
      hΦ₁ae P B' hB'] with ω h₁ h₂ h₃
    rw [h₁, h₂, h₃]
  have hae₀ : ∀ᵐ ω ∂P, annulusOuterData (e ω) (quantumConeArea γ 0 X₀ B₀ B₀' ω) δ M =
      G (e ω, Λ (X₀ ω), coneInnerPath 0 T (fun t => B₀ t ω), Φ₀ (fun t => B₀' t ω)) := by
    filter_upwards [hloc 0 (lqgQ_pos hγ.1) P X₀ B₀ B₀' e hX₀ hB₀ hB₀' hind₀, hΛae P X₀ hX₀,
      hΦ₀ae P B₀' hB₀'] with ω h₁ h₂ h₃
    rw [h₁, h₂, h₃]
  rw [map_annulusOuterData_eq_map_prod hG hΛ hΦ₁ hX.measurable (h0 P B hB) (h0 P B' hB') he hie₁
      hind.1 hind.2 hae₁,
    map_annulusOuterData_eq_map_prod hG hΛ hΦ₀ hX₀.measurable (h0 P B₀ hB₀) (h0 P B₀' hB₀') he
      hie₀ hind₀.1 hind₀.2 hae₀, hΛlaw P X X₀ hX hX₀]
  -- the outer windows through their measurable versions
  have hO₁ : P.map (fun ω => Φ₁ (fun t => B' t ω)) =
      P.map (fun ω => coneOuterWindow (lqgQ γ - γ) S (fun t => B' t ω)) :=
    Measure.map_congr ((hΦ₁ae P B' hB').mono fun ω h => h.symm)
  have hO₀ : P.map (fun ω => Φ₀ (fun t => B₀' t ω)) =
      P.map (fun ω => coneOuterWindow (lqgQ γ - 0) S (fun t => B₀' t ω)) :=
    Measure.map_congr ((hΦ₀ae P B₀' hB₀').mono fun ω h => h.symm)
  rw [hO₁, hO₀]
  constructor
  · refine Measure.AbsolutelyContinuous.map ?_ hG
    refine Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl
      (Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl
        (Measure.AbsolutelyContinuous.prod ?_ ?_))
    · exact (h2 γ 0 T hT P B B₀ hB hB₀).2
    · exact (h3 (lqgQ γ - γ) (lqgQ γ - 0) S hQγ hQ0 hS P B' B₀' hB' hB₀').2
  · refine Measure.AbsolutelyContinuous.map ?_ hG
    refine Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl
      (Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl
        (Measure.AbsolutelyContinuous.prod ?_ ?_))
    · exact (h2 0 γ T hT P B₀ B hB₀ hB).2
    · exact (h3 (lqgQ γ - 0) (lqgQ γ - γ) S hQ0 hQγ hS P B₀' B' hB₀' hB').2

end MatedCRT
