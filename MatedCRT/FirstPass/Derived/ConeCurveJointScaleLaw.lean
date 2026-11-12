import MatedCRT.FirstPass.Derived.IGCurveScaleLaw
import MatedCRT.FirstPass.Derived.ConeLQGAreaMeasurableOf

/-!
# Joint scaling law of the γ-quantum cone and the imaginary-geometry curve

In a mating-of-trees coupling, let `h = coneFieldOf γ X B B'` be the circle-average embedding of the
γ-quantum cone, `R_b` its scale at level `b` (`coneScale`), `h_b = h(R_b ·) + Q log R_b − γ⁻¹ log b`
the rescaled field (`coneRescaleField`), and `η_L` the whole-plane space-filling SLE given by
imaginary geometry. Then the rescaled pair `(h_b, R_b⁻¹ η_L(R_b² ·))` has the law of `(h, η_L)`
(Duplantier-Miller-Sheffield, Proposition 4.13(i) for the field, together with the scale invariance
of `η_L` and the independence of `η_L` from the field).

The proof writes `h` and `h_b` as measurable functions of the pair `Z = (X, W)` of the whole-plane GFF
and the continuous radial path `W` of `exists_radialPath`, shows `η_L ⊥ Z`, applies the scaling law
`map_prod_igDilate_igCurve` of `η_L` jointly with `Z`, pushes it forward, and uses the field law
`map_coneRescaleField_coneFieldOf` with the independence once more.

The independence `η_L ⊥ (X, W)` is obtained by regrouping mutually independent triples
(`indepFun_prodMk_left_of_indepFun_prodMk`, `indepFun_prodMk_right_of_indepFun_prodMk`) after
replacing the Brownian paths by measurable continuous versions.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

open MatedCRTHarmonic.CellScaling MatedCRTHarmonic.ConeScaling LQGMetric

section Grouping

variable {Ω α β δ : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace δ] {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → α} {g : Ω → β}
  {k : Ω → δ}

/-- Regrouping a mutually independent triple: if `f ⊥ (g, k)` and `g ⊥ k`, then `(f, g) ⊥ k`. -/
theorem indepFun_prodMk_left_of_indepFun_prodMk (hf : Measurable f) (hg : Measurable g)
    (hk : Measurable k) (hfgk : IndepFun f (fun ω => (g ω, k ω)) P) (hgk : IndepFun g k P) :
    IndepFun (fun ω => (f ω, g ω)) k P := by
  have hfg : IndepFun f g P := hfgk.comp measurable_id measurable_fst
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable
    (hg.prodMk hk).aemeasurable).1 hfgk
  rw [(indepFun_iff_map_prod_eq_prod_map_map hg.aemeasurable hk.aemeasurable).1 hgk] at h1
  rw [indepFun_iff_map_prod_eq_prod_map_map (hf.prodMk hg).aemeasurable hk.aemeasurable,
    (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).1 hfg]
  have e : (fun ω => ((f ω, g ω), k ω)) =
      (MeasurableEquiv.prodAssoc : (α × β) × δ ≃ᵐ α × β × δ).symm ∘
        fun ω => (f ω, (g ω, k ω)) := by
    funext ω
    rfl
  rw [e, ← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (hf.prodMk (hg.prodMk hk)), h1]
  exact (MeasurePreserving.symm _ (measurePreserving_prodAssoc _ _ _)).map_eq

/-- Regrouping a mutually independent triple: if `f ⊥ g` and `(f, g) ⊥ k`, then `f ⊥ (g, k)`. -/
theorem indepFun_prodMk_right_of_indepFun_prodMk (hf : Measurable f) (hg : Measurable g)
    (hk : Measurable k) (hfg : IndepFun f g P)
    (hfgk : IndepFun (fun ω => (f ω, g ω)) k P) :
    IndepFun f (fun ω => (g ω, k ω)) P := by
  have hkgf : IndepFun k (fun ω => (g ω, f ω)) P :=
    hfgk.symm.comp measurable_id (measurable_snd.prodMk measurable_fst)
  have h := indepFun_prodMk_left_of_indepFun_prodMk hk hg hf hkgf hfg.symm
  exact h.symm.comp measurable_id (measurable_snd.prodMk measurable_fst)


/-- Push-forward of a joint law along a measurable function of the first coordinate, when the
second coordinate is independent: if `(Z, D)` has the law of `(Z, L)`, `L ⊥ Z`, and `F(Z)` has
the law of `G(Z)`, then `(F(Z), D)` has the law of `(G(Z), L)`. -/
theorem map_prod_comp_eq_of_indepFun {ε ζ : Type*} [MeasurableSpace ε] [MeasurableSpace ζ]
    {Z : Ω → ε} {D L : Ω → β} {F G : ε → ζ} (hZ : Measurable Z) (hD : Measurable D)
    (hL : Measurable L) (hF : Measurable F) (hG : Measurable G)
    (hZD : P.map (fun ω => (Z ω, D ω)) = P.map (fun ω => (Z ω, L ω)))
    (hind : IndepFun Z L P) (hlaw : P.map (fun ω => F (Z ω)) = P.map (fun ω => G (Z ω))) :
    P.map (fun ω => (F (Z ω), D ω)) = P.map (fun ω => (G (Z ω), L ω)) := by
  have hFp : Measurable fun p : ε × β => (F p.1, p.2) := (hF.comp measurable_fst).prodMk measurable_snd
  have e1 : (fun ω => (F (Z ω), D ω)) = (fun p : ε × β => (F p.1, p.2)) ∘ (fun ω => (Z ω, D ω)) :=
    rfl
  have e2 : (fun ω => (F (Z ω), L ω)) = (fun p : ε × β => (F p.1, p.2)) ∘ (fun ω => (Z ω, L ω)) :=
    rfl
  have hFL : P.map (fun ω => (F (Z ω), D ω)) = P.map (fun ω => (F (Z ω), L ω)) := by
    rw [e1, e2, ← Measure.map_map hFp (hZ.prodMk hD), ← Measure.map_map hFp (hZ.prodMk hL), hZD]
  have hm1 : AEMeasurable (fun ω => F (Z ω)) P := (hF.comp hZ).aemeasurable
  have hm2 : AEMeasurable (fun ω => G (Z ω)) P := (hG.comp hZ).aemeasurable
  have hi1 : IndepFun (fun ω => F (Z ω)) L P := hind.comp hF measurable_id
  have hi2 : IndepFun (fun ω => G (Z ω)) L P := hind.comp hG measurable_id
  rw [hFL, (indepFun_iff_map_prod_eq_prod_map_map hm1 hL.aemeasurable).1 hi1,
    (indepFun_iff_map_prod_eq_prod_map_map hm2 hL.aemeasurable).1 hi2, hlaw]

end Grouping

/-- In a mating-of-trees coupling with `γ ∈ (0, 2)`, the radial process of the γ-quantum cone has a
measurable continuous version `W` such that the space-filling SLE `η_L` is independent of the pair
`(X, W)` of the whole-plane GFF and `W`. -/
theorem exists_radialPath_indepFun_igCurve {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ W : Ω → C(ℝ, ℝ), Measurable W ∧ IndepFun ηL (fun ω => (X ω, W ω)) P ∧
      ∀ᵐ ω ∂P, ∀ t, W ω t = coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t := by
  have := h.isProbabilityMeasure
  have hL : Measurable ηL := h.measurable_curves.1
  have hXm : Measurable X := h.gff.measurable
  obtain ⟨Bc, hBcm, hBc⟩ := exists_continuousMap_version h.bm_B
  obtain ⟨Bc', hBc'm, hBc'⟩ := exists_continuousMap_version h.bm_B'
  have hc : Measurable fun f : C(ℝ≥0, ℝ) => (⇑f : ℝ≥0 → ℝ) :=
    measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval t
  let K : Ω → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) := fun ω => ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ))
  have hKm : Measurable K := (hc.comp hBcm).prodMk (hc.comp hBc'm)
  have hpath : (fun ω => ((fun t => B t ω), (fun t => B' t ω))) =ᵐ[P] K := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hLXK : IndepFun ηL (fun ω => (X ω, K ω)) P := by
    have h0 := (indepFun_igCurve_cone h).comp measurable_id
      (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst))
    refine h0.congr (ae_eq_refl _) ?_
    filter_upwards [hpath] with ω hω
    show (X ω, ((fun t => B t ω), (fun t => B' t ω))) = (X ω, K ω)
    rw [hω]
  have hXK : IndepFun X K P := h.indep_cone.1.congr (ae_eq_refl _) hpath
  have hLX_B : IndepFun (fun ω => (ηL ω, X ω))
      (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P :=
    (indepFun_prodMk_left_of_indepFun_prodMk hL hXm hKm hLXK hXK).congr (ae_eq_refl _)
      hpath.symm
  obtain ⟨W, hWm, hLXW, hW⟩ := exists_radialPath hγ hγ2 h.bm_B h.bm_B' hLX_B
  exact ⟨W, hWm, indepFun_prodMk_right_of_indepFun_prodMk hL hXm hWm
    (hLXK.comp measurable_id measurable_fst) hLXW, hW⟩

/-- **Joint scaling law of the γ-quantum cone and the imaginary-geometry curve.** In a
mating-of-trees coupling with `γ ∈ (0, 2)` and any level `b₀`, write `h` for the circle-average
embedding `coneFieldOf γ X B B'` of the γ-quantum cone and `R = coneScale γ γ B B' b₀`. Then
`(h_b, R⁻¹ η_L(R² ·))` has the law of `(h, η_L)`, where `h_b = coneRescaleField γ R b₀ h`. -/
theorem map_coneRescaleField_igDilate_igCurve {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) (b₀ : ℝ) :
    P.map (fun ω =>
        (coneRescaleField γ (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀) b₀
          (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)),
        igDilate (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀) (ηL ω))) =
      P.map (fun ω => (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω), ηL ω)) := by
  have := h.isProbabilityMeasure
  have hL : Measurable ηL := h.measurable_curves.1
  have hXm : Measurable X := h.gff.measurable
  have hB := h.bm_B
  have hB' := h.bm_B'
  obtain ⟨W, hWm, hLZ, hW⟩ := exists_radialPath_indepFun_igCurve h hγ hγ2
  -- the scale and the two fields as measurable functions of Z = (X, W)
  let Z : Ω → DistC × C(ℝ, ℝ) := fun ω => (X ω, W ω)
  have hZm : Measurable Z := hXm.prodMk hWm
  let R : DistC × C(ℝ, ℝ) → ℝ := fun z =>
    Real.exp (lastLevel (lqgQ γ) (γ⁻¹ * Real.log b₀) z.2)
  have hRm : Measurable R :=
    Real.measurable_exp.comp ((measurable_lastLevel _ _).comp measurable_snd)
  let Hb : DistC × C(ℝ, ℝ) → DistC := fun z =>
    fieldOf (affineComp (R z) 0 (lateralPart z.1)) (radShift (lqgQ γ) (γ⁻¹ * Real.log b₀) z.2)
  have hHbm : Measurable Hb :=
    measurable_fieldOf.comp (Measurable.prodMk
      (MatedCRTHarmonic.MoTPort.ConeMeas.measurable_affineComp_joint.comp
        (hRm.prodMk (measurable_lateralPart.comp measurable_fst)))
      ((measurable_radShift _ _).comp measurable_snd))
  let H : DistC × C(ℝ, ℝ) → DistC := fun z => fieldOf (lateralPart z.1) z.2
  have hHm : Measurable H :=
    measurable_fieldOf.comp ((measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  -- local integrability of the radial profile
  have hQ : lqgQ γ = QuantumZipper.Qc γ := by dsimp [lqgQ, QuantumZipper.Qc]
  have hA : MatedCRTHarmonic.MoTPort.IsConeProcess γ (QuantumZipper.Qc γ)
      (fun t ω => MatedCRTHarmonic.LQGCone.motConeRadial γ γ (fun s => B s ω)
        (fun s => B' s ω) t) P :=
    MatedCRTHarmonic.LQGCone.isConeProcess_motConeRadial hB hB' h.indep_cone.2
  have hli : ∀ᵐ ω ∂P, LocallyIntegrable (radialOf (W ω)) volume := by
    filter_upwards [hW, MatedCRTHarmonic.MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA]
      with ω hω hl
    refine hl.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [radialOf, hω, MatedCRTHarmonic.LQGCone.coneRadial_eq_Q_add_motConeRadial, hQ]
  -- the coupling objects agree almost surely with the measurable functions of Z
  have ehR : ∀ᵐ ω ∂P, coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀ = R (Z ω) := by
    filter_upwards [hW] with ω hω
    exact coneScale_eq_exp_lastLevel γ b₀ hω
  have ehb : (fun ω => coneRescaleField γ (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀) b₀
      (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) =ᵐ[P] fun ω => Hb (Z ω) := by
    filter_upwards [hW, hli] with ω hω hl
    rw [coneScale_eq_exp_lastLevel γ b₀ hω, coneFieldOf_eq_fieldOf γ (X ω) hω,
      coneRescaleField_fieldOf γ b₀ _ hl]
  have ehh : (fun ω => coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)) =ᵐ[P]
      fun ω => H (Z ω) := by
    filter_upwards [hW] with ω hω
    exact coneFieldOf_eq_fieldOf γ (X ω) hω
  -- the field law, the scaling law of η_L jointly with Z, and the independence
  have hlaw : P.map (fun ω => Hb (Z ω)) = P.map (fun ω => H (Z ω)) := by
    have h3 := (map_coneRescaleField_coneFieldOf hγ hγ2 h.gff hB hB' h.indep_cone b₀).2.2
    rwa [Measure.map_congr ehb, Measure.map_congr ehh] at h3
  have hD : Measurable fun ω => igDilate (R (Z ω)) (ηL ω) := by
    have hD' := measurable_igDilate_uncurry.comp ((hRm.comp hZm).prodMk hL)
    exact hD'
  have hmap := map_prod_comp_eq_of_indepFun hZm hD hL hHbm hHm
    (map_prod_igDilate_igCurve h hγ hγ2 hZm hLZ.symm hRm
      (Filter.Eventually.of_forall fun ω => Real.exp_pos _)) hLZ.symm hlaw
  calc P.map (fun ω =>
        (coneRescaleField γ (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀) b₀
          (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)),
        igDilate (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀) (ηL ω)))
      = P.map (fun ω => (Hb (Z ω), igDilate (R (Z ω)) (ηL ω))) := by
        refine Measure.map_congr ?_
        filter_upwards [ehb, ehR] with ω h1 h2
        exact Prod.ext h1 (congrArg (fun s => igDilate s (ηL ω)) h2)
    _ = P.map (fun ω => (H (Z ω), ηL ω)) := hmap
    _ = P.map (fun ω => (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω), ηL ω)) := by
        refine Measure.map_congr ?_
        filter_upwards [ehh] with ω hω
        exact Prod.ext hω.symm rfl

end MatedCRT.Sec1
