import MatedCRT.FirstPass.Derived.RadialReadoutTwoSided
import MatedCRT.FirstPass.Derived.ConeRadialIntegrable
import MatedCRT.FirstPass.Derived.GFFRadialTwoSided
import MatedCRT.FirstPass.LPBridge.GFFRadialLateralIndep
import MatedCRT.FirstPass.LPBridge.LateralProcessAEMeasurable
import MatedCRT.Proofs.Sec1.ConeScaleRadius

/-!
# Finite-dimensional laws of the whole-plane field coupled to a quantum cone

Let `(hC, hcirc)` be a `γ`-quantum cone under `P` and let `w` be an independent standard Brownian motion. The coupled
field `(coneCouplingPairing γ hC hcirc w, coneGFFCircle γ hcirc w)` on `Ω × ContinuousPath ℝ` (law `P ⊗ BM`) keeps
the lateral part of the cone and has the two-sided radial path `(t ↦ h_{e^{-t}}(0) - γ t, s ↦ h_1(0) + w(s) - w(0))`.
For every finite family `S` of admissible observables, its joint law is the joint law of the same observables of a
whole-plane GFF: on both sides the observables are a.s. the read-out `readOut2 S` of (the lateral observables in `S`,
the two radial paths at rational times), and these have the same law `(lateral law) ⊗ BM ⊗ BM` (independence of the
radial and lateral parts, the radial law of the cone, the two-sided radial law of the whole-plane GFF).

* `readOut2`, `map_eq_map_readOut2`: the common read-out and the law of an a.s. read-out.
* `ae_cone_circle_one_zero`: `h_1(0) = 0` a.s. for a quantum cone.
* `map_coneLatRad`, `map_gffLatRad`: the joint laws of the lateral observables and the radial paths.
* `ae_eval_coneGFF_eq_readOut2`: the a.s. read-out of the coupled field.
* `map_finset_coneGFF_eq`: equality of the finite-dimensional laws.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

open MatedCRT.ConeMeanZeroRestriction MatedCRT.ConeWholePlaneFieldLaw

section Readout

/-- The common read-out on a finite family `S` of admissible observables: lateral value plus radial read-out. -/
noncomputable def readOut2 (S : Finset GFFObservable.Admissible) :
    (S → ℝ) × ((ℚ≥0 → ℝ) × (ℚ≥0 → ℝ)) → (S → ℝ) :=
  fun p i => p.1 i + radOf2 p.2 i.1.1

theorem measurable_readOut2 (S : Finset GFFObservable.Admissible) : Measurable (readOut2 S) :=
  Measurable.of_eval fun i => ((measurable_pi_apply i).comp measurable_fst).add
    ((measurable_radOf2 i.1.2).comp measurable_snd)

/-- Law of an a.s. read-out. -/
theorem map_eq_map_readOut2 {α : Type*} [MeasurableSpace α] {μ : Measure α} (S : Finset GFFObservable.Admissible)
    {F : α → (S → ℝ)} {X : α → (S → ℝ) × ((ℚ≥0 → ℝ) × (ℚ≥0 → ℝ))}
    (hF : ∀ᵐ a ∂μ, F a = readOut2 S (X a)) (hX : AEMeasurable X μ) :
    μ.map F = (μ.map X).map (readOut2 S) := by
  rw [Measure.map_congr hF]
  exact (AEMeasurable.map_map_of_aemeasurable (measurable_readOut2 S).aemeasurable hX).symm

/-- The lateral observables in `S` of a sample family. -/
noncomputable def latS {Ω : Type} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (S : Finset GFFObservable.Admissible) (ω : Ω) : S → ℝ :=
  fun i => lateralProcess (hC ω) (hcirc ω) i.1

theorem measurable_projS (S : Finset GFFObservable.Admissible) :
    Measurable (fun g : GFFObservable.Admissible → ℝ => fun i : S => g i.1) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- A path on `ℝ≥0` read at the rational times. -/
def ratPath (f : ℝ≥0 → ℝ) : ℚ≥0 → ℝ := fun q => f (q : ℝ≥0)

theorem measurable_ratPath : Measurable ratPath :=
  Measurable.of_eval fun _ => measurable_pi_apply _

theorem radRat2_eq_map_ratPath (hcirc : ℝ → ℂ → ℝ) :
    radRat2 hcirc = Prod.map ratPath ratPath (radialProcess hcirc) := rfl

theorem map_brownianPathLaw_ratPath : brownianPathLaw.map ratPath = bmRat := by
  have h1 : Measurable (fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t) :=
    Measurable.of_eval fun t => ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t
  show ((brownianMotion 0).map fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t).map ratPath = bmRat
  rw [Measure.map_map measurable_ratPath h1]
  rfl

end Readout

section Cone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- For a quantum cone, `h_1(0) = 0` almost surely. -/
theorem ae_cone_circle_one_zero [IsProbabilityMeasure P] (hQ : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, hcirc ω 1 0 = 0 := by
  have hB : Measurable (fun ω => driftRat γ (radRat (hcirc ω))) :=
    Measurable.of_eval fun q => (hQ.measurable_circle _ _ (Real.exp_pos _)).sub measurable_const
  have hs : MeasurableSet {f : ℚ≥0 → ℝ | f 0 = 0} :=
    measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  have h0 : ∀ᵐ f ∂(P.map (fun ω => driftRat γ (radRat (hcirc ω)))), f 0 = 0 := by
    rw [cone_radial_BM hQ, ae_map_iff measurable_restrictRat.aemeasurable hs]
    filter_upwards [MatedCRT.Sec1.brownianMotion_ae_eval_zero] with w hw
    simpa using hw
  filter_upwards [(ae_map_iff hB.aemeasurable hs).1 h0] with ω hω
  simpa [driftRat, radRat, radialProcess] using hω

/-- The lateral observables in `S` of the cone and the two radial paths at rational times (the cone radial path
minus its drift, and the Brownian path), on the product space. -/
noncomputable def coneLatRad (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (S : Finset GFFObservable.Admissible) (p : Ω × ContinuousPath ℝ) :
    (S → ℝ) × ((ℚ≥0 → ℝ) × (ℚ≥0 → ℝ)) :=
  (latS hC hcirc S p.1, (driftRat γ (radRat (hcirc p.1)), fun q : ℚ≥0 => p.2 (q : ℝ≥0)))

theorem aemeasurable_latS_cone [IsProbabilityMeasure P] (hQ : IsQuantumCone γ P hC hcirc)
    (S : Finset GFFObservable.Admissible) : AEMeasurable (latS hC hcirc S) P :=
  (measurable_projS S).comp_aemeasurable (lateralProcessAEMeasurable_holds.1 γ Ω P hC hcirc inferInstance hQ)

/-- The joint law of the lateral observables of the cone and the two radial paths: `(lateral law) ⊗ BM ⊗ BM`. -/
theorem map_coneLatRad [IsProbabilityMeasure P] (hQ : IsQuantumCone γ P hC hcirc)
    (S : Finset GFFObservable.Admissible) :
    (P.prod (brownianMotion 0)).map (coneLatRad γ hC hcirc S) =
      (P.map (latS hC hcirc S)).prod (bmRat.prod bmRat) := by
  have hL := aemeasurable_latS_cone hQ S
  have hB : Measurable (fun ω => driftRat γ (radRat (hcirc ω))) :=
    Measurable.of_eval fun q => (hQ.measurable_circle _ _ (Real.exp_pos _)).sub measurable_const
  have hind : IndepFun (latS hC hcirc S) (fun ω => driftRat γ (radRat (hcirc ω))) P := by
    have hg : Measurable (fun r : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => fun q : ℚ≥0 => r.1 (q : ℝ≥0) - γ * (q : ℝ)) :=
      Measurable.of_eval fun q => ((measurable_pi_apply _).comp measurable_fst).sub measurable_const
    exact (hQ.indep.comp hg (measurable_projS S)).symm
  have hX : AEMeasurable (fun ω => (latS hC hcirc S ω, driftRat γ (radRat (hcirc ω)))) P :=
    hL.prodMk hB.aemeasurable
  have hPX : P.map (fun ω => (latS hC hcirc S ω, driftRat γ (radRat (hcirc ω)))) =
      (P.map (latS hC hcirc S)).prod bmRat := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hL hB.aemeasurable).1 hind, cone_radial_BM hQ]
  have hr := measurable_restrictRat
  have hY : coneLatRad γ hC hcirc S = fun p => MeasurableEquiv.prodAssoc
      (Prod.map (fun ω => (latS hC hcirc S ω, driftRat γ (radRat (hcirc ω))))
        (fun (w : ContinuousPath ℝ) (q : ℚ≥0) => w (q : ℝ≥0)) p) := rfl
  have hae : ∀ᵐ p ∂(P.prod (brownianMotion 0)),
      (latS hC hcirc S p.1, driftRat γ (radRat (hcirc p.1))) = hX.mk _ p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hX.ae_eq_mk
  calc (P.prod (brownianMotion 0)).map (coneLatRad γ hC hcirc S)
      = (P.prod (brownianMotion 0)).map (fun p => MeasurableEquiv.prodAssoc
          (Prod.map (hX.mk _) (fun (w : ContinuousPath ℝ) (q : ℚ≥0) => w (q : ℝ≥0)) p)) := by
        rw [hY]
        apply Measure.map_congr
        filter_upwards [hae] with p hp
        change MeasurableEquiv.prodAssoc ((latS hC hcirc S p.1, driftRat γ (radRat (hcirc p.1))), _) =
          MeasurableEquiv.prodAssoc (hX.mk _ p.1, _)
        rw [hp]
    _ = ((P.prod (brownianMotion 0)).map
          (Prod.map (hX.mk _) (fun (w : ContinuousPath ℝ) (q : ℚ≥0) => w (q : ℝ≥0)))).map
          MeasurableEquiv.prodAssoc := by
        rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable (hX.measurable_mk.prodMap hr)]
        rfl
    _ = ((P.map (hX.mk _)).prod bmRat).map MeasurableEquiv.prodAssoc := by
        rw [← Measure.map_prod_map _ _ hX.measurable_mk hr]
    _ = (((P.map (latS hC hcirc S)).prod bmRat).prod bmRat).map MeasurableEquiv.prodAssoc := by
        rw [← Measure.map_congr hX.ae_eq_mk, hPX]
    _ = (P.map (latS hC hcirc S)).prod (bmRat.prod bmRat) := Measure.prodAssoc_prod

/-- **A.s. read-out of the coupled field.** -/
theorem ae_eval_coneGFF_eq_readOut2 [IsProbabilityMeasure P] (hQ : IsQuantumCone γ P hC hcirc)
    (S : Finset GFFObservable.Admissible) :
    ∀ᵐ p ∂(P.prod (brownianMotion 0)),
      (fun i : S => i.1.1.eval (coneCouplingPairing γ (hC p.1) (hcirc p.1) (fun t => p.2 t))
        (coneGFFCircle γ (hcirc p.1) (fun t => p.2 t))) = readOut2 S (coneLatRad γ hC hcirc S p) := by
  have hlat : ∀ᵐ ω ∂P, ∀ i : S, ∀ w : ℝ≥0 → ℝ, Continuous w →
      lateralProcess (coneCouplingPairing γ (hC ω) (hcirc ω) w) (coneGFFCircle γ (hcirc ω) w) i.1 =
        lateralProcess (hC ω) (hcirc ω) i.1 :=
    ae_all_iff.2 fun i => ae_lateralProcess_coneGFF_apply hQ i.1
  have hA : ∀ᵐ ω ∂P, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi 0 ×ˢ univ) ∧
      hcirc ω 1 0 = 0 ∧ ∀ i : S, ∀ w : ℝ≥0 → ℝ, Continuous w →
        lateralProcess (coneCouplingPairing γ (hC ω) (hcirc ω) w) (coneGFFCircle γ (hcirc ω) w) i.1 =
          lateralProcess (hC ω) (hcirc ω) i.1 := by
    filter_upwards [hQ.ae_continuousOn_circle, ae_cone_circle_one_zero hQ, hlat] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hA' := Measure.quasiMeasurePreserving_fst (μ := P) (ν := brownianMotion 0) |>.ae hA
  have hB' : ∀ᵐ p ∂(P.prod (brownianMotion 0)), p.2 0 = 0 :=
    Measure.quasiMeasurePreserving_snd.ae MatedCRT.Sec1.brownianMotion_ae_eval_zero
  filter_upwards [hA', hB'] with p hp h0
  obtain ⟨hc, h1, hl⟩ := hp
  funext i
  have hw : Continuous (fun t : ℝ≥0 => p.2 t) := p.2.continuous
  rw [eval_coneGFF_eq_lateralProcess_add_radOf2 γ (hC p.1) hc hw i.1, hl i _ hw]
  simp only [readOut2, coneLatRad, latS, h1, h0, zero_add, sub_zero]

end Cone

section GFF

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

theorem aemeasurable_latS_gff [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc)
    (S : Finset GFFObservable.Admissible) : AEMeasurable (latS hC hcirc S) P :=
  (measurable_projS S).comp_aemeasurable (lateralProcessAEMeasurable_holds.2 Ω P hC hcirc inferInstance hh)

/-- The joint law of the lateral observables of a whole-plane GFF and its two radial paths at rational times:
`(lateral law) ⊗ BM ⊗ BM`. -/
theorem map_gffLatRad [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc)
    (S : Finset GFFObservable.Admissible) :
    P.map (fun ω => (latS hC hcirc S ω, radRat2 (hcirc ω))) =
      (P.map (latS hC hcirc S)).prod (bmRat.prod bmRat) := by
  have hL := aemeasurable_latS_gff hh S
  have hR : Measurable (fun ω => radRat2 (hcirc ω)) := measurable_radRat2 hh.measurable_circle
  have hrad : Measurable (fun ω => radialProcess (hcirc ω)) :=
    (Measurable.of_eval fun _ => hh.measurable_circle _ _ (Real.exp_pos _)).prodMk
      (Measurable.of_eval fun _ => hh.measurable_circle _ _ (Real.exp_pos _))
  have hrp : Measurable (Prod.map ratPath ratPath) := measurable_ratPath.prodMap measurable_ratPath
  have hind : IndepFun (latS hC hcirc S) (fun ω => radRat2 (hcirc ω)) P :=
    ((gffRadialLateralIndep_holds Ω P hC hcirc inferInstance hh).comp hrp (measurable_projS S)).symm
  rw [(indepFun_iff_map_prod_eq_prod_map_map hL hR.aemeasurable).1 hind]
  congr 1
  calc P.map (fun ω => radRat2 (hcirc ω))
      = (P.map (fun ω => radialProcess (hcirc ω))).map (Prod.map ratPath ratPath) :=
        (Measure.map_map hrp hrad).symm
    _ = (brownianPathLaw.prod brownianPathLaw).map (Prod.map ratPath ratPath) := by
        rw [map_radialProcess_eq_brownian_prod hh]
    _ = bmRat.prod bmRat := by
        rw [← Measure.map_prod_map _ _ measurable_ratPath measurable_ratPath, map_brownianPathLaw_ratPath]

end GFF

/-- **Finite-dimensional laws of the coupled field.** For a `γ`-quantum cone `(hC, hcirc)` under `P`, an independent
standard Brownian motion `w`, and any whole-plane GFF `(hC', hcirc')`, every finite family `S` of admissible observables
has the same joint law under the coupled field `(coneCouplingPairing γ hC hcirc w, coneGFFCircle γ hcirc w)`
(law `P ⊗ BM`) as under the whole-plane GFF. -/
theorem map_finset_coneGFF_eq {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hQ : IsQuantumCone γ P hC hcirc)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P' hC' hcirc')
    (S : Finset GFFObservable.Admissible) :
    (P.prod (brownianMotion 0)).map (fun p (i : S) => i.1.1.eval
        (coneCouplingPairing γ (hC p.1) (hcirc p.1) (fun t => p.2 t)) (coneGFFCircle γ (hcirc p.1) (fun t => p.2 t))) =
      P'.map (fun ω (i : S) => i.1.1.eval (hC' ω) (hcirc' ω)) := by
  have hLatC := lateralProcessAEMeasurable_holds.1 γ Ω P hC hcirc inferInstance hQ
  have hLatG := lateralProcessAEMeasurable_holds.2 Ω' P' hC' hcirc' inferInstance hh
  have hlat : P.map (latS hC hcirc S) = P'.map (latS hC' hcirc' S) := by
    obtain ⟨Ω'', _, P'', hC'', hcirc'', hP'', hgff'', heq⟩ := hQ.lateral_law
    have hl := heq.trans (MatedCRT.Sec1.IsWholePlaneGFF.lateral_law_eq hgff'' hh)
    have e1 := AEMeasurable.map_map_of_aemeasurable (measurable_projS S).aemeasurable hLatC
    have e2 := AEMeasurable.map_map_of_aemeasurable (measurable_projS S).aemeasurable hLatG
    rw [hl] at e1
    exact e1.symm.trans e2
  have hYc : AEMeasurable (coneLatRad γ hC hcirc S) (P.prod (brownianMotion 0)) := by
    have hB : Measurable (fun ω => driftRat γ (radRat (hcirc ω))) :=
      Measurable.of_eval fun q => (hQ.measurable_circle _ _ (Real.exp_pos _)).sub measurable_const
    exact ((aemeasurable_latS_cone hQ S).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
      ((hB.comp measurable_fst).prodMk (measurable_restrictRat.comp measurable_snd)).aemeasurable
  have hYg : AEMeasurable (fun ω => (latS hC' hcirc' S ω, radRat2 (hcirc' ω))) P' :=
    (aemeasurable_latS_gff hh S).prodMk (measurable_radRat2 hh.measurable_circle).aemeasurable
  have hFg : ∀ᵐ ω ∂P', (fun i : S => i.1.1.eval (hC' ω) (hcirc' ω)) =
      readOut2 S (latS hC' hcirc' S ω, radRat2 (hcirc' ω)) := by
    filter_upwards [hh.ae_continuousOn_circle] with ω hc
    funext i
    exact eval_eq_lateralProcess_add_radOf2 (hC' ω) hc i.1
  rw [map_eq_map_readOut2 S (ae_eval_coneGFF_eq_readOut2 hQ S) hYc, map_eq_map_readOut2 S hFg hYg,
    map_coneLatRad hQ S, map_gffLatRad hh S, hlat]

end MatedCRT.FirstPass.Derived
