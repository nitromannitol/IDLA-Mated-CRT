import MatedCRT.FirstPass.Derived.ConeReferenceLateral
import MatedCRT.FirstPass.LPBridge.GFFRadialLateralIndep
import MatedCRT.Proofs.Measurability.ConePairing
import LatticeProb.Prob.LawAEEqualCoordinates

/-!
# Independence and lateral law of the quantum cone built from a whole-plane GFF and a path

Let `(hC₁, c₁)` be the pairings and circle averages of a whole-plane GFF `h^ℂ` on a probability space `Ω₁`, with
circle averages continuous on `(0, ∞) × ℂ` at every sample and jointly measurable, and `ν` a law of the conditioned
Brownian motion. For the cone data `(coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2, coneRefCircle γ (c₁ p.1) p.2)` on
`Ω₁ × C(ℝ≥0, ℝ)` under `P₁ ⊗ ν`:

* `measurable_lateralProcess_of_continuous`: the lateral process is a random variable (product σ-algebra) when the
  circle averages are continuous at every sample;
* `lateralProcess_coneRef_law`: the lateral process of the cone has the law of the lateral process of `h^ℂ`;
* `indepFun_coneRef`: the radial process of the cone is independent of its lateral process.

The lateral coordinates of the cone data agree almost surely with those of `h^ℂ` (`ae_lateralProcess_coneRef_apply`),
and the radial process of the cone is almost surely `(h^ℂ_{e^{-t}}(0) + γ t, w(s) - w(0) - γ s)`, a function of the
inner radial path of `h^ℂ` and of the path `w`; the independence is then that of the radial and lateral parts of
`h^ℂ` (`gffRadialLateralIndep_holds`) and of `w`, transferred along the laws of processes with almost surely equal
coordinates.
-/

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- The lateral process is a random variable (product σ-algebra on the admissible observables) when the pairings and
circle averages are random variables and the circle average process is continuous at every sample. -/
theorem measurable_lateralProcess_of_continuous {Ω : Type*} [MeasurableSpace Ω]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hmp : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) :
    Measurable fun ω => lateralProcess (hC ω) (hcirc ω) := by
  have h := MatedCRT.CirclePairing.measurable_lateralVersion hmp hmc
  have : (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      fun ω (o : GFFObservable.Admissible) => MatedCRT.CirclePairing.lateralVersionEval hC hcirc ω o.1 :=
    funext fun ω => (MatedCRT.CirclePairing.lateralVersion_eq
      (MatedCRT.CirclePairing.continuousOn_radial (hcont ω))).symm
  rw [this]
  exact h

section Cone

variable {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁} {hC₁ : Ω₁ → (ℂ → ℝ) → ℝ}
  {c₁ : Ω₁ → ℝ → ℂ → ℝ}

/-- The lateral process of the cone data is a random variable on `Ω₁ × C(ℝ≥0, ℝ)`. -/
theorem measurable_lateralProcess_coneRef (hh : IsWholePlaneGFF P₁ hC₁ c₁) (γ : ℝ)
    (hcont : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c₁ ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable fun q : (Ioi (0 : ℝ) × ℂ) × Ω₁ => c₁ q.2 q.1.1 q.1.2) :
    Measurable fun p : Ω₁ × ContinuousPath ℝ =>
      lateralProcess (coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2) (coneRefCircle γ (c₁ p.1) p.2) :=
  measurable_lateralProcess_of_continuous (hC := fun p : Ω₁ × ContinuousPath ℝ =>
      coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2) (hcirc := fun p => coneRefCircle γ (c₁ p.1) p.2)
    (fun _ hφ => measurable_coneRefPairing γ hmeas hh.measurable_pairing hφ)
    (fun _ z hr => measurable_coneRefCircle γ hmeas hr z)
    (fun p => continuousOn_coneRefCircle γ (hcont p.1) p.2)

/-- The lateral coordinates of the cone data agree almost surely with those of the field: for every admissible
observable, `P₁ ⊗ ν`-almost surely. -/
theorem ae_prod_lateralProcess_coneRef_apply (hh : IsWholePlaneGFF P₁ hC₁ c₁) (γ : ℝ)
    (ν : Measure (ContinuousPath ℝ)) [SFinite ν] (o : GFFObservable.Admissible) :
    ∀ᵐ p ∂(P₁.prod ν),
      lateralProcess (coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2) (coneRefCircle γ (c₁ p.1) p.2) o =
        lateralProcess (hC₁ p.1) (c₁ p.1) o := by
  have h := Measure.QuasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_fst (μ := P₁) (ν := ν)) (ae_lateralProcess_coneRef_apply hh γ o)
  filter_upwards [h] with p hp
  exact hp p.2

/-- Under `P₁ ⊗ ν`, the lateral process of the cone data has the same law as the lateral process of the field
composed with the first projection (the lateral coordinates agree almost surely). -/
theorem map_lateralProcess_coneRef_eq_fst (hh : IsWholePlaneGFF P₁ hC₁ c₁) (γ : ℝ)
    (hcont : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c₁ ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable fun q : (Ioi (0 : ℝ) × ℂ) × Ω₁ => c₁ q.2 q.1.1 q.1.2)
    (ν : Measure (ContinuousPath ℝ)) [IsProbabilityMeasure P₁] [IsProbabilityMeasure ν] :
    (P₁.prod ν).map (fun p : Ω₁ × ContinuousPath ℝ =>
        lateralProcess (coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2) (coneRefCircle γ (c₁ p.1) p.2)) =
      (P₁.prod ν).map (fun p : Ω₁ × ContinuousPath ℝ => lateralProcess (hC₁ p.1) (c₁ p.1)) := by
  have hLat := measurable_lateralProcess_coneRef hh γ hcont hmeas
  have hLat1 : Measurable fun ω => lateralProcess (hC₁ ω) (c₁ ω) :=
    measurable_lateralProcess_of_continuous hh.measurable_pairing hh.measurable_circle hcont
  exact LatticeProb.map_eq_of_ae_eq_apply (μ := P₁.prod ν)
    (Y := fun p : Ω₁ × ContinuousPath ℝ =>
      lateralProcess (coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2) (coneRefCircle γ (c₁ p.1) p.2))
    (Y' := fun p => lateralProcess (hC₁ p.1) (c₁ p.1))
    (fun o => (measurable_pi_apply o).comp hLat)
    (fun o => (measurable_pi_apply o).comp (hLat1.comp measurable_fst))
    (fun o => ae_prod_lateralProcess_coneRef_apply hh γ ν o)

/-- **The lateral law of the cone data.** Under `P₁ ⊗ ν`, the lateral process of the cone data has the law of the
lateral process of the whole-plane GFF `h^ℂ`. -/
theorem lateralProcess_coneRef_law [IsProbabilityMeasure P₁] (hh : IsWholePlaneGFF P₁ hC₁ c₁) (γ : ℝ)
    (hcont : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c₁ ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable fun q : (Ioi (0 : ℝ) × ℂ) × Ω₁ => c₁ q.2 q.1.1 q.1.2)
    {ν : Measure (ContinuousPath ℝ)} [IsProbabilityMeasure ν] :
    (P₁.prod ν).map (fun p : Ω₁ × ContinuousPath ℝ =>
        lateralProcess (coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2) (coneRefCircle γ (c₁ p.1) p.2)) =
      P₁.map (fun ω => lateralProcess (hC₁ ω) (c₁ ω)) := by
  have hLat1 : Measurable fun ω => lateralProcess (hC₁ ω) (c₁ ω) :=
    measurable_lateralProcess_of_continuous hh.measurable_pairing hh.measurable_circle hcont
  have hc : (fun p : Ω₁ × ContinuousPath ℝ => lateralProcess (hC₁ p.1) (c₁ p.1)) =
      (fun ω => lateralProcess (hC₁ ω) (c₁ ω)) ∘ Prod.fst := rfl
  rw [map_lateralProcess_coneRef_eq_fst hh γ hcont hmeas ν, hc,
    ← Measure.map_map hLat1 measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

/-- The radial process of the cone data is almost surely a function of the inner radial path of the field and of the
path `w`. -/
theorem ae_radialProcess_coneRef_eq [IsProbabilityMeasure P₁] (hh : IsWholePlaneGFF P₁ hC₁ c₁) (γ : ℝ)
    {c : ℝ} {ν : Measure (ContinuousPath ℝ)} (hν : IsBMConditionedPositive c ν) :
    ∀ᵐ p ∂(P₁.prod ν), radialProcess (coneRefCircle γ (c₁ p.1) p.2) =
      ((fun t : ℝ≥0 => c₁ p.1 (Real.exp (-(t : ℝ))) 0 + γ * t), (fun s : ℝ≥0 => p.2 s - γ * s)) := by
  have := hν.1
  have h1 : ∀ᵐ p ∂(P₁.prod ν), c₁ p.1 1 0 = 0 :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hh.ae_circleAverage_one_zero
  have h2 : ∀ᵐ p ∂(P₁.prod ν), p.2 0 = 0 :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd
      (isBMConditionedPositive_ae_eval_zero hν)
  filter_upwards [h1, h2] with p h1 h2
  rw [radialProcess_coneRefCircle]
  refine Prod.ext rfl (funext fun s => ?_)
  simp only [coneRefRadial, h1, h2, sub_zero, add_zero]

/-- **Independence of the radial and lateral parts of the cone data.** Under `P₁ ⊗ ν`, the radial process of the
cone data is independent of its lateral process. -/
theorem indepFun_coneRef [IsProbabilityMeasure P₁] (hh : IsWholePlaneGFF P₁ hC₁ c₁) (γ : ℝ)
    (hcont : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c₁ ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable fun q : (Ioi (0 : ℝ) × ℂ) × Ω₁ => c₁ q.2 q.1.1 q.1.2)
    {c : ℝ} {ν : Measure (ContinuousPath ℝ)} (hν : IsBMConditionedPositive c ν) :
    IndepFun (fun p : Ω₁ × ContinuousPath ℝ => radialProcess (coneRefCircle γ (c₁ p.1) p.2))
      (fun p => lateralProcess (coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2) (coneRefCircle γ (c₁ p.1) p.2))
      (P₁.prod ν) := by
  have := hν.1
  set μ := P₁.prod ν with hμ
  have hLat := measurable_lateralProcess_coneRef hh γ hcont hmeas
  have hLat1 : Measurable fun ω => lateralProcess (hC₁ ω) (c₁ ω) :=
    measurable_lateralProcess_of_continuous hh.measurable_pairing hh.measurable_circle hcont
  set Φ : Ω₁ → (ℝ≥0 → ℝ) := fun ω t => c₁ ω (Real.exp (-(t : ℝ))) 0 + γ * t with hΦdef
  set Ψ : ContinuousPath ℝ → (ℝ≥0 → ℝ) := fun w s => w s - γ * s with hΨdef
  have hG : Measurable fun (r : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) (t : ℝ≥0) => r.1 t + γ * t :=
    Measurable.of_eval fun t => ((measurable_pi_apply t).comp measurable_fst).add_const _
  have hΦ : Measurable Φ :=
    Measurable.of_eval fun t => (hh.measurable_circle _ 0 (Real.exp_pos _)).add_const _
  have hΨ : Measurable Ψ :=
    Measurable.of_eval fun s => (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) s).sub_const _
  have hI : IndepFun (fun ω => radialProcess (c₁ ω)) (fun ω => lateralProcess (hC₁ ω) (c₁ ω)) P₁ :=
    MatedCRT.ConeMeanZeroRestriction.gffRadialLateralIndep_holds Ω₁ P₁ hC₁ c₁ ‹_› hh
  have hXL : IndepFun Φ (fun ω => lateralProcess (hC₁ ω) (c₁ ω)) P₁ := hI.comp hG measurable_id
  have hX2 : IndepFun (fun p : Ω₁ × ContinuousPath ℝ => (Φ p.1, Ψ p.2))
      (fun p => lateralProcess (hC₁ p.1) (c₁ p.1)) μ :=
    LatticeProb.indepFun_prodMk_snd_of_indepFun hΦ hLat1 hΨ hXL
  have hR' : Measurable fun p : Ω₁ × ContinuousPath ℝ => (Φ p.1, Ψ p.2) :=
    (hΦ.comp measurable_fst).prodMk (hΨ.comp measurable_snd)
  have hL1 : Measurable fun p : Ω₁ × ContinuousPath ℝ => lateralProcess (hC₁ p.1) (c₁ p.1) :=
    hLat1.comp measurable_fst
  have h2 := LatticeProb.map_prodMk_eq_of_ae_eq_apply (μ := μ) hR'
    (Y := fun p : Ω₁ × ContinuousPath ℝ =>
      lateralProcess (coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2) (coneRefCircle γ (c₁ p.1) p.2))
    (Y' := fun p => lateralProcess (hC₁ p.1) (c₁ p.1))
    (fun o => (measurable_pi_apply o).comp hLat) (fun o => (measurable_pi_apply o).comp hL1)
    (fun o => ae_prod_lateralProcess_coneRef_apply hh γ ν o)
  have h3 := map_lateralProcess_coneRef_eq_fst hh γ hcont hmeas ν
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hR'.aemeasurable hL1.aemeasurable).1 hX2
  have hprod : μ.map (fun p : Ω₁ × ContinuousPath ℝ => ((Φ p.1, Ψ p.2),
      lateralProcess (coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2) (coneRefCircle γ (c₁ p.1) p.2))) =
      (μ.map fun p : Ω₁ × ContinuousPath ℝ => (Φ p.1, Ψ p.2)).prod (μ.map fun p : Ω₁ × ContinuousPath ℝ =>
        lateralProcess (coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2) (coneRefCircle γ (c₁ p.1) p.2)) := by
    rw [h2, hlaw, h3]
  have hind := (indepFun_iff_map_prod_eq_prod_map_map hR'.aemeasurable hLat.aemeasurable).2 hprod
  have hae : (fun p : Ω₁ × ContinuousPath ℝ => (Φ p.1, Ψ p.2)) =ᵐ[μ]
      fun p => radialProcess (coneRefCircle γ (c₁ p.1) p.2) :=
    (ae_radialProcess_coneRef_eq hh γ hν).mono fun p hp => hp.symm
  exact hind.congr hae Filter.EventuallyEq.rfl

end Cone

end MatedCRT.FirstPass.Derived
