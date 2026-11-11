import MatedCRT.Proofs.Sec1.EnvironmentScaling.DistributionCode
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import HarmonicBalls.Proofs.Sec8.WholePlaneObservableLaw

/-!
# Rescaled field pairings

The coding and simultaneous representation give
an exactly field-measurable distribution.  Joint measurability of its evaluation at a dilated test is required;
it is proved below.  The observable-law bridge uses Leonardo Bonanno’s LatticeProb field results via
`HarmonicBalls.Proofs.Sec8.WholePlaneObservableLaw`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Distributions Topology
open HarmonicBalls

namespace MatedCRT.Sec1

/-- The weak-limit convention for conditioned Brownian motion determines at
most one law on continuous paths. -/
theorem isBMConditionedPositive_unique {c : ℝ}
    {μ ν : Measure (MarkovProcess.ContinuousPath ℝ)}
    (hμ : IsBMConditionedPositive c μ) (hν : IsBMConditionedPositive c ν) : μ = ν := by
  let : IsProbabilityMeasure μ := hμ.1
  let : IsProbabilityMeasure ν := hν.1
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact tendsto_nhds_unique (hμ.2 f) (hν.2 f)

/-- The radial law in the cone predicate is independent of the choice of
witness for the conditioned Brownian law. -/
theorem IsQuantumCone.radial_law_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {γ : ℝ} {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {a : Ω → ℝ → ℂ → ℝ} {a' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC a) (h' : IsQuantumCone γ P' hC' a') :
    P.map (fun ω => radialProcess (a ω)) = P'.map (fun ω => radialProcess (a' ω)) := by
  obtain ⟨μ, hμ, hμlaw⟩ := h.radial_law
  obtain ⟨ν, hν, hνlaw⟩ := h'.radial_law
  rw [hμlaw, hνlaw, isBMConditionedPositive_unique hμ hν]

/-- The radial process of a cone is measurable in the product sigma algebra. -/
theorem IsQuantumCone.measurable_radialProcess
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {a : Ω → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC a) : Measurable (fun ω => radialProcess (a ω)) := by
  exact (measurable_pi_iff.2 fun t => h.measurable_circle _ _ (Real.exp_pos _)).prodMk
    (measurable_pi_iff.2 fun t => h.measurable_circle _ _ (Real.exp_pos _))

/-- If the lateral laws agree, the independent radial and lateral processes
of two cones with the same parameter have the same joint law. -/
theorem IsQuantumCone.joint_radial_lateral_law_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {γ : ℝ} {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {a : Ω → ℝ → ℂ → ℝ} {a' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC a) (h' : IsQuantumCone γ P' hC' a')
    (hlat : P.map (fun ω => lateralProcess (hC ω) (a ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (a' ω))) :
    P.map (fun ω => (radialProcess (a ω), lateralProcess (hC ω) (a ω))) =
      P'.map (fun ω => (radialProcess (a' ω), lateralProcess (hC' ω) (a' ω))) := by
  have hl := CirclePairing.aemeasurable_lateralProcess h.measurable_pairing
    h.measurable_circle h.ae_continuousOn_circle
  have hl' := CirclePairing.aemeasurable_lateralProcess h'.measurable_pairing
    h'.measurable_circle h'.ae_continuousOn_circle
  rw [h.indep.map_prod_eq_prod_map_map (IsQuantumCone.measurable_radialProcess h).aemeasurable hl,
    h'.indep.map_prod_eq_prod_map_map (IsQuantumCone.measurable_radialProcess h').aemeasurable hl',
    IsQuantumCone.radial_law_eq h h', hlat]

/-- Decode admissible pairings from the product of observable coordinates. -/
private def observablePairing (v : GFFObservable.Admissible → ℝ) (φ : ℂ → ℝ) : ℝ := by
  classical
  exact if h : IsTestFunction univ φ then v ⟨.pairing φ, h⟩ else 0

/-- Decode positive-radius circle averages from observable coordinates. -/
private def observableCircle (v : GFFObservable.Admissible → ℝ) (r : ℝ) (z : ℂ) : ℝ :=
  if h : 0 < r then v ⟨.circle r z, h⟩ else 0

/-- Universal measurable lateral projection of the whole-plane observables. -/
private def observableLateral (v : GFFObservable.Admissible → ℝ) : GFFObservable.Admissible → ℝ :=
  fun o => CirclePairing.lateralVersionEval observablePairing observableCircle v o.1

private theorem measurable_observableLateral : Measurable observableLateral := by
  apply CirclePairing.measurable_lateralVersion
  · intro φ hφ
    change Measurable (fun v : GFFObservable.Admissible → ℝ => observablePairing v φ)
    simp only [observablePairing, dite_eq_left hφ]
    exact measurable_pi_apply _
  · intro r z hr
    change Measurable (fun v : GFFObservable.Admissible → ℝ => observableCircle v r z)
    simp only [observableCircle, dite_eq_left hr]
    exact measurable_pi_apply _

private theorem observableLateral_apply {Ω : Type} [MeasurableSpace Ω]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) :
    observableLateral (wholePlaneObservableProc hC hcirc ω) =
      (fun o : GFFObservable.Admissible => CirclePairing.lateralVersionEval hC hcirc ω o.1) := by
  have hrad : ∀ s, CirclePairing.radialVersion observableCircle
      (wholePlaneObservableProc hC hcirc ω) s = CirclePairing.radialVersion hcirc ω s := by
    intro s
    unfold CirclePairing.radialVersion
    congr 1
    funext n
    by_cases hn : 0 < ⌈s * 2 ^ n⌉
    · have hp : 0 < CirclePairing.dyadicCeil n s :=
        div_pos (Int.cast_pos.2 hn) (by positivity)
      simp [CirclePairing.radialApprox, hn, observableCircle, hp, wholePlaneObservableProc,
        GFFObservable.eval]
    · simp [CirclePairing.radialApprox, hn]
  funext ⟨o, ho⟩
  cases o with
  | pairing φ =>
    have hφ : IsTestFunction univ φ := ho
    simp only [observableLateral, CirclePairing.lateralVersionEval, observablePairing, hφ,
      ↓reduceDIte, wholePlaneObservableProc, GFFObservable.eval, hrad]
  | circle r z =>
    have hr : 0 < r := ho
    simp only [observableLateral, CirclePairing.lateralVersionEval, observableCircle, hr,
      ↓reduceDIte, wholePlaneObservableProc, GFFObservable.eval, hrad]

/-- The lateral projection of the whole-plane GFF has a law determined by its
observable covariance specification, independently of the probability space. -/
theorem IsWholePlaneGFF.lateral_law_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {a : Ω → ℝ → ℂ → ℝ} {a' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC a) (h' : IsWholePlaneGFF P' hC' a') :
    P.map (fun ω => lateralProcess (hC ω) (a ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (a' ω)) := by
  have hrep : (observableLateral ∘ wholePlaneObservableProc hC a) =ᵐ[P]
      (fun ω => lateralProcess (hC ω) (a ω)) := by
    filter_upwards [h.ae_continuousOn_circle] with ω hω
    exact (observableLateral_apply hC a ω).trans
      (CirclePairing.lateralVersion_eq (CirclePairing.continuousOn_radial hω))
  have hrep' : (observableLateral ∘ wholePlaneObservableProc hC' a') =ᵐ[P']
      (fun ω => lateralProcess (hC' ω) (a' ω)) := by
    filter_upwards [h'.ae_continuousOn_circle] with ω hω
    exact (observableLateral_apply hC' a' ω).trans
      (CirclePairing.lateralVersion_eq (CirclePairing.continuousOn_radial hω))
  rw [← Measure.map_congr hrep, ← Measure.map_congr hrep',
    ← Measure.map_map measurable_observableLateral h.measurable_wholePlaneObservableProc,
    ← Measure.map_map measurable_observableLateral h'.measurable_wholePlaneObservableProc,
    h.map_wholePlaneObservableProc_eq h']

/-- The cone predicate determines the law of its lateral process. -/
theorem IsQuantumCone.lateral_law_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {γ : ℝ} {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {a : Ω → ℝ → ℂ → ℝ} {a' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC a) (h' : IsQuantumCone γ P' hC' a') :
    P.map (fun ω => lateralProcess (hC ω) (a ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (a' ω)) := by
  obtain ⟨Ω₁, m₁, P₁, c₁, a₁, _, g₁, l₁⟩ := h.lateral_law
  obtain ⟨Ω₂, m₂, P₂, c₂, a₂, _, g₂, l₂⟩ := h'.lateral_law
  let _ := m₁
  let _ := m₂
  exact l₁.trans ((IsWholePlaneGFF.lateral_law_eq g₁ g₂).trans l₂.symm)

/-- Two cones with the same parameter have the same joint radial and lateral law. -/
theorem IsQuantumCone.joint_radial_lateral_law_unique
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {γ : ℝ} {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {a : Ω → ℝ → ℂ → ℝ} {a' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC a) (h' : IsQuantumCone γ P' hC' a') :
    P.map (fun ω => (radialProcess (a ω), lateralProcess (hC ω) (a ω))) =
      P'.map (fun ω => (radialProcess (a' ω), lateralProcess (hC' ω) (a' ω))) :=
  IsQuantumCone.joint_radial_lateral_law_eq h h' (IsQuantumCone.lateral_law_eq h h')

/-- The two radial paths used in the cone definition. -/
private abbrev RadialData := (NNReal → ℝ) × (NNReal → ℝ)

/-- Recover centered radial circle values from the two logarithmic paths. -/
private def radialCircle (v : RadialData) (r : ℝ) (_z : ℂ) : ℝ :=
  if 1 ≤ r then v.2 (Real.toNNReal (Real.log r))
  else v.1 (Real.toNNReal (-Real.log r))

private theorem measurable_radialCircle (r : ℝ) (z : ℂ) :
    Measurable (fun v : RadialData => radialCircle v r z) := by
  by_cases hr : 1 ≤ r
  · simp only [radialCircle, hr, ↓reduceIte]
    exact (measurable_pi_apply _).comp measurable_snd
  · simp only [radialCircle, hr, ↓reduceIte]
    exact (measurable_pi_apply _).comp measurable_fst

private theorem radialCircle_radialProcess (a : ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    radialCircle (radialProcess a) r z = a r 0 := by
  by_cases h : 1 ≤ r
  · have hl := Real.log_nonneg h
    simp only [radialCircle, h, ↓reduceIte, radialProcess, Real.coe_toNNReal _ hl,
      Real.exp_log hr]
  · have hl : Real.log r ≤ 0 := Real.log_nonpos hr.le (le_of_not_ge h)
    simp only [radialCircle, h, ↓reduceIte, radialProcess, Real.coe_toNNReal _ (neg_nonneg.mpr hl),
      neg_neg, Real.exp_log hr]

private theorem radialVersion_radialProcess (a : ℝ → ℂ → ℝ) (s : ℝ) :
    CirclePairing.radialVersion radialCircle (radialProcess a) s =
      CirclePairing.radialVersion (fun _ : Unit => a) () s := by
  unfold CirclePairing.radialVersion
  congr 1
  funext n
  by_cases hn : 0 < ⌈s * 2 ^ n⌉
  · have hp : 0 < CirclePairing.dyadicCeil n s :=
      div_pos (Int.cast_pos.2 hn) (by positivity)
    simp [CirclePairing.radialApprox, hn, radialCircle_radialProcess a hp]
  · simp [CirclePairing.radialApprox, hn]

/-- Reconstruct admissible observables by adding the radial contribution to
lateral observables, using the measurable dyadic radial version. -/
private def radialLateralObservables (v : RadialData × (GFFObservable.Admissible → ℝ)) :
    GFFObservable.Admissible → ℝ := fun o =>
  match o.1 with
  | .pairing φ => v.2 o + ∫ x, φ x * CirclePairing.radialVersion radialCircle v.1 ‖x‖
  | .circle r z => v.2 o + Real.circleAverage
      (fun x => CirclePairing.radialVersion radialCircle v.1 ‖x‖) z r

private theorem measurable_radialLateralObservables : Measurable radialLateralObservables := by
  have hr := CirclePairing.measurable_radialVersion
    (fun r z _ => measurable_radialCircle r z)
  apply measurable_pi_iff.mpr
  rintro ⟨o, ho⟩
  cases o with
  | pairing φ =>
    have hf : StronglyMeasurable fun p : (RadialData × (GFFObservable.Admissible → ℝ)) × ℂ =>
        φ p.2 * CirclePairing.radialVersion radialCircle p.1.1 ‖p.2‖ :=
      ((ho.1.continuous.measurable.comp measurable_snd).mul
        (hr.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd.norm))).stronglyMeasurable
    exact ((measurable_pi_apply _).comp measurable_snd).add
      (hf.integral_prod_right' (ν := volume)).measurable
  | circle r z =>
    have e : (fun v : RadialData × (GFFObservable.Admissible → ℝ) =>
        Real.circleAverage (fun x => CirclePairing.radialVersion radialCircle v.1 ‖x‖) z r) =
        fun v => (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi),
          CirclePairing.radialVersion radialCircle v.1 ‖circleMap z r θ‖ := funext fun _ => by
      rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity), smul_eq_mul]
    have hf : StronglyMeasurable fun p : (RadialData × (GFFObservable.Admissible → ℝ)) × ℝ =>
        CirclePairing.radialVersion radialCircle p.1.1 ‖circleMap z r p.2‖ :=
      (hr.comp ((measurable_fst.comp measurable_fst).prodMk
        ((continuous_circleMap z r).measurable.comp measurable_snd).norm)).stronglyMeasurable
    have hc : Measurable (fun v : RadialData × (GFFObservable.Admissible → ℝ) =>
        Real.circleAverage (fun x => CirclePairing.radialVersion radialCircle v.1 ‖x‖) z r) := by
      rw [e]
      exact (hf.integral_prod_right' (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).measurable.const_mul _
    exact ((measurable_pi_apply _).comp measurable_snd).add hc

private theorem radialLateralObservables_apply (hC : (ℂ → ℝ) → ℝ) (a : ℝ → ℂ → ℝ)
    (ha : ContinuousOn (fun s => a s 0) (Ioi 0)) :
    radialLateralObservables (radialProcess a, lateralProcess hC a) =
      wholePlaneObservableProc (fun _ : Unit => hC) (fun _ : Unit => a) () := by
  have hrad : ∀ s, CirclePairing.radialVersion radialCircle (radialProcess a) s =
      CirclePairing.radialVersion (fun _ : Unit => a) () s := radialVersion_radialProcess a
  have hlat := CirclePairing.lateralVersion_eq (hC := fun _ : Unit => hC) (hcirc := fun _ : Unit => a) (ω := ()) ha
  funext ⟨o, ho⟩
  have heval := congrFun hlat ⟨o, ho⟩
  cases o with
  | pairing φ =>
    simp only [CirclePairing.lateralVersionEval, lateralProcess, lateralEval] at heval
    simp only [radialLateralObservables, lateralProcess, lateralEval, wholePlaneObservableProc,
      GFFObservable.eval, hrad]
    linarith
  | circle r z =>
    simp only [CirclePairing.lateralVersionEval, lateralProcess, lateralEval] at heval
    simp only [radialLateralObservables, lateralProcess, lateralEval, wholePlaneObservableProc,
      GFFObservable.eval, hrad]
    linarith

/-- The radial and lateral law determines the law of all admissible cone
pairings and positive-radius circle averages. -/
theorem IsQuantumCone.observable_law_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {γ : ℝ} {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {a : Ω → ℝ → ℂ → ℝ} {a' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC a) (h' : IsQuantumCone γ P' hC' a') :
    P.map (wholePlaneObservableProc hC a) = P'.map (wholePlaneObservableProc hC' a') := by
  have hrep : (fun ω => radialLateralObservables (radialProcess (a ω), lateralProcess (hC ω) (a ω))) =ᵐ[P]
      wholePlaneObservableProc hC a := by
    filter_upwards [h.ae_continuousOn_circle] with ω hω
    exact radialLateralObservables_apply (hC ω) (a ω) (CirclePairing.continuousOn_radial hω)
  have hrep' : (fun ω => radialLateralObservables (radialProcess (a' ω), lateralProcess (hC' ω) (a' ω))) =ᵐ[P']
      wholePlaneObservableProc hC' a' := by
    filter_upwards [h'.ae_continuousOn_circle] with ω hω
    exact radialLateralObservables_apply (hC' ω) (a' ω) (CirclePairing.continuousOn_radial hω)
  have hm := (IsQuantumCone.measurable_radialProcess h).aemeasurable.prodMk
    (CirclePairing.aemeasurable_lateralProcess h.measurable_pairing h.measurable_circle h.ae_continuousOn_circle)
  have hm' := (IsQuantumCone.measurable_radialProcess h').aemeasurable.prodMk
    (CirclePairing.aemeasurable_lateralProcess h'.measurable_pairing h'.measurable_circle h'.ae_continuousOn_circle)
  rw [← Measure.map_congr hrep, ← Measure.map_congr hrep']
  change P.map (radialLateralObservables ∘ (fun ω => (radialProcess (a ω), lateralProcess (hC ω) (a ω)))) =
    P'.map (radialLateralObservables ∘ (fun ω => (radialProcess (a' ω), lateralProcess (hC' ω) (a' ω))))
  rw [← AEMeasurable.map_map_of_aemeasurable measurable_radialLateralObservables.aemeasurable hm,
    ← AEMeasurable.map_map_of_aemeasurable measurable_radialLateralObservables.aemeasurable hm',
    IsQuantumCone.joint_radial_lateral_law_unique h h']

/-- Read the two radial paths from admissible observables. -/
private def observableRadial (v : GFFObservable.Admissible → ℝ) : RadialData :=
  (fun t => v ⟨.circle (Real.exp (-(t : ℝ))) 0, Real.exp_pos _⟩,
   fun t => v ⟨.circle (Real.exp (t : ℝ)) 0, Real.exp_pos _⟩)

private theorem measurable_observableRadial : Measurable observableRadial := by
  exact (measurable_pi_iff.mpr fun _ => measurable_pi_apply _).prodMk
    (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)

private def observableRadialLateral (v : GFFObservable.Admissible → ℝ) :
    RadialData × (GFFObservable.Admissible → ℝ) :=
  (observableRadial v, observableLateral v)

private theorem measurable_observableRadialLateral : Measurable observableRadialLateral :=
  measurable_observableRadial.prodMk measurable_observableLateral

/-- Equality of admissible observable laws transfers the cone predicate,
provided that the new observables have the required measurable continuous
circle version. -/
theorem IsQuantumCone.of_observable_law_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {γ : ℝ} {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {a : Ω → ℝ → ℂ → ℝ} {a' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC a)
    (hp : ∀ φ, IsTestFunction univ φ → Measurable fun ω => hC' ω φ)
    (hc : ∀ r z, 0 < r → Measurable fun ω => a' ω r z)
    (hcont : ∀ᵐ ω ∂P', ContinuousOn (fun p : ℝ × ℂ => a' ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hlaw : P.map (wholePlaneObservableProc hC a) = P'.map (wholePlaneObservableProc hC' a')) :
    IsQuantumCone γ P' hC' a' := by
  have hobsm : Measurable (wholePlaneObservableProc hC a) := by
    apply measurable_pi_iff.mpr
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ => exact h.measurable_pairing φ ho
    | circle r z => exact h.measurable_circle r z ho
  have hobs'm : Measurable (wholePlaneObservableProc hC' a') := by
    apply measurable_pi_iff.mpr
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ => exact hp φ ho
    | circle r z => exact hc r z ho
  have ho : ProbabilityTheory.IdentDistrib (wholePlaneObservableProc hC a)
      (wholePlaneObservableProc hC' a') P P' := ⟨hobsm.aemeasurable, hobs'm.aemeasurable, hlaw⟩
  have hj := ho.comp measurable_observableRadialLateral
  have he : (observableRadialLateral ∘ wholePlaneObservableProc hC a) =ᵐ[P]
      (fun ω => (radialProcess (a ω), lateralProcess (hC ω) (a ω))) := by
    filter_upwards [h.ae_continuousOn_circle] with ω hω
    apply Prod.ext
    · rfl
    · exact (observableLateral_apply hC a ω).trans
        (CirclePairing.lateralVersion_eq (CirclePairing.continuousOn_radial hω))
  have he' : (observableRadialLateral ∘ wholePlaneObservableProc hC' a') =ᵐ[P']
      (fun ω => (radialProcess (a' ω), lateralProcess (hC' ω) (a' ω))) := by
    filter_upwards [hcont] with ω hω
    apply Prod.ext
    · rfl
    · exact (observableLateral_apply hC' a' ω).trans
        (CirclePairing.lateralVersion_eq (CirclePairing.continuousOn_radial hω))
  have hjoint := ((ProbabilityTheory.IdentDistrib.of_ae_eq hj.aemeasurable_fst he).symm.trans hj).trans
    (ProbabilityTheory.IdentDistrib.of_ae_eq hj.aemeasurable_snd he')
  refine ⟨hp, hc, hcont, ?_, ?_, ?_⟩
  · obtain ⟨ν, hν, hνlaw⟩ := h.radial_law
    exact ⟨ν, hν, ((hjoint.comp measurable_fst).map_eq).symm.trans hνlaw⟩
  · exact ProbabilityTheory.indepFun_of_identDistrib_pair h.indep hjoint
  · obtain ⟨Ξ, mΞ, Q, gC, g, hQ, hG, hGlaw⟩ := h.lateral_law
    exact ⟨Ξ, mΞ, Q, gC, g, hQ, hG, ((hjoint.comp measurable_snd).map_eq).symm.trans hGlaw⟩

/-- Decode the countable test-function coordinates of an observable family. -/
private def observableDistribution (v : GFFObservable.Admissible → ℝ) : LQGMetric.DistC :=
  planeDistributionCode.decode fun n =>
    v ⟨.pairing (planeDistributionCode.test n),
      ⟨(planeDistributionCode.test n).contDiff,
       (planeDistributionCode.test n).hasCompactSupport,
       (planeDistributionCode.test n).tsupport_subset⟩⟩

private theorem measurable_observableDistribution : Measurable observableDistribution := by
  apply planeDistributionCode.measurable_decode.comp
  apply measurable_pi_iff.mpr
  intro n
  exact measurable_pi_apply _

/-- Observable coordinates of a cone are measurable in the product sigma-algebra. -/
theorem IsQuantumCone.measurable_observables
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {a : Ω → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC a) : Measurable (wholePlaneObservableProc hC a) := by
  apply measurable_pi_iff.mpr
  rintro ⟨o, ho⟩
  cases o with
  | pairing φ => exact h.measurable_pairing φ ho
  | circle r z => exact h.measurable_circle r z ho

/-- The cone predicate determines the law of any simultaneously represented
plane distribution, independently of the probability space and of the
choice of representing distribution. -/
theorem IsQuantumCone.distribution_law_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {γ : ℝ} {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {a : Ω → ℝ → ℂ → ℝ} {a' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC a) (h' : IsQuantumCone γ P' hC' a')
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC}
    (hrep : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂P', ∀ φ : LQGMetric.TestC, hC' ω φ = H' ω φ) :
    P.map H = P'.map H' := by
  have heq : (observableDistribution ∘ wholePlaneObservableProc hC a) =ᵐ[P] H := by
    filter_upwards [hrep] with ω hω
    change planeDistributionCode.decode (fun n => hC ω (planeDistributionCode.test n)) = H ω
    have hc : (fun n => hC ω (planeDistributionCode.test n)) =
        (fun n => H ω (planeDistributionCode.test n)) := funext fun n => hω _
    rw [hc, planeDistributionCode.decode_encode]
  have heq' : (observableDistribution ∘ wholePlaneObservableProc hC' a') =ᵐ[P'] H' := by
    filter_upwards [hrep'] with ω hω
    change planeDistributionCode.decode (fun n => hC' ω (planeDistributionCode.test n)) = H' ω
    have hc : (fun n => hC' ω (planeDistributionCode.test n)) =
        (fun n => H' ω (planeDistributionCode.test n)) := funext fun n => hω _
    rw [hc, planeDistributionCode.decode_encode]
  rw [← Measure.map_congr heq, ← Measure.map_congr heq',
    ← Measure.map_map measurable_observableDistribution (IsQuantumCone.measurable_observables h),
    ← Measure.map_map measurable_observableDistribution (IsQuantumCone.measurable_observables h'),
    IsQuantumCone.observable_law_eq h h']

/-- Joint measurability of evaluation at a variable dilation, on the imported
plane distribution and test-function carriers. -/
def VariableDilationPairingStep : Prop :=
  ∀ φ : LQGMetric.TestC,
    Measurable fun p : LQGMetric.DistC × ℝ => p.1 (LQGMetric.testAffinePull p.2 0 φ)

/-- The remaining topology step can be reduced to continuity of the
nonzero dilation orbit of each fixed test function. -/
def ContinuousDilationTestStep : Prop :=
  ∀ φ : LQGMetric.TestC,
    Continuous fun r : {r : ℝ // r ≠ 0} => LQGMetric.testAffinePull r 0 φ

/-- Dilation of a test function varies continuously at each nonzero scale. -/
theorem continuousAt_testAffinePull (φ : LQGMetric.TestC) {r₀ : ℝ} (hr₀ : r₀ ≠ 0) :
    ContinuousAt (fun r : ℝ => LQGMetric.testAffinePull r 0 φ) r₀ := by
  let δ : ℝ := |r₀| / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let S : Set ℝ := Metric.closedBall r₀ δ
  have hSn : S ∈ 𝓝 r₀ := Metric.closedBall_mem_nhds _ hδ
  have hS0 : ∀ r : S, (r : ℝ) ≠ 0 := by
    intro r hr
    have hbound : dist (r : ℝ) r₀ ≤ δ := Metric.mem_closedBall.mp r.2
    rw [hr, Real.dist_eq, zero_sub, abs_neg] at hbound
    dsimp [δ] at hbound
    have : 0 < |r₀| := abs_pos.mpr hr₀
    linarith
  let K : TopologicalSpace.Compacts ℂ :=
    ⟨(fun p : ℝ × ℂ => p.1 • p.2) '' (S ×ˢ tsupport φ),
      ((isCompact_closedBall _ _).prod φ.hasCompactSupport.isCompact).image (by fun_prop)⟩
  let Ψ : S → ℂ → ℝ := fun r y => φ ((r : ℝ)⁻¹ • y)
  have hs : ∀ r : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ r) := by
    intro r
    exact φ.contDiff.comp (by fun_prop)
  have hK : ∀ r : S, ∀ y ∉ (K : Set ℂ), Ψ r y = 0 := by
    intro r y hy
    change φ ((r : ℝ)⁻¹ • y) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    apply hy
    change y ∈ (fun p : ℝ × ℂ => p.1 • p.2) '' (S ×ˢ tsupport φ)
    refine ⟨⟨r, (r : ℝ)⁻¹ • y⟩, ⟨r.2, ht⟩, ?_⟩
    simp [hS0 r]
  have hD : ∀ i : ℕ, Continuous fun p : S × ℂ => iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
    intro i
    have hr : Continuous fun p : S × ℂ => (p.1 : ℝ)⁻¹ :=
      (continuous_subtype_val.comp continuous_fst).inv₀ fun p => hS0 p.1
    change Continuous fun p : S × ℂ =>
      iteratedFDeriv ℝ i (fun y => φ ((p.1 : ℝ)⁻¹ • y)) p.2
    simp_rw [iteratedFDeriv_comp_const_smul _ (φ.contDiff.of_le (by exact_mod_cast le_top))]
    exact (hr.pow i).smul
      ((φ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
        (hr.smul continuous_snd))
  have hc := LQGMetric.continuous_testFamK K Ψ hs hK hD
  let I : 𝓓^{⊤}_{K}(ℂ, ℝ) →L[ℝ] LQGMetric.TestC :=
    TestFunction.ofSupportedInCLM ℝ (subset_univ _)
  have heq : (fun r : S => LQGMetric.testAffinePull (r : ℝ) 0 φ) =
      I ∘ LQGMetric.testFamK K Ψ hs hK := by
    funext r
    ext y
    rw [LQGMetric.testAffinePull_apply _ _ (hS0 r)]
    simp [I, LQGMetric.testFamK, Ψ, Complex.real_smul, div_eq_inv_mul]
    rfl
  have hlocal : ContinuousOn (fun r : ℝ => LQGMetric.testAffinePull r 0 φ) S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun r : S => LQGMetric.testAffinePull (r : ℝ) 0 φ)
    rw [heq]
    exact I.continuous.comp hc
  exact (hlocal r₀ (Metric.mem_closedBall_self hδ.le)).continuousAt hSn

/-- Dilation is continuous on the nonzero scale parameter space. -/
theorem continuousDilationTestStep : ContinuousDilationTestStep := by
  intro φ
  rw [continuous_iff_continuousAt]
  intro r
  exact (continuousAt_testAffinePull φ r.property).comp continuous_subtype_val.continuousAt

/-- Joint measurability follows from continuity of the test orbit and the
cylinder measurability of fixed test pairings.  At zero the pullback is zero. -/
theorem variableDilationPairingStep_of_continuous
    (hcont : ContinuousDilationTestStep) : VariableDilationPairingStep := by
  classical
  intro φ
  let ρ : ℝ → {r : ℝ // r ≠ 0} := fun r =>
    if hr : r = 0 then ⟨1, one_ne_zero⟩ else ⟨r, hr⟩
  have hρ : Measurable ρ := by
    apply Measurable.subtype_mk
    have hm : Measurable fun r : ℝ => if r = 0 then (1 : ℝ) else r :=
      Measurable.ite (measurableSet_singleton 0) measurable_const measurable_id
    convert hm using 1
    funext r
    change (ρ r : ℝ) = (if r = 0 then 1 else r)
    by_cases hr : r = 0 <;> simp [ρ, hr]
  have hjoint : Measurable fun p : {r : ℝ // r ≠ 0} × LQGMetric.DistC =>
      p.2 (LQGMetric.testAffinePull p.1 0 φ) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun d => (map_continuous d).comp (hcont φ))
      (fun r => LQGMetric.measurable_distOn_apply _)
  have hm : Measurable fun p : LQGMetric.DistC × ℝ =>
      if p.2 = 0 then (0 : ℝ) else p.1 (LQGMetric.testAffinePull (ρ p.2) 0 φ) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
      (hjoint.comp ((hρ.comp measurable_snd).prodMk measurable_fst))
  convert hm using 1
  funext p
  by_cases hp : p.2 = 0
  · simp [hp, LQGMetric.testAffinePull]
  · simp [hp, ρ]

/-- Variable dilation pairings are jointly measurable. -/
theorem variableDilationPairingStep : VariableDilationPairingStep :=
  variableDilationPairingStep_of_continuous continuousDilationTestStep

/-- A version of the circle averages centered at zero, recovered from
field pairings on a countable dyadic set of positive radii. -/
def fieldRadialVersion {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) : Ω → ℝ → ℝ :=
  CirclePairing.radialVersion (fun ω r _ => FieldCircle.circleField S r 0 ω)

/-- The radial version is jointly measurable for the exact field sigma-algebra. -/
theorem measurable_fieldRadialVersion {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) :
    Measurable[S.fieldSigma.prod (borel ℝ)] (Function.uncurry (fieldRadialVersion S)) := by
  have hm : ∀ r : ℝ, Measurable[S.fieldSigma] (FieldCircle.circleField S r 0) :=
    fun r => FieldCircle.measurable_circleField S r 0
  let m := S.fieldSigma
  let : MeasurableSpace Ω := m
  exact CirclePairing.measurable_radialVersion (fun r _ _ => hm r)

/-- One event suffices for recovering all positive-radius centered circles,
using continuity in the radius. -/
theorem ae_fieldRadialVersion_eq {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ r : ℝ, 0 < r → fieldRadialVersion S ω r = S.hcirc ω r 0 := by
  have hdyad : ∀ᵐ ω ∂S.P, ∀ n : ℕ, ∀ k : ℤ, 0 < k →
      FieldCircle.circleField S ((k : ℝ) / 2 ^ n) 0 ω = S.hcirc ω ((k : ℝ) / 2 ^ n) 0 := by
    simp only [ae_all_iff]
    intro n k hk
    have hp : (0 : ℝ) < (k : ℝ) / 2 ^ n := div_pos (Int.cast_pos.mpr hk) (by positivity)
    exact FieldCircle.ae_circleField_eq hS hp (by simpa only [norm_zero] using hp.ne'.symm)
  filter_upwards [hdyad, hS.isQuantumCone.ae_continuousOn_circle] with ω hω hc
  intro r hr
  have heq : fieldRadialVersion S ω r = CirclePairing.radialVersion S.hcirc ω r := by
    unfold fieldRadialVersion CirclePairing.radialVersion
    congr 1
    funext n
    unfold CirclePairing.radialApprox CirclePairing.dyadicCeil
    by_cases hk : 0 < ⌈r * 2 ^ n⌉
    · simp only [hk, ↓reduceIte]
      exact hω n _ hk
    · simp only [hk, ↓reduceIte]
  rw [heq]
  exact CirclePairing.radialVersion_eq (CirclePairing.continuousOn_radial hc) hr

/-- Centered circle averages recovered as a Borel function of a distribution.
Outside the cone-law event the limsup convention supplies a total function. -/
def distributionRadialVersion (H : LQGMetric.DistC) (r : ℝ) : ℝ :=
  CirclePairing.radialVersion
    (fun d s _ => limsup (fun n => d (LQGMetric.CircleAvg.circBump n 0 s)) atTop) H r

/-- The distribution-to-centered-circle map is jointly Borel measurable. -/
theorem measurable_distributionRadialVersion :
    Measurable (Function.uncurry distributionRadialVersion) := by
  apply CirclePairing.measurable_radialVersion
  intro r z hr
  exact Measurable.limsup fun n => LQGMetric.measurable_distOn_apply _

/-- The field-measurable distribution from the countable code recovers all
positive centered circles on one common event. -/
theorem exists_fieldMeasurable_distribution_with_radial
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ H : Ω → LQGMetric.DistC, Measurable[S.fieldSigma] H ∧
      (∀ᵐ ω ∂S.P, (∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) ∧
        ∀ r : ℝ, 0 < r → distributionRadialVersion (H ω) r = S.hcirc ω r 0) := by
  obtain ⟨H, hHm, hH⟩ := exists_fieldMeasurable_coneDistribution hS
  refine ⟨H, hHm, ?_⟩
  filter_upwards [hH, ae_fieldRadialVersion_eq hS] with ω hω hr
  refine ⟨hω, ?_⟩
  have hcircle : ∀ s : ℝ,
      (limsup (fun k => H ω (LQGMetric.CircleAvg.circBump k 0 s)) atTop) =
        FieldCircle.circleField S s 0 ω := by
    intro s
    unfold FieldCircle.circleField
    apply congrArg (fun f : ℕ → ℝ => limsup f atTop)
    funext k
    exact (hω _).symm
  intro r hrpos
  rw [← hr r hrpos]
  unfold distributionRadialVersion fieldRadialVersion CirclePairing.radialVersion
  apply congrArg (fun f : ℕ → ℝ => limsup f atTop)
  funext n
  unfold CirclePairing.radialApprox
  split
  · exact hcircle _
  · rfl

/-- At each circle avoiding the origin, Bonanno's distributional circle
average agrees almost surely with the cone circle observable. This is an
agreement at a fixed circle; no simultaneous continuity of `circleAvg` is
claimed. -/
theorem ae_distribution_circleAvg_eq
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC}
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≠ r) :
    ∀ᵐ ω ∂S.P, LQGMetric.circleAvg (H ω) r z = S.hcirc ω r z := by
  filter_upwards [hH, CirclePairing.ae_tendsto_circBump_of_isQuantumCone
    hS.isQuantumCone hr hz] with ω hω ht
  have ht' : Tendsto (fun n => Real.circleAverage
      (fun x => H ω (LQGMetric.bumpTest n x)) z r) atTop (𝓝 (S.hcirc ω r z)) := by
    apply ht.congr
    intro n
    rw [LQGMetric.CircleAvg.circleAverage_pairing]
    exact hω _
  exact ht'.limUnder_eq

/-- A grid center has irrational norm: in particular it avoids every dyadic
radius, not only reciprocal powers of two. -/
theorem norm_gridPt_ne_dyadic (m n : ℕ) (a b k : ℤ) :
    ‖FieldCircle.gridPt m a b‖ ≠ (k : ℝ) / 2 ^ n := by
  intro h
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  have h2 : ‖FieldCircle.gridPt m a b‖ ^ 2 * ((2 : ℝ) ^ n) ^ 2 = (k : ℝ) ^ 2 := by
    rw [h, div_pow]
    field_simp
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  simp only [FieldCircle.gridPt] at h2
  have hR : (((3 * a + 1) ^ 2 + (3 * b + 1) ^ 2) * ((2 : ℤ) ^ n) ^ 2 : ℤ) =
      ((9 * k ^ 2 * ((2 : ℤ) ^ m) ^ 2 : ℤ) : ℝ) := by
    push_cast
    field_simp at h2
    linear_combination h2
  have hZ : ((3 * a + 1) ^ 2 + (3 * b + 1) ^ 2) * ((2 : ℤ) ^ n) ^ 2 =
      9 * k ^ 2 * ((2 : ℤ) ^ m) ^ 2 := by
    exact_mod_cast hR
  have h3 := congrArg (fun x : ℤ => (x : ZMod 3)) hZ
  push_cast at h3
  have e3 : (3 : ZMod 3) = 0 := rfl
  have e9 : (9 : ZMod 3) = 0 := rfl
  have e4 : ((2 : ZMod 3) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm n 2, pow_mul]
    have : (2 : ZMod 3) ^ 2 = 1 := rfl
    rw [this, one_pow]
  rw [e3, e9, e4] at h3
  simp only [zero_mul, zero_add, one_pow, mul_one] at h3
  exact absurd h3 (by decide)

/-- The spatial interpolation at an arbitrary dyadic radius. -/
def distributionCircleAtDyadic (n : ℕ) (k : ℤ) (H : LQGMetric.DistC) (z : ℂ) : ℝ :=
  FieldCircle.gridVersion (fun w d => LQGMetric.circleAvg d ((k : ℝ) / 2 ^ n) w) H z

theorem measurable_distributionCircleAtDyadic (n : ℕ) (k : ℤ) :
    Measurable (Function.uncurry (distributionCircleAtDyadic n k)) := by
  let X : ℂ → LQGMetric.DistC → ℝ := fun w d => LQGMetric.circleAvg d ((k : ℝ) / 2 ^ n) w
  have hm : ∀ w, Measurable (X w) := fun w => LQGMetric.measurable_circleAvg_left _ w
  change Measurable (Function.uncurry (FieldCircle.gridVersion X))
  exact FieldCircle.measurable_gridVersion X hm

theorem ae_distributionCircleAtDyadic_eq
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC}
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∀ n : ℕ, ∀ k : ℤ, 0 < k → ∀ z : ℂ,
      distributionCircleAtDyadic n k (H ω) z = S.hcirc ω ((k : ℝ) / 2 ^ n) z := by
  have hgrid : ∀ᵐ ω ∂S.P, ∀ n m : ℕ, ∀ k a b : ℤ, 0 < k →
      LQGMetric.circleAvg (H ω) ((k : ℝ) / 2 ^ n) (FieldCircle.gridPt m a b) =
        S.hcirc ω ((k : ℝ) / 2 ^ n) (FieldCircle.gridPt m a b) := by
    simp only [ae_all_iff]
    intro n m k a b hk
    apply ae_distribution_circleAvg_eq hS hH
      (div_pos (Int.cast_pos.mpr hk) (by positivity))
    exact norm_gridPt_ne_dyadic m n a b k
  filter_upwards [hgrid, hS.isQuantumCone.ae_continuousOn_circle] with ω hg hc n k hk z
  have hcont : Continuous fun w => S.hcirc ω ((k : ℝ) / 2 ^ n) w := by
    rw [← continuousOn_univ]
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
      fun w _ => ⟨mem_Ioi.2 (div_pos (Int.cast_pos.mpr hk) (by positivity)), mem_univ _⟩
  exact FieldCircle.gridVersion_eq hcont (fun m a b => hg n m k a b hk) z

/-- A distributional version of the positive-radius circle process. -/
def distributionCircleVersion (H : LQGMetric.DistC) (r : ℝ) (z : ℂ) : ℝ :=
  limsup (fun n : ℕ => if 0 < ⌈r * 2 ^ n⌉ then
    distributionCircleAtDyadic n ⌈r * 2 ^ n⌉ H z else 0) atTop

/-- The full circle version is jointly Borel measurable. -/
theorem measurable_distributionCircleVersion :
    Measurable fun p : LQGMetric.DistC × ℝ × ℂ => distributionCircleVersion p.1 p.2.1 p.2.2 := by
  apply Measurable.limsup
  intro n
  have hg : Measurable fun p : (LQGMetric.DistC × ℂ) × ℤ =>
      if 0 < p.2 then distributionCircleAtDyadic n p.2 p.1.1 p.1.2 else 0 := by
    apply measurable_from_prod_countable_left
    intro k
    by_cases hk : 0 < k
    · change Measurable fun p : LQGMetric.DistC × ℂ =>
        if 0 < k then distributionCircleAtDyadic n k p.1 p.2 else 0
      simp only [hk, ↓reduceIte]
      change Measurable (Function.uncurry (distributionCircleAtDyadic n k))
      exact measurable_distributionCircleAtDyadic n k
    · simpa only [hk, ↓reduceIte] using (measurable_const : Measurable fun _ : LQGMetric.DistC × ℂ => (0 : ℝ))
  exact hg.comp ((measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
    (Int.measurable_ceil.comp ((measurable_fst.comp measurable_snd).mul_const _)))

/-- A continuous circle process is determined by its dyadic-radius, grid-center
circle averages. The statement is deterministic and applies to any distribution. -/
theorem distributionCircleVersion_eq_of_grid
    (H : LQGMetric.DistC) (c : ℝ → ℂ → ℝ)
    (hc : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ))
    (hg : ∀ n m : ℕ, ∀ k a b : ℤ, 0 < k →
      LQGMetric.circleAvg H ((k : ℝ) / 2 ^ n) (FieldCircle.gridPt m a b) =
        c ((k : ℝ) / 2 ^ n) (FieldCircle.gridPt m a b)) :
    ∀ r : ℝ, 0 < r → ∀ z : ℂ, distributionCircleVersion H r z = c r z := by
  have hdyad : ∀ n : ℕ, ∀ k : ℤ, 0 < k → ∀ z : ℂ,
      distributionCircleAtDyadic n k H z = c ((k : ℝ) / 2 ^ n) z := by
    intro n k hk z
    have hcont : Continuous fun w => c ((k : ℝ) / 2 ^ n) w := by
      rw [← continuousOn_univ]
      exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
        fun w _ => ⟨mem_Ioi.2 (div_pos (Int.cast_pos.mpr hk) (by positivity)), mem_univ _⟩
    exact FieldCircle.gridVersion_eq hcont (fun m a b => hg n m k a b hk) z
  intro r hr z
  have hpos : ∀ n : ℕ, 0 < ⌈r * 2 ^ n⌉ := fun n => Int.ceil_pos.2 (by positivity)
  have hcont : ContinuousOn (fun s : ℝ => c s z) (Ioi 0) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn fun s hs => ⟨hs, mem_univ _⟩
  have ht : Tendsto (fun n : ℕ => if 0 < ⌈r * 2 ^ n⌉ then
      distributionCircleAtDyadic n ⌈r * 2 ^ n⌉ H z else 0) atTop (𝓝 (c r z)) := by
    have ht' := (hcont.continuousAt (Ioi_mem_nhds hr)).tendsto.comp
      (CirclePairing.tendsto_dyadicCeil r)
    apply ht'.congr
    intro n
    simp only [hpos n, ↓reduceIte, CirclePairing.dyadicCeil, Function.comp_apply]
    exact (hdyad n _ (hpos n) z).symm
  exact ht.limsup_eq

/-- On one event, the distributional version recovers every positive-radius
circle at every center. -/
theorem ae_distributionCircleVersion_eq
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC}
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      distributionCircleVersion (H ω) r z = S.hcirc ω r z := by
  filter_upwards [ae_distributionCircleAtDyadic_eq hS hH,
    hS.isQuantumCone.ae_continuousOn_circle] with ω hω hc r hr z
  have hpos : ∀ n : ℕ, 0 < ⌈r * 2 ^ n⌉ := fun n => Int.ceil_pos.2 (by positivity)
  have hcont : ContinuousOn (fun s : ℝ => S.hcirc ω s z) (Ioi 0) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn fun s hs => ⟨hs, mem_univ _⟩
  have ht : Tendsto (fun n : ℕ => if 0 < ⌈r * 2 ^ n⌉ then
      distributionCircleAtDyadic n ⌈r * 2 ^ n⌉ (H ω) z else 0) atTop (𝓝 (S.hcirc ω r z)) := by
    have ht' := (hcont.continuousAt (Ioi_mem_nhds hr)).tendsto.comp
      (CirclePairing.tendsto_dyadicCeil r)
    apply ht'.congr
    intro n
    simp only [hpos n, ↓reduceIte, CirclePairing.dyadicCeil, Function.comp_apply]
    exact (hω n _ (hpos n) z).symm
  exact ht.limsup_eq

/-- The countably decoded distribution is field-measurable and recovers both
the test pairings and the entire positive-radius circle process on one event. -/
theorem exists_fieldMeasurable_distribution_with_circles
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ H : Ω → LQGMetric.DistC, Measurable[S.fieldSigma] H ∧
      ∀ᵐ ω ∂S.P, (∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) ∧
        ∀ r : ℝ, 0 < r → ∀ z : ℂ,
          distributionCircleVersion (H ω) r z = S.hcirc ω r z := by
  obtain ⟨H, hHm, hH⟩ := exists_fieldMeasurable_coneDistribution hS
  refine ⟨H, hHm, ?_⟩
  filter_upwards [hH, ae_distributionCircleVersion_eq hS hH] with ω hpair hcircle
  exact ⟨hpair, hcircle⟩

/-- The positive-radius circle process recovered from a distribution, indexed
by positive radii and centers. -/
def distributionCircleCode (H : LQGMetric.DistC) : (Ioi (0 : ℝ) × ℂ) → ℝ :=
  fun p => distributionCircleVersion H p.1 p.2

/-- A fixed positive-radius circle evaluation is Borel. -/
theorem measurable_distributionCircleVersion_fixed (r : ℝ) (z : ℂ) :
    Measurable (fun H : LQGMetric.DistC => distributionCircleVersion H r z) := by
  have hp : Measurable (fun H : LQGMetric.DistC => (H, (r, z))) :=
    measurable_id.prodMk measurable_const
  have hm := measurable_distributionCircleVersion.comp hp
  simpa only [Function.comp_def] using hm

/-- The circle code is measurable for the cylinder sigma algebra. -/
theorem measurable_distributionCircleCode : Measurable distributionCircleCode := by
  refine (measurable_pi_iff (g := distributionCircleCode)).2 ?_
  intro p
  exact measurable_distributionCircleVersion_fixed p.1 p.2

/-- Admissible pairings and recovered positive-radius circles of a distribution. -/
def distributionObservables (H : LQGMetric.DistC) : GFFObservable.Admissible → ℝ
  | ⟨.pairing φ, hφ⟩ => H ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩
  | ⟨.circle r z, _⟩ => distributionCircleVersion H r z

/-- The distribution-to-observable map is Borel for the cylinder sigma algebra. -/
theorem measurable_distributionObservables : Measurable distributionObservables := by
  apply measurable_pi_iff.mpr
  rintro ⟨o, ho⟩
  cases o with
  | pairing φ => exact LQGMetric.measurable_evalDist ⟨φ, ho.1, ho.2.1, ho.2.2⟩
  | circle r z => exact measurable_distributionCircleVersion_fixed r z

/-- Simultaneous distribution and circle representation gives the full
admissible observable process on one event. -/
theorem ae_distributionObservables_eq
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {H : Ω → LQGMetric.DistC} {hC : Ω → (ℂ → ℝ) → ℝ}
    {a : Ω → ℝ → ℂ → ℝ}
    (hrep : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ = H ω φ)
    (hcirc : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      distributionCircleVersion (H ω) r z = a ω r z) :
    (distributionObservables ∘ H) =ᵐ[P] wholePlaneObservableProc hC a := by
  filter_upwards [hrep, hcirc] with ω hrepω hcircω
  funext ⟨o, ho⟩
  cases o with
  | pairing φ => exact (hrepω ⟨φ, ho.1, ho.2.1, ho.2.2⟩).symm
  | circle r z => exact hcircω r ho z

/-- Equal represented distribution laws and recovered circles determine the
full admissible observable law, including all test-function pairings. -/
theorem map_observables_eq_of_distribution_law
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {a : Ω → ℝ → ℂ → ℝ} {a' : Ω' → ℝ → ℂ → ℝ}
    (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂P', ∀ φ : LQGMetric.TestC, hC' ω φ = H' ω φ)
    (hcirc : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      distributionCircleVersion (H ω) r z = a ω r z)
    (hcirc' : ∀ᵐ ω ∂P', ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      distributionCircleVersion (H' ω) r z = a' ω r z)
    (hlaw : P.map H = P'.map H') :
    P.map (wholePlaneObservableProc hC a) = P'.map (wholePlaneObservableProc hC' a') := by
  rw [← Measure.map_congr (ae_distributionObservables_eq hrep hcirc),
    ← Measure.map_congr (ae_distributionObservables_eq hrep' hcirc'),
    ← Measure.map_map measurable_distributionObservables hH,
    ← Measure.map_map measurable_distributionObservables hH', hlaw]

/-- Equal distribution laws determine the joint laws of the distribution and
its recovered positive-radius circle process. -/
theorem map_distribution_circleCode_eq_of_map_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {H : Ω → LQGMetric.DistC}
    {H' : Ω' → LQGMetric.DistC} (hH : Measurable H) (hH' : Measurable H')
    (hlaw : P.map H = P'.map H') :
    P.map (fun ω => (H ω, distributionCircleCode (H ω))) =
      P'.map (fun ω => (H' ω, distributionCircleCode (H' ω))) := by
  have hm : Measurable (fun h : LQGMetric.DistC => (h, distributionCircleCode h)) :=
    measurable_id.prodMk measurable_distributionCircleCode
  change P.map ((fun h : LQGMetric.DistC => (h, distributionCircleCode h)) ∘ H) =
    P'.map ((fun h : LQGMetric.DistC => (h, distributionCircleCode h)) ∘ H')
  rw [← Measure.map_map hm hH, ← Measure.map_map hm hH', hlaw]

/-- A represented field has the same joint law as any distribution with the
same law, paired with that distribution's recovered circle code. -/
theorem map_distribution_circles_eq_code_of_map_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {S : MatedCRTEnv Ω} {P' : Measure Ω'}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC}
    (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hlaw : S.P.map H = P'.map H') :
    S.P.map (fun ω => (H ω, fun p : Ioi (0 : ℝ) × ℂ => S.hcirc ω p.1 p.2)) =
      P'.map (fun ω => (H' ω, distributionCircleCode (H' ω))) := by
  have hleft : (fun ω => (H ω, distributionCircleCode (H ω))) =ᵐ[S.P]
      fun ω => (H ω, fun p : Ioi (0 : ℝ) × ℂ => S.hcirc ω p.1 p.2) := by
    filter_upwards [ae_distributionCircleVersion_eq hS hrep] with ω hω
    congr 1
    funext p
    exact hω p.1 p.1.property p.2
  rw [← Measure.map_congr hleft]
  exact map_distribution_circleCode_eq_of_map_eq hH hH' hlaw

/-- For valid environments, equality of represented distribution laws gives
equality of their joint distribution and positive-radius circle laws. -/
theorem map_distribution_circles_eq_of_map_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {𝒮 𝒮' : SpaceFillingSLEModel} {γ γ' : ℝ}
    (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ')
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC}
    (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂S'.P, ∀ φ : LQGMetric.TestC, S'.hC ω φ = H' ω φ)
    (hlaw : S.P.map H = S'.P.map H') :
    S.P.map (fun ω => (H ω, fun p : Ioi (0 : ℝ) × ℂ => S.hcirc ω p.1 p.2)) =
      S'.P.map (fun ω => (H' ω, fun p : Ioi (0 : ℝ) × ℂ => S'.hcirc ω p.1 p.2)) := by
  have hleft : (fun ω => (H ω, distributionCircleCode (H ω))) =ᵐ[S.P]
      fun ω => (H ω, fun p : Ioi (0 : ℝ) × ℂ => S.hcirc ω p.1 p.2) := by
    filter_upwards [ae_distributionCircleVersion_eq hS hrep] with ω hω
    congr 1
    funext p
    exact hω p.1 p.1.property p.2
  have hright : (fun ω => (H' ω, distributionCircleCode (H' ω))) =ᵐ[S'.P]
      fun ω => (H' ω, fun p : Ioi (0 : ℝ) × ℂ => S'.hcirc ω p.1 p.2) := by
    filter_upwards [ae_distributionCircleVersion_eq hS' hrep'] with ω hω
    congr 1
    funext p
    exact hω p.1 p.1.property p.2
  rw [← Measure.map_congr hleft, ← Measure.map_congr hright]
  exact map_distribution_circleCode_eq_of_map_eq hH hH' hlaw

/-- For valid environments at the same parameter, simultaneously represented
fields have the same joint distribution and positive-radius circle law. -/
theorem map_distribution_circles_eq_of_cones
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {𝒮 𝒮' : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC}
    (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂S'.P, ∀ φ : LQGMetric.TestC, S'.hC ω φ = H' ω φ) :
    S.P.map (fun ω => (H ω, fun p : Ioi (0 : ℝ) × ℂ => S.hcirc ω p.1 p.2)) =
      S'.P.map (fun ω => (H' ω, fun p : Ioi (0 : ℝ) × ℂ => S'.hcirc ω p.1 p.2)) := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  let : IsProbabilityMeasure S'.P := hS'.isProbabilityMeasure
  exact map_distribution_circles_eq_of_map_eq hS hS' hH hH' hrep hrep'
    (IsQuantumCone.distribution_law_eq hS.isQuantumCone hS'.isQuantumCone hrep hrep')

/-- Pair a distribution at a variable scale, with zero on non-tests. -/
def rescaledDistributionPairing (γ b : ℝ) (H : LQGMetric.DistC) (r : ℝ)
    (φ : ℂ → ℝ) : ℝ := by
  classical
  exact if hφ : IsTestFunction univ φ then
    (r⁻¹) ^ 2 * H (LQGMetric.testAffinePull r 0 ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩) +
      (lqgQ γ * Real.log r - γ⁻¹ * Real.log b) * ∫ x, φ x
    else 0

/-- The distribution obtained by dilation and the quantum-cone additive shift. -/
def rescaledDistribution (γ b : ℝ) (H : LQGMetric.DistC) (r : ℝ) : LQGMetric.DistC :=
  LQGMetric.addConst (LQGMetric.affineComp r 0 H)
    (lqgQ γ * Real.log r - γ⁻¹ * Real.log b)

/-- The rescaled distribution has the expected pairings with all test functions. -/
theorem rescaledDistribution_apply (γ b : ℝ) (H : LQGMetric.DistC) (r : ℝ)
    (φ : LQGMetric.TestC) :
    rescaledDistribution γ b H r φ = rescaledDistributionPairing γ b H r φ := by
  have hφ : IsTestFunction univ (φ : ℂ → ℝ) := ⟨φ.contDiff, φ.hasCompactSupport, subset_univ _⟩
  simp only [rescaledDistribution, LQGMetric.GFFInv.addConst_apply,
    LQGMetric.GFFInv.affineComp_apply, rescaledDistributionPairing, dite_eq_left hφ]
  have heq : (⟨(φ : ℂ → ℝ), hφ.1, hφ.2.1, hφ.2.2⟩ : LQGMetric.TestC) = φ := by
    ext x
    rfl
  rw [heq, inv_pow]
  ring

/-- The distribution-valued dilation is jointly measurable, including at
zero scale where the library's affine pullback is defined. -/
theorem measurable_rescaledDistribution (γ b : ℝ) :
    Measurable fun p : LQGMetric.DistC × ℝ => rescaledDistribution γ b p.1 p.2 := by
  apply LQGMetric.measurable_distOn_iff.mpr
  intro φ
  simp only [rescaledDistribution, LQGMetric.GFFInv.addConst_apply,
    LQGMetric.GFFInv.affineComp_apply]
  exact ((measurable_snd.pow_const 2).inv.mul (variableDilationPairingStep φ)).add
    (measurable_const.mul ((measurable_const.mul measurable_snd.log).sub measurable_const))

/-- A measurable distribution and a measurable radius have a measurable
rescaled distribution, with all rescaled test pairings on the same event. -/
theorem ae_rescaledDistribution_represents
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {H : Ω → LQGMetric.DistC}
    {R : Ω → ℝ} {γ b : ℝ} (hH : Measurable H) (hR : Measurable R)
    (hrep : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ = H ω φ)
    (hpair : ∀ᵐ ω ∂P, ∀ φ, IsTestFunction univ φ →
      hC' ω φ = rescaledPairing γ (hC ω) (R ω) b φ)
    (hne : ∀ᵐ ω ∂P, R ω ≠ 0) :
    Measurable (fun ω => rescaledDistribution γ b (H ω) (R ω)) ∧
      ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC,
        hC' ω φ = rescaledDistribution γ b (H ω) (R ω) φ := by
  constructor
  · change Measurable ((fun p : LQGMetric.DistC × ℝ =>
      rescaledDistribution γ b p.1 p.2) ∘ (fun ω => (H ω, R ω)))
    exact (measurable_rescaledDistribution γ b).comp (hH.prodMk hR)
  · filter_upwards [hrep, hpair, hne] with ω hrepω hpairω hneω
    intro φ
    have hφ : IsTestFunction univ (φ : ℂ → ℝ) := ⟨φ.contDiff, φ.hasCompactSupport, subset_univ _⟩
    have hpull : (fun x => φ (((R ω)⁻¹ : ℂ) * x)) =
        ⇑(LQGMetric.testAffinePull (R ω) 0 φ) := by
      funext x
      rw [LQGMetric.testAffinePull_apply _ _ hneω]
      simp [div_eq_mul_inv, mul_comm]
    rw [hpairω φ hφ, rescaledDistribution_apply]
    simp only [rescaledPairing, rescaledDistributionPairing, dite_eq_left hφ]
    rw [hpull, hrepω (LQGMetric.testAffinePull (R ω) 0 φ)]
    have heq : (⟨(φ : ℂ → ℝ), hφ.1, hφ.2.1, hφ.2.2⟩ : LQGMetric.TestC) = φ := by
      ext x
      rfl
    rw [heq]

/-- The explicit distribution version produces all required pairing and
field-sigma conclusions, given the joint dilation measurability boundary and
an exactly field-measurable version of the positive scale radius. -/
theorem exists_rescaled_pairing_of_variableDilation
    (hscale : VariableDilationPairingStep)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (R : Ω → ℝ) (hRm : Measurable[S.fieldSigma] R)
    (hR : ∀ᵐ ω ∂S.P, R ω = coneScaleRadius γ (S.hcirc ω) b ∧ R ω ≠ 0) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ,
      (∀ᵐ ω ∂S.P, ∀ φ, IsTestFunction univ φ →
        hC' ω φ = rescaledPairing γ (S.hC ω)
          (coneScaleRadius γ (S.hcirc ω) b) b φ) ∧
      (∀ φ, IsTestFunction univ φ → Measurable[S.fieldSigma] fun ω => hC' ω φ) ∧
      (∀ φ, IsTestFunction univ φ → Measurable fun ω => hC' ω φ) ∧
      ∀ c, (S.rescaleWithCircle γ b hC' (fun _ _ _ => 0) c).fieldSigma ≤ S.fieldSigma := by
  obtain ⟨H, hHm, hH⟩ := exists_fieldMeasurable_coneDistribution hS
  let hC' : Ω → (ℂ → ℝ) → ℝ := fun ω => rescaledDistributionPairing γ b (H ω) (R ω)
  have hfield : ∀ φ, IsTestFunction univ φ → Measurable[S.fieldSigma] fun ω => hC' ω φ := by
    intro φ hφ
    let ψ : LQGMetric.TestC := ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩
    have heval : Measurable[S.fieldSigma] fun ω => H ω (LQGMetric.testAffinePull (R ω) 0 ψ) := by
      let m := S.fieldSigma
      let : MeasurableSpace Ω := m
      exact (hscale ψ).comp (hHm.prodMk hRm)
    change Measurable[S.fieldSigma] fun ω => rescaledDistributionPairing γ b (H ω) (R ω) φ
    simp only [rescaledDistributionPairing, dite_eq_left hφ]
    let m := S.fieldSigma
    let : MeasurableSpace Ω := m
    exact ((hRm.inv.pow_const 2).mul heval).add
      (((measurable_const.mul hRm.log).sub measurable_const).mul measurable_const)
  have hle : S.fieldSigma ≤ (inferInstance : MeasurableSpace Ω) := by
    simp only [MatedCRTEnv.fieldSigma, fieldSigmaAlgebra]
    refine iSup₂_le fun φ hφ => ?_
    have hm : Measurable fun ω => fieldPairing 0 (S.hC ω) φ := by
      simpa [fieldPairing] using hS.isQuantumCone.measurable_pairing φ hφ
    exact hm.comap_le
  refine ⟨hC', ?_, hfield, (fun φ hφ => (hfield φ hφ).mono hle le_rfl), ?_⟩
  · filter_upwards [hH, hR] with ω hω hRω
    intro φ hφ
    let ψ : LQGMetric.TestC := ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩
    have hpull : (fun x => φ (((R ω)⁻¹ : ℂ) * x)) =
        ⇑(LQGMetric.testAffinePull (R ω) 0 ψ) := by
      funext x
      rw [LQGMetric.testAffinePull_apply _ _ hRω.2]
      simp [ψ, div_eq_mul_inv, mul_comm]
    change rescaledDistributionPairing γ b (H ω) (R ω) φ = _
    simp only [rescaledDistributionPairing, dite_eq_left hφ, rescaledPairing]
    rw [← hRω.1, hpull, hω (LQGMetric.testAffinePull (R ω) 0 ψ)]
  · intro c
    simp only [MatedCRTEnv.fieldSigma, fieldSigmaAlgebra]
    refine iSup₂_le fun φ hφ => ?_
    have hm : Measurable[S.fieldSigma] fun ω => fieldPairing 0 (hC' ω) φ := by
      simpa [fieldPairing] using hfield φ hφ
    exact hm.comap_le

/-- Specialization to the existing field-measurable cone scale radius. -/
theorem exists_rescaled_pairing
    (hscale : QuantumConeScalingInput)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hS : S.IsValid 𝒮 γ) (hb : 0 < b) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ,
      (∀ᵐ ω ∂S.P, ∀ φ, IsTestFunction univ φ →
        hC' ω φ = rescaledPairing γ (S.hC ω)
          (coneScaleRadius γ (S.hcirc ω) b) b φ) ∧
      (∀ φ, IsTestFunction univ φ → Measurable[S.fieldSigma] fun ω => hC' ω φ) ∧
      (∀ φ, IsTestFunction univ φ → Measurable fun ω => hC' ω φ) ∧
      ∀ c, (S.rescaleWithCircle γ b hC' (fun _ _ _ => 0) c).fieldSigma ≤ S.fieldSigma := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨R, hRm, hR⟩ := exists_fieldMeasurable_coneScaleRadius hscale hγ hγ2 hS hb
  have hpos := ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone hb
  apply exists_rescaled_pairing_of_variableDilation variableDilationPairingStep hS R hRm
  filter_upwards [hR, hpos] with ω hRω hposω
  exact ⟨hRω, hRω ▸ hposω.ne'⟩

/-- The distributional cone-scaling boundary, stated on all admissible
observables. This is the remaining law identification;
it is not supplied by the circle-only `QuantumConeScalingInput`. -/
def RescaledConeObservableLawStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ b : ℝ, 0 < b →
    ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (c : Ω → ℝ → ℂ → ℝ),
      (∀ᵐ ω ∂S.P, ∀ φ, IsTestFunction univ φ →
        hC' ω φ = rescaledPairing γ (S.hC ω) (coneScaleRadius γ (S.hcirc ω) b) b φ) →
      (∀ᵐ ω ∂S.P, c ω = rescaledCircle γ (S.hcirc ω) (coneScaleRadius γ (S.hcirc ω) b) b) →
      S.P.map (wholePlaneObservableProc hC' c) = S.P.map (wholePlaneObservableProc S.hC S.hcirc)

/-- The remaining distribution-valued scaling and circle identification.
This is an internal proof obligation, not a stated literature input: the
rescaled representative must have the original distribution law, and its
recovered positive-radius circles must be the supplied rescaled circles. -/
def RescaledConeRepresentedLawStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ b : ℝ, 0 < b →
    ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (c : Ω → ℝ → ℂ → ℝ),
      (∀ᵐ ω ∂S.P, ∀ φ, IsTestFunction univ φ →
        hC' ω φ = rescaledPairing γ (S.hC ω) (coneScaleRadius γ (S.hcirc ω) b) b φ) →
      (∀ᵐ ω ∂S.P, c ω = rescaledCircle γ (S.hcirc ω) (coneScaleRadius γ (S.hcirc ω) b) b) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H →
        (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
        ∃ H' : Ω → LQGMetric.DistC, Measurable H' ∧
          (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, hC' ω φ = H' ω φ) ∧
          (∀ᵐ ω ∂S.P, ∀ r : ℝ, 0 < r → ∀ z : ℂ,
            distributionCircleVersion (H' ω) r z = c ω r z) ∧
          S.P.map H' = S.P.map H

/-- Circle recovery for the explicitly rescaled distribution. This is a
proof obligation for cone fields at a random scale. -/
def RescaledConeDistributionCircleStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ b : ℝ, 0 < b →
    ∀ (H : Ω → LQGMetric.DistC) (R : Ω → ℝ), Measurable H → Measurable R →
      (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      (∀ᵐ ω ∂S.P, R ω = coneScaleRadius γ (S.hcirc ω) b) →
      ∀ᵐ ω ∂S.P, ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        distributionCircleVersion (rescaledDistribution γ b (H ω) (R ω)) r z =
          rescaledCircle γ (S.hcirc ω) (R ω) b r z

/-- The fixed grid-circle boundary for the randomly rescaled distribution.
The exceptional set is common to the countable dyadic-radius and grid-center
indices. -/
def RescaledConeDistributionCircleGridStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ b : ℝ, 0 < b →
    ∀ (H : Ω → LQGMetric.DistC) (R : Ω → ℝ), Measurable H → Measurable R →
      (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      (∀ᵐ ω ∂S.P, R ω = coneScaleRadius γ (S.hcirc ω) b) →
      ∀ᵐ ω ∂S.P, ∀ n m : ℕ, ∀ k a d : ℤ, 0 < k →
        LQGMetric.circleAvg (rescaledDistribution γ b (H ω) (R ω))
          ((k : ℝ) / 2 ^ n) (FieldCircle.gridPt m a d) =
        rescaledCircle γ (S.hcirc ω) (R ω) b ((k : ℝ) / 2 ^ n)
          (FieldCircle.gridPt m a d)

/-- Countable grid-circle recovery and continuity give all rescaled circles
on one event. -/
theorem rescaledConeDistributionCircleStep_of_grid
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hgrid : RescaledConeDistributionCircleGridStep 𝒮) :
    RescaledConeDistributionCircleStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb H R hHm hRm hrep hR
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hpos := ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone hb
  have hcont := ae_continuousOn_rescaledCircle hS.isQuantumCone hpos
  filter_upwards [hgrid γ hγ hγ2 Ω S hS b hb H R hHm hRm hrep hR, hcont, hR]
    with ω hg hc hRω
  apply distributionCircleVersion_eq_of_grid _ _ ?_ hg
  rw [hRω]
  exact hc

/-- Distribution-valued scale invariance for the explicitly constructed
rescaled cone. This is a proof obligation, not a stated literature input. -/
def RescaledConeDistributionLawStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ b : ℝ, 0 < b →
    ∀ (H : Ω → LQGMetric.DistC) (R : Ω → ℝ), Measurable H → Measurable R →
      (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      (∀ᵐ ω ∂S.P, R ω = coneScaleRadius γ (S.hcirc ω) b) →
      S.P.map (fun ω => rescaledDistribution γ b (H ω) (R ω)) = S.P.map H

/-- The explicit rescaled distribution supplies the representation in the
field step, leaving its distributional law and circle recovery. -/
theorem rescaledConeRepresentedLawStep_of_distribution
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hcircles : RescaledConeDistributionCircleStep 𝒮)
    (hlaw : RescaledConeDistributionLawStep 𝒮) :
    RescaledConeRepresentedLawStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb hC' c hpair hcirc H hHm hrep
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨R, hRm, hR⟩ := exists_fieldMeasurable_coneScaleRadius hscale hγ hγ2 hS hb
  have hle : S.fieldSigma ≤ (inferInstance : MeasurableSpace Ω) := by
    simp only [MatedCRTEnv.fieldSigma, fieldSigmaAlgebra]
    refine iSup₂_le fun φ hφ => ?_
    have hm : Measurable fun ω => fieldPairing 0 (S.hC ω) φ := by
      simpa [fieldPairing] using hS.isQuantumCone.measurable_pairing φ hφ
    exact hm.comap_le
  have hRmeas : Measurable R := hRm.mono hle le_rfl
  have hpos := ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone hb
  have hne : ∀ᵐ ω ∂S.P, R ω ≠ 0 := by
    filter_upwards [hR, hpos] with ω hRω hposω
    exact hRω ▸ hposω.ne'
  have hp : ∀ᵐ ω ∂S.P, ∀ φ, IsTestFunction univ φ →
      hC' ω φ = rescaledPairing γ (S.hC ω) (R ω) b φ := by
    filter_upwards [hpair, hR] with ω hpω hRω
    intro φ hφ
    rw [hRω]
    exact hpω φ hφ
  obtain ⟨hH', hrep'⟩ := ae_rescaledDistribution_represents hHm hRmeas hrep hp hne
  refine ⟨fun ω => rescaledDistribution γ b (H ω) (R ω), hH', hrep', ?_,
    hlaw γ hγ hγ2 Ω S hS b hb H R hHm hRmeas hrep hR⟩
  filter_upwards [hcircles γ hγ hγ2 Ω S hS b hb H R hHm hRmeas hrep hR,
    hcirc, hR] with ω hcω hcircω hRω r hr z
  rw [hcircω, ← hRω]
  exact hcω r hr z

/-- Distribution scaling and circle recovery imply scaling of all admissible
observables. -/
theorem rescaledConeObservableLawStep_of_represented_law
    (𝒮 : SpaceFillingSLEModel) (hstep : RescaledConeRepresentedLawStep 𝒮) :
    RescaledConeObservableLawStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb hC' c hpair hcirc
  obtain ⟨H, hHm, hrep⟩ := exists_fieldMeasurable_coneDistribution hS
  have hle : S.fieldSigma ≤ (inferInstance : MeasurableSpace Ω) := by
    simp only [MatedCRTEnv.fieldSigma, fieldSigmaAlgebra]
    refine iSup₂_le fun φ hφ => ?_
    have hm : Measurable fun ω => fieldPairing 0 (S.hC ω) φ := by
      simpa [fieldPairing] using hS.isQuantumCone.measurable_pairing φ hφ
    exact hm.comap_le
  have hH : Measurable H := hHm.mono hle le_rfl
  obtain ⟨H', hH', hrep', hcirc', hlaw⟩ :=
    hstep γ hγ hγ2 Ω S hS b hb hC' c hpair hcirc H hH hrep
  exact map_observables_eq_of_distribution_law hH' hH hrep' hrep hcirc'
    (ae_distributionCircleVersion_eq hS hrep) hlaw

/-- The rescaled field step follows from circle scaling and the remaining
law identification for admissible observables. -/
theorem rescaledConeFieldStep_of_observable_law (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) (hlaw : RescaledConeObservableLawStep 𝒮) :
    RescaledConeFieldStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb c hcm hcraw
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨hC', hpair, _, hpm, hsigma⟩ := exists_rescaled_pairing hscale hγ hγ2 hS hb
  have hpos := ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone hb
  have hcont : ∀ᵐ ω ∂S.P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
    filter_upwards [hcraw, ae_continuousOn_rescaledCircle hS.isQuantumCone hpos] with ω he hc
    rw [he]
    exact hc
  have hcone := IsQuantumCone.of_observable_law_eq hS.isQuantumCone hpm hcm hcont
    (hlaw γ hγ hγ2 Ω S hS b hb hC' c hpair hcraw).symm
  exact ⟨hC', hpair, hpm, hcone.indep, hcone.lateral_law, hsigma c⟩

end MatedCRT.Sec1

