import MatedCRT.FirstPass.S2y.ConeFieldPairing
import MatedCRT.FirstPass.S2y.ConeRadialCodes

/-!
# The generic lateral-transfer theorem (fp-S2y-cone-lateral, sections 5-7 of notes/fp-gaps/CHATGPT-231)

`jointLateralLaw_of_circleLaw` transfers the joint law of (circle process, lateral process) from a circle process
`c` to a quantum cone `hcirc` whenever the circle processes have the same law and the pairing decoder `D` recovers
the pairings from the circle averages. The lateral observables are the pairings `(h, φ) - ∫ φ(x) h_{|x|}(0) dx` and
the circle averages `h_r(z) - ⨍_{∂B_r(z)} h_{|·|}(0)` (Duplantier-Sheffield, arXiv:1409.7055, Section 4.1).

The two radial codes are binders of exact type: `rp φ q` plays the role of `radialPairingCode φ q` and `rs r z q` of
`radialSphereCode r z q` (z11, `S2y/ConeRadialCodes.lean`, not yet committed), and their a.s. identities are the
conclusions of `radialPairingCode_ae_eq` and `radialSphereCode_ae_eq`.

The proof is by finite-dimensional projections: the joint vector `ω ↦ (j ↦ value of observable j)` on the countable
or uncountable index set `ConeJointIndex` is determined by its finite-dimensional marginals
(`MeasureTheory.IsProjectiveLimit.unique`, no countability), and each marginal is a.s. the same measurable function of
the circle process.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.LQGMeasure

/-- The index of the joint vector: the circle averages on `(0,∞) × ℂ` and the admissible lateral observables. -/
abbrev ConeJointIndex := (Set.Ioi (0 : ℝ) × ℂ) ⊕ GFFObservable.Admissible

/-- The value of the joint index `j` at a circle process `q`: a circle average, or the lateral observable obtained
from the decoder `D` and the radial codes `rp, rs` (`D φ q - rp φ q` for a pairing, `q(r,z) - rs r z q` for a circle
average). -/
noncomputable def coneJointCode
    (rp : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (rs : ℝ → ℂ → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (D : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (q : Set.Ioi (0 : ℝ) × ℂ → ℝ) : ConeJointIndex → ℝ
  | .inl p => q p
  | .inr ⟨.pairing φ, _⟩ => D φ q - rp φ q
  | .inr ⟨.circle r z, hr⟩ => q (⟨r, show (0 : ℝ) < r from hr⟩, z) - rs r z q

/-- The finite-dimensional projection of `coneJointCode` on the finite index set `I`. -/
noncomputable def coneJointFinite
    (rp : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (rs : ℝ → ℂ → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (D : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (I : Finset ConeJointIndex) (q : Set.Ioi (0 : ℝ) × ℂ → ℝ) : I → ℝ :=
  fun i => coneJointCode rp rs D q i.1

theorem measurable_coneJointCode_apply
    {rp : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    {rs : ℝ → ℂ → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    {D : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    (hD : ∀ φ, IsTestFunction Set.univ φ → Measurable (D φ)) (hrp : ∀ φ, Measurable (rp φ))
    (hrs : ∀ r z, Measurable (rs r z)) (j : ConeJointIndex) :
    Measurable fun q => coneJointCode rp rs D q j := by
  rcases j with p | ⟨o, ho⟩
  · exact measurable_pi_apply p
  · cases o with
    | pairing φ => exact (hD φ (show IsTestFunction Set.univ φ from ho)).sub (hrp φ)
    | circle r z =>
      exact (measurable_pi_apply (⟨r, show (0 : ℝ) < r from ho⟩, z)).sub (hrs r z)

theorem measurable_coneJointFinite
    {rp : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    {rs : ℝ → ℂ → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    {D : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    (hD : ∀ φ, IsTestFunction Set.univ φ → Measurable (D φ)) (hrp : ∀ φ, Measurable (rp φ))
    (hrs : ∀ r z, Measurable (rs r z)) (I : Finset ConeJointIndex) :
    Measurable (coneJointFinite rp rs D I) :=
  measurable_pi_iff.mpr fun i => measurable_coneJointCode_apply hD hrp hrs i.1

/-- Reassembling a joint vector from its circle and lateral parts is measurable. -/
theorem measurable_sumElimPair :
    Measurable fun z : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (GFFObservable.Admissible → ℝ) =>
      (Sum.elim z.1 z.2 : ConeJointIndex → ℝ) :=
  measurable_pi_iff.mpr fun j => by
    rcases j with p | o
    · exact (measurable_pi_apply p).comp measurable_fst
    · exact (measurable_pi_apply o).comp measurable_snd

/-- The restriction of a joint vector to a finite index set is measurable. -/
theorem measurable_finRestrict (I : Finset ConeJointIndex) :
    Measurable (I.restrict : (ConeJointIndex → ℝ) → (I → ℝ)) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply i.1

/-- Splitting a joint vector into its circle and lateral parts is measurable. -/
theorem measurable_splitConeJoint :
    Measurable fun x : ConeJointIndex → ℝ =>
      ((fun p : Set.Ioi (0 : ℝ) × ℂ => x (Sum.inl p)), (fun o : GFFObservable.Admissible => x (Sum.inr o))) :=
  (measurable_pi_iff.mpr fun p => measurable_pi_apply (Sum.inl p)).prodMk
    (measurable_pi_iff.mpr fun o => measurable_pi_apply (Sum.inr o))

/-- Each joint coordinate of the lateral vector agrees almost surely with `coneJointCode` at the circle process.
The pairing coordinates use the decoder identity `H ω φ = D φ (circleProcess (h ω))` and the radial pairing code
identity; the circle coordinates use the radial sphere code identity. -/
theorem ae_joint_coord {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {rp : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    {rs : ℝ → ℂ → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    {D : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    (h : Ω → ℝ → ℂ → ℝ) (H : Ω → (ℂ → ℝ) → ℝ)
    (hHD : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → ∀ᵐ ω ∂P, H ω φ = D φ (circleProcess (h ω)))
    (hrp : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
      ∀ᵐ ω ∂P, rp φ (circleProcess (h ω)) = ∫ x, φ x * h ω ‖x‖ 0)
    (hrs : ∀ (r : ℝ) (z : ℂ), 0 < r →
      ∀ᵐ ω ∂P, rs r z (circleProcess (h ω)) = Real.circleAverage (fun x => h ω ‖x‖ 0) z r)
    (j : ConeJointIndex) :
    ∀ᵐ ω ∂P, Sum.elim (circleProcess (h ω)) (lateralProcess (H ω) (h ω)) j =
      coneJointCode rp rs D (circleProcess (h ω)) j := by
  rcases j with p | ⟨o, ho⟩
  · exact Filter.Eventually.of_forall fun ω => rfl
  · cases o with
    | pairing φ =>
      filter_upwards [hHD φ (show IsTestFunction Set.univ φ from ho), hrp φ (show IsTestFunction Set.univ φ from ho)]
        with ω h1 h2
      show H ω φ - ∫ x, φ x * h ω ‖x‖ 0 = D φ (circleProcess (h ω)) - rp φ (circleProcess (h ω))
      rw [h1, h2]
    | circle r z =>
      filter_upwards [hrs r z (show (0 : ℝ) < r from ho)] with ω h2
      show h ω r z - Real.circleAverage (fun x => h ω ‖x‖ 0) z r =
        circleProcess (h ω) (⟨r, show (0 : ℝ) < r from ho⟩, z) - rs r z (circleProcess (h ω))
      rw [h2]
      rfl

/-- Almost surely equal coordinates give an almost sure equality of the finite projections. -/
theorem ae_restrict_coneJoint {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {rp : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    {rs : ℝ → ℂ → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    {D : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ}
    (V : Ω → ConeJointIndex → ℝ) (q : Ω → Set.Ioi (0 : ℝ) × ℂ → ℝ)
    (hV : ∀ j : ConeJointIndex, ∀ᵐ ω ∂P, V ω j = coneJointCode rp rs D (q ω) j)
    (I : Finset ConeJointIndex) :
    (fun ω => fun i : I => V ω i.1) =ᵐ[P] fun ω => coneJointFinite rp rs D I (q ω) := by
  have h : ∀ᵐ ω ∂P, ∀ i : I, V ω i.1 = coneJointCode rp rs D (q ω) i.1 :=
    ae_all_iff.2 fun i => hV i.1
  filter_upwards [h] with ω hω
  funext i
  exact hω i

/-- **Generic lateral transfer** (chat 231 §5, `jointLateralLaw_of_circleLaw`). If the circle processes of `c` and
`hcirc` have the same law, `D` is a measurable decoder of the pairings of the cone `hC` from the circle process of
`hcirc`, and the radial codes `rp, rs` have the a.s. identities of `radialPairingCode_ae_eq` and
`radialSphereCode_ae_eq` for `c` and `hcirc`, then the joint laws of (circle process, lateral process) agree. The
laws agree on every finite set of coordinates, hence on the product (`IsProjectiveLimit.unique`). -/
theorem jointLateralLaw_of_circleLaw {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc c : Ω → ℝ → ℂ → ℝ}
    (hP : IsProbabilityMeasure P) (hQ : IsQuantumCone γ P hC hcirc)
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    (hlaw : P.map (fun ω => circleProcess (c ω)) = P.map (fun ω => circleProcess (hcirc ω)))
    (D : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (hD : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
      Measurable (D φ) ∧ (fun ω => D φ (circleProcess (hcirc ω))) =ᵐ[P] (fun ω => hC ω φ))
    (rp : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (rs : ℝ → ℂ → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (hrp_m : ∀ φ, Measurable (rp φ)) (hrs_m : ∀ r z, Measurable (rs r z))
    (hrpc : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
      ∀ᵐ ω ∂P, rp φ (circleProcess (c ω)) = ∫ x, φ x * c ω ‖x‖ 0)
    (hrph : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
      ∀ᵐ ω ∂P, rp φ (circleProcess (hcirc ω)) = ∫ x, φ x * hcirc ω ‖x‖ 0)
    (hrsc : ∀ (r : ℝ) (z : ℂ), 0 < r →
      ∀ᵐ ω ∂P, rs r z (circleProcess (c ω)) = Real.circleAverage (fun x => c ω ‖x‖ 0) z r)
    (hrsh : ∀ (r : ℝ) (z : ℂ), 0 < r →
      ∀ᵐ ω ∂P, rs r z (circleProcess (hcirc ω)) = Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r) :
    P.map (fun ω => (circleProcess (c ω), lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω))) =
      P.map (fun ω => (circleProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) := by
  have hqc : Measurable fun ω => circleProcess (c ω) := measurable_circleProcess_of hcm
  have hqh : Measurable fun ω => circleProcess (hcirc ω) :=
    measurable_circleProcess_of hQ.measurable_circle
  have hmD : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → Measurable fun ω => D φ (circleProcess (c ω)) :=
    fun φ hφ => (hD φ hφ).1.comp hqc
  have hlatC : AEMeasurable (fun ω => lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)) P :=
    MatedCRT.CirclePairing.aemeasurable_lateralProcess hmD hcm hcont
  have hlatH : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    MatedCRT.Sec1.aemeasurable_lateralProcess_of_isQuantumCone hQ
  have hVC : AEMeasurable (fun ω => (Sum.elim (circleProcess (c ω))
      (lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)) : ConeJointIndex → ℝ)) P :=
    measurable_sumElimPair.comp_aemeasurable (hqc.aemeasurable.prodMk hlatC)
  have hVH : AEMeasurable (fun ω => (Sum.elim (circleProcess (hcirc ω))
      (lateralProcess (hC ω) (hcirc ω)) : ConeJointIndex → ℝ)) P :=
    measurable_sumElimPair.comp_aemeasurable (hqh.aemeasurable.prodMk hlatH)
  -- the a.s. coordinates of the two joint vectors
  have hcoordC : ∀ j : ConeJointIndex, ∀ᵐ ω ∂P, Sum.elim (circleProcess (c ω))
      (lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)) j =
        coneJointCode rp rs D (circleProcess (c ω)) j :=
    fun j => ae_joint_coord c (fun ω φ => D φ (circleProcess (c ω)))
      (fun _ _ => Filter.Eventually.of_forall fun ω => rfl) hrpc hrsc j
  have hcoordH : ∀ j : ConeJointIndex, ∀ᵐ ω ∂P, Sum.elim (circleProcess (hcirc ω))
      (lateralProcess (hC ω) (hcirc ω)) j = coneJointCode rp rs D (circleProcess (hcirc ω)) j :=
    fun j => ae_joint_coord hcirc hC (fun φ hφ => (hD φ hφ).2.symm) hrph hrsh j
  -- the finite projections of the two joint vectors
  have hfinC : ∀ I : Finset ConeJointIndex,
      (fun ω => I.restrict (Sum.elim (circleProcess (c ω))
        (lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)) : ConeJointIndex → ℝ)) =ᵐ[P]
        fun ω => coneJointFinite rp rs D I (circleProcess (c ω)) :=
    fun I => ae_restrict_coneJoint _ (fun ω => circleProcess (c ω)) hcoordC I
  have hfinH : ∀ I : Finset ConeJointIndex,
      (fun ω => I.restrict (Sum.elim (circleProcess (hcirc ω))
        (lateralProcess (hC ω) (hcirc ω)) : ConeJointIndex → ℝ)) =ᵐ[P]
        fun ω => coneJointFinite rp rs D I (circleProcess (hcirc ω)) :=
    fun I => ae_restrict_coneJoint _ (fun ω => circleProcess (hcirc ω)) hcoordH I
  -- the common family of finite-dimensional laws
  have hfam : ∀ I : Finset ConeJointIndex,
      P.map (fun ω => coneJointFinite rp rs D I (circleProcess (c ω))) =
        P.map (fun ω => coneJointFinite rp rs D I (circleProcess (hcirc ω))) := by
    intro I
    have hg : Measurable (coneJointFinite rp rs D I) :=
      measurable_coneJointFinite (fun φ hφ => (hD φ hφ).1) hrp_m hrs_m I
    calc P.map (fun ω => coneJointFinite rp rs D I (circleProcess (c ω)))
        = (P.map fun ω => circleProcess (c ω)).map (coneJointFinite rp rs D I) :=
          (Measure.map_map hg hqc).symm
      _ = (P.map fun ω => circleProcess (hcirc ω)).map (coneJointFinite rp rs D I) := by rw [hlaw]
      _ = P.map (fun ω => coneJointFinite rp rs D I (circleProcess (hcirc ω))) :=
          Measure.map_map hg hqh
  -- both joint laws are projective limits of the common family
  have hlimC : IsProjectiveLimit
      (P.map (fun ω => (Sum.elim (circleProcess (c ω))
        (lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)) : ConeJointIndex → ℝ)))
      (fun I => P.map (fun ω => coneJointFinite rp rs D I (circleProcess (c ω)))) := by
    intro I
    rw [(measurable_finRestrict I).aemeasurable.map_map_of_aemeasurable hVC]
    exact Measure.map_congr (hfinC I)
  have hlimH : IsProjectiveLimit
      (P.map (fun ω => (Sum.elim (circleProcess (hcirc ω))
        (lateralProcess (hC ω) (hcirc ω)) : ConeJointIndex → ℝ)))
      (fun I => P.map (fun ω => coneJointFinite rp rs D I (circleProcess (c ω)))) := by
    intro I
    rw [(measurable_finRestrict I).aemeasurable.map_map_of_aemeasurable hVH]
    exact (Measure.map_congr (hfinH I)).trans (hfam I).symm
  have : ∀ I : Finset ConeJointIndex,
      IsFiniteMeasure (P.map (fun ω => coneJointFinite rp rs D I (circleProcess (c ω)))) :=
    fun I => inferInstance
  have hmu := IsProjectiveLimit.unique hlimC hlimH
  -- split the joint vectors back into the pair of processes
  calc P.map (fun ω => (circleProcess (c ω), lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)))
      = (P.map (fun ω => (Sum.elim (circleProcess (c ω))
          (lateralProcess (fun φ => D φ (circleProcess (c ω))) (c ω)) : ConeJointIndex → ℝ))).map
          (fun x : ConeJointIndex → ℝ => ((fun p => x (Sum.inl p)), (fun o => x (Sum.inr o)))) :=
        (measurable_splitConeJoint.aemeasurable.map_map_of_aemeasurable hVC).symm
    _ = (P.map (fun ω => (Sum.elim (circleProcess (hcirc ω))
          (lateralProcess (hC ω) (hcirc ω)) : ConeJointIndex → ℝ))).map
          (fun x : ConeJointIndex → ℝ => ((fun p => x (Sum.inl p)), (fun o => x (Sum.inr o)))) := by
        rw [hmu]
    _ = P.map (fun ω => (circleProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) :=
        measurable_splitConeJoint.aemeasurable.map_map_of_aemeasurable hVH

/-- **Provider for `ConeLateralTransferStep` (chat 231 §6), with the radial codes as binders.** The radial pairing code
`rp` and the radial sphere code `rs` are z11's `radialPairingCode` and `radialSphereCode` (`S2y/ConeRadialCodes.lean`,
not yet committed). The binders `hpairAE` and `hsphereAE` are the a.s. identities of `radialPairingCode_ae_eq` and
`radialSphereCode_ae_eq`, for a field with the radial law. The rescaling uses the scaling input `hscale`; the circle
law equality is `hscale` applied to the rescaled circle process. -/
theorem coneLateralTransferStep_of_radialCodes
    (hscale : QuantumConeScalingInput)
    (rp : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (rs : ℝ → ℂ → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (hrp_m : ∀ φ, Measurable (rp φ)) (hrs_m : ∀ r z, Measurable (rs r z))
    (hpairAE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (c : Ω → ℝ → ℂ → ℝ),
      (∀ r z, 0 < r → Measurable fun ω => c ω r z) →
      (∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) →
      (∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν ∧
        P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν) →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
        ∀ᵐ ω ∂P, rp φ (circleProcess (c ω)) = ∫ x, φ x * c ω ‖x‖ 0)
    (hsphereAE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (c : Ω → ℝ → ℂ → ℝ),
      (∀ r z, 0 < r → Measurable fun ω => c ω r z) →
      (∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) →
      (∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν ∧
        P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν) →
      ∀ (r : ℝ) (z : ℂ), 0 < r →
        ∀ᵐ ω ∂P, rs r z (circleProcess (c ω)) = Real.circleAverage (fun x => c ω ‖x‖ 0) z r) :
    ConeLateralTransferStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc hP hQ b hb c D hcm hc hD
  have hqc : Measurable fun ω => circleProcess (c ω) := measurable_circleProcess_of hcm
  have hqh : Measurable fun ω => circleProcess (hcirc ω) :=
    measurable_circleProcess_of hQ.measurable_circle
  have hpos : ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b :=
    MatedCRT.Sec1.ae_coneScaleRadius_pos hscale hγ hγ2 hQ hb
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) := by
    filter_upwards [hQ.ae_continuousOn_circle, hc, hpos] with ω hω hcω hpω
    rw [hcω]
    exact continuousOn_rescaledCircle γ b _ hpω hω
  have hlaw : P.map (fun ω => circleProcess (c ω)) = P.map (fun ω => circleProcess (hcirc ω)) := by
    calc P.map (fun ω => circleProcess (c ω))
        = P.map (fun ω => circleProcess
            (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) :=
          Measure.map_congr (hc.mono fun ω hω => congrArg circleProcess hω)
      _ = P.map (fun ω => circleProcess (hcirc ω)) := hscale γ hγ hγ2 Ω P hC hcirc hP hQ b hb
  have hradC : ∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν ∧
      P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν := by
    obtain ⟨ν, hν, hrad⟩ := hQ.radial_law
    refine ⟨ν, hν, ?_⟩
    have e1 : ∀ h : ℝ → ℂ → ℝ, radialProcess h = radialOfCircle (circleProcess h) :=
      fun h => radialProcess_eq_radialOfCircle h
    calc P.map (fun ω => radialProcess (c ω))
        = P.map (fun ω => radialOfCircle (circleProcess (c ω))) := by simp only [e1]
      _ = (P.map fun ω => circleProcess (c ω)).map radialOfCircle :=
          (Measure.map_map measurable_radialOfCircle hqc).symm
      _ = (P.map fun ω => circleProcess (hcirc ω)).map radialOfCircle := by rw [hlaw]
      _ = P.map (fun ω => radialOfCircle (circleProcess (hcirc ω))) :=
          Measure.map_map measurable_radialOfCircle hqh
      _ = P.map (fun ω => radialProcess (hcirc ω)) := by simp only [e1]
      _ = quantumConeRadialLaw γ ν := hrad
  exact jointLateralLaw_of_circleLaw hP hQ hcm hcont hlaw D hD rp rs hrp_m hrs_m
    (hpairAE Ω P γ c hcm hcont hradC) (hpairAE Ω P γ hcirc hQ.measurable_circle hQ.ae_continuousOn_circle hQ.radial_law)
    (hsphereAE Ω P γ c hcm hcont hradC) (hsphereAE Ω P γ hcirc hQ.measurable_circle hQ.ae_continuousOn_circle hQ.radial_law)

/-- **`ConeFieldScalingStep` without `hpair` (chat 231 §7), with the circle decoder as a binder.** `hdec` is
`ConeCircleDecoderStep` (z1, `coneCircleDecoderStep_proved`, not yet committed); the lateral transfer is
`coneLateralTransferStep_of_radialCodes`. -/
theorem coneFieldScalingStep_proved_no_hpair
    (hscale : QuantumConeScalingInput) (hdec : ConeCircleDecoderStep)
    (rp : (ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (rs : ℝ → ℂ → (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ)
    (hrp_m : ∀ φ, Measurable (rp φ)) (hrs_m : ∀ r z, Measurable (rs r z))
    (hpairAE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (c : Ω → ℝ → ℂ → ℝ),
      (∀ r z, 0 < r → Measurable fun ω => c ω r z) →
      (∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) →
      (∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν ∧
        P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν) →
      ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ →
        ∀ᵐ ω ∂P, rp φ (circleProcess (c ω)) = ∫ x, φ x * c ω ‖x‖ 0)
    (hsphereAE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (c : Ω → ℝ → ℂ → ℝ),
      (∀ r z, 0 < r → Measurable fun ω => c ω r z) →
      (∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) →
      (∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν ∧
        P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν) →
      ∀ (r : ℝ) (z : ℂ), 0 < r →
        ∀ᵐ ω ∂P, rs r z (circleProcess (c ω)) = Real.circleAverage (fun x => c ω ‖x‖ 0) z r) :
    ConeFieldScalingStep :=
  coneFieldScalingStep_of_decoder hscale hdec
    (coneLateralTransferStep_of_radialCodes hscale rp rs hrp_m hrs_m hpairAE hsphereAE)

/-- **Provider for `ConeLateralTransferStep` (chat 231 §6), with the radial codes concrete.** The radial pairing code
`radialPairingCode` and the radial sphere code `radialSphereCode` are z11's (`S2y/ConeRadialCodes.lean`, sections 3a–3c:
`radialPairingCode_ae_eq` a.s. correct, committed 0c9e804; `radialSphereCode_ae_eq` committed 996e267, conditional on its
named input `hcircInt`). The one named input left is `hcircInt`: for every field with the radial law, the circle
integrand `θ ↦ |c(|z + r e^{iθ}|, 0)|` is a.s. interval integrable on `[0, 2π]`. It is not derived in the paper
(chat 231 §3.2 uses it without argument). -/
theorem coneLateralTransferStep_proved (hscale : QuantumConeScalingInput)
    (hcircInt : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (c : Ω → ℝ → ℂ → ℝ),
      (∀ r z, 0 < r → Measurable fun ω => c ω r z) →
      (∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) →
      (∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν ∧
        P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν) →
      ∀ r z, 0 < r → ∀ᵐ ω ∂P,
        IntervalIntegrable (fun θ : ℝ => |c ω ‖circleMap z r θ‖ 0|) MeasureTheory.volume 0 (2 * Real.pi)) :
    ConeLateralTransferStep :=
  coneLateralTransferStep_of_radialCodes hscale radialPairingCode radialSphereCode
    measurable_radialPairingCode measurable_radialSphereCode
    (fun _ _ _ _ _ hcm hcont hrad φ hφ => radialPairingCode_ae_eq hcm hcont hrad φ hφ)
    (fun Ω _ P γ c hcm hcont hrad _r z hr =>
      radialSphereCode_ae_eq_of_circInt hcm hcont hrad (hcircInt Ω P γ c hcm hcont hrad) hr z)

/-- **`ConeFieldScalingStep` without `hpair`, with the radial codes concrete (chat 231 §7).** Two named inputs remain:
the circle decoder `hdec : ConeCircleDecoderStep` (z1, `coneCircleDecoderStep_proved`, blocked on G1/G2, request 59a) and
the sphere-integrability input `hcircInt` of `coneLateralTransferStep_proved`. -/
theorem coneFieldScalingStep_proved_no_hpair_radial (hscale : QuantumConeScalingInput) (hdec : ConeCircleDecoderStep)
    (hcircInt : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (c : Ω → ℝ → ℂ → ℝ),
      (∀ r z, 0 < r → Measurable fun ω => c ω r z) →
      (∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) →
      (∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν ∧
        P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν) →
      ∀ r z, 0 < r → ∀ᵐ ω ∂P,
        IntervalIntegrable (fun θ : ℝ => |c ω ‖circleMap z r θ‖ 0|) MeasureTheory.volume 0 (2 * Real.pi)) :
    ConeFieldScalingStep :=
  coneFieldScalingStep_of_decoder hscale hdec (coneLateralTransferStep_proved hscale hcircInt)

end MatedCRT.LQGMeasure
