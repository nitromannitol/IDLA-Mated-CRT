import MatedCRT.Proofs.Sec2.LQGMeasureProperties.NonAtomicScaling
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.External.QuantumCone

/-!
# `ConeFieldScalingStep` (internal, eq:quantum-cone-scaling), from the cited law identity

`ConeFieldScalingStep` is an internal
obligation, a named hypothesis (see docs/campaign/COUNTED.md). The cited input is `QuantumConeScalingInput` (DMS14 Proposition 4.13(i),
arXiv:1409.7055v4), which gives the law identity of the circle average processes.

Proved here, from `QuantumConeScalingInput`:
* the cone scale radius `R_b` is a.s. positive and a.s. equal to a measurable `R'`
  (`MatedCRT.Sec1.ae_coneScaleRadius_pos`, `MatedCRT.Sec1.aemeasurable_coneScaleRadius`);
* a measurable positive-circle version `c` of the rescaled circle process
  `(r, z) ↦ h_{R_b r}(R_b z) + Q log R_b - γ⁻¹ log b` (`exists_measurable_rescaledCircle_version`): the circle process
  is a.s. continuous in `(r, z)` and measurable in `ω` at each point, so it is jointly measurable on the good set
  (Carathéodory: `measurable_uncurry_of_continuous_of_measurable`).

Named input of `coneFieldScalingStep_proved`, the same-carrier pairing realization (`hpair`): for a measurable version
`c` of the rescaled circle process, some pairing `hC'` on the same probability space makes `(hC', c)` a quantum cone.
This is the remaining internal content of the verdict row ("the same-carrier measurable realization and reconstruction
of pairings from the rescaled circle process are internal work"). The repository proves it only for a `MatedCRTEnv`
(`RescaledConeFieldStep`, Proofs/Sec1/EnvironmentScaling.lean:113, via `exists_rescaled_pairing`,
Proofs/Sec1/EnvironmentScaling/Field.lean:1081), which needs `S.IsValid` and a distribution-valued version. It is not
written in the paper or its corrected copy for a general quantum cone, so it stays a hypothesis.
-/

namespace MatedCRT.LQGMeasure

open MeasureTheory Set Filter Topology
open HarmonicBalls

/-- A measurable set `G` of full measure, on which the circle average process is continuous on `(0, ∞) × ℂ` and the
cone scale radius is positive and equal to a measurable version `R'`. -/
theorem exists_good_set_rescaled {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ b : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hscale : QuantumConeScalingInput)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hcone : IsQuantumCone γ P hC hcirc) (hb : 0 < b) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∃ R' : Ω → ℝ, Measurable R' ∧ ∀ ω ∈ G,
      ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
        0 < coneScaleRadius γ (hcirc ω) b ∧ R' ω = coneScaleRadius γ (hcirc ω) b := by
  have hpos := MatedCRT.Sec1.ae_coneScaleRadius_pos hscale hγ hγ2 hcone hb
  have hae := MatedCRT.Sec1.aemeasurable_coneScaleRadius hcone hpos
  obtain ⟨R', hR'm, hR'eq⟩ := hae
  have hgood : ∀ᵐ ω ∂P, (ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      0 < coneScaleRadius γ (hcirc ω) b) ∧ coneScaleRadius γ (hcirc ω) b = R' ω := by
    filter_upwards [hcone.ae_continuousOn_circle, hpos, hR'eq] with ω h1 h2 h3
    exact ⟨⟨h1, h2⟩, h3⟩
  obtain ⟨t, hEt, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  refine ⟨tᶜ, htm.compl, by rw [compl_compl]; exact ht0, R', hR'm, fun ω hω => ?_⟩
  have hg : (ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      0 < coneScaleRadius γ (hcirc ω) b) ∧ coneScaleRadius γ (hcirc ω) b = R' ω := by
    by_contra hn
    exact hω (hEt hn)
  exact ⟨hg.1.1, hg.1.2, hg.2.symm⟩

/-- **Measurable positive-circle version of the rescaled circle process** (`c` is a.s. equal to `rescaledCircle` with the
cone scale radius, and each `c · r z` is measurable for `r > 0`). -/
theorem exists_measurable_rescaledCircle_version {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ b : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hscale : QuantumConeScalingInput) (hγ : 0 < γ) (hγ2 : γ < 2) (hcone : IsQuantumCone γ P hC hcirc)
    (hb : 0 < b) :
    ∃ c : Ω → ℝ → ℂ → ℝ, (∀ r z, 0 < r → Measurable fun ω => c ω r z) ∧
      ∀ᵐ ω ∂P, c ω = rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b := by
  classical
  obtain ⟨G, hGm, hG0, R', hR'm, hG⟩ := exists_good_set_rescaled hscale hγ hγ2 hcone hb
  -- a strictly positive measurable version of the radius (equal to `R'` on `G`)
  set Rp : Ω → ℝ := fun ω => if 0 < R' ω then R' ω else 1 with hRp
  have hRpm : Measurable Rp :=
    Measurable.ite (measurableSet_lt measurable_const hR'm) hR'm measurable_const
  have hRp_pos : ∀ ω, 0 < Rp ω := by
    intro ω
    simp only [hRp]
    split_ifs with h
    · exact h
    · exact one_pos
  have hRp_eq : ∀ ω ∈ G, Rp ω = coneScaleRadius γ (hcirc ω) b := by
    intro ω hω
    obtain ⟨_, h1, h2⟩ := hG ω hω
    have hR : 0 < R' ω := by rw [h2]; exact h1
    simp only [hRp, hR, ↓reduceIte]
    exact h2
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hG0
  -- the field `(p, ω) ↦ hcirc ω p` on `G`, continuous in the spatial variable `p ∈ (0, ∞) × ℂ`
  let F : Ioi (0 : ℝ) × ℂ → Ω → ℝ := fun p ω => if ω ∈ G then hcirc ω p.1.1 p.2 else 0
  have hFc : ∀ ω, Continuous fun p : Ioi (0 : ℝ) × ℂ => F p ω := by
    intro ω
    by_cases hω : ω ∈ G
    · have hcont := (hG ω hω).1
      have hmaps : Continuous fun p : Ioi (0 : ℝ) × ℂ => ((p.1 : ℝ), p.2) :=
        (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
      have key := hcont.comp_continuous hmaps (fun p => mk_mem_prod p.1.2 (mem_univ _))
      show Continuous fun p : Ioi (0 : ℝ) × ℂ => if ω ∈ G then hcirc ω p.1.1 p.2 else 0
      simp only [hω, ↓reduceIte]
      exact key
    · show Continuous fun p : Ioi (0 : ℝ) × ℂ => if ω ∈ G then hcirc ω p.1.1 p.2 else 0
      simp only [hω, ↓reduceIte]
      exact continuous_const
  have hFm : ∀ p : Ioi (0 : ℝ) × ℂ, Measurable fun ω => F p ω := by
    intro p
    exact Measurable.ite hGm (hcone.measurable_circle p.1.1 p.2 p.1.2) measurable_const
  have hU : Measurable (Function.uncurry F) := measurable_uncurry_of_continuous_of_measurable hFc hFm
  refine ⟨fun ω r z => if ω ∈ G then rescaledCircle γ (hcirc ω) (Rp ω) b r z else 0, ?_, ?_⟩
  · intro r z hr
    let q : Ω → Ioi (0 : ℝ) × ℂ := fun ω => (⟨Rp ω * r, mul_pos (hRp_pos ω) hr⟩, (Rp ω : ℂ) * z)
    have hq : Measurable q :=
      Measurable.prodMk (Measurable.subtype_mk (hRpm.mul_const r))
        ((Complex.measurable_ofReal.comp hRpm).mul_const z)
    have hA : Measurable fun ω => F (q ω) ω :=
      hU.comp (hq.prodMk measurable_id)
    have hK : Measurable fun ω => lqgQ γ * Real.log (Rp ω) - γ⁻¹ * Real.log b :=
      ((Real.measurable_log.comp hRpm).const_mul _).sub measurable_const
    have heq : (fun ω => if ω ∈ G then rescaledCircle γ (hcirc ω) (Rp ω) b r z else 0) =
        fun ω => if ω ∈ G then F (q ω) ω + (lqgQ γ * Real.log (Rp ω) - γ⁻¹ * Real.log b) else 0 := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [hω, ↓reduceIte, F, q, rescaledCircle]
        ring
      · simp only [hω, ↓reduceIte]
    rw [heq]
    exact Measurable.ite hGm (hA.add hK) measurable_const
  · filter_upwards [hGae] with ω hωG
    simp only [hωG, ↓reduceIte]
    funext r z
    rw [hRp_eq ω hωG]

/-- **`ConeFieldScalingStep` (eq:quantum-cone-scaling; DMS14 Proposition 4.13(i)), proved from the cited law identity
`QuantumConeScalingInput` and the named same-carrier pairing realization `hpair`.** For each `b > 0`, the rescaled
circle process has a measurable version `c`, and `hpair` gives a pairing `hC'` with `IsQuantumCone γ P hC' c`. `hpair`
is the named hypothesis, written out in the signature (the pairing half of `ConeFieldScalingStep` for a given version). -/
theorem coneFieldScalingStep_proved
    (hscale : QuantumConeScalingInput)
    (hpair : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P →
      IsQuantumCone γ P hC hcirc → ∀ b : ℝ, 0 < b → ∀ c : Ω → ℝ → ℂ → ℝ,
        (∀ r z, 0 < r → Measurable fun ω => c ω r z) →
        (∀ᵐ ω ∂P, c ω = rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) →
        ∃ hC' : Ω → (ℂ → ℝ) → ℝ, IsQuantumCone γ P hC' c) :
    ConeFieldScalingStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc hP hcone b hb
  have := hP
  obtain ⟨c, hcm, hc⟩ := exists_measurable_rescaledCircle_version hscale hγ hγ2 hcone hb
  obtain ⟨hC', hq⟩ := hpair γ hγ hγ2 Ω P hC hcirc hP hcone b hb c hcm hc
  exact ⟨hC', c, hq, hc⟩

end MatedCRT.LQGMeasure

#print axioms MatedCRT.LQGMeasure.exists_measurable_rescaledCircle_version
#print axioms MatedCRT.LQGMeasure.coneFieldScalingStep_proved
