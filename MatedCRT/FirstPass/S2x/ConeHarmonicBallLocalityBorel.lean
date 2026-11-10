import MatedCRT.FirstPass.S2x.ConeHarmonicBallLocality
import MatedCRT.FirstPass.Frozen.S1c

/-!
# Borel replacement for the locality Step `ConeHarmonicBallLocalityStep` (fp-S2x-hM-replacement)

**`hA` RETIRED** (operator, chat 223; notes/fp-gaps/CHATGPT-223-idla-z9-hA-analytic-PRO.md): `hA` is FALSE as typed, so the
route below is not a proof of the Step. The Step is proved with `S = Set.univ` and no `hA` by
`coneHarmonicBallLocalityStep_of_univ` (FirstPass/S2x/ConeHarmonicBallLocalityUniv.lean). Do not use `hA` or
`coneHarmonicBallLocalityStep_of_borel` as an input.

`coneHarmonicBallLocalityStep_of_locality` (ConeHarmonicBallLocality.lean) reduces `ConeHarmonicBallLocalityStep` to a
measurability hypothesis `hM` on the raw set `coneHarmonicBallSet γ ⊆ (UnitBallCircle → ℝ)`. That hypothesis is false as
typed: membership is not decided by countably many coordinates, so the raw set is not product-measurable (CHATGPT-213 PRO
audit, section 3). This file proves the Step without `hM`, by the countable-code / analytic / Borel-representative route
of that audit (section 3, steps 1-7):

* a dense sequence `codeSeq` in `UnitBallCircle` codes a raw function `f` by `codeMap f = (f (codeSeq n))_n`, and `codeMap`
  is product-measurable;
* the coded event is analytic: hypothesis `hA` (the internal coding step, not yet proved);
* `FrozenUniversalMeasurabilityOfAnalytic` gives a Borel representative `B` of the analytic code set, modulo the code law
  of a reference restriction law `μ0`; `S = codeMap ⁻¹' B` is product-measurable and agrees with the raw set `μ0`-a.e.;
* `ConeRestrictionStep` makes the restriction law of every quantum cone and of every whole-plane GFF equal to `μ0`, so one
  set `S` serves both clauses of the Step.

The locality input `hL` (HB22 Proposition 1.3, measure form) enters as in `coneHarmonicBallLocalityStep_of_locality`.
Nothing frozen is edited. Hypotheses beyond `hL`, `FrozenUniversalMeasurabilityOfAnalytic` and `ConeRestrictionStep`:
`hQ` (existence of a quantum cone for each `γ`, which also gives a whole-plane GFF through `IsQuantumCone.lateral_law`) and
`hA` (analytic coding). See the docstring of `coneHarmonicBallLocalityStep_of_borel`.
-/

namespace MatedCRT.FirstPass2x

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open _root_.HarmonicBalls

/-- `UnitBallCircle` is nonempty: the circle of radius `1/2` about `0` lies in `B_1`. -/
instance unitBallCircle_nonempty : Nonempty UnitBallCircle :=
  ⟨⟨(⟨(1 / 2 : ℝ), by norm_num⟩, (0 : ℂ)), Metric.closedBall_subset_ball (by norm_num)⟩⟩

/-- A dense sequence in `UnitBallCircle`: the countable carrier of the code (CHATGPT-213 PRO, section 3, step 1). -/
noncomputable def codeSeq : ℕ → UnitBallCircle :=
  Classical.choose (TopologicalSpace.exists_dense_seq UnitBallCircle)

/-- The countable code of a raw function `f : UnitBallCircle → ℝ`: its values on the dense sequence `codeSeq`. -/
noncomputable def codeMap (f : UnitBallCircle → ℝ) : ℕ → ℝ := fun n => f (codeSeq n)

/-- The code map is measurable for the product σ-algebra on both sides (coordinate evaluations). -/
theorem measurable_codeMap : Measurable codeMap :=
  Measurable.of_eval fun n => measurable_pi_apply (codeSeq n)

/-- **Borel representative modulo a common law (CHATGPT-213 PRO, section 3, steps 4-6).** If an analytic set `A` of codes
represents the raw set `E` modulo a finite measure `μ0` on `UnitBallCircle → ℝ`, then `E` agrees `μ0`-a.e. with a
product-measurable set. Proof: `FrozenUniversalMeasurabilityOfAnalytic` applied to the code law `μ0.map codeMap` gives a
Borel representative `B` of `A`; then `S = codeMap ⁻¹' B`. -/
theorem exists_measurable_ae_eq_of_codeMap
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    {μ0 : Measure (UnitBallCircle → ℝ)} [IsFiniteMeasure μ0]
    {E : Set (UnitBallCircle → ℝ)} {A : Set (ℕ → ℝ)} (hAn : AnalyticSet A)
    (hEA : E =ᵐ[μ0] codeMap ⁻¹' A) :
    ∃ S : Set (UnitBallCircle → ℝ), MeasurableSet S ∧ E =ᵐ[μ0] S := by
  obtain ⟨B, hB, hAB⟩ := hU (ℕ → ℝ) (μ0.map codeMap) inferInstance A hAn
  refine ⟨codeMap ⁻¹' B, measurable_codeMap hB, ?_⟩
  have hpre : ∀ᵐ x ∂μ0, (codeMap x ∈ A ↔ codeMap x ∈ B) :=
    ae_of_ae_map (p := fun y => y ∈ A ↔ y ∈ B) measurable_codeMap.aemeasurable
      (hAB.mono fun _ hy => Iff.of_eq hy)
  have hEq : codeMap ⁻¹' A =ᵐ[μ0] codeMap ⁻¹' B := hpre.mono fun x hx => propext hx
  exact hEA.trans hEq

/-- A random element whose law `P.map X` agrees a.e. with `S` on `E` is, almost surely, in `E` iff in `S`. -/
theorem ae_mem_iff_of_ae_eq_map {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → (UnitBallCircle → ℝ)} (hX : AEMeasurable X P) {E S : Set (UnitBallCircle → ℝ)}
    (hES : E =ᵐ[P.map X] S) : ∀ᵐ ω ∂P, X ω ∈ E ↔ X ω ∈ S :=
  ae_of_ae_map (p := fun y => y ∈ E ↔ y ∈ S) hX (hES.mono fun _ hy => Iff.of_eq hy)

/-- The restriction `ω ↦ unitBallCircleProcess (hcirc ω)` of a quantum cone is a random variable (`measurable_circle`). -/
theorem measurable_unitBallCircleProcess_of_quantumCone {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    Measurable fun ω => unitBallCircleProcess (hcirc ω) :=
  Measurable.of_eval fun p => h.measurable_circle _ _ p.1.1.2

/-- The restriction `ω ↦ unitBallCircleProcess (fieldCircleAverage γ (hcirc ω))` of a whole-plane GFF is a random variable:
`hcirc ω r z` is measurable (`IsWholePlaneGFF.measurable_circle`) and `fieldCircleAverage` subtracts a deterministic term. -/
theorem measurable_unitBallCircleProcess_of_wholePlane {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) :
    Measurable fun ω => unitBallCircleProcess (fieldCircleAverage γ (hcirc ω)) :=
  Measurable.of_eval fun p => by
    unfold unitBallCircleProcess fieldCircleAverage
    exact (h.measurable_circle _ _ p.1.1.2).sub_const _

/-- **`ConeHarmonicBallLocalityStep` without the false measurability `hM`** (fp-S2x-hM-replacement). For `γ ∈ (0, 2)` one
measurable set `S` of restrictions to `B_1` works for the quantum cone and for `h^ℂ - γ log |·|` (Step
`ConeHarmonicBallLocalityStep`, Steps/Sec2/ConeHarmonicBallsUpToFixedTime.lean:94). Inputs:
* `hL`: harmonic balls depend on the measure only through its restriction to `B_1` (HB22 Proposition 1.3; the locality
  hypothesis of `coneHarmonicBallLocalityStep_of_locality`; z12 proves it in S2x/ConeHarmonicBallLocalityL.lean);
* `hU = FrozenUniversalMeasurabilityOfAnalytic` (Kechris 21.10);
* `hR = ConeRestrictionStep` (IR-A1: the restriction laws of cone and whole-plane fields agree);
* `hQ`: for each `γ ∈ (0, 2)` there is a quantum cone (existence; the lateral part of a cone gives a whole-plane GFF);
* `hA`: the coded event is analytic modulo the whole-plane restriction law. This is the internal coding step of CHATGPT-213
  section 3 (step 3, the set of codes admitting witnesses `ν, T, Λ` is analytic), which no source states; it is NOT proved here. RETIRED: `hA` is false as typed (module docstring).
`ConeHarmonicBallLocalityStep` is not used as an input (ruling 43(c)). -/
theorem coneHarmonicBallLocalityStep_of_borel
    (hL : ∀ ν ν' : Measure ℂ, ν.restrict (ball 0 1) = ν'.restrict (ball 0 1) →
      (HasConeHarmonicBallsUpToHalfBall ν ↔ HasConeHarmonicBallsUpToHalfBall ν'))
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hR : ConeRestrictionStep)
    (hQ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P ∧ IsQuantumCone γ P hC hcirc)
    (hA : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ A : Set (ℕ → ℝ), AnalyticSet A ∧
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
        (hcirc' : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → IsWholePlaneGFF P' hC' hcirc' →
        coneHarmonicBallSet γ =ᵐ[P'.map (fun ω => unitBallCircleProcess (fieldCircleAverage γ (hcirc' ω)))]
          codeMap ⁻¹' A) :
    ConeHarmonicBallLocalityStep := by
  intro γ hγ0 hγ2
  obtain ⟨A, hAn, hAeq⟩ := hA γ hγ0 hγ2
  obtain ⟨Ωc, mΩc, Pc, hCc, hcircc, hPc, hQc⟩ := hQ γ hγ0 hγ2
  obtain ⟨Ωw, mΩw, Pw, hCw, hcircw, hPw, hWw, -⟩ := hQc.lateral_law
  -- the reference restriction law: the law of the restriction of the chosen quantum cone
  set μ0 : Measure (UnitBallCircle → ℝ) := Pc.map (fun ω => unitBallCircleProcess (hcircc ω)) with hμ0
  have : IsProbabilityMeasure μ0 := by
    rw [hμ0]
    infer_instance
  -- every quantum cone and every whole-plane GFF restricts to the law μ0 (ConeRestrictionStep through the cone Pc)
  have hconeLaw : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      P.map (fun ω => unitBallCircleProcess (hcirc ω)) = μ0 := by
    intro Ω _ P hC hcirc hP hQ'
    exact (hR γ hγ0 hγ2 Ω P hC hcirc hP hQ' Ωw Pw hCw hcircw hPw hWw).trans
      (hR γ hγ0 hγ2 Ωc Pc hCc hcircc hPc hQc Ωw Pw hCw hcircw hPw hWw).symm
  have hwpLaw : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
      P.map (fun ω => unitBallCircleProcess (fieldCircleAverage γ (hcirc ω))) = μ0 := by
    intro Ω _ P hC hcirc hP hW
    exact (hR γ hγ0 hγ2 Ωc Pc hCc hcircc hPc hQc Ω P hC hcirc hP hW).symm
  -- the coded event is analytic modulo μ0; a measurable representative S
  have hEμ : coneHarmonicBallSet γ =ᵐ[μ0] codeMap ⁻¹' A := by
    have h := hAeq Ωw Pw hCw hcircw hPw hWw
    rw [hwpLaw Ωw Pw hCw hcircw hPw hWw] at h
    exact h
  obtain ⟨S, hSm, hES⟩ := exists_measurable_ae_eq_of_codeMap hU hAn hEμ
  refine ⟨S, hSm, ?_, ?_⟩
  · -- clause for the quantum cone
    intro Ω _ P hC hcirc μ hcone
    obtain ⟨hP, hQ', hL'⟩ := hcone
    have hraw : ∀ᵐ ω ∂P, HasConeHarmonicBallsUpToHalfBall (μ ω) ↔
        unitBallCircleProcess (hcirc ω) ∈ coneHarmonicBallSet γ := by
      have hω0 : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hL'
      filter_upwards [hω0] with ω hω
      constructor
      · intro hE
        exact ⟨hcirc ω, rfl, μ ω, hω, hE⟩
      · rintro ⟨c, hc, ν, hν, hνE⟩
        exact (hL (μ ω) ν (lqgLimit_restrict_ball_eq hω hν hc.symm)).2 hνE
    have hlaw := hconeLaw Ω P hC hcirc hP hQ'
    have hX : AEMeasurable (fun ω => unitBallCircleProcess (hcirc ω)) P :=
      (measurable_unitBallCircleProcess_of_quantumCone hQ').aemeasurable
    have hES' : coneHarmonicBallSet γ =ᵐ[P.map (fun ω => unitBallCircleProcess (hcirc ω))] S := by
      rw [hlaw]
      exact hES
    filter_upwards [hraw, ae_mem_iff_of_ae_eq_map hX hES'] with ω h1 h2
    exact h1.trans h2
  · -- clause for h^ℂ - γ log |·| (whole-plane GFF with the LQG measure)
    intro Ω _ P hC hcirc μ hP hW hcone
    have hraw : ∀ᵐ ω ∂P, HasConeHarmonicBallsUpToHalfBall (μ ω) ↔
        unitBallCircleProcess (fieldCircleAverage γ (hcirc ω)) ∈ coneHarmonicBallSet γ := by
      have hω0 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage γ (hcirc ω)) (μ ω) := hcone
      filter_upwards [hω0] with ω hω
      constructor
      · intro hE
        exact ⟨fieldCircleAverage γ (hcirc ω), rfl, μ ω, hω, hE⟩
      · rintro ⟨c, hc, ν, hν, hνE⟩
        exact (hL (μ ω) ν (lqgLimit_restrict_ball_eq hω hν hc.symm)).2 hνE
    have hlaw := hwpLaw Ω P hC hcirc hP hW
    have hX : AEMeasurable (fun ω => unitBallCircleProcess (fieldCircleAverage γ (hcirc ω))) P :=
      (measurable_unitBallCircleProcess_of_wholePlane hW).aemeasurable
    have hES' : coneHarmonicBallSet γ =ᵐ[P.map (fun ω => unitBallCircleProcess (fieldCircleAverage γ (hcirc ω)))] S := by
      rw [hlaw]
      exact hES
    filter_upwards [hraw, ae_mem_iff_of_ae_eq_map hX hES'] with ω h1 h2
    exact h1.trans h2

end MatedCRT.FirstPass2x
