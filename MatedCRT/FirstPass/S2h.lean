import MatedCRT.FirstPass.S2g.Family
import MatedCRT.FirstPass.Frozen.S1c
import MatedCRT.FirstPass.Frozen.S2h
import MatedCRT.FirstPass.S2h.LeastSuper
import MatedCRT.FirstPass.S2h.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Cone bad null hull: reduction to two measurable null hulls (fp-S2h, z1)

Owner: z1 (task fp-S2h-cone-bad-null-hull). Target: `ConeBadNullHullStep` (FirstPass/S2g/Family.lean) and
`ConeClosureGoodMeasureLawStep` (FirstPass/S2f.lean).

The bad set of `BadMeasureNullHull` is the union of two sets of measures:
* `{ν | HasRatPlateauCert ν}` (certificate part; written argument: notes/fp-gaps/CHATGPT-cone-good-set.md
  Sections 1-3, 5, 6);
* `{ν | ¬ LeastSuperOK ν}` (least-supersolution part; NO measure-level written argument, see
  `ConeLeastSuperNullHullStep`).

This file proves the code bridge `nullHull_of_analytic_code` (a Lusin-type code set gives a measurable null hull on
`Measure ℂ`) and the union lemma, and reduces `ConeBadNullHullStep` and `ConeClosureGoodMeasureLawStep` to the two
open steps. Nothing here is frozen; the open steps are NEW.
-/

namespace MatedCRT

open MeasureTheory Set Filter Metric HarmonicBalls

/-- A union of two measurable null hulls is a measurable null hull. -/
theorem nullHull_union {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    {A₁ A₂ : Set (Measure ℂ)}
    (h₁ : ∃ N : Set (Measure ℂ), MeasurableSet N ∧ A₁ ⊆ N ∧ P (μ ⁻¹' N) = 0)
    (h₂ : ∃ N : Set (Measure ℂ), MeasurableSet N ∧ A₂ ⊆ N ∧ P (μ ⁻¹' N) = 0) :
    ∃ N : Set (Measure ℂ), MeasurableSet N ∧ A₁ ∪ A₂ ⊆ N ∧ P (μ ⁻¹' N) = 0 := by
  obtain ⟨N₁, hN₁, hs₁, h₀₁⟩ := h₁
  obtain ⟨N₂, hN₂, hs₂, h₀₂⟩ := h₂
  refine ⟨N₁ ∪ N₂, hN₁.union hN₂, Set.union_subset_union hs₁ hs₂, ?_⟩
  rw [Set.preimage_union]
  exact measure_union_null h₀₁ h₀₂

/-- **Code bridge (fp-S2h).** Let `f` be a measurable code of measures with values in `ℕ → ℝ`, and let `A` be a set
of measures whose codes lie in an analytic set `B` of codes. Suppose the code event `{ω | f (μ ω) ∈ B}` lies in a
measurable `P`-null set `M`. Then `A` has a measurable null hull on `Measure ℂ`. The proof uses Lusin's theorem
(`FrozenUniversalMeasurabilityOfAnalytic`: an analytic set is null-measurable for every finite measure) for the law
of the codes: `B` agrees a.e. with a measurable `S`, and the discrepancy set `D` is covered by a measurable null set `T`. -/
theorem nullHull_of_analytic_code {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (μ : Ω → Measure ℂ) (f : Measure ℂ → (ℕ → ℝ))
    (hf : Measurable f) (hμ : Measurable fun ω => f (μ ω)) (A : Set (Measure ℂ)) (B : Set (ℕ → ℝ))
    (hBa : AnalyticSet B) (hAB : A ⊆ f ⁻¹' B) (M : Set Ω) (hM0 : P M = 0)
    (hcov : ∀ ω, f (μ ω) ∈ B → ω ∈ M) :
    ∃ N : Set (Measure ℂ), MeasurableSet N ∧ A ⊆ N ∧ P (μ ⁻¹' N) = 0 := by
  have : IsProbabilityMeasure (P.map fun ω => f (μ ω)) :=
    (Measure.isProbabilityMeasure_map_iff hμ.aemeasurable).mpr inferInstance
  have hnull : NullMeasurableSet B (P.map fun ω => f (μ ω)) :=
    hF1 (ℕ → ℝ) (P.map fun ω => f (μ ω)) inferInstance B hBa
  obtain ⟨S, hS, hBS⟩ := hnull
  have hD : (P.map fun ω => f (μ ω)) {x | ¬ (x ∈ B ↔ x ∈ S)} = 0 := by
    refine measure_mono_null (fun x hx => fun heq => hx (eq_iff_iff.mp heq)) (ae_iff.1 hBS)
  have hT : P ((fun ω => f (μ ω)) ⁻¹' toMeasurable (P.map fun ω => f (μ ω)) {x | ¬ (x ∈ B ↔ x ∈ S)}) = 0 := by
    rw [← Measure.map_apply hμ (measurableSet_toMeasurable _ _), measure_toMeasurable]
    exact hD
  refine ⟨f ⁻¹' (S ∪ toMeasurable (P.map fun ω => f (μ ω)) {x | ¬ (x ∈ B ↔ x ∈ S)}),
    hf (hS.union (measurableSet_toMeasurable _ _)), ?_, ?_⟩
  · intro ν hν
    have hBν : f ν ∈ B := hAB hν
    by_cases hSν : f ν ∈ S
    · exact Or.inl hSν
    · exact Or.inr (subset_toMeasurable _ _ (fun hiff => hSν (hiff.mp hBν)))
  · refine measure_mono_null ?_ (measure_union_null hM0 hT)
    intro ω hω
    by_cases hB : f (μ ω) ∈ B
    · exact Or.inl (hcov ω hB)
    · refine Or.inr ?_
      have h' : f (μ ω) ∈ S ∪ toMeasurable (P.map fun ω => f (μ ω)) {x | ¬ (x ∈ B ↔ x ∈ S)} := hω
      rcases h' with h | h
      · exact subset_toMeasurable _ _ (show f (μ ω) ∈ {x | ¬ (x ∈ B ↔ x ∈ S)} from fun hiff => hB (hiff.mpr h))
      · exact h

/-- **OPEN (NEW; z1, fp-S2h).** The certificate part of the bad set has a measurable null hull for every cone field:
the measures with a rational plateau pair of certificates are covered by a measurable set of `Measure ℂ` whose
preimage under the field is `P`-null. Written argument: notes/fp-gaps/CHATGPT-cone-good-set.md Sections 1-3 (Borel
relation of certificate codes, analytic projection), 5 (plateau radii, Tonelli, scaling, zero law), 5.4 (transfer to
the cone), 6 (null hull). Not proved here. -/
def ConeCertificateNullHullStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∃ N : Set (Measure ℂ), MeasurableSet N ∧ {ν | HasRatPlateauCert ν} ⊆ N ∧ P (μ ⁻¹' N) = 0

/-- **OPEN (NEW, NO WRITTEN MEASURE-LEVEL ARGUMENT; z1, fp-S2h).** The least-supersolution part of the bad set has a
measurable null hull for every cone field: the measures `ν` for which `leastSupersolution ν (3/4) 0 s` is not a
supersolution for some `s > 0` are covered by a measurable set of `Measure ℂ` with `P`-null preimage. The source
(HB Draft `LeastSupersolutionMemStmt`, harmonic-balls-lqg `HarmonicBalls/Draft/Section3.lean:47`) is only an
almost-sure statement `∀ᵐ ω, ...` for the LQG measure; an almost-sure property of `μ ω` does not give a measurable
superset in `Measure ℂ` (CHATGPT-cone-good-set.md Section 8, bullet "almost-sure closure theorem alone"). Not proved. -/
def ConeLeastSuperNullHullStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∃ N : Set (Measure ℂ), MeasurableSet N ∧ {ν | ¬ LeastSuperOK ν} ⊆ N ∧ P (μ ⁻¹' N) = 0

/-- **Reduction (fp-S2h).** The two open parts give the bad null hull `ConeBadNullHullStep`. -/
theorem coneBadNullHull_of_parts (hc : ConeCertificateNullHullStep) (hl : ConeLeastSuperNullHullStep) :
    ConeBadNullHullStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  have h := nullHull_union P μ (hc γ hγ hγ2 Ω P hC hcirc μ hcone) (hl γ hγ hγ2 Ω P hC hcirc μ hcone)
  unfold BadMeasureNullHull
  rw [Set.ofPred_or]
  exact h

/-- **Reduction (fp-S2h).** `ConeClosureGoodMeasureLawStep` (FirstPass/S2f.lean) from the two open parts. -/
theorem coneClosureGoodMeasureLawStep_of_parts (hpole : FrozenGreenDiscPole) (hc : ConeCertificateNullHullStep)
    (hl : ConeLeastSuperNullHullStep) : ConeClosureGoodMeasureLawStep :=
  coneClosureGoodMeasureLawStep_of_badNullHull hpole (coneBadNullHull_of_parts hc hl)

/-- Moment code of a measure on the test family `φs`: `k ↦ ∫ φs k dν`. -/
noncomputable def localCode (φs : ℕ → ℂ → ℝ) (ν : Measure ℂ) : ℕ → ℝ := fun k => ∫ x, φs k x ∂ν

/-- The moment code is Giry-measurable for continuous test functions (fp-S2h; the measurability of `ν ↦ ∫ φ dν`
is `measurable_integral_measure_real`, FirstPass/S2h/MeasurableIntegral.lean). -/
theorem measurable_localCode {φs : ℕ → ℂ → ℝ} (hcont : ∀ k, Continuous (φs k)) :
    Measurable (localCode φs) :=
  Measurable.of_eval fun k => measurable_integral_measure_real (hcont k).measurable

/-- Code bridge against a law (fp-S2h): if the code law of `μ` gives the code set `B` null mass, and the certificate
measures with finite mass have codes in `B`, then the certificate measures have a measurable null hull. No measurability
of `B` is needed: `toMeasurable` gives the measurable superset with the same outer mass. -/
theorem nullHull_of_code_law {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ) {X : Type}
    [MeasurableSpace X] (f : Measure ℂ → X) (hf : Measurable f) (hμ : Measurable fun ω => f (μ ω))
    (A : Set (Measure ℂ)) (B : Set X) (hAB : A ⊆ f ⁻¹' B) (hB : (P.map fun ω => f (μ ω)) B = 0) :
    ∃ N : Set (Measure ℂ), MeasurableSet N ∧ A ⊆ N ∧ P (μ ⁻¹' N) = 0 := by
  refine ⟨f ⁻¹' toMeasurable (P.map fun ω => f (μ ω)) B, hf (measurableSet_toMeasurable _ _),
    fun ν hν => Set.preimage_mono (subset_toMeasurable _ _) (hAB hν), ?_⟩
  show P ((fun ω => f (μ ω)) ⁻¹' toMeasurable (P.map fun ω => f (μ ω)) B) = 0
  rw [← Measure.map_apply hμ (measurableSet_toMeasurable _ _), measure_toMeasurable]
  exact hB

/-- A measure on `ℂ` is locally finite when it has finite mass on every closed disc `B̄_n` (the LQG measure of the cone
field lies in this class almost surely, `IsLQGLimit.isLocallyFiniteMeasure`). -/
def LocFinMeasure (ν : Measure ℂ) : Prop := ∀ n : ℕ, ν (closedBall (0 : ℂ) n) < ⊤

/-- Admissible test family of the certificate code: each `φs k` is continuous and nonnegative (the restricted moments of
CHATGPT (12) are suprema of nonnegative moments; signed tests are recovered by linearity), with compact support in `B(0,1)`. -/
def CertTestFamily (φs : ℕ → ℂ → ℝ) : Prop :=
  ∀ k, Continuous (φs k) ∧ HasCompactSupport (φs k) ∧ tsupport (φs k) ⊆ Metric.ball 0 1 ∧ ∀ x, 0 ≤ φs k x

/-- **OPEN (NEW; z1, fp-S2h).** The certificate code set for the family `φs`: an analytic set `B` of moment codes such
that, for every locally finite measure `ν`, having a rational plateau pair of certificates is equivalent to the moment code
`localCode φs ν` lying in `B`. Repaired in round 6 (the earlier form quantified over all `ν` of finite mass on `B̄_{3/4}`
with an arbitrary `φs`, which fails for `φs = 0`; the family must also carry the cutoff coordinates of CHATGPT (12), and
the iff needs local finiteness). The family is chosen in `CertCodeNullStep`. Written argument:
notes/fp-gaps/CHATGPT-cone-good-set.md Sections 1-3 (countable tests, restricted moments (12), the Borel relation of
Section 3, analytic projection). Not proved. -/
def CertCodeExactStep (φs : ℕ → ℂ → ℝ) (B : Set (ℕ → ℝ)) : Prop :=
  AnalyticSet B ∧ ∀ ν : Measure ℂ, LocFinMeasure ν → (HasRatPlateauCert ν ↔ localCode φs ν ∈ B)

/-- **OPEN (NEW; z1, fp-S2h).** The log-GFF zero law for the code set: for every whole-plane log field `h^ℂ − γ log|·|`
(`IsWholePlaneGFF`, `IsLQGMeasureOfField P γ γ`), the code law of its LQG measure gives the code set `B` mass zero.
Written argument: notes/fp-gaps/CHATGPT-cone-good-set.md Section 5 (plateau radii countable (37), Tonelli (39), scaling
(41)-(44), zero law (45)) with Transfer.lean:82 (1/2-plateau from a certificate pair, which needs the HB Lemma 3.5
compatibility `ClusterCompatibilityStmt`, `harmonic-balls-lqg/HarmonicBalls/Draft/Section3.lean:119`, and the Radon
property of the LQG measure). The zero law still needs the measurability of the plateau event on `Ω × ℝ`
(PlateauZero.lean:95 hypothesis `hmeas`) and the scale covariance of the log-GFF (hypothesis `hscale`). Not proved. -/
def LogCertCodeNullStep (φs : ℕ → ℂ → ℝ) (B : Set (ℕ → ℝ)) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ γ hcirc μ → (P.map fun ω => localCode φs (μ ω)) B = 0

/-- **OPEN (NEW; z1, fp-S2h): the certificate code step.** Some admissible test family `φs` and some set `B` satisfy the
exact code relation `CertCodeExactStep φs B` (analytic `B`, iff for locally finite measures) and the log-GFF zero law
`LogCertCodeNullStep φs B`. This is the single open input of the certificate null hull. Not proved. -/
def CertCodeNullStep : Prop :=
  ∃ (φs : ℕ → ℂ → ℝ) (B : Set (ℕ → ℝ)), CertTestFamily φs ∧ CertCodeExactStep φs B ∧ LogCertCodeNullStep φs B

/-- **Cone certificate null hull from its steps (fp-S2h).** The certificate part of the bad set has a measurable null
hull for every cone field, given the frozen local-law equality, the frozen measurability of test integrals and the
certificate code step `CertCodeNullStep` (NEW). The infinite-mass part is handled by the Radon property of `IsLQGMeasure`
(`IsLQGLimit.isLocallyFiniteMeasure`), which makes almost every LQG measure locally finite. -/
theorem coneCertificateNullHull_of_steps (hlaw : FrozenConeLogLocalCodeLaw)
    (hmeasF : FrozenLQGTestIntegralMeasurable) (hcode : CertCodeNullStep) : ConeCertificateNullHullStep := by
  obtain ⟨φs, B, hφs, hB, hlog⟩ := hcode
  have hfm : Measurable (localCode φs) := measurable_localCode fun k => (hφs k).1
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨Ω', _, P', hC', hcirc', μ', hP', hgff, hlgm, heq⟩ := hlaw γ hγ hγ2 Ω P hC hcirc μ hcone
  have hcodeLaw : P.map (fun ω => localCode φs (μ ω)) = P'.map (fun ω => localCode φs (μ' ω)) :=
    heq φs (fun k => ⟨(hφs k).1, (hφs k).2.1, (hφs k).2.2.1⟩)
  have hlogB : (P'.map fun ω => localCode φs (μ' ω)) B = 0 :=
    hlog γ hγ hγ2 Ω' P' hC' hcirc' μ' hP' hgff hlgm
  have hconeB : (P.map fun ω => localCode φs (μ ω)) B = 0 := by
    rw [hcodeLaw]
    exact hlogB
  have hμm : Measurable fun ω => localCode φs (μ ω) :=
    Measurable.of_eval fun k => hmeasF γ hγ hγ2 Ω P hC hcirc μ hcone (φs k) (hφs k).1 (hφs k).2.1
  obtain ⟨N₁, hN₁m, hN₁, hN₁0⟩ := nullHull_of_code_law P μ (localCode φs) hfm hμm
    {ν | HasRatPlateauCert ν ∧ LocFinMeasure ν} B
    (fun ν hν => (hB.2 ν hν.2).1 hν.1) hconeB
  have hL : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
  have hfin : ∀ᵐ ω ∂P, LocFinMeasure (μ ω) := by
    filter_upwards [hL] with ω hω
    have := hω.isLocallyFiniteMeasure
    intro n
    exact (isCompact_closedBall (0 : ℂ) n).measure_lt_top
  have hN₂m : MeasurableSet {ν : Measure ℂ | ¬ LocFinMeasure ν} := by
    have hset : {ν : Measure ℂ | ¬ LocFinMeasure ν} =
        ⋃ n : ℕ, {ν : Measure ℂ | ¬ ν (closedBall (0 : ℂ) n) < ⊤} := by
      ext ν
      simp [LocFinMeasure]
    rw [hset]
    exact MeasurableSet.iUnion fun n =>
      (measurableSet_lt (Measure.measurable_coe measurableSet_closedBall) measurable_const).compl
  have hN₂0 : P (μ ⁻¹' {ν : Measure ℂ | ¬ LocFinMeasure ν}) = 0 :=
    ae_iff.1 hfin
  obtain ⟨N, hNm, hNs, hN0⟩ := nullHull_union P μ ⟨N₁, hN₁m, hN₁, hN₁0⟩
    ⟨_, hN₂m, subset_rfl, hN₂0⟩
  refine ⟨N, hNm, fun ν hν => ?_, hN0⟩
  by_cases hK : LocFinMeasure ν
  · exact hNs (Or.inl ⟨hν, hK⟩)
  · exact hNs (Or.inr hK)

/-! ## The least-supersolution null hull (fp-S2h, round 3): proved from the volume-growth input -/

/-- **Proved (fp-S2h, z1).** The least-supersolution part of the bad set has a measurable null hull, namely the
complement of `lsoClass γ` (the measures with finite mass on `B̄_{7/8}` and countably many two-sided dyadic bounds).
Inputs: `VolumeGrowthStmt` (Draft, Lemma 2.7) for the cone measure, and the frozen deterministic input
`LeastSupersolutionMemOfVolumeGrowthStmt` (HB Appendix A, Lemma A.1). Written argument:
notes/fp-gaps/CHATGPT-cone-leastsuper-null-hull.md, Sections 2-7. Lemmas: FirstPass/S2h/LeastSuper.lean. -/
theorem coneLeastSuperNullHull_proved (hV : VolumeGrowthStmt) (hL : LeastSupersolutionMemOfVolumeGrowthStmt) :
    ConeLeastSuperNullHullStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  refine ⟨(lsoClass γ)ᶜ, (measurableSet_lsoClass γ).compl, ?_, ?_⟩
  · intro ν hν hmem
    exact hν (lsoClass_leastSuperOK hL hγ2 hmem)
  · exact ae_iff.1 (ae_mem_lsoClass hV hγ hγ2 Ω P hC hcirc μ hcone)

/-- **Reduction (fp-S2h, z1).** `ConeBadNullHullStep` (FirstPass/S2g/Family.lean) from the certificate part, taken as
the explicit open hypothesis `hc` (`ConeCertificateNullHullStep`, NEW, still open), and the proved
least-supersolution part. -/
theorem coneBadNullHull_proved (hc : ConeCertificateNullHullStep) (hV : VolumeGrowthStmt)
    (hL : LeastSupersolutionMemOfVolumeGrowthStmt) : ConeBadNullHullStep :=
  coneBadNullHull_of_parts hc (coneLeastSuperNullHull_proved hV hL)

/-- **Reduction (fp-S2h, z1).** `ConeClosureGoodMeasureLawStep` (FirstPass/S2f.lean) from the same inputs as
`coneBadNullHull_proved`, with the frozen pole input `FrozenGreenDiscPole` (FirstPass/Frozen/S2g.lean). -/
theorem coneClosureGoodMeasureLaw_proved (hpole : FrozenGreenDiscPole) (hc : ConeCertificateNullHullStep)
    (hV : VolumeGrowthStmt) (hL : LeastSupersolutionMemOfVolumeGrowthStmt) :
    ConeClosureGoodMeasureLawStep :=
  coneClosureGoodMeasureLawStep_of_parts hpole hc (coneLeastSuperNullHull_proved hV hL)

end MatedCRT
