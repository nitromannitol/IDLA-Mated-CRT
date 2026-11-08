import MatedCRT.Proofs.Sec5.StoppedActualValueVersions
import MatedCRT.Proofs.Sec5.StoppedRationalMembership
import MatedCRT.Proofs.Sec5.StoppedInterior

/-!
# Measurable margin code from the actual compact-code and surplus producers (steps2-r3:3390-3420)

Source: `notes/wpn-steps2/steps2-r3.tex`, lines 3390-3420 (the erosion minimum `m(K, f)` of the random compact code
`K = closure Λ_t` and the decoder `f` of the surplus on `A = {s ≤ |x| ≤ ρ/2}`, with the consumer changes), and the
field-measurable circle version of lines 3326-3354.

Construction, for `t > 0`, `δ > 0`, `s > 0`:

* `E z = c⁻¹(B z)`, where `B z` is a Borel version on `PosCircleFns` of the limsup rational-ball code `freqCodeSet 𝒜 t z`
  (`nullMeasurableSet_freqCodeSet`, under the law `P.map c`, from the Preston input). The code `codeCompact E` is the actual
  compact code: it equals `closure (Λ ω t)` almost surely (`ae_codeCompact_eq_closure`).
* `f ω = D (c ω)`, with `D` the Borel decoder of `exists_actualSurplus_decoder`. Almost surely on `{t < T}` it equals the
  actual surplus on `A`. When `s > ρ/2` the domain `A` is empty and `f = 0`.
* `M̂ ω = erodedMin A δ (K ω) (f ω)` (the everywhere-defined erosion minimum, empty index set `↦ 0`) is `S.fieldSigma`-measurable
  and hence `S.envSigma`-measurable, because `c` is `S.fieldSigma`-measurable. Almost surely on `{t < T}` it equals the raw
  compact-index minimum (`erodedMin_eq_raw`). No continuity outside `{t < T}` is used.

The one residual producer is `FieldCircleVersionStmt`: a `S.fieldSigma`-measurable Borel version of the circle process.
The Preston inputs and `CodeSectionStmt` are the repository's named inputs. No numbered result is claimed here.
-/

namespace MatedCRT.StoppedActualMarginCode

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls (fieldSigmaAlgebra fieldPairing)
open TopologicalSpace (NonemptyCompacts)
open MatedCRT.StoppedRationalMembership (ratBallCode)
open MatedCRT.ConeOriginNull (BallFns superTraces gaussRat gaussRat_countable CodeSectionStmt)
open MatedCRT.CircleProcessSpace (PosCircleFns PosCircleIndex)
open MatedCRT.StoppedInteriorMargin (marginDomain)

/-- **Field-measurable circle version (residual producer; steps2-r3:3326-3354).** For every valid environment there is a
Borel version `c : Ω → PosCircleFns` of the circle process which is measurable for the field σ-algebra `S.fieldSigma` alone
and almost surely equal to `S.hcirc` at every index `(r, z) ∈ (0,∞) × ℂ`. The source obtains it from the countable dense family
of circles, the convergence in probability of the mollified pairings and the countable continuous-extension decoder of
Section origin. It is not formalized. The nearest existing producers give only ambient measurability:
`exists_measurable_circleFns_version` (ConeOriginNullMeasurableProof.lean:64) and `CanonicalCircleVersionStep`
(AllStartsClock.lean:1360). -/
def FieldCircleVersionStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∃ c : Ω → PosCircleFns, Measurable[S.fieldSigma] c ∧
      ∀ᵐ ω ∂S.P, ∀ p : PosCircleIndex, c ω p = S.hcirc ω (p.1 : ℝ) p.2

/-- The field σ-algebra lies in the ambient σ-algebra, since the pairings `h(φ)` are measurable (`measurable_pairing`). -/
theorem fieldSigma_le_ambient {Ω : Type} [mΩ : MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) : S.fieldSigma ≤ mΩ := by
  simp only [MatedCRTEnv.fieldSigma, fieldSigmaAlgebra]
  refine iSup₂_le fun φ hφ => ?_
  have hm : Measurable fun ω => fieldPairing 0 (S.hC ω) φ := by
    simpa [fieldPairing] using hS.isQuantumCone.measurable_pairing φ hφ
  exact hm.comap_le

/-- The limsup event of the rational-ball codes on the state space `PosCircleFns`: the code holds at infinitely many integer
radii `n + 1` (the set-valued form of `ratLimsupEvent`, steps2-r3:3158-3160). -/
def freqCodeSet (𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))) (t : ℝ) (z : ℂ) : Set PosCircleFns :=
  ⋂ N : ℕ, ⋃ n ∈ {n : ℕ | N ≤ n}, {x | ratBallCode (𝒜 n) t z x}

theorem mem_freqCodeSet_iff (𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))) (t : ℝ) (z : ℂ)
    (x : PosCircleFns) : x ∈ freqCodeSet 𝒜 t z ↔ ∃ᶠ n in atTop, ratBallCode (𝒜 n) t z x := by
  simp only [freqCodeSet, mem_iInter, mem_iUnion, Set.mem_ofPred_eq, exists_prop, Filter.frequently_atTop]

/-- A proposition that holds for all indices of a frequently/eventually pattern: if `p ↔ q n` eventually, then the
frequent truth of `q` is equivalent to `p`. -/
theorem frequently_iff_of_eventually {p : Prop} {q : ℕ → Prop} (h : ∀ᶠ n in atTop, (p ↔ q n)) :
    (∃ᶠ n in atTop, q n) ↔ p := by
  by_cases hp : p
  · exact ⟨fun _ => hp, fun _ => (h.mono fun n hn => hn.1 hp).frequently⟩
  · refine ⟨fun hf => ?_, fun hp' => absurd hp' hp⟩
    have hnq : ∀ᶠ n in atTop, ¬ q n := h.mono fun n hn hq => hp (hn.2 hq)
    obtain ⟨n, hn1, hn2⟩ := (hf.and_eventually hnq).exists
    exact (hn2 hn1).elim

/-- The limsup code set is null-measurable for every finite measure on the state space (Preston input). -/
theorem nullMeasurableSet_freqCodeSet (hP : PrestonAnalyticUniversallyMeasurableStmt)
    {𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))} (h𝒜 : ∀ n : ℕ, MeasurableSet (𝒜 n)) (t : ℝ) (z : ℂ)
    (ν : Measure PosCircleFns) [IsFiniteMeasure ν] : NullMeasurableSet (freqCodeSet 𝒜 t z) ν :=
  NullMeasurableSet.iInter fun _ => NullMeasurableSet.biUnion (Set.to_countable _) fun n _ =>
    MatedCRT.StoppedRationalMembership.nullMeasurableSet_ratBallCode hP (h𝒜 n) z ν

/-- The actual compact code is measurable for any σ-algebra for which the membership events are measurable. -/
theorem measurable_codeCompact_field {Ω : Type} (m : MeasurableSpace Ω) {E : ℂ → Set Ω}
    (hE : ∀ z ∈ gaussRat, MeasurableSet[m] (E z)) :
    @Measurable Ω (NonemptyCompacts ℂ) m (borel _) (MatedCRT.StoppedCompactCode.codeCompact E) := by
  let : MeasurableSpace (NonemptyCompacts ℂ) := borel _
  have : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩
  exact @MatedCRT.StoppedCompactCode.measurable_codeCompact Ω m _ _ E hE

/-- Measurability of a pair of measurable maps into the Borel σ-algebra of `NonemptyCompacts ℂ × C(A, ℝ)`. -/
theorem measurable_pair_borel {Ω : Type} (m : MeasurableSpace Ω) {A : Set ℂ}
    {K : Ω → NonemptyCompacts ℂ} {f : Ω → C(↥A, ℝ)}
    (hK : @Measurable Ω (NonemptyCompacts ℂ) m (borel _) K)
    (hf : @Measurable Ω C(↥A, ℝ) m (borel _) f) :
    @Measurable Ω (NonemptyCompacts ℂ × C(↥A, ℝ)) m (borel _) (fun ω => (K ω, f ω)) := by
  let : MeasurableSpace (NonemptyCompacts ℂ) := borel _
  have : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩
  let : MeasurableSpace C(↥A, ℝ) := borel _
  have : BorelSpace C(↥A, ℝ) := ⟨rfl⟩
  have e : (Prod.instMeasurableSpace : MeasurableSpace (NonemptyCompacts ℂ × C(↥A, ℝ))) = borel _ :=
    BorelSpace.measurable_eq
  rw [← e]
  exact hK.prodMk hf

/-- **Composition of the actual producers into the margin code (steps2-r3:3390-3420).** Given the Preston inputs, the
section input `CodeSectionStmt` and the field-measurable circle version, the residual `StoppedMarginCodeStep` holds: the
random compact code is the actual closure `closure Λ_t` almost surely and the decoder is the actual surplus almost surely on
`{t < T}`, both `S.fieldSigma`-measurable (hence `S.envSigma`-measurable) as functions of the environment. -/
theorem stoppedMarginCode_of_inputs (𝒮 : SpaceFillingSLEModel)
    (hP : PrestonAnalyticUniversallyMeasurableStmt) (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) (hCS : CodeSectionStmt 𝒮) (hFC : FieldCircleVersionStmt 𝒮) :
    MatedCRT.StoppedInterior.StoppedMarginCodeStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ _ Ω _ S hS Λ hΛ δ s t hδ hs ht
  obtain ⟨c, hcF, hcirc⟩ := hFC γ hγ hγ2 Ω S hS
  have hle : S.fieldSigma ≤ ‹MeasurableSpace Ω› := fieldSigma_le_ambient hS
  have hc : Measurable c := hcF.mono hle le_rfl
  have hEnv : S.fieldSigma ≤ S.envSigma := le_sup_left
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have : IsProbabilityMeasure (S.P.map c) :=
    (Measure.isProbabilityMeasure_map_iff hc.aemeasurable).2 inferInstance
  -- (1) the sections of the stopped code at the integer radii `n + 1`
  have hsecN : ∀ n : ℕ, ∃ 𝒜 : Set (PosCircleFns × BallFns ((n : ℝ) + 1)), MeasurableSet 𝒜 ∧
      ∀ᵐ ω ∂S.P, ∀ w : BallFns ((n : ℝ) + 1), (c ω, w) ∈ 𝒜 ↔ w ∈ superTraces (S.μ ω) ((n : ℝ) + 1) t :=
    fun n => hCS γ hγ hγ2 Ω S hS c hc hcirc ((n : ℝ) + 1) (by positivity) t ht
  choose 𝒜 h𝒜 hsec0 using hsecN
  have hsec : ∀ᵐ ω ∂S.P, ∀ (n : ℕ) (w : BallFns ((n : ℝ) + 1)),
      (c ω, w) ∈ 𝒜 n ↔ w ∈ superTraces (S.μ ω) ((n : ℝ) + 1) t :=
    ae_all_iff.2 hsec0
  -- (2) Borel versions of the limsup code sets on the state space, under the law `P.map c`
  have hBex : ∀ z : ℂ, ∃ B : Set PosCircleFns, MeasurableSet B ∧ freqCodeSet 𝒜 t z =ᵐ[S.P.map c] B :=
    fun z => nullMeasurableSet_freqCodeSet hP h𝒜 t z (S.P.map c)
  choose B hBm hBeq using hBex
  have hBω : ∀ z : ℂ, ∀ᵐ ω ∂S.P, (c ω ∈ freqCodeSet 𝒜 t z ↔ c ω ∈ B z) := fun z =>
    ae_of_ae_map (p := fun y => y ∈ freqCodeSet 𝒜 t z ↔ y ∈ B z) hc.aemeasurable
      (Filter.Eventually.mono (hBeq z) fun y hy => hy.to_iff)
  -- (3) the rational membership events of the actual closure `Λ_t`
  have hLam : ∀ᵐ ω ∂S.P, ∀ z ∈ gaussRat, (ω ∈ c ⁻¹' B z ↔ z ∈ Λ ω t) := by
    have h1 : ∀ᵐ ω ∂S.P, ∀ z ∈ gaussRat, (c ω ∈ freqCodeSet 𝒜 t z ↔ c ω ∈ B z) :=
      (ae_ball_iff gaussRat_countable).2 fun z _ => hBω z
    have h2 := MatedCRT.StoppedRationalMembership.ae_forall_eventually_mem_iff_ratBallCode ht hΛ hsec
    filter_upwards [h1, h2] with ω hω1 hω2 z hz
    rw [Set.mem_preimage, ← hω1 z hz, mem_freqCodeSet_iff]
    exact frequently_iff_of_eventually (hω2 z)
  -- (4) the actual compact code is `closure Λ_t` almost surely, and is `S.fieldSigma`-measurable
  have hΛo : ∀ᵐ ω ∂S.P, IsOpen (Λ ω t) := hΛ.mono fun ω h => (h.1 t ht).1
  have hΛb : ∀ᵐ ω ∂S.P, Bornology.IsBounded (Λ ω t) := hΛ.mono fun ω h => h.2.1.isBounded t ht
  have hΛne : ∀ᵐ ω ∂S.P, (Λ ω t).Nonempty := hΛ.mono fun ω h => ⟨0, (h.1 t ht).2.1⟩
  have hKae : ∀ᵐ ω ∂S.P,
      ((MatedCRT.StoppedCompactCode.codeCompact (fun z => c ⁻¹' B z) ω : NonemptyCompacts ℂ) : Set ℂ) =
        closure (Λ ω t) :=
    MatedCRT.StoppedCompactCode.ae_codeCompact_eq_closure (E := fun z => c ⁻¹' B z) hΛo hΛb hΛne hLam
  have hEm : ∀ z ∈ gaussRat, MeasurableSet[S.fieldSigma] ((fun z => c ⁻¹' B z) z) := fun z _ => hcF (hBm z)
  have hKm := measurable_codeCompact_field S.fieldSigma hEm
  -- (5) the decoder on `A`, or the empty domain
  by_cases hsR : s ≤ ρ / 2
  · obtain ⟨a, D, -, hDm, hD⟩ :=
      MatedCRT.StoppedActualValueVersions.exists_actualSurplus_decoder hCantor hT61 𝒮 hγ hγ2 Ω S hS c hc hcirc
        hρ ht hs hsR Λ hΛ
    have hfm : @Measurable Ω C(marginDomain s (ρ / 2), ℝ) S.fieldSigma (borel _) (fun ω => D (c ω)) :=
      hDm.comp hcF
    refine ⟨fun ω => MatedCRT.StoppedCompactCode.codeCompact (fun z => c ⁻¹' B z) ω, fun ω => D (c ω), ?_, ?_⟩
    · exact (measurable_pair_borel S.fieldSigma hKm hfm).mono hEnv le_rfl
    · filter_upwards [hKae, hD] with ω hKω hDω hT
      exact ⟨hKω, fun x => hDω hT x⟩
  · refine ⟨fun ω => MatedCRT.StoppedCompactCode.codeCompact (fun z => c ⁻¹' B z) ω,
      fun _ => ContinuousMap.const _ (0 : ℝ), ?_, ?_⟩
    · exact (measurable_pair_borel S.fieldSigma hKm measurable_const).mono hEnv le_rfl
    · filter_upwards [hKae] with ω hKω _
      refine ⟨hKω, fun x => ?_⟩
      exfalso
      obtain ⟨h1, h2⟩ := x.2
      have h1' : ‖x.1‖ ≤ ρ / 2 := mem_closedBall_zero_iff.1 h1
      have h2' : s ≤ ‖x.1‖ := h2
      have hlt : ρ / 2 < s := not_le.1 hsR
      linarith

/-- **Measurable margin from the residual producers.** Under the same named inputs, the measurable margin
`StoppedInteriorMeasurableStep` holds: `M̂ = erodedMin` of the actual code and decoder is `S.envSigma`-measurable and equals
the raw minimum almost surely on `{t < T}`. -/
theorem stoppedInteriorMeasurableStep_of_inputs (𝒮 : SpaceFillingSLEModel)
    (hP : PrestonAnalyticUniversallyMeasurableStmt) (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) (hCS : CodeSectionStmt 𝒮) (hFC : FieldCircleVersionStmt 𝒮) :
    MatedCRT.StoppedInterior.StoppedInteriorMeasurableStep 𝒮 :=
  MatedCRT.StoppedInterior.stoppedInteriorMeasurable_of_code 𝒮
    (stoppedMarginCode_of_inputs 𝒮 hP hCantor hT61 hCS hFC)

end MatedCRT.StoppedActualMarginCode
