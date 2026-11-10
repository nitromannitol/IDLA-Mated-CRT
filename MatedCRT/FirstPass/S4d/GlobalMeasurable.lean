import MatedCRT.FirstPass.S4d.GlueDet
import MatedCRT.FirstPass.S4d.RegDecode
import MatedCRT.FirstPass.S4d.Horizon
import MatedCRT.Draft.Section2
import MatedCRT.Steps.Sec2.ConeHarmonicBalls
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime
import MatedCRT.Proofs.Measurability.ConeRescaledCircle

/-!
# B2: measurability of the whole global family process (FIRST PASS, S4d)

`ConeGlobalFamilyAEMeasurableStep` (ChatGPT answer §4, operator 01:12): the pair `(circleProcess (hcirc ω), globalFamilyProcess
(Λ ω))` is a.e. measurable. Proved from the stopped measurability theorem `ConeFamilyAEMeasurableStep` (conj 1 and conj 2),
Lemma 2.4 (`ConeHarmonicBallsUpToFixedTimeStmt`) and Lemma 2.5 (`ConeScaleInvarianceUpToFixedTimeStmt`), by gluing the
countably many rescaled stopped families `n ↦ (n+1)`: on a conull event the glued decoded process equals the global family
(`glue_det`), and horizons are unbounded (`ae_horizon_unbounded`). Only the law equality in Lemma 2.5 is used; no
uniqueness or global factorization input.
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT

/-- The glued decoded process: `(t, z)` is in it iff `0 < t` and, for some `n`, the rescaled stopped process decodes
`z / R n` at time `t / (n + 1)` (ball tests over the countable dense set `D`). -/
def glueProc {Ω : Type*} (D : Set ℂ) (Fm : ℕ → Ω → ℝ × ℂ → Prop) (Rm : ℕ → Ω → ℝ) (ω : Ω) (p : ℝ × ℂ) : Prop :=
  0 < p.1 ∧ ∃ n : ℕ, ∃ q ∈ D, ∃ r : ℚ, 0 < r ∧ p.2 / (Rm n ω : ℂ) ∈ closedBall q (r : ℝ) ∧
    ProxySub D (famOf (Fm n ω) (p.1 / ((n : ℝ) + 1))) q (r : ℝ)

/-- **Gluing.** Given measurable-up-to-null stopped processes `Fn n` and radii `Rn n`, with the stopped identities and
unbounded horizons almost surely, the pair with the global family is a.e. measurable. -/
theorem aemeasurable_of_glue {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {Λ : Ω → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    (hCm : Measurable fun ω => circleProcess (hcirc ω))
    {Λn : ℕ → Ω → ℝ → Set ℂ} {Tn Rn : ℕ → Ω → ℝ} {Fn : ℕ → Ω → ℝ × ℂ → Prop}
    (hFae : ∀ n, AEMeasurable (Fn n) P) (hRae : ∀ n, AEMeasurable (Rn n) P)
    (hpr : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < Rn n ω ∧ Fn n ω = familyProcess
        (rescaledFamily (Λn n ω) (Rn n ω) ((n : ℝ) + 1)) (Tn n ω) ∧
      IsConeHarmonicBallFamilyOn (μ ω) (Λn n ω) (((n : ℝ) + 1) * Tn n ω) ∧
      IsStoppedAtHalfBall (rescaledFamily (Λn n ω) (Rn n ω) ((n : ℝ) + 1)) (Tn n ω))
    (hhor : ∀ᵐ ω ∂P, ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) + 1 < ((n : ℝ) + 1) * Tn n ω) :
    AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hFex : ∀ n, ∃ F : Ω → ℝ × ℂ → Prop, Measurable F ∧ Fn n =ᵐ[P] F :=
    fun n => ⟨(hFae n).mk (Fn n), (hFae n).measurable_mk, (hFae n).ae_eq_mk⟩
  choose Fm hFm hFeq using hFex
  have hRex : ∀ n, ∃ R : Ω → ℝ, Measurable R ∧ Rn n =ᵐ[P] R :=
    fun n => ⟨(hRae n).mk (Rn n), (hRae n).measurable_mk, (hRae n).ae_eq_mk⟩
  choose Rm hRm hReq using hRex
  have hconf : ∀ᵐ ω ∂P, (∀ n, Fn n ω = Fm n ω) ∧ (∀ n, Rn n ω = Rm n ω) :=
    (ae_all_iff.2 hFeq).and (ae_all_iff.2 hReq)
  -- the coordinates of the decoded process are measurable
  have hcoord : ∀ n (s : ℝ) (d : ℂ), MeasurableSet {ω | d ∈ famOf (Fm n ω) s} := fun n s d =>
    measurableSet_setOfPred.2 ((measurable_pi_apply (s, d)).comp (hFm n))
  have hgl_meas : ∀ p : ℝ × ℂ, MeasurableSet {ω | glueProc D Fm Rm ω p} := by
    intro p
    by_cases hp : 0 < p.1
    · have hset : {ω | glueProc D Fm Rm ω p} = ⋃ n : ℕ, {ω | ∃ q ∈ D, ∃ r : ℚ, 0 < r ∧
          p.2 / (Rm n ω : ℂ) ∈ closedBall q (r : ℝ) ∧
            ProxySub D (famOf (Fm n ω) (p.1 / ((n : ℝ) + 1))) q (r : ℝ)} := by
        ext ω
        simp only [glueProc, hp, true_and, mem_iUnion, mem_ofPred_eq]
      rw [hset]
      refine MeasurableSet.iUnion fun n => ?_
      have hw : Measurable (fun ω => p.2 / (Rm n ω : ℂ)) :=
        measurable_const.div (Complex.measurable_ofReal.comp (hRm n))
      exact measurableSet_exists_proxy hDc (U := fun ω => famOf (Fm n ω) (p.1 / ((n : ℝ) + 1)))
        (fun d _ => hcoord n _ d) hw
    · have hset : {ω | glueProc D Fm Rm ω p} = ∅ := by
        ext ω
        simp [glueProc, hp]
      rw [hset]
      exact MeasurableSet.empty
  have hglm : Measurable (glueProc D Fm Rm) :=
    measurable_pi_iff.2 fun p => measurableSet_setOfPred.1 (hgl_meas p)
  -- the a.e. identity of the glued process with the global family process
  have hpt : ∀ᵐ ω ∂P, ∀ p : ℝ × ℂ, glueProc D Fm Rm ω p ↔ globalFamilyProcess (Λ ω) p := by
    filter_upwards [hΛ, hpr, hhor, hconf] with ω hΛω hprω hhorω hconfω
    intro p
    obtain ⟨hFc, hRc⟩ := hconfω
    have hRne : ∀ n, Rn n ω ≠ 0 := fun n => (hprω n).1.ne'
    -- each decoded ball test is the rescaled stopped membership
    have hn_iff : ∀ n : ℕ, (∃ q ∈ D, ∃ r : ℚ, 0 < r ∧ p.2 / (Rm n ω : ℂ) ∈ closedBall q (r : ℝ) ∧
        ProxySub D (famOf (Fm n ω) (p.1 / ((n : ℝ) + 1))) q (r : ℝ)) ↔
        familyProcess (rescaledFamily (Λn n ω) (Rn n ω) ((n : ℝ) + 1)) (Tn n ω)
          (p.1 / ((n : ℝ) + 1), p.2 / (Rn n ω : ℂ)) := by
      intro n
      have hslice := familyProcess_rescaled_slice_regular (b := (n : ℝ) + 1) (T := Tn n ω) (R := Rn n ω)
        (by positivity) (hRne n) (hprω n).2.2.1 (p.1 / ((n : ℝ) + 1))
      have hfmk : famOf (Fm n ω) (p.1 / ((n : ℝ) + 1)) =
          famOf (familyProcess (rescaledFamily (Λn n ω) (Rn n ω) ((n : ℝ) + 1)) (Tn n ω))
            (p.1 / ((n : ℝ) + 1)) := by
        rw [← hFc n, (hprω n).2.1]
      rw [← hRc n, hfmk]
      exact (mem_iff_proxy_of_regular hDd hslice.1 hslice.2 _).symm
    have hunb : ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) < ((n : ℝ) + 1) * Tn n ω := by
      intro M
      obtain ⟨n, hn⟩ := hhorω M
      exact ⟨n, by linarith⟩
    have hgd : (0 < p.1 ∧ ∃ n : ℕ, familyProcess (rescaledFamily (Λn n ω) (Rn n ω) ((n : ℝ) + 1))
        (Tn n ω) (p.1 / ((n : ℝ) + 1), p.2 / (Rn n ω : ℂ))) ↔ (0 < p.1 ∧ p.2 ∈ Λ ω p.1) :=
      glue_det (μ := μ ω) (Λg := Λ ω) (Λs := fun n => Λn n ω) (Ts := fun n => Tn n ω)
        (R := fun n => Rn n ω) (b := fun n => (n : ℝ) + 1) hΛω (fun n => by positivity)
        (fun n => (hprω n).1) (fun n => (hprω n).2.2.1) (fun n => (hprω n).2.2.2) hunb p.1 p.2
    unfold glueProc globalFamilyProcess
    exact (and_congr_right fun _ => exists_congr fun n => hn_iff n).trans hgd
  have hGg : (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) =ᵐ[P]
      (fun ω => (circleProcess (hcirc ω), glueProc D Fm Rm ω)) := by
    filter_upwards [hpt] with ω hω
    refine Prod.ext rfl ?_
    funext p
    exact propext (hω p).symm
  exact ((hCm.prodMk hglm).aemeasurable).congr hGg.symm

/-- A pointwise choice from an almost sure existence statement (`Classical.epsilon`). -/
theorem ae_choose_of_exists {Ω X : Type*} [MeasurableSpace Ω] {P : Measure Ω} [Nonempty X] {Q : Ω → X → Prop}
    (h : ∀ᵐ ω ∂P, ∃ x, Q ω x) : ∃ f : Ω → X, ∀ᵐ ω ∂P, Q ω (f ω) :=
  ⟨fun ω => Classical.epsilon (Q ω), by
    filter_upwards [h] with ω hω
    exact Classical.epsilon_spec hω⟩

/-- The origin is in the family process of a positive time: `(s, 0)` is in the family process up to `T` iff `s < T`. -/
theorem familyProcess_zero_iff {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {T s : ℝ}
    (hfam : IsConeHarmonicBallFamilyOn μ Λ T) (hs : 0 < s) :
    familyProcess Λ T (s, 0) ↔ s < T := by
  constructor
  · intro h
    exact h.1.2
  · intro h
    exact ⟨⟨hs, h⟩, hfam.2.1.mem s ⟨hs, h⟩⟩

/-- The origin is in the rescaled family process: `(s, 0)` is in the rescaled family process up to `T` iff `s < T`. -/
theorem familyProcess_rescaled_zero_iff {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {T s b R : ℝ} (hb : 0 < b)
    (hfam : IsConeHarmonicBallFamilyOn μ Λ (b * T)) (hs : 0 < s) :
    familyProcess (rescaledFamily Λ R b) T (s, 0) ↔ s < T := by
  constructor
  · intro h
    exact h.1.2
  · intro h
    refine ⟨⟨hs, h⟩, ?_⟩
    show (R : ℂ) * 0 ∈ Λ (b * s)
    rw [mul_zero]
    exact hfam.2.1.mem (b * s) ⟨mul_pos hb hs, mul_lt_mul_of_pos_left h hb⟩

/-- **Existence part of Lemma 2.4 (q4, fp-S4d-4-2-h24-gate-consumers).** For a.e. sample there are `T > 0` and a family
`Λ` of cone harmonic balls on `(0, T)` stopped at `∂B_{1/2}` at `T`. This is the existence clause of the provider form
`ConeHarmonicBallsProviderFP4` (FirstPass/S4d/Provider24.lean) and of the Draft `ConeHarmonicBallsUpToFixedTimeStmt`
(Draft/Section2.lean:66); the uniqueness clauses (the Draft `T' = T`) are not used by the measurability steps. -/
def ConeStoppedBaseExistsFP4 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧ ∃ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn (μ ω) Λ T ∧ IsStoppedAtHalfBall Λ T

/-- The existence part of the Draft Lemma 2.4 (`ConeHarmonicBallsUpToFixedTimeStmt`), by forgetting the clause `T' = T`. -/
theorem coneStoppedBaseExists_of_draft (h24 : ConeHarmonicBallsUpToFixedTimeStmt) : ConeStoppedBaseExistsFP4 := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hF
  filter_upwards [h24 γ hγ hγ2 Ω P hC hcirc μ hF] with ω hω
  obtain ⟨T, hT, Λ', h1, h2, -⟩ := hω
  exact ⟨T, hT, Λ', h1, h2⟩

/-- **B2: the global family process is a.e. measurable** (`ConeGlobalFamilyAEMeasurableStep`, ChatGPT §4). From the
stopped measurability theorem `ConeFamilyAEMeasurableStep` (conjunctions 1 and 2), Lemma 2.4 and Lemma 2.5, with the
weights `b n = n + 1`. -/
theorem coneGlobalFamilyAEMeasurable_of_exists {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hF : IsConeField γ P hC hcirc μ)
    (hexist : ConeStoppedBaseExistsFP4) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) (hpos : ConeScaleRadiusPosStep)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) :
    AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P := by
  have hQC : IsQuantumCone γ P hC hcirc := hF.2.1
  -- the base stopped family (Lemma 2.4), chosen pointwise
  have hbase : ∀ᵐ ω ∂P, ∃ x : ℝ × (ℝ → Set ℂ), 0 < x.1 ∧ IsConeHarmonicBallFamilyOn (μ ω) x.2 x.1 ∧
      IsStoppedAtHalfBall x.2 x.1 := by
    filter_upwards [hexist γ hγ hγ2 Ω P hC hcirc μ hF] with ω hω
    obtain ⟨T, hT, Λ', h1, h2⟩ := hω
    exact ⟨(T, Λ'), hT, h1, h2⟩
  obtain ⟨T0, Λ0, hT0eq⟩ : ∃ (T0 : Ω → ℝ) (Λ0 : Ω → ℝ → Set ℂ), ∀ᵐ ω ∂P,
      0 < T0 ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ0 ω) (T0 ω) ∧ IsStoppedAtHalfBall (Λ0 ω) (T0 ω) := by
    obtain ⟨xf, hxf⟩ := ae_choose_of_exists (Q := fun (ω : Ω) (x : ℝ × (ℝ → Set ℂ)) => 0 < x.1 ∧
      IsConeHarmonicBallFamilyOn (μ ω) x.2 x.1 ∧ IsStoppedAtHalfBall x.2 x.1) hbase
    exact ⟨fun ω => (xf ω).1, fun ω => (xf ω).2, hxf⟩
  -- the rescaled stopped families for the weights `n + 1` (Lemma 2.5), chosen for each `n`
  have hsc := fun n : ℕ => h25 γ hγ hγ2 Ω P hC hcirc μ hF T0 Λ0 hT0eq ((n : ℝ) + 1) (by positivity)
  choose Tn Λn hTn using hsc
  have hRae : ∀ n : ℕ, AEMeasurable (fun ω => coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) P :=
    fun n => aemeasurable_coneScaleRadius hQC _
  have hRpos : ∀ n : ℕ, ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1) :=
    fun n => hpos γ hγ hγ2 Ω P hC hcirc hF.1 hQC _ (by positivity)
  have hpair : ∀ n : ℕ, AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)), familyProcess (rescaledFamily (Λn n ω)
      (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)) (Tn n ω))) P :=
    fun n => (hfam γ hγ hγ2 Ω P hC hcirc μ hF).2 ((n : ℝ) + 1) (by positivity) (Tn n) (Λn n) ((hTn n).1.mono fun ω h => ⟨h.1, h.2.1, h.2.2.1⟩)
  have hFae : ∀ n : ℕ, AEMeasurable (fun ω => familyProcess (rescaledFamily (Λn n ω)
      (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)) (Tn n ω)) P :=
    fun n => (hpair n).snd
  have hprn : ∀ n : ℕ, ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1) ∧
      IsConeHarmonicBallFamilyOn (μ ω) (Λn n ω) (((n : ℝ) + 1) * Tn n ω) ∧
      IsStoppedAtHalfBall (rescaledFamily (Λn n ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))
        (Tn n ω) :=
    fun n => (hRpos n).and ((hTn n).1.mono fun ω h => ⟨h.2.1, h.2.2.1⟩)
  have hpr : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1) ∧
      (fun ω => familyProcess (rescaledFamily (Λn n ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1))
        ((n : ℝ) + 1)) (Tn n ω)) ω = familyProcess (rescaledFamily (Λn n ω)
        (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)) (Tn n ω) ∧
      IsConeHarmonicBallFamilyOn (μ ω) (Λn n ω) (((n : ℝ) + 1) * Tn n ω) ∧
      IsStoppedAtHalfBall (rescaledFamily (Λn n ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))
        (Tn n ω) := by
    filter_upwards [ae_all_iff.2 hprn] with ω hω n
    exact ⟨(hω n).1, rfl, (hω n).2.1, (hω n).2.2⟩
  -- the horizons are unbounded almost surely (Horizon.lean, equations (4.5)-(4.7))
  have hhor : ∀ᵐ ω ∂P, ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) + 1 < ((n : ℝ) + 1) * Tn n ω := by
    refine ae_horizon_unbounded (Φ0 := fun ω => (circleProcess (hcirc ω), familyProcess (Λ0 ω) (T0 ω)))
      (Φn := fun n ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1))
        ((n : ℝ) + 1)), familyProcess (rescaledFamily (Λn n ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1))
        ((n : ℝ) + 1)) (Tn n ω))) (T0 := T0) (Tn := Tn)
      (hT0eq.mono fun ω h => h.1)
      ((hfam γ hγ hγ2 Ω P hC hcirc μ hF).1 T0 Λ0 hT0eq) hpair (fun n => (hTn n).2)
      (fun s hs => hT0eq.mono fun ω h => familyProcess_zero_iff h.2.1 hs)
      (fun n s hs => ((hTn n).1.and (hRpos n)).mono fun ω h =>
        familyProcess_rescaled_zero_iff (by positivity) h.1.2.1 hs)
  have hCm : Measurable fun ω => circleProcess (hcirc ω) :=
    measurable_pi_iff.2 fun p => hQC.measurable_circle (p.1 : ℝ) p.2 p.1.2
  exact aemeasurable_of_glue hΛ hCm (Λn := Λn) (Tn := Tn)
    (Rn := fun n ω => coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1))
    (Fn := fun n ω => familyProcess (rescaledFamily (Λn n ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1))
      ((n : ℝ) + 1)) (Tn n ω))
    hFae hRae hpr hhor

/-- **B2 with the Draft Lemma 2.4 (`coneGlobalFamilyAEMeasurable_of_stopped`, signature unchanged for FixedTimeFinal,
RescaledMeasurable and S2z.lean:71).** The Draft is used only through `coneStoppedBaseExists_of_draft`. -/
theorem coneGlobalFamilyAEMeasurable_of_stopped {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hF : IsConeField γ P hC hcirc μ)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) (hpos : ConeScaleRadiusPosStep)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) :
    AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P :=
  coneGlobalFamilyAEMeasurable_of_exists hγ hγ2 hF (coneStoppedBaseExists_of_draft h24) h25 hfam hpos Λ hΛ

end MatedCRT
