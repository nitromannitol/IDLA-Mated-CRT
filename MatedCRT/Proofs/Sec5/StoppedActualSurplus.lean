import MatedCRT.Proofs.Sec5.SupersolutionSectionIdentity
import MatedCRT.Proofs.Sec5.StoppedMarginValueVersions
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ExitTime

/-!
# The actual obstacle-section infimum and the continuous surplus on `marginDomain s (ρ/2)`

Source: `notes/wpn-steps2/steps2-r3.tex` (sha256 `88dfb1f9…`): lines 1039-1043 (on the masscode event the section of
`A_R` is exactly the set of supersolutions; it contains zero and is bounded below by `-tG_R(0,·)` at the nonzero points,
so its real infimum is the actual finite infimum) and lines 3374-3388 (the continuous surplus
`f(x) = v_ρ(μ,t)(x) + tG_ρ(0,x)` on `A = marginDomain s (ρ/2)`, decoded from a countable dense family of infima).

For a measure `μ` on `ℂ` and `0 ≤ t`:

* zero is a supersolution, so the trace set `superTraces μ R t` is nonempty (`zero_mem_superTraces`);
* every trace `w` satisfies `-tG_R(0,x) ≤ w x` at each `x ≠ 0` of `closedBall 0 R` (`lower_of_mem_superTraces`);
* at such `x` the real infimum of the evaluations of the traces is the least supersolution `v_R(μ,t)(x)`, and it is a
  genuine infimum: nonemptiness and the lower bound prevent the `sInf ∅` and unbounded-infimum totalizations
  (`leastSupersolution_eq_sInf_image`, `isGLB_image_superTraces`, `neg_mul_green_le_leastSupersolution_le_zero`);
* the actual surplus `v_ρ(μ,t) + tG_ρ(0,·)` is continuous on `marginDomain s (ρ/2)` under the hypotheses of the existing
  cone-family continuity result `MatedCRT.coneFamily_leastSupersolution_continuous` (`continuousOn_actualSurplus_marginDomain`),
  and is packaged as an element `continuousSurplusMargin` of `C(marginDomain s (ρ/2), ℝ)`;
* the `hbdd` and `hId` inputs of `MatedCRT.StoppedMarginValueVersions.exists_continuous_surplus_version_marginDomain`
  (and of its `_ae` form) are exposed for the sections `relSection 𝒜 (c ω)` of the Borel obstacle code. The section
  identity is `CodeSectionStmt` (reused through `codeSectionStmt_holds`, not reproved).

Not here: the pullback of these almost-sure statements to the law of the circle-array state `c`; that is the next task
(`z5-stopped-actual-value-versions`).
-/

namespace MatedCRT.StoppedActualSurplus

open MeasureTheory Filter Topology Set Metric
open MatedCRT.ConeOriginNull (BallFns superTraces restrict_mem_superTraces continuousOn_greenFunction_zero
  codeSectionStmt_holds)
open MatedCRT.StoppedInteriorMargin (marginDomain)
open MatedCRT.StoppedMarginValueVersions (relSection)
open MatedCRT.CircleProcessSpace (PosCircleFns PosCircleIndex)

/-! ### Points of the margin domain `A = marginDomain s R` -/

lemma mem_closedBall_of_mem_marginDomain {s R : ℝ} {x : ℂ} (hx : x ∈ marginDomain s R) :
    x ∈ closedBall (0 : ℂ) R := by
  unfold marginDomain at hx
  exact hx.1

lemma ne_zero_of_mem_marginDomain {s R : ℝ} (hs : 0 < s) {x : ℂ} (hx : x ∈ marginDomain s R) :
    x ≠ 0 := by
  unfold marginDomain at hx
  have h2 : s ≤ ‖x‖ := hx.2
  intro h0
  rw [h0, norm_zero] at h2
  linarith

lemma mem_closedBall_of_mem_marginDomain_half {s ρ : ℝ} (hρ : 0 < ρ) {x : ℂ}
    (hx : x ∈ marginDomain s (ρ / 2)) : x ∈ closedBall (0 : ℂ) ρ :=
  closedBall_subset_closedBall (by linarith) (mem_closedBall_of_mem_marginDomain hx)

lemma mem_ball_of_mem_marginDomain {s ρ : ℝ} (hρ : 0 < ρ) {x : ℂ} (hx : x ∈ marginDomain s (ρ / 2)) :
    x ∈ ball (0 : ℂ) ρ := by
  have h1 : ‖x‖ ≤ ρ / 2 := mem_closedBall_zero_iff.1 (mem_closedBall_of_mem_marginDomain hx)
  exact mem_ball_zero_iff.2 (by linarith)

/-- The margin domain `marginDomain s (ρ/2)` is nonempty when `0 < s ≤ ρ/2` (the point `s`), the `hne` input of the
generic value-version theorem. -/
theorem marginDomain_nonempty {s ρ : ℝ} (hs : 0 < s) (hsρ : s ≤ ρ / 2) :
    (marginDomain s (ρ / 2)).Nonempty := by
  refine ⟨(s : ℂ), ?_⟩
  unfold marginDomain
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs.le]
    exact hsρ
  · show s ≤ ‖(s : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg hs.le]

/-! ### Evaluation at a point of the margin domain -/

/-- Evaluation at `x ∈ A = marginDomain s (ρ/2)` on the trace space `C(closedBall 0 ρ, ℝ)`: the `ev` of
`MatedCRT.StoppedMarginValueVersions`. -/
noncomputable def marginEval {s ρ : ℝ} (hρ : 0 < ρ) (x : marginDomain s (ρ / 2)) : BallFns ρ → ℝ :=
  fun w => w ⟨x.1, mem_closedBall_of_mem_marginDomain_half hρ x.2⟩

theorem continuous_marginEval {s ρ : ℝ} (hρ : 0 < ρ) (x : marginDomain s (ρ / 2)) :
    Continuous (marginEval hρ x) :=
  continuous_eval_const _

/-! ### Zero is a supersolution: nonemptiness and evaluation lower bounds -/

/-- Zero is a supersolution of the obstacle problem `(μ, R, t)` for every measure `μ` and every `t ≥ 0`: it is continuous;
`LaplacianLE 0 μ` reads `0 ≤ ∫ φ dμ` for the nonnegative tests; and the obstacle `-tG_R(0,x) ≤ 0` because the Green
function is nonnegative (`HarmonicBalls.greenFunction_nonneg`). -/
theorem zero_mem_supersolutions (μ : Measure ℂ) {R t : ℝ} (ht : 0 ≤ t) :
    (0 : ℂ → ℝ) ∈ HarmonicBalls.supersolutions μ R 0 t := by
  refine ⟨continuousOn_const, ⟨locallyIntegrableOn_zero, fun φ _ hφ _ => ?_⟩, fun x _ _ => ?_⟩
  · simp only [Pi.zero_apply, zero_mul, integral_zero]
    exact integral_nonneg hφ
  · have hG : 0 ≤ HarmonicBalls.greenFunction (ball (0 : ℂ) R) 0 x :=
      HarmonicBalls.greenFunction_nonneg Metric.isBounded_ball 0 x
    show -t * HarmonicBalls.greenFunction (ball (0 : ℂ) R) 0 x ≤ 0
    rw [neg_mul]
    exact neg_nonpos.2 (mul_nonneg ht hG)

/-- The zero trace is a trace of a supersolution, so `superTraces μ R t` is nonempty for `t ≥ 0`. -/
theorem zero_mem_superTraces (μ : Measure ℂ) {R t : ℝ} (ht : 0 ≤ t) :
    (0 : BallFns R) ∈ superTraces μ R t :=
  ⟨0, zero_mem_supersolutions μ ht, fun _ => rfl⟩

/-- **Evaluation lower bound.** A trace of a supersolution satisfies `-tG_R(0,x) ≤ w x` at each `x ≠ 0` of
`closedBall 0 R`. -/
theorem lower_of_mem_superTraces {μ : Measure ℂ} {R t : ℝ} {w : BallFns R} (hw : w ∈ superTraces μ R t)
    {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) (hx0 : x ≠ 0) :
    -t * HarmonicBalls.greenFunction (ball (0 : ℂ) R) 0 x ≤ w ⟨x, hx⟩ := by
  obtain ⟨u, hu, hagree⟩ := hw
  obtain ⟨-, -, hobs⟩ := hu
  have e : u x = w ⟨x, hx⟩ := hagree ⟨x, hx⟩
  rw [← e]
  exact hobs x hx hx0

/-! ### The real infimum of the traces is the least supersolution on the punctured disk -/

/-- The evaluations at `x ∈ closedBall 0 R` of the traces are the evaluations of the supersolutions. -/
theorem image_superTraces_eq (μ : Measure ℂ) {R t : ℝ} {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) :
    (fun w : BallFns R => w ⟨x, hx⟩) '' superTraces μ R t =
      (fun u : ℂ → ℝ => u x) '' HarmonicBalls.supersolutions μ R 0 t := by
  ext r
  constructor
  · rintro ⟨w, ⟨u, hu, hagree⟩, rfl⟩
    exact ⟨u, hu, hagree ⟨x, hx⟩⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, restrict_mem_superTraces hu, rfl⟩

/-- **Defining identity.** At `x ∈ closedBall 0 R`, the least supersolution `v_R(μ,t)(x)` is the real infimum of the
evaluations of the traces of the supersolutions. -/
theorem leastSupersolution_eq_sInf_image (μ : Measure ℂ) {R t : ℝ} {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) :
    HarmonicBalls.leastSupersolution μ R 0 t x =
      sInf ((fun w : BallFns R => w ⟨x, hx⟩) '' superTraces μ R t) := by
  rw [image_superTraces_eq μ hx]
  rfl

/-- The evaluations of the traces at `x ∈ closedBall 0 R` are nonempty (the zero trace is one) for `t ≥ 0`. -/
theorem nonempty_image_superTraces (μ : Measure ℂ) {R t : ℝ} (ht : 0 ≤ t) {x : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) R) :
    ((fun w : BallFns R => w ⟨x, hx⟩) '' superTraces μ R t).Nonempty :=
  ⟨(0 : BallFns R) ⟨x, hx⟩, Set.mem_image_of_mem (fun w : BallFns R => w ⟨x, hx⟩) (zero_mem_superTraces μ ht)⟩

/-- At `x ≠ 0` the evaluations of the traces are bounded below by `-tG_R(0,x)`, so the real infimum is not a
totalization of an unbounded-below set. -/
theorem bddBelow_image_superTraces {μ : Measure ℂ} {R t : ℝ} {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R)
    (hx0 : x ≠ 0) :
    BddBelow ((fun w : BallFns R => w ⟨x, hx⟩) '' superTraces μ R t) := by
  refine ⟨-t * HarmonicBalls.greenFunction (ball (0 : ℂ) R) 0 x, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact lower_of_mem_superTraces hw hx hx0

/-- At `x ∈ closedBall 0 R \ {0}` the real infimum of the trace evaluations is a genuine infimum, equal to the least
supersolution `v_R(μ,t)(x)`. -/
theorem isGLB_image_superTraces (μ : Measure ℂ) {R t : ℝ} (ht : 0 ≤ t) {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R)
    (hx0 : x ≠ 0) :
    IsGLB ((fun w : BallFns R => w ⟨x, hx⟩) '' superTraces μ R t) (HarmonicBalls.leastSupersolution μ R 0 t x) := by
  rw [leastSupersolution_eq_sInf_image μ hx]
  exact isGLB_csInf (nonempty_image_superTraces μ ht hx) (bddBelow_image_superTraces hx hx0)

/-- Evaluation bounds for the least supersolution on the punctured disk: `-tG_R(0,x) ≤ v_R(μ,t)(x) ≤ 0`. -/
theorem neg_mul_green_le_leastSupersolution_le_zero (μ : Measure ℂ) {R t : ℝ} (ht : 0 ≤ t) {x : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) R) (hx0 : x ≠ 0) :
    -t * HarmonicBalls.greenFunction (ball (0 : ℂ) R) 0 x ≤ HarmonicBalls.leastSupersolution μ R 0 t x ∧
      HarmonicBalls.leastSupersolution μ R 0 t x ≤ 0 := by
  rw [leastSupersolution_eq_sInf_image μ hx]
  refine ⟨le_csInf (nonempty_image_superTraces μ ht hx) ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact lower_of_mem_superTraces hw hx hx0
  · exact csInf_le (bddBelow_image_superTraces hx hx0) ⟨0, zero_mem_superTraces μ ht, rfl⟩

/-! ### The actual surplus and its continuity on `marginDomain s (ρ/2)` -/

/-- The actual surplus `v_ρ(μ,t)(x) + tG_ρ(0,x)` of the obstacle problem `(μ, ρ, t)`, the function of
`steps2-r3.tex:3374-3388`. -/
noncomputable def actualSurplus (μ : Measure ℂ) (ρ t : ℝ) (x : ℂ) : ℝ :=
  HarmonicBalls.leastSupersolution μ ρ 0 t x + t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x

/-- **Continuity of the actual surplus on the margin domain.** Under the hypotheses of the existing continuity result
`MatedCRT.coneFamily_leastSupersolution_continuous` (`IsConeHarmonicBallFamily μ Λ`, `0 < ρ`, `0 < t`,
`t < clusterExitTime Λ ρ`), and `0 < s`, the actual surplus is continuous on `marginDomain s (ρ/2)`, which avoids the pole. -/
theorem continuousOn_actualSurplus_marginDomain {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {ρ t s : ℝ}
    (hfam : MatedCRT.IsConeHarmonicBallFamily μ Λ) (hρ : 0 < ρ) (ht : 0 < t)
    (hT : t < MatedCRT.clusterExitTime Λ ρ) (hs : 0 < s) :
    ContinuousOn (actualSurplus μ ρ t) (marginDomain s (ρ / 2)) := by
  have hsub : marginDomain s (ρ / 2) ⊆ closedBall (0 : ℂ) ρ := fun x hx =>
    mem_closedBall_of_mem_marginDomain_half hρ hx
  have hsub' : marginDomain s (ρ / 2) ⊆ ball (0 : ℂ) ρ \ {0} := fun x hx =>
    ⟨mem_ball_of_mem_marginDomain hρ hx, ne_zero_of_mem_marginDomain hs hx⟩
  have hv := (MatedCRT.coneFamily_leastSupersolution_continuous hfam hρ ht hT).mono hsub
  have hG := (continuousOn_greenFunction_zero hρ).mono hsub'
  show ContinuousOn (fun x => HarmonicBalls.leastSupersolution μ ρ 0 t x +
    t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x) (marginDomain s (ρ / 2))
  exact hv.add (continuousOn_const.mul hG)

/-- **The continuous surplus on `A = marginDomain s (ρ/2)`**, as an element of `C(A, ℝ)`, from the continuity of the actual
surplus on `A`. -/
noncomputable def continuousSurplusMargin {μ : Measure ℂ} {ρ t s : ℝ}
    (hc : ContinuousOn (actualSurplus μ ρ t) (marginDomain s (ρ / 2))) : C(marginDomain s (ρ / 2), ℝ) :=
  ⟨fun x => actualSurplus μ ρ t x.1, hc.comp_continuous continuous_subtype_val (fun x => x.2)⟩

lemma continuousSurplusMargin_apply {μ : Measure ℂ} {ρ t s : ℝ}
    (hc : ContinuousOn (actualSurplus μ ρ t) (marginDomain s (ρ / 2))) (x : marginDomain s (ρ / 2)) :
    continuousSurplusMargin hc x = actualSurplus μ ρ t x.1 :=
  rfl

/-! ### The `hbdd` and `hId` inputs of the generic value-version theorem, for the trace sections -/

/-- **`hbdd` input.** For `0 < s` and `0 ≤ t`, each trace set `superTraces μ ρ t` is nonempty and, at each point of
`A = marginDomain s (ρ/2)`, bounded below under the evaluation `marginEval hρ x`. -/
theorem hbdd_marginEval {μ : Measure ℂ} {s ρ t : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (ht : 0 ≤ t)
    (x : marginDomain s (ρ / 2)) :
    (superTraces μ ρ t).Nonempty ∧ BddBelow (marginEval hρ x '' superTraces μ ρ t) :=
  ⟨⟨0, zero_mem_superTraces μ ht⟩,
    bddBelow_image_superTraces (μ := μ) (R := ρ) (t := t) (mem_closedBall_of_mem_marginDomain_half hρ x.2)
      (ne_zero_of_mem_marginDomain hs x.2)⟩

/-- **`hId` input (defining identity).** The real infimum of the evaluations of the traces, shifted by `tG_ρ(0,·)`, is the
actual surplus at each `x ∈ A`. The infimum is the one of the actual trace set, not of an arbitrary family. -/
theorem hId_marginEval {μ : Measure ℂ} {s ρ t : ℝ} (hρ : 0 < ρ) (x : marginDomain s (ρ / 2)) :
    sInf (marginEval hρ x '' superTraces μ ρ t) + t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x.1 =
      actualSurplus μ ρ t x.1 := by
  have h : HarmonicBalls.leastSupersolution μ ρ 0 t x.1 = sInf (marginEval hρ x '' superTraces μ ρ t) :=
    leastSupersolution_eq_sInf_image μ (mem_closedBall_of_mem_marginDomain_half hρ x.2)
  show sInf (marginEval hρ x '' superTraces μ ρ t) + t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x.1 =
    HarmonicBalls.leastSupersolution μ ρ 0 t x.1 + t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x.1
  rw [h]

/-- **`hId` input in the form of the generic theorem:** the shifted infimum equals the continuous surplus
`continuousSurplusMargin hc` at each point of `A`, under the continuity `hc`. -/
theorem hId_marginEval_continuousSurplus {μ : Measure ℂ} {s ρ t : ℝ} (hρ : 0 < ρ)
    (hc : ContinuousOn (actualSurplus μ ρ t) (marginDomain s (ρ / 2))) (x : marginDomain s (ρ / 2)) :
    sInf (marginEval hρ x '' superTraces μ ρ t) + t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x.1 =
      continuousSurplusMargin hc x :=
  hId_marginEval hρ x

/-! ### The section identity from the Borel obstacle code (`CodeSectionStmt`, reused) -/

/-- **Section identity.** `CodeSectionStmt` (proved as `codeSectionStmt_holds`, reused and not reproved) gives a measurable
`𝒜 ⊆ PosCircleFns × BallFns R` whose section at `c ω` is `superTraces (S.μ ω) R t` for almost every `ω`. -/
theorem exists_relSection_ae_eq_superTraces (𝒮 : SpaceFillingSLEModel) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (c : Ω → PosCircleFns)
    (hc : Measurable c)
    (hcirc : ∀ᵐ ω ∂S.P, ∀ p : PosCircleIndex, c ω p = S.hcirc ω (p.1 : ℝ) p.2) {R t : ℝ} (hR : 0 < R)
    (ht : 0 < t) :
    ∃ 𝒜 : Set (PosCircleFns × BallFns R), MeasurableSet 𝒜 ∧
      ∀ᵐ ω ∂S.P, relSection 𝒜 (c ω) = superTraces (S.μ ω) R t := by
  obtain ⟨𝒜, h𝒜, hae⟩ := codeSectionStmt_holds 𝒮 γ hγ hγ2 Ω S hS c hc hcirc R hR t ht
  exact ⟨𝒜, h𝒜, hae.mono fun ω hω => Set.ext fun w => hω w⟩

/-- **Almost-sure `hbdd` and `hId` inputs** of the generic value-version theorem (`_ae` form) for the sections
`relSection 𝒜 (c ω)`, which equal the trace sets `superTraces (μ ω) ρ t` almost surely. -/
theorem ae_hbdd_hId_marginEval {s ρ t : ℝ} {X Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Ω → Measure ℂ} {c : Ω → X} {𝒜 : Set (X × BallFns ρ)} (hρ : 0 < ρ) (hs : 0 < s) (ht : 0 ≤ t)
    (hsec : ∀ᵐ ω ∂P, relSection 𝒜 (c ω) = superTraces (μ ω) ρ t) :
    (∀ᵐ ω ∂P, ∀ x : marginDomain s (ρ / 2),
        (relSection 𝒜 (c ω)).Nonempty ∧ BddBelow (marginEval hρ x '' relSection 𝒜 (c ω))) ∧
    (∀ᵐ ω ∂P, ∀ x : marginDomain s (ρ / 2),
        sInf (marginEval hρ x '' relSection 𝒜 (c ω)) +
          t * HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x.1 = actualSurplus (μ ω) ρ t x.1) := by
  constructor
  · exact hsec.mono fun ω hω x => by
      rw [hω]
      exact hbdd_marginEval hρ hs ht x
  · exact hsec.mono fun ω hω x => by
      rw [hω]
      exact hId_marginEval hρ x

/-- **Almost-sure continuity input.** The cone-family hypotheses of `coneFamily_leastSupersolution_continuous`, holding
almost surely, give the continuity of the actual surplus on `marginDomain s (ρ/2)` almost surely. -/
theorem ae_continuousOn_actualSurplus {s ρ t : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Ω → Measure ℂ} {Λ : Ω → ℝ → Set ℂ} (hρ : 0 < ρ) (ht : 0 < t) (hs : 0 < s)
    (hfam : ∀ᵐ ω ∂P, MatedCRT.IsConeHarmonicBallFamily (μ ω) (Λ ω))
    (hT : ∀ᵐ ω ∂P, t < MatedCRT.clusterExitTime (Λ ω) ρ) :
    ∀ᵐ ω ∂P, ContinuousOn (actualSurplus (μ ω) ρ t) (marginDomain s (ρ / 2)) :=
  (hfam.and hT).mono fun _ h => continuousOn_actualSurplus_marginDomain h.1 hρ ht h.2 hs

end MatedCRT.StoppedActualSurplus
