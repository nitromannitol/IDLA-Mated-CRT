import MatedCRT.FirstPass.Derived.WindowChartFieldMeasurable
import MarkovProcess.Path.ExitTimeShift

/-!
# Measurability of the chart laws of the windows

For the normalized inverse chart `ψ = windowChart a u b η` of the window `(a, u, b)` of the curve of a joint-limit
sample `q`, the window chart law `windowChartLaw a u b ψ q` (the image of the limiting law `P_{η(u)}` under "stop at
the exit from the window `U` and apply `ψ`", the law `P^D_0` of Berestycki–Gwynne (2020), (7.34)) is a measurable
function of `q` (`measurable_windowChartLaw_windowChart`):

* if the window has no inverse chart, then `ψ = 0` (`windowChart_eq_zero`) and the chart image of every path is the
  constant path `0`;
* if it has one, then `U = φ(𝔻)` for the normalized conformal map `φ` of the closed disc, and a path stays in `U` up
  to time `t` iff it stays in the image `φ(B̄(0, r))` of a smaller closed disc (`forall_le_mem_image_ball_iff`); the
  pairs `(φ, f)` such that `f([0, t]) ⊆ φ(B̄(0, r))` form a closed set, so the exit time from the window is a
  measurable function of the sample and the path (`measurable_windowExitTime`);
* hence the stopped chart path is jointly measurable (`measurable_windowStopPath`), and its image law under the
  Markov kernel `q ↦ P_{η(u)}` is a measurable function of `q` (`Kernel.measurable_kernel_prodMk_left`).

`BG20NormalizedChartLBMInput` is `BG20NormalizedChartKernelInput` without the measurability of the window chart
laws, and implies it (`bg20NormalizedChartKernelInput_of_normalizedChartLBMInput`), hence `BG20ChartFieldInput`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-! ### Paths staying in the image of a disc -/

/-- The pairs `(φ, f)` such that `f(s) ∈ φ(B̄(0, r))` form a closed set. -/
theorem isClosed_setOf_apply_mem_image_closedBall (s : ℝ≥0) (r : ℝ) :
    IsClosed {p : C(ℂ, ℂ) × ContinuousPath ℂ | p.2 s ∈ p.1 '' closedBall 0 r} :=
  isClosed_setOf_exists_mem_of_isCompact (isCompact_closedBall (0 : ℂ) r)
    (P := fun (p : C(ℂ, ℂ) × ContinuousPath ℂ) (y : ℂ) => p.1 y = p.2 s)
    (isClosed_eq (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
      ((continuous_eval_const s).comp (continuous_snd.comp continuous_fst)))

/-- The pairs `(φ, f)` such that `f([0, t]) ⊆ φ(B̄(0, r))` form a closed set. -/
theorem isClosed_setOf_forall_le_mem_image_closedBall (t : ℝ≥0) (r : ℝ) :
    IsClosed {p : C(ℂ, ℂ) × ContinuousPath ℂ | ∀ s ≤ t, p.2 s ∈ p.1 '' closedBall 0 r} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_setOf_apply_mem_image_closedBall s r

/-- **A path stays in the image of the open disc iff it stays in the image of a smaller closed disc**, for a map `φ`
injective on the closed unit disc. -/
theorem forall_le_mem_image_ball_iff {φ : C(ℂ, ℂ)} (hφ : InjOn φ (closedBall 0 1)) (f : ContinuousPath ℂ)
    (t : ℝ≥0) :
    (∀ s ≤ t, f s ∈ φ '' ball 0 1) ↔
      ∃ n : ℕ, ∀ s ≤ t, f s ∈ φ '' closedBall 0 (1 - 1 / ((n : ℝ) + 1)) := by
  constructor
  · intro h
    have hLc : IsClosed (closedBall (0 : ℂ) 1 ∩ φ ⁻¹' (f '' Icc 0 t)) :=
      isClosed_closedBall.inter ((isCompact_Icc.image f.continuous).isClosed.preimage φ.continuous)
    have hLb : closedBall (0 : ℂ) 1 ∩ φ ⁻¹' (f '' Icc 0 t) ⊆ ball 0 1 := by
      rintro w ⟨hw, s, hs, hsw⟩
      obtain ⟨w', hw', hw'w⟩ := h s hs.2
      rw [hφ hw (ball_subset_closedBall hw') (hsw.symm.trans hw'w.symm)]
      exact hw'
    obtain ⟨r', hr', hLr'⟩ := exists_lt_subset_ball hLc hLb
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hr')
    refine ⟨n, fun s hs => ?_⟩
    obtain ⟨w', hw', hw'w⟩ := h s hs
    have hw'L : w' ∈ closedBall (0 : ℂ) 1 ∩ φ ⁻¹' (f '' Icc 0 t) :=
      ⟨ball_subset_closedBall hw', s, ⟨zero_le, hs⟩, hw'w.symm⟩
    refine ⟨w', ?_, hw'w⟩
    have hr := hLr' hw'L
    rw [mem_ball_zero_iff] at hr
    rw [mem_closedBall_zero_iff]
    linarith
  · rintro ⟨n, hn⟩ s hs
    obtain ⟨w, hw, hwf⟩ := hn s hs
    refine ⟨w, ?_, hwf⟩
    have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    rw [mem_closedBall_zero_iff] at hw
    rw [mem_ball_zero_iff]
    linarith

/-! ### The exit time from the window -/

/-- If the window `(a, u, b)` of the sample `q` has no inverse chart, then its normalized inverse chart is `0`. -/
theorem windowChart_eq_zero {a u b : ℝ} {q : JointSample} (hq : q ∉ windowChartSet a u b) :
    windowChart a u b q.1.2 = 0 := by
  have hne : ¬∃ φ, (q.1.2, φ) ∈ windowDiscMapGraph a u b := by
    rintro ⟨φ, hφ⟩
    exact hq ⟨_, (mem_windowDiscMapGraph.1 hφ).1.isInverseChart_discInverseExt⟩
  have h0 : ¬InjOn ⇑(0 : C(ℂ, ℂ)) (closedBall 0 1) := fun h =>
    zero_ne_one (h (mem_closedBall_self zero_le_one) (mem_closedBall_zero_iff.2 norm_one.le) rfl)
  ext x
  rw [windowChart, windowDiscMap, dite_eq_right hne, discInverseExt_apply_of_not_injOn h0,
    ContinuousMap.zero_apply]

open Classical in
/-- The exit time of the path `p.2` from the window `(a, u, b)` of the sample `p.1`, if the window has an inverse
chart (`∞` otherwise). -/
noncomputable def windowExitTime (a u b : ℝ) (p : JointSample × ContinuousPath ℂ) : ℝ≥0∞ :=
  if p.1 ∈ windowChartSet a u b then ContinuousPath.exitTime (windowDomain p.1.1.2 a u b) p.2 else ⊤

theorem windowExitTime_of_mem {a u b : ℝ} {p : JointSample × ContinuousPath ℂ}
    (hp : p.1 ∈ windowChartSet a u b) :
    windowExitTime a u b p = ContinuousPath.exitTime (windowDomain p.1.1.2 a u b) p.2 := by
  rw [windowExitTime, ite_eq_left hp]

/-- **The exit time from the window is a measurable function of the sample and the path.** -/
theorem measurable_windowExitTime (a u b : ℝ) : Measurable (windowExitTime a u b) := by
  have hφ : Measurable fun p : JointSample × ContinuousPath ℂ => (windowDiscMap a u b p.1.1.2, p.2) :=
    (((measurable_windowDiscMap a u b).comp measurable_jointSample_curve).comp measurable_fst).prodMk
      measurable_snd
  refine measurable_of_Iic fun x => ?_
  by_cases hx : x = ⊤
  · rw [hx, Iic_top, preimage_univ]
    exact MeasurableSet.univ
  obtain ⟨t, rfl⟩ : ∃ t : ℝ≥0, (t : ℝ≥0∞) = x := ⟨x.toNNReal, ENNReal.coe_toNNReal hx⟩
  have heq : windowExitTime a u b ⁻¹' Iic (t : ℝ≥0∞) =
      (Prod.fst ⁻¹' windowChartSet a u b) ∩
        (⋃ n : ℕ, (fun p : JointSample × ContinuousPath ℂ => (windowDiscMap a u b p.1.1.2, p.2)) ⁻¹'
          {p : C(ℂ, ℂ) × ContinuousPath ℂ |
            ∀ s ≤ t, p.2 s ∈ p.1 '' closedBall 0 (1 - 1 / ((n : ℝ) + 1))})ᶜ := by
    ext p
    by_cases hq : p.1 ∈ windowChartSet a u b
    · have hD := (isNormalizedDiscMap_of_mem_windowChartSet hq).isDiscMap
      have key := forall_le_mem_image_ball_iff hD.injOn p.2 t
      rw [hD.image_ball] at key
      have hU := isOpen_windowDomain p.1.1.2 a u b
      constructor
      · intro hle
        have hle' : ContinuousPath.exitTime (windowDomain p.1.1.2 a u b) p.2 ≤ t := by
          rw [← windowExitTime_of_mem hq]
          exact hle
        refine ⟨hq, fun hn => ?_⟩
        obtain ⟨n, hn⟩ := mem_iUnion.1 hn
        obtain ⟨⟨s, hs⟩, hsU⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy _ hU t p.2).1 hle'
        exact hsU (key.2 ⟨n, hn⟩ s hs)
      · rintro ⟨-, hn⟩
        show windowExitTime a u b p ≤ t
        rw [windowExitTime_of_mem hq]
        by_contra hlt
        exact hn (mem_iUnion.2 (key.1 fun s hs => ContinuousPath.mem_of_lt_exitTime _ _ _
          (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (not_le.1 hlt))))
    · have hT : windowExitTime a u b p = ⊤ := by
        rw [windowExitTime, ite_eq_right hq]
      constructor
      · intro hle
        have hle' : windowExitTime a u b p ≤ t := hle
        rw [hT] at hle'
        exact absurd (top_le_iff.1 hle') ENNReal.coe_ne_top
      · rintro ⟨hq', -⟩
        exact (hq hq').elim
  rw [heq]
  exact (measurable_fst (measurableSet_windowChartSet a u b)).inter
    (MeasurableSet.iUnion fun _ => hφ (isClosed_setOf_forall_le_mem_image_closedBall _ _).measurableSet).compl

/-! ### The stopped chart path and the chart law -/

/-- The chart image `ψ ∘ f(· ∧ τ)` of the path `f = p.2` stopped at its exit time `τ` from the window `(a, u, b)` of
the sample `p.1`, for the normalized inverse chart `ψ` of the window. -/
noncomputable def windowStopPath (a u b : ℝ) (p : JointSample × ContinuousPath ℂ) : ContinuousPath ℂ :=
  (windowChart a u b p.1.1.2).comp (p.2.comp (exitClamp (windowExitTime a u b p)))

theorem windowStopPath_eq (a u b : ℝ) (p : JointSample × ContinuousPath ℂ) :
    windowStopPath a u b p =
      chartStopPath (windowDomain p.1.1.2 a u b) (windowChart a u b p.1.1.2) p.2 := by
  by_cases hp : p.1 ∈ windowChartSet a u b
  · rw [windowStopPath, windowExitTime_of_mem hp]
    rfl
  · rw [windowStopPath, chartStopPath, windowChart_eq_zero hp]
    ext t
    simp only [ContinuousMap.comp_apply, ContinuousMap.zero_apply]

/-- **The stopped chart path is a measurable function of the sample and the path.** -/
theorem measurable_windowStopPath (a u b : ℝ) : Measurable (windowStopPath a u b) := by
  have hτ := measurable_windowExitTime a u b
  have hψ : Measurable fun p : JointSample × ContinuousPath ℂ => windowChart a u b p.1.1.2 :=
    (measurable_windowChart a u b).comp (measurable_jointSample_curve.comp measurable_fst)
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hT : Measurable fun p : JointSample × ContinuousPath ℂ => exitClamp (windowExitTime a u b p) t := by
    simp only [exitClamp_apply]
    exact Measurable.ite (hτ (measurableSet_singleton ⊤)) measurable_const
      (measurable_const.min (ENNReal.measurable_toNNReal.comp hτ))
  have hf : Measurable fun p : JointSample × ContinuousPath ℂ =>
      p.2 (exitClamp (windowExitTime a u b p) t) :=
    (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp (measurable_snd.prodMk hT)
  exact (ContinuousEval.continuous_eval (F := C(ℂ, ℂ))).measurable.comp (hψ.prodMk hf)

/-- The Markov kernel `q ↦ P_{η(u)}`: the limiting law of the sample `q` at the curve point `η(u)`. -/
noncomputable def windowPointLawKernel (u : ℝ) : Kernel JointSample (ContinuousPath ℂ) where
  toFun q := (q.2 (q.1.2 u) : Measure (ContinuousPath ℂ))
  measurable' := measurable_subtype_coe.comp
    ((ContinuousEval.continuous_eval (F := PathLawFamily)).measurable.comp
      (measurable_snd.prodMk ((continuous_eval_const u).measurable.comp measurable_jointSample_curve)))

theorem windowPointLawKernel_apply (u : ℝ) (q : JointSample) :
    windowPointLawKernel u q = (q.2 (q.1.2 u) : Measure (ContinuousPath ℂ)) :=
  rfl

instance isMarkovKernel_windowPointLawKernel (u : ℝ) : IsMarkovKernel (windowPointLawKernel u) :=
  ⟨fun q => by
    rw [windowPointLawKernel_apply]
    infer_instance⟩

theorem windowChartLaw_windowChart_apply (a u b : ℝ) (q : JointSample) {s : Set (ContinuousPath ℂ)}
    (hs : MeasurableSet s) :
    windowChartLaw a u b (windowChart a u b q.1.2) q s =
      windowPointLawKernel u q (Prod.mk q ⁻¹' (windowStopPath a u b ⁻¹' s)) := by
  have hf : chartStopPath (windowDomain q.1.2 a u b) (windowChart a u b q.1.2) =
      fun f => windowStopPath a u b (q, f) :=
    funext fun f => (windowStopPath_eq a u b (q, f)).symm
  have hG : Measurable fun f : ContinuousPath ℂ => windowStopPath a u b (q, f) :=
    (measurable_windowStopPath a u b).comp measurable_prodMk_left
  rw [windowChartLaw, chartLaw, hf, Measure.map_apply hG hs]
  rfl

/-- **The chart law of a window for its normalized inverse chart is a measurable function of the sample.** -/
theorem measurable_windowChartLaw_windowChart (a u b : ℝ) :
    Measurable fun q : JointSample => windowChartLaw a u b (windowChart a u b q.1.2) q := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  convert Kernel.measurable_kernel_prodMk_left (κ := windowPointLawKernel u)
    (measurable_windowStopPath a u b hs) using 1
  funext q
  exact windowChartLaw_windowChart_apply a u b q hs

/-! ### The chart input with measurable chart fields and chart laws -/

/-- **Literature input (Berestycki–Gwynne (2020), Lemma 7.20 without the time change, and Lemma 7.21, on the joint
limit, with the normalized inverse charts).** As `BG20NormalizedChartKernelInput`, without the measurability of the
window chart laws (`measurable_windowChartLaw_windowChart`). For times `a < u < b < a' < u' < b'`:

* almost surely the two windows have inverse charts at the curve points;
* the kernel `K` depends measurably on the chart field;
* (Lemma 7.20 without the time change; Berestycki (2015), Theorem 1.3) almost surely the chart image of the
  Liouville Brownian law of the field from `η(u)` is `K` of the chart field, and likewise for the second window;
* (Lemma 7.21) the pairs (chart field, window chart law) of the two windows are independent. -/
def BG20NormalizedChartLBMInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ ν'' : Measure JointSample, IsProbabilityMeasure ν'' →
    (∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), interpWalkLaw S η' (ε n) ω) ∂S.P)
        atTop (𝓝 (∫ q, f q ∂ν''))) →
    (∀ᵐ q ∂ν'', ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, q.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ q.1.1.1) z) →
    ∀ a u b a' u' b' : ℝ, a < u → u < b → b < a' → a' < u' → u' < b' →
    ∃ K : (𝓓(unitDiscOpens, ℝ) → ℝ) → Measure (ContinuousPath ℂ),
      (∀ᵐ q ∂ν'', ∃ ψ, IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) ψ) ∧
      (∀ᵐ q ∂ν'', ∃ ψ, IsInverseChart (windowDomain q.1.2 a' u' b') (q.1.2 u') ψ) ∧
      Measurable K ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q =
        K (windowChartField γ a u b (windowChart a u b q.1.2) q)) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a' u' b' (windowChart a' u' b' q.1.2) q =
        K (windowChartField γ a' u' b' (windowChart a' u' b' q.1.2) q)) ∧
      IndepFun (fun q : JointSample => (windowChartField γ a u b (windowChart a u b q.1.2) q,
          windowChartLaw a u b (windowChart a u b q.1.2) q))
        (fun q : JointSample => (windowChartField γ a' u' b' (windowChart a' u' b' q.1.2) q,
          windowChartLaw a' u' b' (windowChart a' u' b' q.1.2) q)) ν''

/-- The input without the measurability of the window chart laws implies `BG20NormalizedChartKernelInput`. -/
theorem bg20NormalizedChartKernelInput_of_normalizedChartLBMInput {𝒮 : SpaceFillingSLEModel}
    (hC : BG20NormalizedChartLBMInput 𝒮) : BG20NormalizedChartKernelInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
    hau hub hba' ha'u' hu'b'
  obtain ⟨K, hψ, hψ', hK, hb, hb', hind⟩ :=
    hC γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
      hau hub hba' ha'u' hu'b'
  exact ⟨K, hψ, hψ', hK, measurable_windowChartLaw_windowChart a u b,
    measurable_windowChartLaw_windowChart a' u' b', hb, hb', hind⟩

/-- The input without the measurability of the window chart laws and chart fields implies
`BG20ChartFieldInput`. -/
theorem bg20ChartFieldInput_of_normalizedChartLBMInput {𝒮 : SpaceFillingSLEModel}
    (hC : BG20NormalizedChartLBMInput 𝒮) : BG20ChartFieldInput 𝒮 :=
  bg20ChartFieldInput_of_kernelInput (bg20NormalizedChartKernelInput_of_normalizedChartLBMInput hC)

end MatedCRT
