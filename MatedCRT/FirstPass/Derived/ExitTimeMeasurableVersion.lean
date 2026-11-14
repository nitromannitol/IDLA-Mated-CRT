import MatedCRT.FirstPass.Closure.M0CdfMeasurable
import MatedCRT.FirstPass.Derived.ExitTimeClockAtExit
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.JointCauchySubsequence

/-!
# A jointly measurable version of the Liouville Brownian exit time from `B_{1/2}`

The LQG clock `S.clock ω` of a valid environment is characterised only by convergence in probability of the
approximating clocks `lqgClockApprox` along the dyadic scales (`IsLQGClock`; Garban-Rhodes-Vargas 2016, Theorem 2.7 (2);
Berestycki 2015, Theorem 1.2), so the exit time `T(ω, b) = lbmExitTime (S.clock ω) (ball 0 (1/2)) b` of Liouville
Brownian motion need not be jointly measurable in the environment `ω` and the Brownian path `b`. This file constructs a
jointly measurable version of it under `S.P ⊗ P₀` (`P₀ = planarBrownianMotion 0`).

* `ExitTimeVersion.measurable_lqgClockApprox_of_measurable_field`,
  `ExitTimeVersion.measurable_lqgClockApprox_comp_time`: for a field `φ` whose circle averages at the scale `ε` are
  jointly measurable in `(ω, z)`, the approximating clock `lqgClockApprox γ (φ ω) ε b t` is jointly measurable in
  `((ω, b), t)`, and so is its value `lqgClockApprox γ (φ ω) ε b (τ b)` at a measurable random time `τ`
  (for instance the Brownian exit time `τ_{B_{1/2}}`, or `τ_{B_{1/2}} ∧ N`).
* `ExitTimeVersion.exists_strictMono_ae_tendsto_of_ae_cauchy`: measurable functions on `Ω × X` which are, for
  `P`-almost every `ω`, Cauchy in `Q`-probability have a deterministic subsequence converging `P ⊗ Q`-almost surely
  (dominated convergence for the sections; `exists_strictMono_joint_cauchy`).
* `ExitTimeVersion.exists_measurable_version_of_ae_tendstoInMeasure`: if, for `P`-almost every `ω`, the sections
  converge in `Q`-probability to some (not necessarily measurable) `Y ω`, then `Y` has a jointly measurable version.
* `MatedCRTEnv.IsValid.exists_measurable_lbmExitTime_ball_half_version`: for a valid environment, a measurable
  `T* : Ω × ContinuousPath ℂ → [0, ∞)` with `T*(ω, ·) = lbmExitTime (S.clock ω) (ball 0 (1/2))` `P₀`-a.s. for
  `S.P`-a.e. `ω`; hence the annealed exit-time distribution function of `MatedCRTEnv.m₀` (eq:mo, line 727) is
  `s ↦ (S.P ⊗ P₀) {T* ≤ s}`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

namespace ExitTimeVersion

/-! ## Joint measurability of the approximating clocks -/

/-- If the circle averages `(ω, z) ↦ φ ω ε z` of a random field at the scale `ε` are jointly measurable, then the
approximating LQG clock `∫_0^t ε^{γ²/2} e^{γ φ_ε(b_s)} ds` is jointly measurable in the environment, the path and the
time. -/
theorem measurable_lqgClockApprox_of_measurable_field {Ω : Type*} [MeasurableSpace Ω] {φ : Ω → ℝ → ℂ → ℝ}
    (γ : ℝ) {ε : ℝ} (hφ : Measurable fun p : Ω × ℂ => φ p.1 ε p.2) :
    Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ≥0 => lqgClockApprox γ (φ q.1.1) ε q.1.2 q.2 := by
  have heval : Measurable fun x : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ => x.1.1.2 x.2.toNNReal := by
    have hc : Continuous fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal :=
      ContinuousEval.continuous_eval.comp
        (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
    exact hc.measurable.comp (measurable_fst.fst.snd.prodMk measurable_snd)
  have hg : Measurable fun x : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * φ x.1.1.1 ε (x.1.1.2 x.2.toNNReal)) :=
    measurable_const.mul (Real.continuous_exp.measurable.comp
      (measurable_const.mul (hφ.comp (measurable_fst.fst.fst.prodMk heval))))
  have hD : MeasurableSet {x : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ | x.2 ≤ (x.1.2 : ℝ)} :=
    measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp measurable_fst.snd)
  have hF : Measurable fun x : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
      (Iic (x.1.2 : ℝ)).indicator
        (fun s => ε ^ (γ ^ 2 / 2) * Real.exp (γ * φ x.1.1.1 ε (x.1.1.2 s.toNNReal))) x.2 := by
    have heq : (fun x : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
        (Iic (x.1.2 : ℝ)).indicator
          (fun s => ε ^ (γ ^ 2 / 2) * Real.exp (γ * φ x.1.1.1 ε (x.1.1.2 s.toNNReal))) x.2) =
        {x : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ | x.2 ≤ (x.1.2 : ℝ)}.indicator
          (fun x => ε ^ (γ ^ 2 / 2) * Real.exp (γ * φ x.1.1.1 ε (x.1.1.2 x.2.toNNReal))) := by
      funext x
      by_cases hx : x.2 ≤ (x.1.2 : ℝ)
      · rw [Set.indicator_of_mem (show x.2 ∈ Iic (x.1.2 : ℝ) from hx),
          Set.indicator_of_mem
            (show x ∈ {y : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ | y.2 ≤ (y.1.2 : ℝ)} from hx)]
      · rw [Set.indicator_of_notMem (show x.2 ∉ Iic (x.1.2 : ℝ) from hx),
          Set.indicator_of_notMem
            (show x ∉ {y : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ | y.2 ≤ (y.1.2 : ℝ)} from hx)]
    rw [heq]
    exact hg.indicator hD
  have hI := hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))
  have hfun : (fun q : (Ω × ContinuousPath ℂ) × ℝ≥0 => lqgClockApprox γ (φ q.1.1) ε q.1.2 q.2) =
      fun q => ∫ s, (Iic (q.2 : ℝ)).indicator
        (fun s => ε ^ (γ ^ 2 / 2) * Real.exp (γ * φ q.1.1 ε (q.1.2 s.toNNReal))) s
          ∂(volume.restrict (Ioi (0 : ℝ))) := by
    funext q
    show lqgClockApprox γ (φ q.1.1) ε q.1.2 q.2 = _
    rw [lqgClockApprox, intervalIntegral.integral_of_le q.2.coe_nonneg,
      setIntegral_indicator measurableSet_Iic,
      show Ioi (0 : ℝ) ∩ Iic (q.2 : ℝ) = Ioc 0 (q.2 : ℝ) from rfl]
  rw [hfun]
  exact hI.measurable

/-- The approximating LQG clock of a field with jointly measurable circle averages, evaluated at a measurable random
time `τ b` of the path (e.g. the Brownian exit time of `B_{1/2}`, or its minimum with `N`), is jointly measurable in
the environment and the path. -/
theorem measurable_lqgClockApprox_comp_time {Ω : Type*} [MeasurableSpace Ω] {φ : Ω → ℝ → ℂ → ℝ}
    (γ : ℝ) {ε : ℝ} (hφ : Measurable fun p : Ω × ℂ => φ p.1 ε p.2)
    {τ : ContinuousPath ℂ → ℝ≥0} (hτ : Measurable τ) :
    Measurable fun p : Ω × ContinuousPath ℂ => lqgClockApprox γ (φ p.1) ε p.2 (τ p.2) :=
  (measurable_lqgClockApprox_of_measurable_field γ hφ).comp
    (measurable_id.prodMk (hτ.comp measurable_snd))

/-! ## A deterministic subsequence and a jointly measurable limit -/

/-- Convergence in probability implies the Cauchy property in probability. -/
theorem tendsto_measure_gap_of_tendsto_measure {X : Type*} [MeasurableSpace X] (Q : Measure X)
    {a : ℕ → X → ℝ} {F : X → ℝ}
    (hF : ∀ η : ℝ, 0 < η → Tendsto (fun k => Q {x | η ≤ |a k x - F x|}) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun kl : ℕ × ℕ => Q {x | η ≤ |a kl.1 x - a kl.2 x|}) atTop (𝓝 0) := by
  have hB := hF (η / 2) (half_pos hη)
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun n => ⟨(n, 0), fun c hc => (Prod.le_def.1 hc).1⟩
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.2 fun n => ⟨(0, n), fun c hc => (Prod.le_def.1 hc).2⟩
  have hsq : Tendsto (fun kl : ℕ × ℕ =>
      Q {x | η / 2 ≤ |a kl.1 x - F x|} + Q {x | η / 2 ≤ |a kl.2 x - F x|}) atTop (𝓝 0) := by
    have h := (hB.comp hfst).add (hB.comp hsnd)
    rw [add_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq (fun _ => zero_le) fun kl => ?_
  have hsub : {x | η ≤ |a kl.1 x - a kl.2 x|} ⊆
      {x | η / 2 ≤ |a kl.1 x - F x|} ∪ {x | η / 2 ≤ |a kl.2 x - F x|} := by
    intro x hx
    have hx' : η ≤ |a kl.1 x - a kl.2 x| := hx
    rcases le_or_gt (η / 2) |a kl.1 x - F x| with h1 | h1
    · exact Or.inl h1
    · refine Or.inr ?_
      show η / 2 ≤ |a kl.2 x - F x|
      have htri := abs_sub_le (a kl.1 x) (F x) (a kl.2 x)
      rw [abs_sub_comm (F x) (a kl.2 x)] at htri
      linarith
  exact (measure_mono hsub).trans (measure_union_le _ _)

/-- **Deterministic subsequence.** Let `A k : Ω × X → ℝ` be measurable and, for `P`-almost every `ω`, Cauchy in
`Q`-probability in the second variable. Then a deterministic subsequence `A (φ j)` converges `P ⊗ Q`-almost surely
(to its `limsup`, which is measurable). -/
theorem exists_strictMono_ae_tendsto_of_ae_cauchy {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure X) [IsProbabilityMeasure Q]
    {A : ℕ → Ω × X → ℝ} (hA : ∀ k, Measurable (A k))
    (hcauchy : ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η →
      Tendsto (fun kl : ℕ × ℕ => Q {x | η ≤ |A kl.1 (ω, x) - A kl.2 (ω, x)|}) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ p ∂(P.prod Q),
      Tendsto (fun j => A (φ j) p) atTop (𝓝 (limsup (fun j => A (φ j) p) atTop)) := by
  have hE : ∀ (η : ℝ) (k l : ℕ), MeasurableSet {p : Ω × X | η ≤ |A k p - A l p|} := fun η k l =>
    measurableSet_le measurable_const ((hA k).sub (hA l)).abs
  have hconv : ∀ (T : ℕ) (η : ℝ), 0 < η → Tendsto (fun kl : ℕ × ℕ =>
      (P.prod Q) {p | ∃ q : ℚ≥0, (q : ℝ) ≤ T ∧ η ≤ |A kl.1 p - A kl.2 p|}) atTop (𝓝 0) := by
    intro T η hη
    have hset : ∀ kl : ℕ × ℕ, {p : Ω × X | ∃ q : ℚ≥0, (q : ℝ) ≤ T ∧ η ≤ |A kl.1 p - A kl.2 p|} =
        {p | η ≤ |A kl.1 p - A kl.2 p|} := by
      intro kl
      ext p
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨0, by simp, h⟩⟩
    have hfun : (fun kl : ℕ × ℕ =>
        (P.prod Q) {p | ∃ q : ℚ≥0, (q : ℝ) ≤ T ∧ η ≤ |A kl.1 p - A kl.2 p|}) =
        fun kl => ∫⁻ ω, Q (Prod.mk ω ⁻¹' {p | η ≤ |A kl.1 p - A kl.2 p|}) ∂P := by
      funext kl
      rw [hset kl]
      exact Measure.prod_apply (hE η kl.1 kl.2)
    rw [hfun]
    have hpt : ∀ᵐ ω ∂P, Tendsto (fun kl : ℕ × ℕ =>
        Q (Prod.mk ω ⁻¹' {p | η ≤ |A kl.1 p - A kl.2 p|})) atTop (𝓝 0) := by
      filter_upwards [hcauchy] with ω hω
      exact hω η hη
    have hlim := tendsto_lintegral_filter_of_dominated_convergence (μ := P) (l := atTop)
      (fun _ => (1 : ℝ≥0∞))
      (F := fun (kl : ℕ × ℕ) (ω : Ω) => Q (Prod.mk ω ⁻¹' {p | η ≤ |A kl.1 p - A kl.2 p|}))
      (f := fun _ => (0 : ℝ≥0∞))
      (Eventually.of_forall fun kl => measurable_measure_prodMk_left (hE η kl.1 kl.2))
      (Eventually.of_forall fun _ => Eventually.of_forall fun _ => prob_le_one)
      (by simp) hpt
    simpa using hlim
  obtain ⟨φ, hφ, hc⟩ := exists_strictMono_joint_cauchy (P.prod Q) (fun k p (_ : ℝ≥0) => A k p) hconv
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hc] with p hp
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hp 0)
  have hy' : Tendsto (fun j => A (φ j) p) atTop (𝓝 y) := hy
  rw [hy'.limsup_eq]
  exact hy'

/-- **Identification of the limit.** If a subsequence `A (φ j)` converges `P ⊗ Q`-almost surely to its `limsup`
and, for `P`-almost every `ω`, `A k (ω, ·)` converges in `Q`-probability to some (not necessarily measurable)
`Y ω`, then the `limsup` agrees with `Y ω` `Q`-almost surely, for `P`-almost every `ω`. -/
theorem ae_ae_limsup_eq_of_ae_tendstoInMeasure {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (Q : Measure X) [IsFiniteMeasure Q]
    {A : ℕ → Ω × X → ℝ} (hA : ∀ k, Measurable (A k)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hlim : ∀ᵐ p ∂(P.prod Q), Tendsto (fun j => A (φ j) p) atTop (𝓝 (limsup (fun j => A (φ j) p) atTop)))
    (Y : Ω → X → ℝ)
    (hY : ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → Tendsto (fun k => Q {x | η ≤ |A k (ω, x) - Y ω x|}) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂Q, limsup (fun j => A (φ j) (ω, x)) atTop = Y ω x := by
  have hlim' := Measure.ae_ae_of_ae_prod hlim
  filter_upwards [hlim', hY] with ω hω hYω
  exact ae_eq_of_ae_tendsto_of_outer Q (fun j x => A (φ j) (ω, x))
    (fun x => limsup (fun j => A (φ j) (ω, x)) atTop) (Y ω)
    (fun j => (hA (φ j)).comp measurable_prodMk_left)
    ((Measurable.limsup fun j => hA (φ j)).comp measurable_prodMk_left) hω
    (fun η hη => (hYω η hη).comp hφ.tendsto_atTop)

/-- **Jointly measurable version of a quenched limit in probability.** Let `A k : Ω × X → ℝ` be measurable and
suppose that, for `P`-almost every `ω`, `A k (ω, ·)` converges in `Q`-probability to some (not necessarily
measurable) `Y ω`. Then there is a measurable `V : Ω × X → ℝ` with `V (ω, ·) = Y ω` `Q`-almost surely for
`P`-almost every `ω`. -/
theorem exists_measurable_version_of_ae_tendstoInMeasure {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure X) [IsProbabilityMeasure Q]
    {A : ℕ → Ω × X → ℝ} (hA : ∀ k, Measurable (A k)) (Y : Ω → X → ℝ)
    (hY : ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → Tendsto (fun k => Q {x | η ≤ |A k (ω, x) - Y ω x|}) atTop (𝓝 0)) :
    ∃ V : Ω × X → ℝ, Measurable V ∧ ∀ᵐ ω ∂P, ∀ᵐ x ∂Q, V (ω, x) = Y ω x := by
  have hcauchy : ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η →
      Tendsto (fun kl : ℕ × ℕ => Q {x | η ≤ |A kl.1 (ω, x) - A kl.2 (ω, x)|}) atTop (𝓝 0) := by
    filter_upwards [hY] with ω hω η hη
    exact tendsto_measure_gap_of_tendsto_measure Q (a := fun k x => A k (ω, x)) (F := Y ω) hω hη
  obtain ⟨φ, hφ, hlim⟩ := exists_strictMono_ae_tendsto_of_ae_cauchy P Q hA hcauchy
  exact ⟨fun p => limsup (fun j => A (φ j) p) atTop, Measurable.limsup fun j => hA (φ j),
    ae_ae_limsup_eq_of_ae_tendstoInMeasure P Q hA hφ hlim Y hY⟩

/-- Fubini for a jointly measurable version: if `T (ω, ·) = L ω` `Q`-almost surely for `P`-almost every `ω`, then the
annealed probability `∫ Q {L ω ∈ E} dP(ω)` is the `P ⊗ Q`-probability of `{T ∈ E}`. No measurability of `L` is
needed. -/
theorem lintegral_measure_mem_eq_prod_of_ae_ae_eq {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (Q : Measure X) [SFinite Q] {T : Ω × X → ℝ≥0∞} (hT : Measurable T)
    {L : Ω → X → ℝ≥0∞} (hL : ∀ᵐ ω ∂P, ∀ᵐ x ∂Q, T (ω, x) = L ω x) {E : Set ℝ≥0∞}
    (hE : MeasurableSet E) :
    ∫⁻ ω, Q {x | L ω x ∈ E} ∂P = (P.prod Q) {p | T p ∈ E} := by
  rw [Measure.prod_apply (show MeasurableSet {p | T p ∈ E} from hT hE)]
  apply lintegral_congr_ae
  filter_upwards [hL] with ω hω
  apply measure_congr
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [hω] with x hx
  show L ω x ∈ E ↔ T (ω, x) ∈ E
  rw [hx]

/-! ## The approximating clocks at the Brownian exit time -/

/-- For an LQG clock `F` of planar Brownian motion from `x` (`IsLQGClock`) and an open set whose exit time is
measurable and a.s. finite, the approximating clocks at the Brownian exit time `τ = pathExitTime O b` (set to `0`
on `{τ = ∞}`) converge in probability to the clock at `τ`: split according to `τ > T` and use the uniform
convergence on `[0, T]`. -/
theorem tendsto_measure_lqgClockApprox_exitTime_sub_clock {O : Set ℂ} {x : ℂ}
    (hσ : Measurable fun b : ContinuousPath ℂ => pathExitTime O b)
    (hfin : ∀ᵐ b : ContinuousPath ℂ ∂planarBrownianMotion x, pathExitTime O b < ⊤)
    {γ : ℝ} {hc : ℝ → ℂ → ℝ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ hc x F) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun k : ℕ => planarBrownianMotion x {b | η ≤ |lqgClockApprox γ hc (dyadicScale k) b
      (pathExitTime O b).toNNReal - F b (pathExitTime O b).toNNReal|}) atTop (𝓝 0) := by
  have hlimsup : limsup (fun k : ℕ => planarBrownianMotion x {b | η ≤ |lqgClockApprox γ hc (dyadicScale k) b
      (pathExitTime O b).toNNReal - F b (pathExitTime O b).toNNReal|}) atTop ≤ 0 := by
    refine M0Cdf.le_of_forall_add_tendsto_zero
      (M0Cdf.tendsto_measure_tailEvent (planarBrownianMotion x) hσ hfin) fun T => ?_
    refine M0Cdf.limsup_le_add_of_tendsto_zero (hF (T : ℝ≥0) η hη) fun k => ?_
    have hsub : {b : ContinuousPath ℂ | η ≤ |lqgClockApprox γ hc (dyadicScale k) b (pathExitTime O b).toNNReal -
        F b (pathExitTime O b).toNNReal|} ⊆
        {b | ∃ t ≤ (T : ℝ≥0), η ≤ |lqgClockApprox γ hc (dyadicScale k) b t - F b t|} ∪
          M0Cdf.tailEvent O (T : ℝ≥0) := by
      intro b hb
      by_cases hbT : ((T : ℝ≥0) : ℝ≥0∞) < pathExitTime O b
      · exact Or.inr hbT
      · have hτT : (pathExitTime O b).toNNReal ≤ (T : ℝ≥0) := by
          have h1 := ENNReal.toNNReal_mono ENNReal.coe_ne_top (not_lt.1 hbT)
          rwa [ENNReal.toNNReal_coe] at h1
        have hmem : ∃ t ≤ (T : ℝ≥0), η ≤ |lqgClockApprox γ hc (dyadicScale k) b t - F b t| :=
          ⟨(pathExitTime O b).toNNReal, hτT, hb⟩
        exact Or.inl hmem
    rw [zero_add]
    exact (measure_mono hsub).trans (measure_union_le _ _)
  exact tendsto_of_le_liminf_of_limsup_le zero_le hlimsup

end ExitTimeVersion

/-! ## The jointly measurable exit time of a valid environment -/

/-- **A jointly measurable version of the Liouville Brownian exit time from `B_{1/2}`.** For a valid environment
there is a measurable `T* : Ω × ContinuousPath ℂ → [0, ∞]`, finite everywhere, such that for `S.P`-almost every `ω`,
`T*(ω, b) = lbmExitTime (S.clock ω) (ball 0 (1/2)) b` for `P₀`-almost every Brownian path `b` from `0`. Consequently
the annealed exit-time distribution function `G` of `MatedCRTEnv.m₀` (eq:mo, line 727) is
`G(s) = (S.P ⊗ P₀) {T* ≤ s}`.

`T*` is the `S.P ⊗ P₀`-almost sure limit, along a deterministic subsequence, of the approximating clocks at the
Brownian exit time `τ` of `B_{1/2}`, built from a jointly measurable version of the circle averages
(Garban-Rhodes-Vargas 2016, Theorem 2.7 (2); Berestycki 2015, Theorem 1.2 and Section 2). -/
theorem MatedCRTEnv.IsValid.exists_measurable_lbmExitTime_ball_half_version {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ T : Ω × ContinuousPath ℂ → ℝ≥0∞, Measurable T ∧ (∀ p, T p < ⊤) ∧
      (∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
        T (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b) ∧
      ∀ s : ℝ, ∫⁻ ω, planarBrownianMotion 0
          {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal s} ∂S.P =
        (S.P.prod (planarBrownianMotion 0)) {p | T p ≤ ENNReal.ofReal s} := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hσ : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball (0 : ℂ) (1 / 2)) b :=
    KilledOccupation.measurable_pathExitTime_ball 0 (1 / 2)
  have hfin : ∀ᵐ b : ContinuousPath ℂ ∂planarBrownianMotion 0,
      pathExitTime (ball (0 : ℂ) (1 / 2)) b < ⊤ :=
    ae_lt_top hσ (KilledOccupation.lintegral_pathExitTime_planar_ne_top 0 0 (1 / 2))
  -- a jointly measurable version of the circle averages: `0` on a measurable null set `N`
  obtain ⟨N, hsubN, hNm, hN0⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hS.isQuantumCone.ae_continuousOn_circle)
  have hcont : ∀ ω ∉ N, ∀ r : ℝ, 0 < r → Continuous fun z => S.hcirc ω r z := by
    intro ω hω r hr
    have h1 : ContinuousOn (fun p : ℝ × ℂ => S.hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
      by_contra h
      exact hω (hsubN h)
    exact h1.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨hr, mem_univ z⟩)
  have hNae : ∀ᵐ ω ∂S.P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  have hε : ∀ k : ℕ, 0 < dyadicScale k := fun k => pow_pos (by norm_num) k
  have hφ : ∀ k : ℕ, Measurable fun p : Ω × ℂ => M0Cdf.hcT N S.hcirc p.1 (dyadicScale k) p.2 := fun k =>
    (measurable_uncurry_of_continuous_of_measurable
      (u := fun z ω => M0Cdf.hcT N S.hcirc ω (dyadicScale k) z)
      (fun ω => M0Cdf.continuous_hcT hcont (hε k) ω)
      (fun z => M0Cdf.measurable_hcT hNm hS.isQuantumCone.measurable_circle (hε k) z)).comp measurable_swap
  -- the approximating clocks at the Brownian exit time
  have hA : ∀ k : ℕ, Measurable fun p : Ω × ContinuousPath ℂ =>
      lqgClockApprox γ (M0Cdf.hcT N S.hcirc p.1) (dyadicScale k) p.2
        (pathExitTime (ball (0 : ℂ) (1 / 2)) p.2).toNNReal := fun k =>
    ExitTimeVersion.measurable_lqgClockApprox_comp_time (φ := M0Cdf.hcT N S.hcirc) γ (hφ k)
      hσ.ennreal_toNNReal
  have hconv : ∀ᵐ ω ∂S.P, ∀ η : ℝ, 0 < η → Tendsto (fun k : ℕ => planarBrownianMotion 0
      {b | η ≤ |lqgClockApprox γ (M0Cdf.hcT N S.hcirc ω) (dyadicScale k) b
        (pathExitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal -
          S.clock ω b (pathExitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal|}) atTop (𝓝 0) := by
    filter_upwards [hS.isLQGClock, hNae] with ω hω hωN η hη
    rw [M0Cdf.hcT_eq_of_not_mem hωN]
    exact ExitTimeVersion.tendsto_measure_lqgClockApprox_exitTime_sub_clock hσ hfin (hω 0).1 hη
  obtain ⟨V, hV, hVeq⟩ := ExitTimeVersion.exists_measurable_version_of_ae_tendstoInMeasure S.P
    (planarBrownianMotion 0)
    (A := fun k p => lqgClockApprox γ (M0Cdf.hcT N S.hcirc p.1) (dyadicScale k) p.2
      (pathExitTime (ball (0 : ℂ) (1 / 2)) p.2).toNNReal) hA
    (fun ω b => S.clock ω b (pathExitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal) hconv
  -- identification with the Liouville Brownian exit time
  have hTeq : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      ENNReal.ofReal (V (ω, b)) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b := by
    filter_upwards [hVeq, hS.ae_lbmExitTime_ball_half_eq_clock] with ω hω1 hω2
    filter_upwards [hω1, hω2] with b hb1 hb2
    obtain ⟨τ, -, hτ, hlbm⟩ := hb2
    have hb1' : V (ω, b) = S.clock ω b (pathExitTime (ball (0 : ℂ) (1 / 2)) b).toNNReal := hb1
    rw [hlbm, hb1', hτ, ENNReal.toNNReal_coe]
  refine ⟨fun p => ENNReal.ofReal (V p), ENNReal.measurable_ofReal.comp hV,
    fun _ => ENNReal.ofReal_lt_top, hTeq, fun s => ?_⟩
  exact ExitTimeVersion.lintegral_measure_mem_eq_prod_of_ae_ae_eq S.P (planarBrownianMotion 0)
    (T := fun p => ENNReal.ofReal (V p)) (ENNReal.measurable_ofReal.comp hV)
    (L := fun ω b => lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b) hTeq
    (E := Iic (ENNReal.ofReal s)) measurableSet_Iic

end MatedCRT
