import MatedCRT.Defs.Setting
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockBinders

/-!
# AE-measurability of the annealed exit-time cdf of Liouville Brownian motion

Step 5 of `MQ-li-11` in `MATH-ANSWERS.md` (the hypothesis `hcdf` of `MatedCRTEnv.m₀_pos`): for a valid
environment and `s : ℝ`, `ω ↦ P₀{b | lbmExitTime (S.clock ω) (ball 0 (1/2)) b ≤ ofReal s}` is AE-measurable.

Notation: `O = ball 0 (1/2)`, `σ b = pathExitTime O b` (planar exit time), `τ b = (σ b).toNNReal`.

* Clock inversion (Berestycki 2015, Section 2; Garban-Rhodes-Vargas 2016, Definition 2.17): for a time-change
  clock `F`, `lbmExitTime F O b ≤ ofReal s ↔ σ b < ⊤ ∧ F b (τ b) ≤ s` when `0 ≤ s`.
* Approximation: `S.clock ω` is the `P₀`-limit in probability of the dyadic clocks
  `lqgClockApprox γ (hcirc ω) (dyadicScale k)` (`IsLQGClock`). A jointly measurable version of the circle averages
  (zero on a measurable superset `N` of the discontinuity set; Carathéodory in the spatial variable) makes the dyadic
  clocks jointly measurable, so `Φ k s ω = P₀{σ < ⊤ ∧ F_k(τ) ≤ s}` is measurable in `ω` (Tonelli).
* Sandwich: `P₀(A s) ≤ liminf_k Φ k (s + η)` and `limsup_k Φ k (s + η) ≤ P₀(A (s + 2η))`, from `IsLQGClock` and
  `P₀(σ > T) → 0`, where `A s = {σ < ⊤ ∧ F(τ) ≤ s}`.
* Right-continuity `η ↓ 0` of `P₀(A (s + η))` then squeezes the cdf between measurable functions.

Gap (not written in the source). The right-continuity step needs the event `A s` to be `P₀`-measurable (or to agree
`P₀`-a.e. with a measurable event). `S.clock ω` is only determined `P₀`-a.e. by `IsLQGClock`, and `IsValid` gives no
measurability of `S.clock ω` in the path. The hypothesis `hsub` (a.s. convergence along a subsequence of the dyadic
clocks, from convergence in probability) supplies this and is kept as a named hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT

namespace M0Cdf

/-! ## Clock inversion (deterministic) -/

/-- The clock inverse of a strictly increasing clock is a left inverse of the clock. -/
theorem clockInverse_clock {f : ℝ≥0 → ℝ} (hf : StrictMono f) {m : ℝ≥0} (hfm : 0 ≤ f m) :
    clockInverse f (f m).toNNReal = m := by
  unfold clockInverse
  have hset : {u : ℝ≥0 | (((f m).toNNReal : ℝ≥0) : ℝ) < f u} = Ioi m := by
    ext u
    show (((f m).toNNReal : ℝ≥0) : ℝ) < f u ↔ m < u
    rw [Real.coe_toNNReal _ hfm]
    exact hf.lt_iff_lt
  rw [hset, csInf_Ioi]

/-- The clock inverse is a right inverse of a time-change clock (intermediate value theorem). -/
theorem apply_clockInverse {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f) (t : ℝ≥0) :
    f (clockInverse f t) = t := by
  obtain ⟨s₁, hs₁⟩ := (hf.tendsto_atTop.eventually_gt_atTop (t : ℝ)).exists
  have hgc : ContinuousOn (fun x : ℝ => f x.toNNReal) (Icc 0 (s₁ : ℝ)) :=
    (hf.continuous.comp continuous_real_toNNReal).continuousOn
  have hmem : (t : ℝ) ∈ Icc ((fun x : ℝ => f x.toNNReal) 0) ((fun x : ℝ => f x.toNNReal) (s₁ : ℝ)) := by
    refine ⟨?_, ?_⟩
    · simp only [Real.toNNReal_zero, hf.map_zero]
      exact NNReal.coe_nonneg t
    · simp only [Real.toNNReal_coe]
      exact hs₁.le
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (NNReal.coe_nonneg s₁) hgc hmem
  have hfs : f x.toNNReal = (t : ℝ) := hx
  have hnn : (0 : ℝ) ≤ f x.toNNReal := by
    rw [hfs]
    exact NNReal.coe_nonneg t
  have htt : t = (f x.toNNReal).toNNReal := by
    rw [hfs, Real.toNNReal_coe]
  have hkey : clockInverse f t = x.toNNReal := by
    rw [htt]
    exact clockInverse_clock hf.strictMono hnn
  rw [hkey, hfs]

/-- Points of an `ℝ≥0∞`-valued infimum over a path: a bound from one exit point. -/
theorem pathExitTime_le_of_not_mem {α : Type*} {O : Set α} {f : ℝ≥0 → α} {t : ℝ≥0} (h : f t ∉ O) :
    pathExitTime O f ≤ t := by
  unfold pathExitTime
  exact sInf_le ⟨t, rfl, h⟩

/-- A lower bound for the exit time from all exit points. -/
theorem le_pathExitTime {α : Type*} {O : Set α} {f : ℝ≥0 → α} {c : ℝ≥0∞}
    (h : ∀ t : ℝ≥0, f t ∉ O → c ≤ t) : c ≤ pathExitTime O f := by
  unfold pathExitTime
  refine le_sInf ?_
  rintro _ ⟨t, rfl, ht⟩
  exact h t ht

/-- For a continuous path and an open set, a finite exit time is attained at an exit point. -/
theorem exists_exit_eq {O : Set ℂ} (hO : IsOpen O) (b : ContinuousPath ℂ) (hσ : pathExitTime O b < ⊤) :
    ∃ m : ℝ≥0, pathExitTime O b = m ∧ b m ∉ O := by
  set E : Set ℝ≥0 := {t | b t ∉ O} with hE
  have hEc : IsClosed E := hO.isClosed_compl.preimage b.continuous
  have hne : E.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have hempty : {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = (t : ℝ≥0∞) ∧ b t ∉ O} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 ?_
      rintro s ⟨t, -, ht⟩
      have hmem : t ∈ E := ht
      rw [h] at hmem
      simp at hmem
    unfold pathExitTime at hσ
    rw [hempty, sInf_empty] at hσ
    exact lt_irrefl _ hσ
  obtain ⟨m, hm⟩ : ∃ m : ℝ≥0, m = sInf E := ⟨_, rfl⟩
  have hmE : m ∈ E := by
    rw [hm]
    exact hEc.csInf_mem hne (OrderBot.bddBelow E)
  refine ⟨m, ?_, hmE⟩
  unfold pathExitTime
  apply le_antisymm
  · exact sInf_le ⟨m, rfl, hmE⟩
  · refine le_sInf ?_
    rintro _ ⟨t, rfl, ht⟩
    have hmem : t ∈ E := ht
    have h1 : m ≤ t := by
      rw [hm]
      exact csInf_le (OrderBot.bddBelow E) hmem
    exact_mod_cast h1

/-- Clock inversion: for a time-change clock `F b` and `0 ≤ s`, the Liouville Brownian exit time from `O` is
`≤ ofReal s` exactly when the planar exit time `σ b` is finite and `F b (σ b) ≤ s`
(Berestycki 2015, Section 2; Garban-Rhodes-Vargas 2016, Definition 2.17). -/
theorem lbmExitTime_le_ofReal_iff {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {O : Set ℂ} (hO : IsOpen O)
    (b : ContinuousPath ℂ) (hF : IsTimeChangeClock (F b)) {s : ℝ} (hs : 0 ≤ s) :
    lbmExitTime F O b ≤ ENNReal.ofReal s ↔
      pathExitTime O b < ⊤ ∧ F b (pathExitTime O b).toNNReal ≤ s := by
  by_cases hσ : pathExitTime O b < ⊤
  · obtain ⟨m, hm, hbm⟩ := exists_exit_eq hO b hσ
    have hfm : (0 : ℝ) ≤ F b m := by
      have h := hF.strictMono.monotone (by positivity : (0 : ℝ≥0) ≤ m)
      rw [hF.map_zero] at h
      exact h
    have hσm : (pathExitTime O b).toNNReal = m := by
      rw [hm, ENNReal.toNNReal_coe]
    have hlbm : lbmExitTime F O b = ENNReal.ofReal (F b m) := by
      unfold lbmExitTime liouvilleBrownianPath
      apply le_antisymm
      · refine pathExitTime_le_of_not_mem (t := (F b m).toNNReal) ?_
        show b (clockInverse (F b) (F b m).toNNReal) ∉ O
        rw [clockInverse_clock hF.strictMono hfm]
        exact hbm
      · refine le_pathExitTime fun t ht => ?_
        have h1 : pathExitTime O b ≤ (clockInverse (F b) t : ℝ≥0∞) :=
          pathExitTime_le_of_not_mem ht
        rw [hm] at h1
        have h2 : m ≤ clockInverse (F b) t := by exact_mod_cast h1
        have h3 : F b m ≤ t := by
          have h4 := hF.strictMono.monotone h2
          rwa [apply_clockInverse hF] at h4
        calc ENNReal.ofReal (F b m) ≤ ENNReal.ofReal (t : ℝ) := ENNReal.ofReal_le_ofReal h3
          _ = t := ENNReal.ofReal_coe_nnreal
    rw [hlbm, ENNReal.ofReal_le_ofReal_iff hs, hσm]
    exact ⟨fun h => ⟨hσ, h⟩, fun h => h.2⟩
  · have hσ' : pathExitTime O b = ⊤ := top_le_iff.1 (not_lt.1 hσ)
    have hl : lbmExitTime F O b = ⊤ := by
      unfold lbmExitTime liouvilleBrownianPath
      refine top_le_iff.1 (le_pathExitTime fun t ht => ?_)
      have h1 : pathExitTime O b ≤ (clockInverse (F b) t : ℝ≥0∞) :=
        pathExitTime_le_of_not_mem ht
      rw [hσ'] at h1
      exact absurd h1 (not_le.2 ENNReal.coe_lt_top)
    rw [hl]
    constructor
    · intro h
      exact absurd (top_le_iff.1 h) ENNReal.ofReal_ne_top
    · intro h
      exact absurd h.1 hσ

/-! ## Approximating clocks with a jointly measurable version of the circle averages -/

section Approximations

variable {Ω : Type*} [MeasurableSpace Ω]

open Classical in
/-- The jointly measurable version `ĥ` of the circle averages: `0` on the set `N` (the discontinuity set). -/
def hcT (N : Set Ω) (hc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (r : ℝ) (z : ℂ) : ℝ :=
  if ω ∈ N then 0 else hc ω r z

omit [MeasurableSpace Ω] in
theorem hcT_eq_of_not_mem {N : Set Ω} {hc : Ω → ℝ → ℂ → ℝ} {ω : Ω} (h : ω ∉ N) :
    hcT N hc ω = hc ω := by
  funext r z
  simp [hcT, h]

variable {N : Set Ω} {hc : Ω → ℝ → ℂ → ℝ}

omit [MeasurableSpace Ω] in
theorem continuous_hcT (hcont : ∀ ω ∉ N, ∀ r : ℝ, 0 < r → Continuous fun z => hc ω r z) {r : ℝ}
    (hr : 0 < r) (ω : Ω) : Continuous fun z => hcT N hc ω r z := by
  unfold hcT
  split_ifs with h
  · exact continuous_const
  · exact hcont ω h r hr

theorem measurable_hcT (hN : MeasurableSet N) (hc_meas : ∀ (r : ℝ) (z : ℂ), 0 < r → Measurable fun ω => hc ω r z)
    {r : ℝ} (hr : 0 < r) (z : ℂ) : Measurable fun ω => hcT N hc ω r z := by
  unfold hcT
  exact Measurable.ite hN measurable_const (hc_meas r z hr)

variable (γ : ℝ)

/-- The integrand of the LQG clock at a fixed scale, as a function of `(ω, z)`. -/
theorem measurable_integrand (hN : MeasurableSet N) (hc_meas : ∀ (r : ℝ) (z : ℂ), 0 < r → Measurable fun ω => hc ω r z)
    (hcont : ∀ ω ∉ N, ∀ r : ℝ, 0 < r → Continuous fun z => hc ω r z) {ε : ℝ} (hε : 0 < ε) :
    Measurable fun p : Ω × ℂ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcT N hc p.1 ε p.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun z ω => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcT N hc ω ε z))
    (fun ω => continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_hcT hcont hε ω))))
    (fun z => measurable_const.mul (Real.continuous_exp.measurable.comp
      (measurable_const.mul (measurable_hcT hN hc_meas hε z))))
  exact h.comp measurable_swap

/-- The integrand of the LQG clock along a path, as a function of `((ω, b), s)`. -/
theorem measurable_integrand_path (hN : MeasurableSet N)
    (hc_meas : ∀ (r : ℝ) (z : ℂ), 0 < r → Measurable fun ω => hc ω r z)
    (hcont : ∀ ω ∉ N, ∀ r : ℝ, 0 < r → Continuous fun z => hc ω r z) {ε : ℝ} (hε : 0 < ε) :
    Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcT N hc q.1.1 ε (q.1.2 q.2.toNNReal)) := by
  have hbase := measurable_integrand γ hN hc_meas hcont hε
  have h := measurable_uncurry_of_continuous_of_measurable
    (ι := ℝ) (α := Ω × ContinuousPath ℂ)
    (u := fun s x => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcT N hc x.1 ε (x.2 s.toNNReal)))
    (fun x => continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_hcT hcont hε x.1).comp (x.2.continuous.comp continuous_real_toNNReal)))))
    (fun s => by
      have hev : Measurable fun x : Ω × ContinuousPath ℂ => x.2 s.toNNReal :=
        ContinuousPath.measurable_eval_of_measurable (fun _ => s.toNNReal) measurable_const |>.comp
          measurable_snd
      exact hbase.comp (measurable_fst.prodMk hev))
  exact h.comp measurable_swap

/-- The dyadic LQG clock built from `hcT` is jointly measurable in `(ω, b, t)`. -/
theorem measurable_approxClock (hN : MeasurableSet N)
    (hc_meas : ∀ (r : ℝ) (z : ℂ), 0 < r → Measurable fun ω => hc ω r z)
    (hcont : ∀ ω ∉ N, ∀ r : ℝ, 0 < r → Continuous fun z => hc ω r z) {ε : ℝ} (hε : 0 < ε) :
    Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ≥0 => lqgClockApprox γ (hcT N hc q.1.1) ε q.1.2 q.2 := by
  have hint : ∀ x : Ω × ContinuousPath ℂ, Continuous fun s : ℝ =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcT N hc x.1 ε (x.2 s.toNNReal)) := fun x =>
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_hcT hcont hε x.1).comp (x.2.continuous.comp continuous_real_toNNReal))))
  have hmeas_t : ∀ t : ℝ≥0, Measurable fun x : Ω × ContinuousPath ℂ =>
      lqgClockApprox γ (hcT N hc x.1) ε x.2 t := by
    intro t
    have hS : StronglyMeasurable fun q : (Ω × ContinuousPath ℂ) × ℝ =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcT N hc q.1.1 ε (q.1.2 q.2.toNNReal)) :=
      (measurable_integrand_path γ hN hc_meas hcont hε).stronglyMeasurable
    have hI := hS.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) (t : ℝ)))
    have heq : (fun x : Ω × ContinuousPath ℂ => lqgClockApprox γ (hcT N hc x.1) ε x.2 t) =
        fun x => ∫ s in Ioc (0 : ℝ) (t : ℝ),
          ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcT N hc x.1 ε (x.2 s.toNNReal)) := by
      funext x
      unfold lqgClockApprox
      exact intervalIntegral.integral_of_le (NNReal.coe_nonneg t)
    rw [heq]
    exact hI.measurable
  have hcarat := measurable_uncurry_of_continuous_of_measurable
    (ι := ℝ≥0) (α := Ω × ContinuousPath ℂ)
    (u := fun t x => lqgClockApprox γ (hcT N hc x.1) ε x.2 t)
    (fun x => (intervalIntegral.continuous_primitive
      (fun a b => (hint x).intervalIntegrable a b) 0).comp NNReal.continuous_coe) hmeas_t
  exact hcarat.comp measurable_swap

/-- The event `{σ < ⊤ ∧ F(τ) ≤ s}`: `σ` the planar exit time of `O`, `τ = σ.toNNReal`. -/
def cdfEvent (O : Set ℂ) (F : ContinuousPath ℂ → ℝ≥0 → ℝ) (s : ℝ) : Set (ContinuousPath ℂ) :=
  {b | pathExitTime O b < ⊤ ∧ F b (pathExitTime O b).toNNReal ≤ s}

/-- The event that two clocks differ by at least `η` at some time `t ≤ T`. -/
def closeEvent (T : ℝ≥0) (η : ℝ) (G F : ContinuousPath ℂ → ℝ≥0 → ℝ) : Set (ContinuousPath ℂ) :=
  {b | ∃ t : ℝ≥0, t ≤ T ∧ η ≤ |G b t - F b t|}

/-- The tail event `{T < σ}` of the planar exit time. -/
def tailEvent (O : Set ℂ) (T : ℝ≥0) : Set (ContinuousPath ℂ) :=
  {b | (T : ℝ≥0∞) < pathExitTime O b}

theorem measurableSet_cdfEvent {O : Set ℂ} (hσ : Measurable fun b : ContinuousPath ℂ => pathExitTime O b)
    {G : ContinuousPath ℂ → ℝ≥0 → ℝ} (hG : Measurable fun q : ContinuousPath ℂ × ℝ≥0 => G q.1 q.2) (s : ℝ) :
    MeasurableSet (cdfEvent O G s) := by
  have hτ : Measurable fun b : ContinuousPath ℂ => (pathExitTime O b).toNNReal := hσ.ennreal_toNNReal
  have hA : Measurable fun b : ContinuousPath ℂ => G b (pathExitTime O b).toNNReal :=
    hG.comp (measurable_id.prodMk hτ)
  exact (measurableSet_lt hσ measurable_const).inter (measurableSet_le hA measurable_const)

theorem measurableSet_tailEvent {O : Set ℂ} (hσ : Measurable fun b : ContinuousPath ℂ => pathExitTime O b)
    (T : ℝ≥0) : MeasurableSet (tailEvent O T) :=
  measurableSet_lt measurable_const hσ

/-- The cdf event of the dyadic clock at a fixed `ω` is measurable in `ω` (Tonelli). -/
theorem measurable_cdf_approx (hN : MeasurableSet N)
    (hc_meas : ∀ (r : ℝ) (z : ℂ), 0 < r → Measurable fun ω => hc ω r z)
    (hcont : ∀ ω ∉ N, ∀ r : ℝ, 0 < r → Continuous fun z => hc ω r z) {ε : ℝ} (hε : 0 < ε)
    {O : Set ℂ} (hσ : Measurable fun b : ContinuousPath ℂ => pathExitTime O b) (s : ℝ) :
    Measurable fun ω => planarBrownianMotion 0
      (cdfEvent O (fun b t => lqgClockApprox γ (hcT N hc ω) ε b t) s) := by
  set E : Set (Ω × ContinuousPath ℂ) :=
    {q | pathExitTime O q.2 < ⊤ ∧ lqgClockApprox γ (hcT N hc q.1) ε q.2 (pathExitTime O q.2).toNNReal ≤ s}
    with hE
  have hσ2 : Measurable fun q : Ω × ContinuousPath ℂ => pathExitTime O q.2 := hσ.comp measurable_snd
  have hτ2 : Measurable fun q : Ω × ContinuousPath ℂ => (pathExitTime O q.2).toNNReal :=
    hσ2.ennreal_toNNReal
  have hA : Measurable fun q : Ω × ContinuousPath ℂ =>
      lqgClockApprox γ (hcT N hc q.1) ε q.2 (pathExitTime O q.2).toNNReal :=
    (measurable_approxClock γ hN hc_meas hcont hε).comp ((measurable_fst.prodMk measurable_snd).prodMk hτ2)
  have hEm : MeasurableSet E :=
    (measurableSet_lt hσ2 measurable_const).inter (measurableSet_le hA measurable_const)
  have hind : Measurable fun q : Ω × ContinuousPath ℂ => E.indicator (fun _ => (1 : ℝ≥0∞)) q :=
    measurable_const.indicator hEm
  have hT := hind.lintegral_prod_right' (ν := planarBrownianMotion 0)
  have key : ∀ ω, planarBrownianMotion 0 (cdfEvent O (fun b t => lqgClockApprox γ (hcT N hc ω) ε b t) s) =
      ∫⁻ b, E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, b) ∂(planarBrownianMotion 0) := by
    intro ω
    have hsec : MeasurableSet (Prod.mk ω ⁻¹' E) := measurable_prodMk_left hEm
    calc planarBrownianMotion 0 (cdfEvent O (fun b t => lqgClockApprox γ (hcT N hc ω) ε b t) s)
        = planarBrownianMotion 0 (Prod.mk ω ⁻¹' E) := rfl
      _ = ∫⁻ b, (Prod.mk ω ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) b ∂(planarBrownianMotion 0) :=
          (lintegral_indicator_one hsec).symm
      _ = ∫⁻ b, E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, b) ∂(planarBrownianMotion 0) := rfl
  convert hT using 1
  funext ω
  exact key ω

/-- Tail of the planar exit time: `P₀(T < σ) → 0` as `T → ∞` (from `lintegral_pathExitTime_planar_ne_top`). -/
theorem tendsto_measure_tailEvent (μ : Measure (ContinuousPath ℂ)) [IsFiniteMeasure μ] {O : Set ℂ}
    (hσ : Measurable fun b : ContinuousPath ℂ => pathExitTime O b)
    (hfin : ∀ᵐ b : ContinuousPath ℂ ∂μ, pathExitTime O b < ⊤) :
    Tendsto (fun T : ℕ => μ (tailEvent O (T : ℝ≥0))) atTop (𝓝 0) := by
  have hanti : Antitone fun T : ℕ => tailEvent O (T : ℝ≥0) := by
    intro T T' hTT' b hb
    have hb' : (T' : ℝ≥0∞) < pathExitTime O b := hb
    show (T : ℝ≥0∞) < pathExitTime O b
    exact lt_of_le_of_lt (by exact_mod_cast hTT' : (T : ℝ≥0∞) ≤ T') hb'
  have hnull : μ (⋂ T : ℕ, tailEvent O (T : ℝ≥0)) = 0 := by
    apply measure_mono_null (t := {b : ContinuousPath ℂ | ¬ pathExitTime O b < ⊤})
    · intro b hb
      have hb' : ∀ T : ℕ, (T : ℝ≥0∞) < pathExitTime O b := fun T => by
        have := mem_iInter.1 hb T
        exact this
      intro hlt
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hlt)
      exact absurd (hb' n) (not_lt.2 hn.le)
    · exact ae_iff.1 hfin
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (fun T : ℕ => (measurableSet_tailEvent hσ (T : ℝ≥0)).nullMeasurableSet) hanti
    ⟨0, measure_ne_top μ _⟩
  rw [hnull] at hlim
  exact hlim

/-- Right-continuity of the cdf events in the threshold (continuity from above along measurable events). -/
theorem tendsto_measure_cdfEvent (μ : Measure (ContinuousPath ℂ)) [IsFiniteMeasure μ] {O : Set ℂ}
    (hσ : Measurable fun b : ContinuousPath ℂ => pathExitTime O b)
    {G : ContinuousPath ℂ → ℝ≥0 → ℝ} (hG : Measurable fun q : ContinuousPath ℂ × ℝ≥0 => G q.1 q.2)
    (s : ℝ) {c : ℕ → ℝ} (hc0 : ∀ j, 0 ≤ c j) (hanti : Antitone c) (hlim : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun j => μ (cdfEvent O G (s + c j))) atTop (𝓝 (μ (cdfEvent O G s))) := by
  have hanti' : Antitone fun j => cdfEvent O G (s + c j) := by
    intro j j' hjj' b hb
    have hb' : pathExitTime O b < ⊤ ∧ G b (pathExitTime O b).toNNReal ≤ s + c j' := hb
    show pathExitTime O b < ⊤ ∧ G b (pathExitTime O b).toNNReal ≤ s + c j
    exact ⟨hb'.1, hb'.2.trans (by linarith [hanti hjj'])⟩
  have hinter : (⋂ j : ℕ, cdfEvent O G (s + c j)) = cdfEvent O G s := by
    ext b
    simp only [mem_iInter]
    constructor
    · intro h
      have h0 : pathExitTime O b < ⊤ ∧ G b (pathExitTime O b).toNNReal ≤ s + c 0 := h 0
      refine ⟨h0.1, ?_⟩
      by_contra hcon
      have hpos : 0 < G b (pathExitTime O b).toNNReal - s := sub_pos.2 (not_le.1 hcon)
      obtain ⟨j, hj⟩ := ((tendsto_order.1 hlim).2 _ hpos).exists
      have hj2 : G b (pathExitTime O b).toNNReal ≤ s + c j := (h j).2
      linarith
    · rintro ⟨h1, h2⟩ j
      exact ⟨h1, h2.trans (by linarith [hc0 j])⟩
  have hmeas : ∀ j, MeasurableSet (cdfEvent O G (s + c j)) := fun j =>
    measurableSet_cdfEvent hσ hG _
  have hT := tendsto_measure_iInter_atTop (μ := μ) (fun j => (hmeas j).nullMeasurableSet) hanti'
    ⟨0, measure_ne_top μ _⟩
  rw [hinter] at hT
  exact hT

/-! ## Elementary measure and limit inequalities -/

theorem measure_le_of_subset_union {X : Type*} [MeasurableSpace X] {μ : Measure X} {A B C D : Set X}
    (h : A ⊆ (B ∪ C) ∪ D) : μ A ≤ μ B + μ C + μ D := by
  calc μ A ≤ μ ((B ∪ C) ∪ D) := measure_mono h
    _ ≤ μ (B ∪ C) + μ D := measure_union_le _ _
    _ ≤ (μ B + μ C) + μ D := by gcongr; exact measure_union_le _ _

/-- A bound `a ≤ c + Y T` for all `T` with `Y T → 0` gives `a ≤ c`. -/
theorem le_of_forall_add_tendsto_zero {a c : ℝ≥0∞} {Y : ℕ → ℝ≥0∞} (hY : Tendsto Y atTop (𝓝 0))
    (h : ∀ T, a ≤ c + Y T) : a ≤ c := by
  by_cases hc : c = ⊤
  · rw [hc]
    exact le_top
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨T, hT⟩ := ((tendsto_order.1 hY).2 (ε : ℝ≥0∞) (ENNReal.coe_pos.2 hε)).exists
  have hT' : Y T ≤ ε := hT.le
  calc a ≤ c + Y T := h T
    _ ≤ c + ε := by gcongr

/-- A lower bound for `a` with `liminf` up to an error sequence tending to `0`. -/
theorem le_liminf_add_of_tendsto_zero {a y : ℝ≥0∞} {x z : ℕ → ℝ≥0∞} (hz : Tendsto z atTop (𝓝 0))
    (h : ∀ k, a ≤ x k + z k + y) : a ≤ liminf x atTop + y := by
  by_cases hc : liminf x atTop = ⊤
  · rw [hc, top_add]
    exact le_top
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεpos : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := ENNReal.coe_pos.2 hε
  have hd : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := ENNReal.half_pos hεpos.ne'
  have hfreq : ∃ᶠ k in atTop, x k < liminf x atTop + (ε : ℝ≥0∞) / 2 :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) (ENNReal.lt_add_right hc hd.ne')
  have hev : ∀ᶠ k in atTop, z k < (ε : ℝ≥0∞) / 2 := (tendsto_order.1 hz).2 _ hd
  obtain ⟨k, hk1, hk2⟩ := (hfreq.and_eventually hev).exists
  calc a ≤ x k + z k + y := h k
    _ ≤ (liminf x atTop + (ε : ℝ≥0∞) / 2) + (ε : ℝ≥0∞) / 2 + y :=
        add_le_add (add_le_add hk1.le hk2.le) le_rfl
    _ = liminf x atTop + y + ((ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2) := by ac_rfl
    _ = liminf x atTop + y + (ε : ℝ≥0∞) := by rw [ENNReal.add_halves]

/-- An upper bound for `limsup` up to an error sequence tending to `0`. -/
theorem limsup_le_add_of_tendsto_zero {b y : ℝ≥0∞} {x z : ℕ → ℝ≥0∞} (hz : Tendsto z atTop (𝓝 0))
    (h : ∀ k, x k ≤ b + z k + y) : limsup x atTop ≤ b + y := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hev : ∀ᶠ k in atTop, z k < ε := (tendsto_order.1 hz).2 _ (ENNReal.coe_pos.2 hε)
  have hle : ∀ᶠ k in atTop, x k ≤ b + y + ε := by
    filter_upwards [hev] with k hk
    have hk' : z k ≤ (ε : ℝ≥0∞) := hk.le
    calc x k ≤ b + z k + y := h k
      _ ≤ b + ε + y := by gcongr
      _ = b + y + ε := by ring
  exact limsup_le_of_le (by isBoundedDefault) hle

end Approximations

/-! ## Sandwich of the dyadic cdfs (pointwise inclusions) -/

/-- Lower comparison: a dyadic clock `G` within `η` of `F` on `[0, T]` moves the exit cdf by at most `η`. -/
theorem cdfEvent_subset_sub {O : Set ℂ} (F G : ContinuousPath ℂ → ℝ≥0 → ℝ) (s η : ℝ) (T : ℝ≥0) :
    cdfEvent O F s ⊆ (cdfEvent O G (s + η) ∪ closeEvent T η G F) ∪ tailEvent O T := by
  intro b hb
  have hb' : pathExitTime O b < ⊤ ∧ F b (pathExitTime O b).toNNReal ≤ s := hb
  by_cases hT : (T : ℝ≥0∞) < pathExitTime O b
  · exact Or.inr hT
  · by_cases hD : b ∈ closeEvent T η G F
    · exact Or.inl (Or.inr hD)
    · have hle : pathExitTime O b ≤ T := not_lt.1 hT
      have hτ : (pathExitTime O b).toNNReal ≤ T := by
        have h := ENNReal.toNNReal_mono ENNReal.coe_ne_top hle
        rwa [ENNReal.toNNReal_coe] at h
      have hall : ∀ t : ℝ≥0, t ≤ T → |G b t - F b t| < η := by
        intro t ht
        by_contra hcon
        exact hD (show ∃ t : ℝ≥0, t ≤ T ∧ η ≤ |G b t - F b t| from ⟨t, ht, not_lt.1 hcon⟩)
      have habs := abs_lt.1 (hall _ hτ)
      have hmem : pathExitTime O b < ⊤ ∧ G b (pathExitTime O b).toNNReal ≤ s + η :=
        ⟨hb'.1, by linarith [habs.2, hb'.2]⟩
      exact Or.inl (Or.inl hmem)

/-- Upper comparison: the exit cdf of `G` is contained, up to `η` and the tail, in the cdf of `F`. -/
theorem cdfEvent_sub_subset {O : Set ℂ} (F G : ContinuousPath ℂ → ℝ≥0 → ℝ) (s η : ℝ) (T : ℝ≥0) :
    cdfEvent O G s ⊆ (cdfEvent O F (s + η) ∪ closeEvent T η G F) ∪ tailEvent O T := by
  intro b hb
  have hb' : pathExitTime O b < ⊤ ∧ G b (pathExitTime O b).toNNReal ≤ s := hb
  by_cases hT : (T : ℝ≥0∞) < pathExitTime O b
  · exact Or.inr hT
  · by_cases hD : b ∈ closeEvent T η G F
    · exact Or.inl (Or.inr hD)
    · have hle : pathExitTime O b ≤ T := not_lt.1 hT
      have hτ : (pathExitTime O b).toNNReal ≤ T := by
        have h := ENNReal.toNNReal_mono ENNReal.coe_ne_top hle
        rwa [ENNReal.toNNReal_coe] at h
      have hall : ∀ t : ℝ≥0, t ≤ T → |G b t - F b t| < η := by
        intro t ht
        by_contra hcon
        exact hD (show ∃ t : ℝ≥0, t ≤ T ∧ η ≤ |G b t - F b t| from ⟨t, ht, not_lt.1 hcon⟩)
      have habs := abs_lt.1 (hall _ hτ)
      have hmem : pathExitTime O b < ⊤ ∧ F b (pathExitTime O b).toNNReal ≤ s + η :=
        ⟨hb'.1, by linarith [habs.1, hb'.2]⟩
      exact Or.inl (Or.inl hmem)

/-- The dyadic index sequence `η j = 1 / (j + 1)`. -/
def etaSeq (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem etaSeq_pos (j : ℕ) : 0 < etaSeq j := by
  unfold etaSeq
  positivity

theorem etaSeq_anti : Antitone etaSeq := by
  intro j j' hjj'
  unfold etaSeq
  have h : (j : ℝ) ≤ j' := Nat.cast_le.2 hjj'
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem etaSeq_tendsto : Tendsto etaSeq atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The right-continuity sequence `2 η j`. -/
theorem two_etaSeq_tendsto : Tendsto (fun j => etaSeq j + etaSeq j) atTop (𝓝 0) := by
  have h := etaSeq_tendsto.add etaSeq_tendsto
  simpa using h

/-- The cdf of the Liouville Brownian exit time under a time-change clock, at a fixed `ω` whose dyadic clocks
converge along a subsequence `k` (hypothesis `hsubω`): the limit of the liminf of the dyadic cdfs. -/
theorem tendsto_cdf_good {O : Set ℂ} (hO : IsOpen O)
    (hσ : Measurable fun b : ContinuousPath ℂ => pathExitTime O b)
    (hfin : ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion 0), pathExitTime O b < ⊤)
    (γ : ℝ) (hc : ℝ → ℂ → ℝ) (F : ContinuousPath ℂ → ℝ≥0 → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hLQG : IsLQGClock planarBrownianMotion γ hc 0 F)
    (hF_tc : ∀ᵐ b ∂(planarBrownianMotion 0), IsTimeChangeClock (F b))
    (hJoint : ∀ k : ℕ, Measurable fun q : ContinuousPath ℂ × ℝ≥0 =>
      lqgClockApprox γ hc (dyadicScale k) q.1 q.2)
    (hsubω : ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ b ∂(planarBrownianMotion 0), ∀ t : ℝ≥0,
      Tendsto (fun j => lqgClockApprox γ hc (dyadicScale (k j)) b t) atTop (𝓝 (F b t))) :
    Tendsto (fun j : ℕ => liminf (fun k : ℕ => planarBrownianMotion 0
        (cdfEvent O (fun b t => lqgClockApprox γ hc (dyadicScale k) b t) (s + etaSeq j))) atTop)
      atTop (𝓝 (planarBrownianMotion 0 {b | lbmExitTime F O b ≤ ENNReal.ofReal s})) := by
  obtain ⟨k, -, hB⟩ := hsubω
  have hA : planarBrownianMotion 0 {b | lbmExitTime F O b ≤ ENNReal.ofReal s} =
      planarBrownianMotion 0 (cdfEvent O F s) := by
    apply measure_congr
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hF_tc] with b hb
    exact lbmExitTime_le_ofReal_iff hO b hb hs
  have hmeasG : Measurable fun q : ContinuousPath ℂ × ℝ≥0 =>
      limsup (fun j => lqgClockApprox γ hc (dyadicScale (k j)) q.1 q.2) atTop :=
    Measurable.limsup (fun j => hJoint (k j))
  have hGF : ∀ᵐ b ∂(planarBrownianMotion 0), ∀ t : ℝ≥0,
      limsup (fun j => lqgClockApprox γ hc (dyadicScale (k j)) b t) atTop = F b t :=
    hB.mono fun b hb t => (hb t).limsup_eq
  have hEvt : ∀ s' : ℝ, planarBrownianMotion 0 (cdfEvent O F s') = planarBrownianMotion 0
      (cdfEvent O (fun b t => limsup (fun j => lqgClockApprox γ hc (dyadicScale (k j)) b t) atTop) s') := by
    intro s'
    apply measure_congr
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hGF] with b hb
    simp only [cdfEvent, Set.mem_ofPred_eq, hb]
  have hRC : Tendsto (fun j : ℕ => planarBrownianMotion 0 (cdfEvent O F (s + (etaSeq j + etaSeq j))))
      atTop (𝓝 (planarBrownianMotion 0 (cdfEvent O F s))) := by
    have h := tendsto_measure_cdfEvent (planarBrownianMotion 0) hσ (G := fun b t => limsup (fun j => lqgClockApprox γ hc (dyadicScale (k j)) b t) atTop) hmeasG s
      (c := fun j => etaSeq j + etaSeq j) (fun j => by linarith [etaSeq_pos j])
      (fun j j' hjj' => add_le_add (etaSeq_anti hjj') (etaSeq_anti hjj')) two_etaSeq_tendsto
    simp only [hEvt]
    exact h
  have hlow : ∀ j : ℕ, planarBrownianMotion 0 (cdfEvent O F s) ≤ liminf (fun k : ℕ =>
      planarBrownianMotion 0 (cdfEvent O (fun b t => lqgClockApprox γ hc (dyadicScale k) b t)
        (s + etaSeq j))) atTop := by
    intro j
    apply le_of_forall_add_tendsto_zero
      (Y := fun T : ℕ => planarBrownianMotion 0 (tailEvent O (T : ℝ≥0)))
      (tendsto_measure_tailEvent _ hσ hfin)
    intro T
    refine le_liminf_add_of_tendsto_zero ?_ (fun k => measure_le_of_subset_union
      (cdfEvent_subset_sub F (fun b t => lqgClockApprox γ hc (dyadicScale k) b t) s (etaSeq j) (T : ℝ≥0)))
    have h := hLQG (T : ℝ≥0) (etaSeq j) (etaSeq_pos j)
    exact h
  have hup : ∀ j : ℕ, limsup (fun k : ℕ =>
      planarBrownianMotion 0 (cdfEvent O (fun b t => lqgClockApprox γ hc (dyadicScale k) b t)
        (s + etaSeq j))) atTop ≤ planarBrownianMotion 0 (cdfEvent O F (s + (etaSeq j + etaSeq j))) := by
    intro j
    apply le_of_forall_add_tendsto_zero
      (Y := fun T : ℕ => planarBrownianMotion 0 (tailEvent O (T : ℝ≥0)))
      (tendsto_measure_tailEvent _ hσ hfin)
    intro T
    refine limsup_le_add_of_tendsto_zero (z := fun k => planarBrownianMotion 0
      (closeEvent (T : ℝ≥0) (etaSeq j) (fun b t => lqgClockApprox γ hc (dyadicScale k) b t) F)) ?_ (fun k => ?_)
    · have h := hLQG (T : ℝ≥0) (etaSeq j) (etaSeq_pos j)
      exact h
    · have h := measure_le_of_subset_union (μ := planarBrownianMotion 0) (cdfEvent_sub_subset (O := O) F
        (fun b t => lqgClockApprox γ hc (dyadicScale k) b t) (s + etaSeq j) (etaSeq j) (T : ℝ≥0))
      have e : s + etaSeq j + etaSeq j = s + (etaSeq j + etaSeq j) := add_assoc _ _ _
      rw [e] at h
      exact h
  have hsqueeze := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRC
    (fun j => hlow j) (fun j => (liminf_le_limsup).trans (hup j))
  rw [hA]
  exact hsqueeze

/-- The AE-measurability of the exit-time cdf, for a family of clocks satisfying the hypotheses of `IsValid`
(with the subsequence convergence `hsub` as a named hypothesis). -/
theorem aemeasurable_cdf_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hc : Ω → ℝ → ℂ → ℝ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hc_meas : ∀ (r : ℝ) (z : ℂ), 0 < r → Measurable fun ω => hc ω r z)
    (hae_cont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hclock : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hc ω) 0 (F ω) ∧
      ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion 0), IsTimeChangeClock (F ω b))
    (hsub : ∀ᵐ ω ∂P, ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion 0),
      ∀ t : ℝ≥0, Tendsto (fun j => lqgClockApprox γ (hc ω) (dyadicScale (k j)) b t) atTop (𝓝 (F ω b t)))
    {s : ℝ} (hs : 0 ≤ s) :
    AEMeasurable (fun ω => planarBrownianMotion 0
      {b | lbmExitTime (F ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal s}) P := by
  obtain ⟨N, hsubN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae_cont)
  have hcont : ∀ ω ∉ N, ∀ r : ℝ, 0 < r → Continuous fun z => hc ω r z := by
    intro ω hω r hr
    have h1 : ContinuousOn (fun p : ℝ × ℂ => hc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
      by_contra h
      exact hω (hsubN h)
    exact h1.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨hr, mem_univ z⟩)
  have hσ : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball (0 : ℂ) (1 / 2)) b :=
    KilledOccupation.measurable_pathExitTime_ball 0 (1 / 2)
  have hfin : ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion 0), pathExitTime (ball (0 : ℂ) (1 / 2)) b < ⊤ :=
    ae_lt_top hσ (KilledOccupation.lintegral_pathExitTime_planar_ne_top 0 0 (1 / 2))
  have hε : ∀ k : ℕ, 0 < dyadicScale k := fun k => pow_pos (by norm_num) k
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  have hJoint : ∀ ω, ω ∉ N → ∀ k : ℕ, Measurable fun q : ContinuousPath ℂ × ℝ≥0 =>
      lqgClockApprox γ (hc ω) (dyadicScale k) q.1 q.2 := by
    intro ω hωN k
    have h : Measurable fun q : ContinuousPath ℂ × ℝ≥0 =>
        lqgClockApprox γ (hcT N hc ω) (dyadicScale k) q.1 q.2 :=
      (measurable_approxClock γ hNm hc_meas hcont (hε k)).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    rw [hcT_eq_of_not_mem hωN] at h
    exact h
  have hMeas : ∀ j : ℕ, Measurable fun ω => liminf (fun k : ℕ => planarBrownianMotion 0
      (cdfEvent (ball 0 (1 / 2)) (fun b t => lqgClockApprox γ (hcT N hc ω) (dyadicScale k) b t)
        (s + etaSeq j))) atTop :=
    fun j => Measurable.liminf fun k =>
      measurable_cdf_approx γ hNm hc_meas hcont (hε k) hσ (s + etaSeq j)
  refine aemeasurable_of_tendsto_metrizable_ae atTop (fun j => (hMeas j).aemeasurable) ?_
  filter_upwards [hNae, hclock, hsub] with ω hωN hcl hsb
  have hG := tendsto_cdf_good isOpen_ball hσ hfin γ (hc ω) (F ω) hs hcl.1 hcl.2 (hJoint ω hωN) hsb
  rw [hcT_eq_of_not_mem hωN]
  exact hG

end M0Cdf

/-- **Step 5 of `MQ-li-11`** (`hcdf` of `MatedCRTEnv.m₀_pos`): for a valid environment, the annealed exit-time cdf
`ω ↦ P₀{b | lbmExitTime (S.clock ω) (ball 0 (1/2)) b ≤ ofReal s}` is AE-measurable. The subsequence convergence
`hsub` of the dyadic LQG clocks is a named hypothesis (see the module docstring). -/
theorem MatedCRTEnv.aemeasurable_exitTimeCdf {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (𝒮 : SpaceFillingSLEModel) (γ : ℝ) (_hγ : 0 < γ) (_hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ)
    (hsub : ∀ᵐ ω ∂S.P, ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion 0),
      ∀ t : ℝ≥0, Tendsto (fun j => lqgClockApprox γ (S.hcirc ω) (dyadicScale (k j)) b t) atTop
        (𝓝 (S.clock ω b t)))
    (s : ℝ) :
    AEMeasurable (fun ω => planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal s}) S.P := by
  have hclock : ∀ᵐ ω ∂S.P, IsLQGClock planarBrownianMotion γ (S.hcirc ω) 0 (S.clock ω) ∧
      ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion 0), IsTimeChangeClock (S.clock ω b) :=
    hS.isLQGClock.mono fun ω h => ⟨(h 0).1, (h 0).2⟩
  have hcore : ∀ t : ℝ, 0 ≤ t → AEMeasurable (fun ω => planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal t}) S.P := fun t ht =>
    M0Cdf.aemeasurable_cdf_core S.P γ S.hcirc S.clock hS.isQuantumCone.measurable_circle
      hS.isQuantumCone.ae_continuousOn_circle hclock hsub ht
  rcases le_total 0 s with hs | hs
  · exact hcore s hs
  · have h0 := hcore 0 le_rfl
    simpa [ENNReal.ofReal_of_nonpos hs] using h0

end MatedCRT

end
