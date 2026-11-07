import MatedCRT.Defs.KilledGMCClock
import MatedCRT.Defs.DirichletGFF
import MarkovProcess.Path.ExitTimeShift

/-! # Localization of convergence of Liouville clocks -/

namespace MatedCRT

open HarmonicBalls MarkovProcess MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-- A stopped clock only uses the circle-average field inside the domain:
the exit time itself is a Lebesgue-null endpoint. -/
theorem killedGMCClockApprox_eq_of_eqOn (D : Set ℂ) (γ : ℝ)
    (hε gε : ℝ → ℂ → ℝ) (ε : ℝ) (b : ContinuousPath ℂ) (t : ℝ≥0)
    (hfield : Set.EqOn (hε ε) (gε ε) D) :
    killedGMCClockApprox D γ hε ε b t = killedGMCClockApprox D γ gε ε b t := by
  let T : ℝ≥0 := (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal
  have hT : (T : ℝ≥0∞) ≤ ContinuousPath.exitTime D b := by
    dsimp [T]
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
    exact min_le_right _ _
  change (∫ s in (0 : ℝ)..(T : ℝ),
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal))) =
    ∫ s in (0 : ℝ)..(T : ℝ),
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * gε ε (b s.toNNReal))
  apply intervalIntegral.integral_congr_Ioo_of_le T.2
  intro s hs
  have hsT : s.toNNReal < T := by
    apply NNReal.coe_lt_coe.mp
    simpa [Real.toNNReal_of_nonneg (le_of_lt hs.1)] using hs.2
  have hsτ : (s.toNNReal : ℝ≥0∞) < ContinuousPath.exitTime D b :=
    (ENNReal.coe_lt_coe.mpr hsT).trans_le hT
  change ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal)) =
    ε ^ (γ ^ 2 / 2) * Real.exp (γ * gε ε (b s.toNNReal))
  rw [hfield (ContinuousPath.mem_of_lt_exitTime D b s.toNNReal hsτ)]

/-- The circle-average clock is jointly measurable in the path and time
when the circle-average field is measurable. -/
theorem measurable_lqgClockApprox (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ)
    (hfield : Measurable (hε ε)) :
    Measurable (fun p : ContinuousPath ℂ × ℝ≥0 => lqgClockApprox γ hε ε p.1 p.2) := by
  let A : Set ((ContinuousPath ℂ × ℝ≥0) × ℝ) :=
    {q | 0 < q.2 ∧ q.2 ≤ (q.1.2 : ℝ)}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (NNReal.continuous_coe.measurable.comp (measurable_snd.comp measurable_fst)))
  have heval : Measurable (fun q : (ContinuousPath ℂ × ℝ≥0) × ℝ =>
      q.1.1 q.2.toNNReal) := by
    exact (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk
        (continuous_real_toNNReal.measurable.comp measurable_snd))
  have hf : Measurable (fun q : (ContinuousPath ℂ × ℝ≥0) × ℝ =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (q.1.1 q.2.toNNReal))) := by
    exact measurable_const.mul ((measurable_const.mul (hfield.comp heval)).exp)
  have hint := (hf.indicator hA).stronglyMeasurable.integral_prod_right' (ν := volume)
  convert hint.measurable using 1
  funext p
  change (∫ s in (0 : ℝ)..(p.2 : ℝ),
    ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (p.1 s.toNNReal))) = _
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (p.2 : ℝ) from p.2.2),
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with s
  have hpair : (p, s) ∈ A ↔ s ∈ Set.Ioc (0 : ℝ) (p.2 : ℝ) := Iff.rfl
  simp only [Set.indicator, hpair]

/-- A jointly measurable circle-average clock remains measurable when stopped
at the exit time of an open set. -/
theorem measurable_killedGMCClockApprox {D : Set ℂ} (hD : IsOpen D)
    (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) (t : ℝ≥0)
    (hclock : Measurable (fun p : ContinuousPath ℂ × ℝ≥0 =>
      lqgClockApprox γ hε ε p.1 p.2)) :
    Measurable (fun b => killedGMCClockApprox D γ hε ε b t) := by
  have hexit : Measurable (ContinuousPath.exitTime D : ContinuousPath ℂ → ℝ≥0∞) :=
    ContinuousPath.measurable_exitTime D hD
  have htime : Measurable (fun b : ContinuousPath ℂ =>
      (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal) :=
    ENNReal.measurable_toNNReal.comp (measurable_const.min hexit)
  exact hclock.comp (measurable_id.prodMk htime)

/-- Measurability of the field at a scale implies measurability of the
corresponding clock stopped at the exit of an open set. -/
theorem measurable_killedGMCClockApprox_of_field {D : Set ℂ} (hD : IsOpen D)
    (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) (t : ℝ≥0)
    (hfield : Measurable (hε ε)) :
    Measurable (fun b => killedGMCClockApprox D γ hε ε b t) :=
  measurable_killedGMCClockApprox hD γ hε ε t (measurable_lqgClockApprox γ hε ε hfield)

/-- Only the field on the domain needs to be continuous for the stopped
clock to be measurable; its values outside the domain are irrelevant. -/
theorem measurable_killedGMCClockApprox_of_continuousOn {D : Set ℂ} (hD : IsOpen D)
    (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) (t : ℝ≥0)
    (hfield : ContinuousOn (hε ε) D) :
    Measurable (fun b => killedGMCClockApprox D γ hε ε b t) := by
  have hr : Measurable (fun z : D => hε ε z) :=
    (continuousOn_iff_continuous_domRestrict.mp hfield).measurable
  obtain ⟨g, hg, hgeq⟩ := MeasurableEmbedding.exists_measurable_extend
    (MeasurableEmbedding.subtype_coe hD.measurableSet) hr (fun _ => ⟨0⟩)
  have heq : Set.EqOn (hε ε) g D := by
    intro z hz
    exact (congrFun hgeq ⟨z, hz⟩).symm
  have hk := measurable_killedGMCClockApprox_of_field hD γ (fun _ => g) ε t hg
  convert hk using 1
  funext b
  exact killedGMCClockApprox_eq_of_eqOn D γ hε (fun _ => g) ε b t heq

/-- The Dirichlet GFF circle-average continuity gives measurability of each
localized clock at scales whose averaging disks stay inside the field domain. -/
theorem IsDirichletGFF.ae_measurable_killedGMCClockApprox
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D U : Set ℂ}
    {h : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsDirichletGFF P D h hcirc) (hU : IsOpen U)
    (γ ε : ℝ) (hε : 0 < ε)
    (hdisks : ∀ z ∈ U, Metric.closedBall z ε ⊆ D) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Measurable (fun b => killedGMCClockApprox U γ (hcirc ω) ε b t) := by
  filter_upwards [hGFF.continuous_circle] with ω hcont
  apply measurable_killedGMCClockApprox_of_continuousOn hU γ (hcirc ω) ε t
  exact hcont.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => ⟨hε, hdisks z hz⟩)

/-- Stopping preserves the uniform-on-compacts convergence in probability
in `IsLQGClock`. The stopping time may depend on the whole path, and may be
infinite; measurability is not required for this outer-probability bound. -/
theorem IsLQGClock.stopped_uniform_in_probability
    {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock Q γ hε x F) (τ : ContinuousPath ℂ → ℝ≥0∞)
    (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => Q x {b | ∃ t ≤ T,
      η ≤ |lqgClockApprox γ hε (dyadicScale n) b
          (min (t : ℝ≥0∞) (τ b)).toNNReal -
        F b (min (t : ℝ≥0∞) (τ b)).toNNReal|}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hclock T η hη) (fun _ => bot_le) ?_
  intro n
  apply measure_mono
  rintro b ⟨t, ht, hdiff⟩
  refine ⟨(min (t : ℝ≥0∞) (τ b)).toNNReal, ?_, hdiff⟩
  have hle : (min (t : ℝ≥0∞) (τ b)).toNNReal ≤ t := by
    simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top (min_le_left (t : ℝ≥0∞) (τ b))
  exact hle.trans ht

/-- The stopped circle-average approximations converge to the global LQG
clock stopped on leaving the domain, uniformly on compact time intervals. -/
theorem IsLQGClock.killed_uniform_in_probability
    {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock Q γ hε x F) (D : Set ℂ)
    (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => Q x {b | ∃ t ≤ T,
      η ≤ |killedGMCClockApprox D γ hε (dyadicScale n) b t -
        F b (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal|}) atTop (𝓝 0) := by
  simpa only [killedGMCClockApprox] using
    IsLQGClock.stopped_uniform_in_probability hclock (ContinuousPath.exitTime D) T hη

/-- At a deterministic time, the stopped approximations converge in measure
to the stopped global clock. -/
theorem IsLQGClock.killed_tendstoInMeasure
    {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock Q γ hε x F) (D : Set ℂ) (t : ℝ≥0) :
    TendstoInMeasure (Q x) (fun n b => killedGMCClockApprox D γ hε (dyadicScale n) b t)
      atTop (fun b => F b (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal) := by
  apply tendstoInMeasure_iff_norm.mpr
  intro η hη
  have hlim := IsLQGClock.killed_uniform_in_probability hclock D t hη
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) ?_
  intro n
  apply measure_mono
  intro b hb
  simp only [mem_ofPred_eq] at hb
  exact ⟨t, le_rfl, by simpa only [Real.norm_eq_abs] using hb⟩

/-- Any other limit in measure of the killed approximations agrees almost
surely, at the specified time, with the restriction of the global clock. -/
theorem IsLQGClock.ae_killed_clock_eq_of_tendstoInMeasure
    {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock Q γ hε x F) (D : Set ℂ) (t : ℝ≥0)
    {G : ContinuousPath ℂ → ℝ}
    (hG : TendstoInMeasure (Q x)
      (fun n b => killedGMCClockApprox D γ hε (dyadicScale n) b t) atTop G) :
    ∀ᵐ b ∂Q x, G b = F b (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal := by
  exact tendstoInMeasure_ae_unique hG (IsLQGClock.killed_tendstoInMeasure hclock D t)

/-- An almost-sure dyadic construction of a killed clock agrees, at each
fixed time, with the stopped global clock whenever the approximations are
almost everywhere measurable. -/
theorem IsLQGClock.ae_killed_clock_eq_of_ae_tendsto
    {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {x : ℂ} [IsFiniteMeasure (Q x)] {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock Q γ hε x F) (D : Set ℂ) (t : ℝ≥0)
    {G : ContinuousPath ℂ → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable
      (fun b => killedGMCClockApprox D γ hε (dyadicScale n) b t) (Q x))
    (hG : ∀ᵐ b ∂Q x, Tendsto
      (fun n => killedGMCClockApprox D γ hε (dyadicScale n) b t) atTop (𝓝 (G b))) :
    ∀ᵐ b ∂Q x, G b = F b (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal := by
  exact IsLQGClock.ae_killed_clock_eq_of_tendstoInMeasure hclock D t
    (tendstoInMeasure_of_tendsto_ae hmeas hG)

/-- Stopping at an extended nonnegative time preserves clock continuity. -/
theorem continuous_stopped_clock {f : ℝ≥0 → ℝ} (hf : Continuous f) (τ : ℝ≥0∞) :
    Continuous (fun t : ℝ≥0 => f (min (t : ℝ≥0∞) τ).toNNReal) := by
  by_cases hτ : τ = ⊤
  · simpa [hτ] using hf
  · have heq : τ = (τ.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hτ).symm
    rw [heq]
    simp only [← ENNReal.coe_min, ENNReal.toNNReal_coe]
    exact hf.comp (continuous_id.min continuous_const)

/-- Continuous killed clock versions that arise as almost-sure dyadic limits
agree with the stopped global clock simultaneously at every time. -/
theorem IsLQGClock.ae_killed_clock_eq_all_of_ae_tendsto
    {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {x : ℂ} [IsFiniteMeasure (Q x)] {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock Q γ hε x F) (D : Set ℂ)
    {G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hmeas : ∀ n t, AEStronglyMeasurable
      (fun b => killedGMCClockApprox D γ hε (dyadicScale n) b t) (Q x))
    (hG : ∀ t, ∀ᵐ b ∂Q x, Tendsto
      (fun n => killedGMCClockApprox D γ hε (dyadicScale n) b t) atTop (𝓝 (G b t)))
    (hcont : ∀ᵐ b ∂Q x, Continuous (G b) ∧ Continuous (F b)) :
    ∀ᵐ b ∂Q x, ∀ t, G b t =
      F b (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal := by
  obtain ⟨s, hs, hdense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have heq : ∀ᵐ b ∂Q x, ∀ t ∈ s, G b t =
      F b (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal := by
    apply (ae_ball_iff hs).2
    intro t _
    exact IsLQGClock.ae_killed_clock_eq_of_ae_tendsto hclock D t
      (fun n => hmeas n t) (hG t)
  filter_upwards [heq, hcont] with b hb hc
  have := hc.1.ext_on hdense (continuous_stopped_clock hc.2 _) hb
  intro t
  exact congrFun this t

end MatedCRT
