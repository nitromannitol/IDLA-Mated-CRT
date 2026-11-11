import MatedCRT.Steps.Sec3.DirichletStoppedClock
import MatedCRT.Defs.KilledGMCClock
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.DirichletClockTransfer
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.StoppedClockDenseLimit

/-!
# Stopped-clock step: time-zero obstruction, dense-time upgrade, existence specification

Repair of the audited stopped-clock route (`env-steps.tex` lines 1060-1252; routing record
`docs/campaign/ENV-STEPS-ROUTING-20261108.md`, section "Stopped clocks").

* **Obstruction.** Every killed approximation vanishes at time zero (`killedGMCClockApprox` at `t = 0`
  integrates over `[0, 0]`). So any limit `G` supplied to `DirichletStoppedClockConvergenceStep` must
  satisfy `G = 0` at time zero, almost everywhere (`dirichlet_stopped_clock_convergence_time_zero`).
  Hence `G ≡ 1` is impossible under a probability law (`not_dirichlet_stopped_clock_convergence_const_one`).
  This refutes only a universal discharge of the source hypothesis, not the transfer theorem.
* **Dense-time upgrade.** Eventually monotone killed clocks that converge at nonnegative rational
  times to a continuous limit converge at every time (`dirichlet_stopped_clock_convergence_of_rat_limit`).
  The deterministic lemmas are in `StoppedClockDenseLimit.lean`.
* **Existence specification (NOT PROVED).** `AuditedDirichletStoppedClockExistenceStep` records the
  constructor of `prop:correctstopped` as a `Prop`. The consumer wrapper
  `berestycki_dirichlet_time_change_eq_lbm_of_existence` is CONDITIONAL on it.
-/

open HarmonicBalls MarkovProcess MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT

universe u

/-- The killed clock approximation vanishes at time zero: the defining integral runs over `[0, 0]`. -/
theorem killed_gmc_clock_approx_zero_time (D : Set ℂ) (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ)
    (b : ContinuousPath ℂ) :
    killedGMCClockApprox D γ hε ε b 0 = 0 := by
  simp [killedGMCClockApprox, lqgClockApprox]

/-- **Time-zero obstruction.** Under `DirichletStoppedClockConvergenceStep`, the supplied limit
vanishes at time zero for almost every `(ω, b)` under the product law. -/
theorem dirichlet_stopped_clock_convergence_time_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : Set ℂ} {γ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {x : ℂ}
    {G : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hstep : DirichletStoppedClockConvergenceStep P U γ hcirc x G) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), G q.1 q.2 0 = 0 := by
  filter_upwards [hstep] with q hq
  have h0 := hq.1 0
  have h0' : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (G q.1 q.2 0)) :=
    Tendsto.congr (fun n => killed_gmc_clock_approx_zero_time U γ (hcirc q.1) (dyadicScale n) q.2)
      h0
  exact (tendsto_nhds_unique tendsto_const_nhds h0').symm

/-- **Obstruction for a supplied limit.** If `G` is nonzero at time zero for every `(ω, b)` and the
product law is nonzero, then `G` does not satisfy `DirichletStoppedClockConvergenceStep`. -/
theorem not_dirichlet_stopped_clock_convergence_of_time_zero_ne {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : Set ℂ} {γ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {x : ℂ}
    {G : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hne : P.prod (planarBrownianMotion x) ≠ 0) (hpos : ∀ ω b, G ω b 0 ≠ 0) :
    ¬ DirichletStoppedClockConvergenceStep P U γ hcirc x G := by
  intro hstep
  have hfalse : ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), False :=
    (dirichlet_stopped_clock_convergence_time_zero hstep).mono fun q hq => hpos q.1 q.2 hq
  exact hne (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hfalse))

/-- **Time-zero obstruction for `G ≡ 1`.** Under any probability measure `P` on `Ω`, the
constant limit `G ≡ 1` does not satisfy `DirichletStoppedClockConvergenceStep`, because every killed
approximation is zero at time zero. -/
theorem not_dirichlet_stopped_clock_convergence_const_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Set ℂ) (γ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (x : ℂ) :
    ¬ DirichletStoppedClockConvergenceStep P U γ hcirc x (fun _ _ _ => 1) :=
  not_dirichlet_stopped_clock_convergence_of_time_zero_ne
    (IsProbabilityMeasure.ne_zero _) (fun _ _ => one_ne_zero)

/-- **Dense-time upgrade to the Step.** If, for almost every `(ω, b)`, the killed approximations are
eventually monotone in time, converge at every nonnegative rational time to `G`, and `G` is
continuous, then `G` satisfies `DirichletStoppedClockConvergenceStep`. -/
theorem dirichlet_stopped_clock_convergence_of_rat_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (x : ℂ)
    (G : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hmono : ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∀ᶠ n in atTop,
      Monotone (fun t : ℝ≥0 => killedGMCClockApprox U γ (hcirc q.1) (dyadicScale n) q.2 t))
    (hrat : ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∀ r : ℚ, 0 ≤ r →
      Tendsto (fun n => killedGMCClockApprox U γ (hcirc q.1) (dyadicScale n) q.2
        (Real.toNNReal (r : ℝ))) atTop (𝓝 (G q.1 q.2 (Real.toNNReal (r : ℝ)))))
    (hcont : ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), Continuous (G q.1 q.2)) :
    DirichletStoppedClockConvergenceStep P U γ hcirc x G := by
  filter_upwards [hmono, hrat, hcont] with q hm hr hc
  exact ⟨fun t => StoppedClockDenseLimit.tendsto_nnreal_of_rat_limit
    (K := fun n s => killedGMCClockApprox U γ (hcirc q.1) (dyadicScale n) q.2 s) hm hc hr t, hc⟩

/-- **Specification of the existential stopped-clock constructor (NOT PROVED; a proof target).**
For a Dirichlet GFF on a bounded simply connected field domain `D`, with `U` open and bounded,
`closure U ⊆ D`, `x ∈ U` and `0 ≤ γ < 2`, there is a jointly measurable continuous-path-valued limit
`Gc` that satisfies the stopped-clock Step, and that is identified, almost surely in `ω` and then
`planarBrownianMotion x`-almost surely in `b`, with the stopped time change `F ω b (t ⊓ τ_U b)`.
Source: `env-steps.tex` `prop:correctstopped` (lines 1106-1252), in existential form. No
measurability of the supplied `F` is assumed. This is not a literature input. -/
def AuditedDirichletStoppedClockExistenceStep : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D U : Set ℂ) (h : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (x : ℂ) (γ : ℝ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ),
    IsOpen D → IsOpen U → Bornology.IsBounded D → SimplyConnectedSpace D →
    Bornology.IsBounded U → closure U ⊆ D → x ∈ U →
    IsDirichletGFF P D h hcirc → 0 ≤ γ → γ < 2 →
    (∀ᵐ ω ∂P,
      IsLQGClock planarBrownianMotion γ (hcirc ω) x (F ω) ∧
      ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω b)) →
    ∃ Gc : Ω × ContinuousPath ℂ → C(ℝ≥0, ℝ),
      Measurable Gc ∧
      DirichletStoppedClockConvergenceStep P U γ hcirc x
        (fun ω b t => Gc (ω, b) t) ∧
      ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion x), ∀ t : ℝ≥0,
        Gc (ω, b) t = F ω b
          (((t : ℝ≥0∞) ⊓ ContinuousPath.exitTime U b).toNNReal)

/-- **CONDITIONAL on `AuditedDirichletStoppedClockExistenceStep`, which is not proved.** The unchanged
consumer `berestycki_dirichlet_time_change_eq_lbm`, applied to the limit that the existential
specification supplies. It is not an unconditional result. It passes the consumer's hypotheses through
unchanged. The simple connectivity and `0 ≤ γ < 2` hypotheses are those of the specification,
not of the consumer. -/
theorem berestycki_dirichlet_time_change_eq_lbm_of_existence {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D U : Set ℂ) (h : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (x : ℂ) (γ : ℝ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hex : AuditedDirichletStoppedClockExistenceStep.{u})
    (hD : IsOpen D) (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hclosure : closure U ⊆ D) (hx : x ∈ U) (hgff : IsDirichletGFF P D h hcirc)
    (hDbounded : Bornology.IsBounded D) (hsc : SimplyConnectedSpace D)
    (hγ0 : 0 ≤ γ) (hγ2 : γ < 2)
    (hglobal : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hcirc ω) x (F ω) ∧
      ∀ᵐ b ∂planarBrownianMotion x, IsTimeChangeClock (F ω b)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < lbmExitTime (F ω) U b →
          Tendsto (fun n => b ((killedClockInverse
            (killedGMCClockApprox U γ (hcirc ω) (dyadicScale n) b)
            (ContinuousPath.exitTime U b) t).toNNReal)) atTop
            (𝓝 (liouvilleBrownianPath (F ω) b t)) := by
  obtain ⟨G, -, hsource, -⟩ :=
    hex Ω P D U h hcirc x γ F hD hU hDbounded hsc hbounded hclosure hx hgff hγ0 hγ2 hglobal
  exact berestycki_dirichlet_time_change_eq_lbm P D U h hcirc x γ F (fun ω b t => G (ω, b) t)
    hsource hD hU hbounded hclosure hx hgff hglobal

/-- **Consistency of the specification with the obstruction.** The identification in
`AuditedDirichletStoppedClockExistenceStep` and `IsTimeChangeClock` (which forces `F ω b 0 = 0`)
make the identified limit vanish at time zero. So the time-zero obstruction above does not contradict
the specification. -/
theorem stopped_identification_time_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : Measure (ContinuousPath ℂ)) (U : Set ℂ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (Gc : Ω × ContinuousPath ℂ → C(ℝ≥0, ℝ))
    (hF : ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, IsTimeChangeClock (F ω b))
    (hid : ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, ∀ t : ℝ≥0,
      Gc (ω, b) t = F ω b (((t : ℝ≥0∞) ⊓ ContinuousPath.exitTime U b).toNNReal)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, Gc (ω, b) 0 = 0 := by
  filter_upwards [hF, hid] with ω hFω hidω
  filter_upwards [hFω, hidω] with b hb hb'
  rw [hb' 0]
  simp [hb.map_zero]

end MatedCRT
