import Mathlib
import MatedCRT.FirstPass.S6e.Final
import MatedCRT.FirstPass.S6e.Uniform
import MatedCRT.FirstPass.S6e.Guard
import MatedCRT.FirstPass.S6e.Cutoff
import MatedCRT.FirstPass.S6f.UniformEvents
import MatedCRT.FirstPass.S4S6c.DyadicCutoff68
import MatedCRT.FirstPass.S6r.Window
import MatedCRT.FirstPass.S6r.Count
import MatedCRT.FirstPass.S6r.Amplification
import MatedCRT.FirstPass.S4S6c.Uniform68Final

/-!
# Lemma 6.8, redesigned guard (q2, S10): `GuardProbStmt` from the mesh events and the shell chain

Route (operator 06:52; redesign note section 12 (S10); shells note section 13): the guard
`Lemma68Uniform.GuardProbStmt` (S6e/Uniform.lean:132) follows from

* `meshEventsStmt_of_draft`: the three events of `draft68_uniform_events` (S6f/UniformEvents.lean:114), proved from
  the Draft hypotheses `GreenKernelLowerBoundStmt`, `CellSizeEstimateStmt`, `ExitTimeUpperBoundStmt` with the
  exponent `ζ = 1/(2+γ)² < 1/2` (the exponent used in the q1 proof; its statement only records `ζ < 1`).
* `ShellChainStmt`: the per-radius quenched count bound on the good event, with the count constant
  `countConst ζ = 2^{-a}/800` of the landed count lemma (S6r/Count.lean:25, `count_bound`, `count_hypothesis`).
  The window good event at the dyadic window scale `dyadicD r` (S6r/Window.lean:25) is supplied by a family `Ew` of
  polynomially high probability (the S2.3 short-window prevalence, owned by z5 as `S6r/Prevalence.lean`; not yet in Lean).
  OPEN.
* `window_cutoff`: the dyadic Borel-Cantelli cutoff for `Ew`, proved from `DyadicCutoff68.ae_mem_goodFrom` and `ddOf`.
* the count-to-half step: `exit_le_half_of_count` from `one_sub_pow_le_exp`, `exp_le_of_counts` and
  `constant_order_conclusion` (S6r/Amplification.lean), proved.
* the almost sure escape and finite-exit facts, proved from `IsValid` (S6e/Guard.lean).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68Guard10

open DyadicCutoff68 Lemma68Window

/-- The mesh-indexed good event of Lemma 6.8 at the constants of `draft68_uniform_events`: the green-kernel
event, the cell-size event and the exit-time event, all at mesh `ε`. -/
def meshEvent {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (γ ω₀ ρ CG ζ α CE : ℝ) (ε : ℝ) : Set Ω :=
  greenLowEvent68 S ω₀ ρ CG ε ∩ cellSizeEvent68 S γ ζ ρ ε ∩ exitTimeEvent68 S α ρ CE ε

/-- The almost sure field event used by the guard: the curve escapes both ends, the multiplicities are locally finite
with consecutive adjacency, and every window radius `0 < r ≤ dd ω` has its dyadic window event `Ew (dyadicD r)`. -/
def goodField {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Ew : ℝ → Set Ω) (dd : Ω → ℝ) : Set Ω :=
  {ω | Lemma68Inputs.CurveEscapesBothEnds (S.η ω) ∧
    (∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) ∧
    ∀ r : ℝ, 0 < r → r ≤ dd ω → ω ∈ Ew (dyadicD r)}

/-- The mesh events with the exponents of `draft68_uniform_events` and the clause `ζ < 1/2` that `GuardProbStmt`
needs. Proved by `meshEventsStmt_of_draft` from the Draft hypotheses. -/
def MeshEventsStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 / 2 ∧ ∃ ω₀ α : ℝ, 0 < ω₀ ∧ ω₀ < α ∧ 0 < α ∧
    ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ CG : ℝ, 0 < CG ∧ ∃ CE : ℝ, 0 < CE ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) ∧
        HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) ∧
        HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE)

/-- OPEN INPUT (redesign S10 with the S2.3 window family and the S5-S8 shell chain). For constants satisfying the
q1 constraints, `R ≤ ρ/4`, `R ≤ rAmp q0 ζ`, `ζ < 1/2`, `0 < q0 ≤ 1`, and every valid environment whose mesh events are
of polynomially high probability, there is a window family `Ew` of polynomially high probability such that on the
mesh event, for every admissible configuration at radius `r ∈ [10 ε^ω₀, R]` whose dyadic window event holds, the
quenched exit probability is at most `(1 - q0/(1 + log(1/r))²)^N` for some shell count `N` with
`countConst ζ · r^{-ζ} ≤ N` (`count_hypothesis`, S6r/Count.lean:92). The clause is almost sure in `ω` for each `ε` (`∀ᵐ ω ∂S.P`), with every radius
`r` quantified inside it: a per-radius almost-sure clause cannot be combined over uncountably many `r`, while the
pointwise-in-`ω` window clause is not obtained from the field-measurable window family (S4S6c/ShellChain68.lean). -/
def ShellChainStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE R q0 s₀ : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 → 0 < q0 → q0 ≤ 1 → 0 < R → R ≤ ρ / 4 →
    R ≤ Lemma68Cutoff.rAmp q0 ζ → 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      ∃ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) ∧
        HarmonicBalls.PolyHighProb S.P Ew ∧
        ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
          Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
          (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
          ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
            ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
              ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
                Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- A polynomially high probability family has `ProbTendsToOne` (`P(E ε)ᶜ → 0` as `ε ↓ 0`). -/
lemma probTendsToOne_of_polyHighProb {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    (hE : HarmonicBalls.PolyHighProb P E) : ProbTendsToOne P E := by
  obtain ⟨p, hp, C, r₀, hr₀, h⟩ := hE
  have hpow : Tendsto (fun r : ℝ => r ^ p) (𝓝 0) (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto
    simpa [Real.zero_rpow hp.ne'] using hc
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ p)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => C * r ^ p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hmul : Tendsto (fun r : ℝ => C * r ^ p) (𝓝 0) (𝓝 (C * 0)) := hpow.const_mul C
      rw [mul_zero] at hmul
      exact hmul.mono_left nhdsWithin_le_nhds
    have h3 := ENNReal.tendsto_ofReal h1
    simpa using h3
  unfold ProbTendsToOne
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun _ => zero_le
  · filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr using h r hr.1 hr.2

/-- (S10, dyadic window cutoff) If the window events `Ew δ` are `F`-measurable and of polynomially high probability,
there is an `F`-measurable `dd` with `0 < dd ≤ 1` such that almost surely every radius `0 < r ≤ dd ω` has its dyadic
window event: `ω ∈ Ew (dyadicD r)`. Proof: the Borel-Cantelli family `goodFrom` of `DyadicCutoff68`, with the cutoff
`min 1 (sqrt (ddOf ω))`; for `ω ∈ goodFrom k` at the least such `k`, `r² ≤ 2^{-k}` gives `k ≤ Nat.log 2 ⌊1/r²⌋₊`. -/
theorem window_cutoff {Ω : Type} {F : MeasurableSpace Ω} [m : MeasurableSpace Ω] (P : @Measure Ω m)
    (Ew : ℝ → Set Ω) (hE : ∀ δ : ℝ, MeasurableSet[F] (Ew δ))
    (hpoly : HarmonicBalls.PolyHighProb P Ew) :
    ∃ dd : Ω → ℝ, Measurable[F] dd ∧ (∀ ω, 0 < dd ω) ∧ (∀ ω, dd ω ≤ 1) ∧
      ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → r ≤ dd ω → ω ∈ Ew (dyadicD r) := by
  obtain ⟨p, hp, C, r₀, hr₀, hpo⟩ := hpoly
  have hU : MeasurableSet[F] (⋃ k : ℕ, goodFrom Ew r₀ k) :=
    MeasurableSet.iUnion fun k => measurableSet_goodFrom hE k
  have hdd_meas : Measurable[F] (ddOf Ew r₀) := by
    unfold ddOf
    refine Measurable.ite (p := fun ω => ω ∈ ⋃ k : ℕ, goodFrom Ew r₀ k) hU ?_ measurable_const
    exact measurable_const.min
      (Measurable.iSup fun k => measurable_const.indicator (measurableSet_goodFrom hE k))
  have hddpos : ∀ ω, 0 < ddOf Ew r₀ ω := by
    intro ω
    unfold ddOf
    split_ifs with h
    · obtain ⟨k, hk⟩ := mem_iUnion.1 h
      have hpos : 0 < (goodFrom Ew r₀ k).indicator (fun _ => (1 / 2 : ℝ) ^ k) ω := by
        rw [Set.indicator_of_mem hk]
        exact pow_pos (by norm_num) k
      refine lt_min (half_pos hr₀) (lt_of_lt_of_le hpos (le_ciSup (f := fun i =>
        (goodFrom Ew r₀ i).indicator (fun _ => (1 / 2 : ℝ) ^ i) ω) ?_ k))
      exact ⟨1, by rintro _ ⟨i, rfl⟩; exact indicator_dyadic_le_one Ew r₀ ω i⟩
    · exact half_pos hr₀
  have hddr : ∀ ω, ddOf Ew r₀ ω ≤ r₀ / 2 := by
    intro ω
    unfold ddOf
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  refine ⟨fun ω => min 1 (Real.sqrt (ddOf Ew r₀ ω)), ?_, ?_, ?_, ?_⟩
  · exact measurable_const.min (Real.continuous_sqrt.measurable.comp hdd_meas)
  · intro ω
    exact lt_min one_pos (Real.sqrt_pos.2 (hddpos ω))
  · intro ω
    exact min_le_left _ _
  · filter_upwards [ae_mem_goodFrom P Ew r₀ C p hr₀ hp hpo] with ω hω
    intro r hr hrd
    classical
    have hex : ∃ k : ℕ, ω ∈ goodFrom Ew r₀ k := mem_iUnion.1 hω
    have hkspec : ω ∈ goodFrom Ew r₀ (Nat.find hex) := Nat.find_spec hex
    have hkmin : ∀ j : ℕ, ω ∈ goodFrom Ew r₀ j → Nat.find hex ≤ j := fun j hj => Nat.find_min' hex hj
    have hdd_le : ddOf Ew r₀ ω ≤ (1 / 2 : ℝ) ^ Nat.find hex := by
      unfold ddOf
      simp only [hω, ↓reduceIte]
      refine (min_le_right _ _).trans (ciSup_le fun j => ?_)
      by_cases hj : ω ∈ goodFrom Ew r₀ j
      · rw [Set.indicator_of_mem hj]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hkmin j hj)
      · rw [Set.indicator_of_notMem hj]
        positivity
    have hr1 : r ≤ 1 := hrd.trans (min_le_left _ _)
    have hsq : r ≤ Real.sqrt (ddOf Ew r₀ ω) := hrd.trans (min_le_right _ _)
    have hr2 : r ^ 2 ≤ ddOf Ew r₀ ω := by
      have h := pow_le_pow_left₀ hr.le hsq 2
      rwa [Real.sq_sqrt (hddpos ω).le] at h
    have hr3 : r ^ 2 ≤ (1 / 2 : ℝ) ^ Nat.find hex := hr2.trans hdd_le
    have hm : Nat.find hex ≤ Nat.log 2 ⌊1 / r ^ 2⌋₊ := by
      apply Nat.le_log_of_pow_le (by norm_num)
      apply Nat.le_floor
      push_cast
      have h2k : (0 : ℝ) < 2 ^ Nat.find hex := by positivity
      have hprod : (2 : ℝ) ^ Nat.find hex * (1 / 2 : ℝ) ^ Nat.find hex = 1 := by
        rw [← mul_pow]; norm_num
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < r ^ 2)]
      calc (2 : ℝ) ^ Nat.find hex * r ^ 2 ≤ 2 ^ Nat.find hex * (1 / 2 : ℝ) ^ Nat.find hex :=
            mul_le_mul_of_nonneg_left hr3 h2k.le
        _ = 1 := hprod
    have hlt : dyadicD r < r₀ := by
      have h1 : dyadicD r < 2 * r ^ 2 := dyadicD_lt_two_mul_sq hr hr1
      have h2 := hddr ω
      linarith
    have hmem := (mem_goodFrom.1 hkspec) (Nat.log 2 ⌊1 / r ^ 2⌋₊) hm
    unfold dyadicEvent at hmem
    simp only [show (1 / 2 : ℝ) ^ Nat.log 2 ⌊1 / r ^ 2⌋₊ < r₀ from hlt, ↓reduceIte] at hmem
    exact hmem

/-- (S10) The mesh events of `draft68_uniform_events`, with `ζ = 1/(2+γ)² < 1/2` (the q1 proof's exponent; the
statement of q1 only records `ζ < 1`), from the three Draft hypotheses. -/
theorem meshEventsStmt_of_draft (𝒮 : SpaceFillingSLEModel) (hG : GreenKernelLowerBoundStmt 𝒮)
    (hC : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮) : MeshEventsStmt 𝒮 := by
  intro γ hγ hγ2
  obtain ⟨ωG, hωG, hGr⟩ := greenLowEvent68_polyHighProb hG hγ hγ2
  obtain ⟨α, hα, hEr⟩ := hE γ hγ hγ2
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = 1 / (2 + γ) ^ 2 := ⟨_, rfl⟩
  have h2γ : 0 < (2 + γ) ^ 2 := by positivity
  have hq0 : 0 < q := by rw [hq_def]; positivity
  have hq1 : q < 1 / 2 := by
    rw [hq_def, div_lt_iff₀ h2γ]
    nlinarith
  have hqq : 2 / (2 + γ) ^ 2 - q = q := by rw [hq_def]; ring
  obtain ⟨ω₀, hω₀def⟩ : ∃ ω₀ : ℝ, ω₀ = min ωG (min (α / 2) (q / 2)) := ⟨_, rfl⟩
  have hω₀1 : ω₀ ≤ ωG := by rw [hω₀def]; exact min_le_left _ _
  have hω₀2 : ω₀ ≤ α / 2 := by rw [hω₀def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hω₀pos : 0 < ω₀ := by
    rw [hω₀def]; exact lt_min hωG (lt_min (half_pos hα) (half_pos hq0))
  have hω₀3 : ω₀ ≤ q / 2 := by rw [hω₀def]; exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨q, hq0, hq1, ω₀, α, hω₀pos, by linarith, hα, by rw [hqq]; linarith, ?_⟩
  intro ρ hρ0 hρ1
  obtain ⟨CG, hCG, hGS⟩ := hGr ρ hρ0 hρ1
  obtain ⟨CE, hCE, hES⟩ := hEr ρ hρ0 hρ1
  refine ⟨CG, hCG, CE, hCE, fun Ω _ S hS => ⟨?_, ?_, ?_⟩⟩
  · exact hGS ω₀ hω₀pos hω₀1 Ω S hS
  · exact hC γ hγ hγ2 q ρ hq0 (by linarith) hρ0 hρ1 Ω S hS
  · exact hES Ω S hS

/-- The count-to-half step (pure real analysis): with `N ≥ countConst ζ · r^{-ζ}`-type count `cN r^{-ζ} ≤ N`,
`(1 - q0/(1+log(1/r))²)^N ≤ exp(-cN q0 r^{-ζ}/(1+log(1/r))²)`, and the exponential is at most `1/2` by
`constant_order_conclusion`. -/
lemma exit_le_half_of_count {cN q0 ζ r x : ℝ} {N : ℕ} (hcN : 0 < cN) (hq0 : 0 < q0) (hq1 : q0 ≤ 1)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hN : cN * r ^ (-ζ) ≤ (N : ℝ))
    (hx : x ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N)
    (hexp : Real.exp (-(cN * q0 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) ≤ 1 / 2) : x ≤ 1 / 2 := by
  have hL : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr0 hr1)
  have hD : 1 ≤ (1 + Real.log (1 / r)) ^ 2 := by nlinarith
  have hq1' : q0 / (1 + Real.log (1 / r)) ^ 2 ≤ 1 := (div_le_self hq0.le hD).trans hq1
  exact hx.trans ((one_sub_pow_le_exp hq1' N).trans
    ((exp_le_of_counts hcN.le hq0.le hr0 hr1 hN le_rfl).trans hexp))

/-- Monotonicity of `ProbTendsToOne` under an inclusion holding `P`-almost surely for each `ε`: if `E ε ⊆ F ε` up to a
null set, then `F` has probability tending to one (the almost-sure form of `ProbTendsToOne.mono_pos`). -/
lemma probTendsToOne_mono_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (h : ProbTendsToOne P E) (hEF : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ω ∈ E ε → ω ∈ F ε) : ProbTendsToOne P F := by
  unfold ProbTendsToOne at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h (Eventually.of_forall fun _ => zero_le)
    (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  have hN : P {ω | ¬ (ω ∈ E ε → ω ∈ F ε)} = 0 := ae_iff.1 (hEF ε hε)
  calc P (F ε)ᶜ ≤ P ((E ε)ᶜ ∪ {ω | ¬ (ω ∈ E ε → ω ∈ F ε)}) := by
        refine measure_mono (fun ω hω => ?_)
        by_cases hωE : ω ∈ E ε
        · exact Or.inr (fun himp => hω (himp hωE))
        · exact Or.inl hωE
    _ ≤ P (E ε)ᶜ + P {ω | ¬ (ω ∈ E ε → ω ∈ F ε)} := measure_union_le _ _
    _ = P (E ε)ᶜ := by rw [hN, add_zero]

/-- The guard from a per-configuration count bound on the good event (the analogue of
`Lemma68Final.probTendsToOne_uniform_half_guarded` with the count constant `cN` in place of `1/200`). -/
theorem probTendsToOne_half_of_count {Ω ι : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (hE : ProbTendsToOne P E) {G : Set Ω} (hG : P Gᶜ = 0)
    {α : ℝ → ℝ} (hα : ∀ ε, 0 < ε → 0 < α ε)
    {dd : Ω → ℝ} {R cN q0 ζ : ℝ} (hdd : ∀ ω, dd ω ≤ R) (hR1 : R ≤ 1) (hcN : 0 < cN) (hq0 : 0 < q0)
    (hq1 : q0 ≤ 1)
    (hRr : ∀ r : ℝ, 0 < r → r ≤ R →
      Real.exp (-(cN * q0 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) ≤ 1 / 2)
    (Adm : ℝ → Ω → ℝ → ι → Prop) (exitF : ℝ → Ω → ℝ → ι → ℝ)
    (hpt : ∀ ε, 0 < ε → ∀ᵐ ω ∂P, ω ∈ E ε ∩ G → ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι, Adm ε ω r i →
      ∃ N : ℕ, cN * r ^ (-ζ) ≤ (N : ℝ) ∧
        exitF ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N) :
    ProbTendsToOne P (fun ε => {ω | ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι,
      Lemma68Final.guardedExit Adm exitF ε ω r i ≤ 1 / 2}) := by
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hG
  have hGa : ProbTendsToOne P (fun _ => G) := by
    unfold ProbTendsToOne
    simp only [hG]
    exact tendsto_const_nhds
  refine probTendsToOne_mono_ae (hE.inter hGa) fun ε hε => ?_
  filter_upwards [hpt ε hε] with ω hω
  intro hωEG r hαr hrd i
  have hr0 : 0 < r := (hα ε hε).trans_le hαr
  have hrR : r ≤ R := hrd.trans (hdd ω)
  by_cases hA : Adm ε ω r i
  · rw [Lemma68Final.guardedExit_of_adm hA]
    obtain ⟨N, hN, hQ⟩ := hω hωEG r hαr hrd i hA
    exact exit_le_half_of_count hcN hq0 hq1 hr0 (hrR.trans hR1) hN hQ (hRr r hr0 hrR)
  · rw [Lemma68Final.guardedExit_of_not_adm hA]
    norm_num

/-- (S10) The guard `GuardProbStmt` from the mesh events (`MeshEventsStmt`) and the shell chain (`ShellChainStmt`).
The constants: `ω₀` and `ζ` from the mesh events; `q0 = 1/9` (`qStar = 1`), `p = 2`; `cN = countConst ζ`;
`R = min (ρ/4) (min (rAmp q0 ζ) r_amp)` where `r_amp` is the radius of `constant_order_conclusion` for `cN q0`;
the cutoff `dd` is `min R (dd₀)` with `dd₀` from `window_cutoff`. -/
theorem guardProbStmt_of_chain (𝒮 : SpaceFillingSLEModel) (hMesh : MeshEventsStmt 𝒮)
    (hChain : ShellChainStmt 𝒮) : Lemma68Uniform.GuardProbStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ζ, hζ0, hζ1, ω₀, α, hω₀, hωα, hα0, hωζ, hmesh⟩ := hMesh γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨CG, hCG, CE, hCE, hPH⟩ := hmesh ρ hρ0 hρ1
  have hq0 : (0 : ℝ) < 1 / 9 := by norm_num
  have hq1 : (1 / 9 : ℝ) ≤ 1 := by norm_num
  have hrA : 0 < Lemma68Cutoff.rAmp (1 / 9) ζ := Lemma68Cutoff.rAmp_pos hq0 hζ0
  have hcN : 0 < countConst ζ := countConst_pos ζ
  obtain ⟨r_amp, hra0, hra1, hbd⟩ :=
    constant_order_conclusion (c := countConst ζ * (1 / 9)) (ζ := ζ) (mul_pos hcN hq0) hζ0
  have hR0 : 0 < min (ρ / 4) (min (Lemma68Cutoff.rAmp (1 / 9) ζ) r_amp) :=
    lt_min (by linarith) (lt_min hrA hra0)
  refine ⟨min (ρ / 4) (min (Lemma68Cutoff.rAmp (1 / 9) ζ) r_amp), ζ, 2, 1, 1 / 9, hR0,
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), hζ0, hζ1, hq0, hq1,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro s₀ hs₀ hs₁ Ω _ S hS
  set R : ℝ := min (ρ / 4) (min (Lemma68Cutoff.rAmp (1 / 9) ζ) r_amp) with hRdef
  have hRA : R ≤ Lemma68Cutoff.rAmp (1 / 9) ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hRρ : R ≤ ρ / 4 := min_le_left _ _
  have hRr' : R ≤ r_amp := (min_le_right _ _).trans (min_le_right _ _)
  have hR1 : R ≤ 1 := hRρ.trans (by linarith)
  have hRr : ∀ r : ℝ, 0 < r → r ≤ R →
      Real.exp (-(countConst ζ * (1 / 9) * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) ≤ 1 / 2 :=
    fun r hr hrle => hbd r hr (hrle.trans hRr')
  obtain ⟨hGp, hCp, hEp⟩ := hPH Ω S hS
  obtain ⟨Ew, hEwm, hEwp, hpt⟩ := hChain γ hγ0 hγ2 ω₀ α ζ ρ CG CE R (1 / 9) s₀ hω₀ hωα hα0 hωζ hCG hCE
    hζ0 hζ1 hρ0 hρ1 hq0 hq1 hR0 hRρ hRA hs₀ hs₁ Ω S hS hGp hCp hEp
  obtain ⟨dd0, hdd0m, hdd0pos, _, hdd0⟩ := window_cutoff (F := S.fieldSigma) S.P Ew hEwm hEwp
  have hE : ProbTendsToOne S.P (fun ε => meshEvent S γ ω₀ ρ CG ζ α CE ε) :=
    ((probTendsToOne_of_polyHighProb hGp).inter (probTendsToOne_of_polyHighProb hCp)).inter
      (probTendsToOne_of_polyHighProb hEp)
  have hGae : ∀ᵐ ω ∂S.P, ω ∈ goodField S Ew dd0 := by
    filter_upwards [Lemma68Guard.ae_escapes_of_valid hS,
      Lemma68Guard.ae_finiteExit_of_valid hγ0 hγ2 hS, hdd0] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hG : S.P (goodField S Ew dd0)ᶜ = 0 := ae_iff.1 hGae
  have hpt' : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε ∩ goodField S Ew dd0 →
      ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ min R (dd0 ω) → ∀ i : Lemma68Config.Config68,
        Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
          ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
            Lemma68Config.exitQ S ε ω r i ≤ (1 - (1 / 9 : ℝ) / (1 + Real.log (1 / r)) ^ 2) ^ N := by
    intro ε hε
    filter_upwards [hpt ε hε] with ω hω
    rintro ⟨hωm, h1, h2, h3⟩ r hr hrd i hadm
    have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
    exact hω hωm h1 h2 r hr (hrd.trans (min_le_left _ _))
      (h3 r hr0 (hrd.trans (min_le_right _ _))) i hadm
  refine ⟨fun ω => min R (dd0 ω), measurable_const.min hdd0m, fun ω => lt_min hR0 (hdd0pos ω),
    fun ω => min_le_left _ _, ?_⟩
  exact probTendsToOne_half_of_count (α := fun ε => 10 * ε ^ ω₀)
    (dd := fun ω => min R (dd0 ω)) (E := fun ε => meshEvent S γ ω₀ ρ CG ζ α CE ε)
    (G := goodField S Ew dd0) (R := R) (cN := countConst ζ) (q0 := 1 / 9) (ζ := ζ) hE hG
    (fun ε hε => by positivity) (fun ω => min_le_left _ _) hR1 hcN hq0 hq1 hRr
    (fun ε ω r i => Lemma68Config.FullAdm S ρ s₀ γ ε ω r i) (Lemma68Config.exitQ S) hpt'

end Lemma68Guard10

/-- **Lemma 6.8, uniform constant-order lower bound (`UniformConstantOrderLowerBoundStmt`, FirstPass/S6d.lean:95)**,
from the Draft hypotheses `GreenKernelLowerBoundStmt`, `CellSizeEstimateStmt`, `ExitTimeUpperBoundStmt` (the inputs of
q1's `draft68_uniform_events`) and the open shell chain `Lemma68Guard10.ShellChainStmt`. -/
theorem uniformConstantOrderLowerBound_of_chain (𝒮 : SpaceFillingSLEModel)
    (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hChain : Lemma68Guard10.ShellChainStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  uniformConstantOrderLowerBound_of_guard 𝒮
    (Lemma68Guard10.guardProbStmt_of_chain 𝒮 (Lemma68Guard10.meshEventsStmt_of_draft 𝒮 hG hC hE) hChain)

end MatedCRT
