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
import MatedCRT.FirstPass.S4S6c.ShellConstOrder68
import MatedCRT.FirstPass.S4S6c.HoneCellGood68
import MatedCRT.FirstPass.S4S6c.HoneModelInputs68

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

/-- **The mesh event with the cell-size component at the mesh radius `ρmesh = (1 + ρ)/2` (q2, fp-S4S6c-meshEventR;
chat 252 §1).** The Green and exit components stay at the radius `ρ`; only the cell-size component is at `(1 + ρ)/2`
(`rhoCell68 ρ`). Then `hmesh_local_of_cellSize` (HoneSetup239_68.lean:197) bounds the cells on the ball `B(0, (1+ρ)/2)`,
which contains the exit cell of the walk (`hmeshExit_of_cellSize`, MeshExitPw68.lean:60). `meshEvent` is kept. -/
def meshEventR {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (γ ω₀ ρ CG ζ α CE : ℝ) (ε : ℝ) : Set Ω :=
  greenLowEvent68 S ω₀ ρ CG ε ∩ cellSizeEvent68 S γ ζ ((1 + ρ) / 2) ε ∩ exitTimeEvent68 S α ρ CE ε

/-- The cell-size component of `meshEventR` (q2, fp-S4S6c-meshEventR). It is the hypothesis `hω` of
`hmeshExit_of_cellSize` (MeshExitPw68.lean:60) and of `hCellGood_fixedOmega` (HoneCellGoodSelPw68.lean:53), with
`rhoCell68 ρ = (1 + ρ)/2` (definitional). -/
lemma meshEventR_cell {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {γ ω₀ ρ CG ζ α CE ε : ℝ} {ω : Ω}
    (h : ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε) : ω ∈ cellSizeEvent68 S γ ζ ((1 + ρ) / 2) ε :=
  h.1.2

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
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ 1 ∧ ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
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
            ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
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

/-- **Probability bound of `meshEventR` (q2, fp-S4S6c-meshEventR).** As for `meshEvent`: the three events have
polynomially high probability, the cell-size one at `(1 + ρ)/2`, so the mesh event has `ProbTendsToOne` as `ε ↓ 0`. -/
lemma probTendsToOne_meshEventR {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {γ ω₀ ρ CG ζ α CE : ℝ}
    (hG : HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG))
    (hC : HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)))
    (hE : HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE)) :
    ProbTendsToOne S.P (fun ε => meshEventR S γ ω₀ ρ CG ζ α CE ε) :=
  ((probTendsToOne_of_polyHighProb hG).inter (probTendsToOne_of_polyHighProb hC)).inter
    (probTendsToOne_of_polyHighProb hE)

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
  -- the admissible `q0` comes from the chain, after the constants (CHATGPT-234 Q1); no fixed `q0 = 1/9`
  obtain ⟨q0, hq0, hq1, hchain⟩ :=
    hChain γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1
  have hrA : 0 < Lemma68Cutoff.rAmp q0 ζ := Lemma68Cutoff.rAmp_pos hq0 hζ0
  have hcN : 0 < countConst ζ := countConst_pos ζ
  obtain ⟨r_amp, hra0, hra1, hbd⟩ :=
    constant_order_conclusion (c := countConst ζ * q0) (ζ := ζ) (mul_pos hcN hq0) hζ0
  have hR0 : 0 < min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) r_amp) :=
    lt_min (by linarith) (lt_min hrA hra0)
  refine ⟨min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) r_amp), ζ, 2, 9 * q0, q0, hR0,
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), hζ0, hζ1, hq0, hq1,
    by ring, by linarith, by linarith, by norm_num,
    Lemma68Config.sparsityS1 γ, Lemma68Config.sparsityS1_pos γ, Lemma68Config.sparsityS1_lt_one γ, ?_⟩
  intro s₀ hs₀ hs₁ Ω _ S hS
  set R : ℝ := min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) r_amp) with hRdef
  have hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hRρ : R ≤ ρ / 4 := min_le_left _ _
  have hRr' : R ≤ r_amp := (min_le_right _ _).trans (min_le_right _ _)
  have hR1 : R ≤ 1 := hRρ.trans (by linarith)
  have hRr : ∀ r : ℝ, 0 < r → r ≤ R →
      Real.exp (-(countConst ζ * q0 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) ≤ 1 / 2 :=
    fun r hr hrle => hbd r hr (hrle.trans hRr')
  obtain ⟨hGp, hCp, hEp⟩ := hPH Ω S hS
  obtain ⟨Ew, hEwm, hEwp, hpt⟩ := hchain R hR0 hRρ hRA s₀ hs₀ hs₁ Ω S hS hGp hCp hEp
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
        Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
          ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
            Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
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
    (G := goodField S Ew dd0) (R := R) (cN := countConst ζ) (q0 := q0) (ζ := ζ) hE hG
    (fun ε hε => by positivity) (fun ω => min_le_left _ _) hR1 hcN hq0 hq1 hRr
    (fun ε ω r i => Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i) (Lemma68Config.exitQ S) hpt'

/-! ### The Eps forms: mesh threshold, exponent antecedents, radius cutoff (q2, fp-S4S6c-eps-chain)

The old statements `MeshEventsStmt`, `ShellChainStmt` and the guard are kept unchanged (their importers build).
The Eps forms add: `ε ≤ shellEps0 γ α ω₀` in the ε-clause; `2 ω₀ β⁻ < α` and `2 ω₀ < 2/(2+γ)² - ζ` next to the `ω₀`
hypotheses (`β⁻ = chosenBetaMinus γ`); and the deterministic radius cutoff `(dyadicD r)^{shortExp ζ} < rhoCell68 ρ - ρ`
for `0 < r ≤ R`, next to `R ≤ rAmp q₀ ζ`. The consumer chooses `ω₀ ≤ α/(4β⁻)`, `ω₀ ≤ q/4` and `R ≤ Rc`. -/

/-- **The mesh threshold `ε₀` of the Eps chain.** `shellEps0 γ α ω₀ = min (e⁻²/2) (((100 c₀)^{β⁻}/4)^{1/(α - 2ω₀β⁻)})` with
`c₀ = shellC068 = e⁻²/32` and `β⁻ = chosenBetaMinus γ`. The first entry is the leaf threshold `ε ≤ 16 K.c0` (q1 G2, `16 c₀ = e⁻²/2`);
the second is the threshold of `hsc_of_volC_threshold` (z10). -/
noncomputable def shellEps0 (γ α ω₀ : ℝ) : ℝ :=
  min (Real.exp (-2) / 2)
    (((100 * Lemma68ConstOrder.shellC068) ^ chosenBetaMinus γ / 4) ^ (1 / (α - 2 * ω₀ * chosenBetaMinus γ)))

/-- `shellEps0` is positive (the base of the second entry is positive, whatever the exponent). -/
lemma shellEps0_pos (γ α ω₀ : ℝ) : 0 < shellEps0 γ α ω₀ := by
  unfold shellEps0 Lemma68ConstOrder.shellC068
  apply lt_min (by positivity)
  apply Real.rpow_pos_of_pos
  apply div_pos (Real.rpow_pos_of_pos (by positivity) _) (by norm_num)

/-- **The mesh threshold with the cell entry (q2, fp-S4S6c-core-fixes, z5 GAP 1).** With `A = 2/(2+γ)² - ζ` and
`c₀ = shellC068`, `shellEps0Z γ α ω₀ ζ = min (shellEps0 γ α ω₀) (c₀^{1/(A - 2ω₀)})`. The second entry gives the leaf
binder `ε^{A - 2ω₀} ≤ c₀` (B1Assembly68.lean:86 at `r = 10 ε^{ω₀}`), see `shellEps0Z_pow_le`. The old `shellEps0` is kept
unchanged (ShellCorePw68 uses it). -/
noncomputable def shellEps0Z (γ α ω₀ ζ : ℝ) : ℝ :=
  min (shellEps0 γ α ω₀) (Lemma68ConstOrder.shellC068 ^ (1 / (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀)))

/-- `shellEps0Z` is positive. -/
lemma shellEps0Z_pos (γ α ω₀ ζ : ℝ) : 0 < shellEps0Z γ α ω₀ ζ := by
  unfold shellEps0Z
  apply lt_min (shellEps0_pos γ α ω₀)
  apply Real.rpow_pos_of_pos
  unfold Lemma68ConstOrder.shellC068
  positivity

/-- `shellEps0Z` is at most `shellEps0`, so every `ε ≤ shellEps0Z` also satisfies `ε ≤ shellEps0`. -/
lemma shellEps0Z_le (γ α ω₀ ζ : ℝ) : shellEps0Z γ α ω₀ ζ ≤ shellEps0 γ α ω₀ :=
  min_le_left _ _

/-- **The cell entry of the Eps threshold.** If `2ω₀ < A` and `0 < ε ≤ shellEps0Z γ α ω₀ ζ`, then
`ε^{A - 2ω₀} ≤ shellC068` (the leaf binder `hεcell` of B1Assembly68.lean:86 at `r = 10 ε^{ω₀}`). -/
lemma shellEps0Z_pow_le {γ α ω₀ ζ ε : ℝ} (hε : 0 < ε) (hd : 0 < 2 / (2 + γ) ^ 2 - ζ - 2 * ω₀)
    (hle : ε ≤ shellEps0Z γ α ω₀ ζ) :
    ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) ≤ Lemma68ConstOrder.shellC068 := by
  have hc : 0 < Lemma68ConstOrder.shellC068 := by
    unfold Lemma68ConstOrder.shellC068
    positivity
  have h1 : ε ≤ Lemma68ConstOrder.shellC068 ^ (1 / (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀)) :=
    le_trans hle (min_le_right _ _)
  calc ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀)
      ≤ (Lemma68ConstOrder.shellC068 ^ (1 / (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀)))
          ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) := Real.rpow_le_rpow hε.le h1 hd.le
    _ = Lemma68ConstOrder.shellC068 := by
      rw [← Real.rpow_mul hc.le, one_div_mul_cancel hd.ne', Real.rpow_one]

/-! ### The Eps chain at the Green constant `CG` (q2, fp-S4S6c-cg-param, lead item 3: parameterize, do not restrict CG)

`c₀(CG) = shellC0 CG = exp(-2CG)/32` (`Lemma68ConstOrder.shellC0`) replaces `shellC068` in the Eps chain, so that the leaf
constant `K.C := CG` (`shellKCG`) satisfies `hc0C : c₀ ≤ exp(-2 K.C)/16`. The leaf threshold `16 c₀(CG) = exp(-2CG)/2`
replaces `e⁻²/2`. The CG-free `shellEps0`, `shellEps0Z` are kept unchanged (ShellCorePw68 and B1Assembly68 use them). -/

/-- **The mesh threshold at the Green constant `CG`.** `shellEps0CG γ α ω₀ CG = min (exp(-2CG)/2)
(((100 c₀(CG))^{β⁻}/4)^{1/(α - 2ω₀β⁻)})`, `β⁻ = chosenBetaMinus γ`. -/
noncomputable def shellEps0CG (γ α ω₀ CG : ℝ) : ℝ :=
  min (Real.exp (-(2 * CG)) / 2)
    (((100 * Lemma68ConstOrder.shellC0 CG) ^ chosenBetaMinus γ / 4) ^ (1 / (α - 2 * ω₀ * chosenBetaMinus γ)))

/-- `shellEps0CG` is positive (for every `CG`). -/
lemma shellEps0CG_pos (γ α ω₀ CG : ℝ) : 0 < shellEps0CG γ α ω₀ CG := by
  unfold shellEps0CG Lemma68ConstOrder.shellC0
  apply lt_min (by positivity)
  apply Real.rpow_pos_of_pos
  apply div_pos (Real.rpow_pos_of_pos (by positivity) _) (by norm_num)

/-- **The mesh threshold with the cell entry at `CG`.** `shellEps0ZCG γ α ω₀ ζ CG = min (shellEps0CG γ α ω₀ CG)
(c₀(CG)^{1/(A - 2ω₀)})`, `A = 2/(2+γ)² - ζ`. -/
noncomputable def shellEps0ZCG (γ α ω₀ ζ CG : ℝ) : ℝ :=
  min (shellEps0CG γ α ω₀ CG) ((Lemma68ConstOrder.shellC0 CG) ^ (1 / (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀)))

/-- `shellEps0ZCG` is positive. -/
lemma shellEps0ZCG_pos (γ α ω₀ ζ CG : ℝ) : 0 < shellEps0ZCG γ α ω₀ ζ CG := by
  unfold shellEps0ZCG
  apply lt_min (shellEps0CG_pos γ α ω₀ CG)
  apply Real.rpow_pos_of_pos
  unfold Lemma68ConstOrder.shellC0
  positivity

/-- `shellEps0ZCG` is at most `shellEps0CG`. -/
lemma shellEps0ZCG_le (γ α ω₀ ζ CG : ℝ) : shellEps0ZCG γ α ω₀ ζ CG ≤ shellEps0CG γ α ω₀ CG :=
  min_le_left _ _

/-- **The cell entry of the CG Eps threshold.** If `2ω₀ < A` and `0 < ε ≤ shellEps0ZCG γ α ω₀ ζ CG`, then
`ε^{A - 2ω₀} ≤ c₀(CG)` (the leaf binder `hεcell` at `r = 10 ε^{ω₀}`). -/
lemma shellEps0ZCG_pow_le {γ α ω₀ ζ CG ε : ℝ} (hε : 0 < ε) (hd : 0 < 2 / (2 + γ) ^ 2 - ζ - 2 * ω₀)
    (hle : ε ≤ shellEps0ZCG γ α ω₀ ζ CG) :
    ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) ≤ Lemma68ConstOrder.shellC0 CG := by
  have hc : 0 < Lemma68ConstOrder.shellC0 CG := by
    unfold Lemma68ConstOrder.shellC0
    positivity
  have h1 : ε ≤ (Lemma68ConstOrder.shellC0 CG) ^ (1 / (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀)) :=
    le_trans hle (min_le_right _ _)
  calc ε ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀)
      ≤ ((Lemma68ConstOrder.shellC0 CG) ^ (1 / (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀)))
          ^ (2 / (2 + γ) ^ 2 - ζ - 2 * ω₀) := Real.rpow_le_rpow hε.le h1 hd.le
    _ = Lemma68ConstOrder.shellC0 CG := by
      rw [← Real.rpow_mul hc.le, one_div_mul_cancel hd.ne', Real.rpow_one]

/-- **The sparsity constant at the Green constant `CG`.** `shellS1CG γ CG = c₀(CG)^{βm}/44` with
`βm = (2+γ)²/2 + 1` (the `s1` of `shellKCG`, the coefficient of `FullAdmAt`). -/
noncomputable def shellS1CG (γ CG : ℝ) : ℝ :=
  (Lemma68ConstOrder.shellC0 CG) ^ ((2 + γ) ^ 2 / 2 + 1) / 44

/-- `shellS1CG` is positive. -/
lemma shellS1CG_pos (γ CG : ℝ) : 0 < shellS1CG γ CG := by
  unfold shellS1CG Lemma68ConstOrder.shellC0
  positivity

/-- `shellS1CG` is below one for `CG > 0` (`c₀(CG) ≤ 1`). -/
lemma shellS1CG_lt_one (γ CG : ℝ) (hCG : 0 < CG) : shellS1CG γ CG < 1 := by
  have h0 : 0 < Lemma68ConstOrder.shellC0 CG := (Lemma68ConstOrder.shellC0_bounds CG hCG).1
  have h1 : Lemma68ConstOrder.shellC0 CG ≤ 1 := by
    have := (Lemma68ConstOrder.shellC0_bounds CG hCG).2
    linarith
  have h2 : (Lemma68ConstOrder.shellC0 CG) ^ ((2 + γ) ^ 2 / 2 + 1) ≤ 1 :=
    Real.rpow_le_one h0.le h1 (by positivity)
  unfold shellS1CG
  linarith

/-- **The deterministic radius cutoff of the Eps chain** (CHATGPT-237 l.335-348). For `0 < ρ < 1` and `ζ > 0` there is
`Rc > 0` such that every `0 < R ≤ Rc` satisfies `∀ r, 0 < r → r ≤ R → (dyadicD r)^{shortExp ζ} < rhoCell68 ρ - ρ`.
Proof: `rhoCell68 ρ - ρ = (1-ρ)/2 =: g`, `Rc := g/2`; then `dyadicD r < 2 r² ≤ 2 Rc² < g²` (`dyadicD_lt_two_mul_sq`),
and `(dyadicD r)^{shortExp ζ} ≤ (dyadicD r)^{1/2} = √(dyadicD r) < g` since `shortExp ζ ≥ 1/2` and `dyadicD r ≤ 1`. -/
lemma exists_radius_cutoff_gap {ρ ζ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ : 0 < ζ) :
    ∃ Rc : ℝ, 0 < Rc ∧ ∀ R : ℝ, 0 < R → R ≤ Rc → ∀ r : ℝ, 0 < r → r ≤ R →
      (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
  have hg : Lemma68HoneCellGood.rhoCell68 ρ - ρ = (1 - ρ) / 2 := by
    unfold Lemma68HoneCellGood.rhoCell68; ring
  have hgpos : 0 < (1 - ρ) / 2 := by linarith
  refine ⟨(1 - ρ) / 4, by linarith, fun R hR0 hRc r hr0 hrR => ?_⟩
  have hr1 : r ≤ 1 := by linarith
  have hd : dyadicD r < 2 * r ^ 2 := dyadicD_lt_two_mul_sq hr0 hr1
  have hr2 : r ^ 2 ≤ ((1 - ρ) / 4) ^ 2 := pow_le_pow_left₀ hr0.le (hrR.trans hRc) 2
  have hx0 : 0 < dyadicD r := dyadicD_pos r
  have hx1 : dyadicD r ≤ 1 := dyadicD_le_one r
  have hxg : dyadicD r < ((1 - ρ) / 2) ^ 2 := by nlinarith
  have ha : (1 : ℝ) / 2 ≤ shortExp ζ := by unfold shortExp; linarith
  rw [hg]
  calc (dyadicD r) ^ shortExp ζ ≤ (dyadicD r) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hx0 hx1 ha
    _ = Real.sqrt (dyadicD r) := (Real.sqrt_eq_rpow _).symm
    _ < (1 - ρ) / 2 := (Real.sqrt_lt' hgpos).2 hxg

/-- **`MeshEventsStmt` with the exponent antecedents (q2, fp-S4S6c-eps-chain).** The same mesh events, and the chosen `ω₀`
also satisfies `2 ω₀ β⁻ < α` and `2 ω₀ < 2/(2+γ)² - ζ`. -/
def MeshEventsEpsStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 / 2 ∧ ∃ ω₀ α : ℝ, 0 < ω₀ ∧ ω₀ < α ∧ 0 < α ∧
    ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧ 2 * ω₀ * chosenBetaMinus γ < α ∧ 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ CG : ℝ, 0 < CG ∧ ∃ CE : ℝ, 0 < CE ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) ∧
        HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) ∧
        HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE)

/-- **`MeshEventsEpsStmt` from the Draft hypotheses (q2, fp-S4S6c-eps-chain).** As `meshEventsStmt_of_draft`, with
`ω₀ = min ωG (min (α/(4β⁻)) (q/4))` where `q = 1/(2+γ)² = 2/(2+γ)² - ζ`; then `2ω₀β⁻ ≤ α/2 < α` and `2ω₀ ≤ q/2 < q`. -/
theorem meshEventsEpsStmt_of_draft (𝒮 : SpaceFillingSLEModel) (hG : GreenKernelLowerBoundStmt 𝒮)
    (hC : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮) : MeshEventsEpsStmt 𝒮 := by
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
  have hβ : 0 < chosenBetaMinus γ := by unfold chosenBetaMinus; positivity
  have hβ1 : 1 ≤ chosenBetaMinus γ := by
    unfold chosenBetaMinus; have := sq_nonneg (2 + γ); linarith
  obtain ⟨ω₀, hω₀def⟩ : ∃ ω₀ : ℝ, ω₀ = min ωG (min (α / (4 * chosenBetaMinus γ)) (q / 4)) := ⟨_, rfl⟩
  have hω₀1 : ω₀ ≤ ωG := by rw [hω₀def]; exact min_le_left _ _
  have hω₀2 : ω₀ ≤ α / (4 * chosenBetaMinus γ) := by
    rw [hω₀def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hω₀3 : ω₀ ≤ q / 4 := by rw [hω₀def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hω₀pos : 0 < ω₀ := by
    rw [hω₀def]; exact lt_min hωG (lt_min (div_pos hα (by linarith)) (by linarith))
  have hexp1 : 2 * ω₀ * chosenBetaMinus γ < α := by
    have h4 : ω₀ * (4 * chosenBetaMinus γ) ≤ α := by
      rwa [le_div_iff₀ (by linarith)] at hω₀2
    nlinarith
  have hωα : ω₀ < α := by nlinarith [mul_le_mul_of_nonneg_left hβ1 hω₀pos.le]
  have hωq : ω₀ < 2 / (2 + γ) ^ 2 - q := by rw [hqq]; linarith
  have hexp2 : 2 * ω₀ < 2 / (2 + γ) ^ 2 - q := by rw [hqq]; linarith
  refine ⟨q, hq0, hq1, ω₀, α, hω₀pos, hωα, hα, hωq, hexp1, hexp2, ?_⟩
  intro ρ hρ0 hρ1
  obtain ⟨CG, hCG, hGS⟩ := hGr ρ hρ0 hρ1
  obtain ⟨CE, hCE, hES⟩ := hEr ρ hρ0 hρ1
  refine ⟨CG, hCG, CE, hCE, fun Ω _ S hS => ⟨?_, ?_, ?_⟩⟩
  · exact hGS ω₀ hω₀pos hω₀1 Ω S hS
  · exact hC γ hγ hγ2 q ρ hq0 (by linarith) hρ0 hρ1 Ω S hS
  · exact hES Ω S hS

/-- **`ShellChainStmt` with the Eps antecedents (q2, fp-S4S6c-eps-chain).** The body of `ShellChainStmt`, plus `2 ω₀ β⁻ < α`
and `2 ω₀ < 2/(2+γ)² - ζ` next to the `ω₀` hypotheses; `ε ≤ shellEps0 γ α ω₀` in the ε-clause; and the radius cutoff
`∀ r, 0 < r → r ≤ R → (dyadicD r)^{shortExp ζ} < rhoCell68 ρ - ρ` next to `R ≤ rAmp q0 ζ`. -/
def ShellChainEpsStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ 1 ∧ ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      ∃ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) ∧
        HarmonicBalls.PolyHighProb S.P Ew ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0Z γ α ω₀ ζ → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
          Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
          (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
          ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
            ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
              ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
                Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **Old implies Eps (q2, fp-S4S6c-eps-chain).** `ShellChainStmt` specialises to `ShellChainEpsStmt`: the Eps antecedents are
ignored and the ε-clause is used for `ε ≤ shellEps0`. -/
theorem shellChainEpsStmt_of_shellChainStmt {𝒮 : SpaceFillingSLEModel} (h : ShellChainStmt 𝒮) :
    ShellChainEpsStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ _ _ hCG hCE hζ0 hζ1 hρ0 hρ1
  obtain ⟨q0, hq0, hq1, hR⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1
  refine ⟨q0, hq0, hq1, fun R hR0 hRρ hRA _ s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp => ?_⟩
  obtain ⟨Ew, hEwm, hEwp, hpt⟩ := hR R hR0 hRρ hRA s₀ hs₀ hs₁ Ω S hS hGp hCp hEp
  exact ⟨Ew, hEwm, hEwp, fun ε hε _ => hpt ε hε⟩

/-- **`ShellChainEpsStmt` at the Green constant `CG` (q2, fp-S4S6c-cg-param).** The body of `ShellChainEpsStmt` with the
threshold `shellEps0ZCG γ α ω₀ ζ CG` and the sparsity constant `shellS1CG γ CG` (both at the ball ratio `c₀(CG)`). The Green
event `greenLowEvent68 S ω₀ ρ CG` is the event of the leaf constant `K.C = CG` (`shellKCG`). -/
def ShellChainCGStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ 1 ∧ ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      ∃ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) ∧
        HarmonicBalls.PolyHighProb S.P Ew ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
          Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
          (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
          ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
            ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
              ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
                Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **`ShellChainCGStmt` with the mesh-radius cell event (q2, fp-S4S6c-meshEventR; chat 252 §1).** The body of
`ShellChainCGStmt`, with the cell-size hypothesis at the mesh radius `(1 + ρ)/2` (`rhoCell68 ρ`) and the almost sure
mesh clause on `meshEventR` (cell component at `(1 + ρ)/2`; Green and exit components at `ρ`). -/
def ShellChainCGRStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ 1 ∧ ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      ∃ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) ∧
        HarmonicBalls.PolyHighProb S.P Ew ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P, ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε →
          Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
          (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
          ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
            ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
              ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
                Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **Transfer to a small-ε family.** If `E` has `ProbTendsToOne` and `F = E` for `0 < ε ≤ e₀` (`e₀ > 0`), then `F` has
`ProbTendsToOne`: `ProbTendsToOne` is a limit along `𝓝[>] 0`, which only sees `ε ∈ (0, e₀)`. -/
lemma probTendsToOne_congr_small {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω} {e0 : ℝ}
    (he0 : 0 < e0) (h : ProbTendsToOne P E) (hEF : ∀ ε : ℝ, 0 < ε → ε ≤ e0 → F ε = E ε) :
    ProbTendsToOne P F := by
  unfold ProbTendsToOne at h ⊢
  refine Tendsto.congr' ?_ h
  filter_upwards [Ioo_mem_nhdsGT he0] with ε hε
  rw [hEF ε hε.1 hε.2.le]

/-- **The guard `GuardProbStmt` from the Eps mesh events and the Eps shell chain (q2, fp-S4S6c-eps-chain).** As
`guardProbStmt_of_chain`, with `ω₀, ζ` from `MeshEventsEpsStmt`, `R = min (ρ/4) (min (rAmp q₀ ζ) (min r_amp Rc))` (`Rc` the radius
cutoff of `exists_radius_cutoff_gap`), and the ε-events `E ε = if ε ≤ shellEps0 then meshEvent ε else ∅`: for `ε > shellEps0` the
event is empty and the inclusion is vacuous; `ProbTendsToOne` only sees `ε ≤ shellEps0`. -/
theorem guardProbStmtEps_of_chainEps (𝒮 : SpaceFillingSLEModel) (hMesh : MeshEventsEpsStmt 𝒮)
    (hChain : ShellChainEpsStmt 𝒮) : Lemma68Uniform.GuardProbStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ζ, hζ0, hζ1, ω₀, α, hω₀, hωα, hα0, hωζ, hexp1, hexp2, hmesh⟩ := hMesh γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨CG, hCG, CE, hCE, hPH⟩ := hmesh ρ hρ0 hρ1
  obtain ⟨q0, hq0, hq1, hchain⟩ :=
    hChain γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1
  have hrA : 0 < Lemma68Cutoff.rAmp q0 ζ := Lemma68Cutoff.rAmp_pos hq0 hζ0
  have hcN : 0 < countConst ζ := countConst_pos ζ
  obtain ⟨r_amp, hra0, hra1, hbd⟩ :=
    constant_order_conclusion (c := countConst ζ * q0) (ζ := ζ) (mul_pos hcN hq0) hζ0
  obtain ⟨Rc, hRc0, hRc⟩ := exists_radius_cutoff_gap hρ0 hρ1 hζ0
  have hR0 : 0 < min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)) :=
    lt_min (by linarith) (lt_min hrA (lt_min hra0 hRc0))
  refine ⟨min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)), ζ, 2, 9 * q0, q0, hR0,
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), hζ0, hζ1, hq0, hq1,
    by ring, by linarith, by linarith, by norm_num,
    Lemma68Config.sparsityS1 γ, Lemma68Config.sparsityS1_pos γ, Lemma68Config.sparsityS1_lt_one γ, ?_⟩
  intro s₀ hs₀ hs₁ Ω _ S hS
  set R : ℝ := min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)) with hRdef
  have hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hRρ : R ≤ ρ / 4 := min_le_left _ _
  have hRr' : R ≤ r_amp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRRc : R ≤ Rc := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hR1 : R ≤ 1 := hRρ.trans (by linarith)
  have hRr : ∀ r : ℝ, 0 < r → r ≤ R →
      Real.exp (-(countConst ζ * q0 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) ≤ 1 / 2 :=
    fun r hr hrle => hbd r hr (hrle.trans hRr')
  obtain ⟨hGp, hCp, hEp⟩ := hPH Ω S hS
  obtain ⟨Ew, hEwm, hEwp, hpt⟩ :=
    hchain R hR0 hRρ hRA (hRc R hR0 hRRc) s₀ hs₀ hs₁ Ω S hS hGp hCp hEp
  obtain ⟨dd0, hdd0m, hdd0pos, _, hdd0⟩ := window_cutoff (F := S.fieldSigma) S.P Ew hEwm hEwp
  have hE : ProbTendsToOne S.P (fun ε => meshEvent S γ ω₀ ρ CG ζ α CE ε) :=
    ((probTendsToOne_of_polyHighProb hGp).inter (probTendsToOne_of_polyHighProb hCp)).inter
      (probTendsToOne_of_polyHighProb hEp)
  have hGae : ∀ᵐ ω ∂S.P, ω ∈ goodField S Ew dd0 := by
    filter_upwards [Lemma68Guard.ae_escapes_of_valid hS,
      Lemma68Guard.ae_finiteExit_of_valid hγ0 hγ2 hS, hdd0] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hG : S.P (goodField S Ew dd0)ᶜ = 0 := ae_iff.1 hGae
  have he0 : 0 < shellEps0Z γ α ω₀ ζ := shellEps0Z_pos γ α ω₀ ζ
  set e0 : ℝ := shellEps0Z γ α ω₀ ζ with he0def
  set E : ℝ → Set Ω := fun ε => if ε ≤ e0 then meshEvent S γ ω₀ ρ CG ζ α CE ε else ∅ with hEdef
  have hEp' : ProbTendsToOne S.P E :=
    probTendsToOne_congr_small he0 hE (fun ε _ hle => by simp [hEdef, hle])
  have hpt' : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε ∩ goodField S Ew dd0 →
      ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ min R (dd0 ω) → ∀ i : Lemma68Config.Config68,
        Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
          ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
            Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
    intro ε hε
    by_cases hle : ε ≤ e0
    · filter_upwards [hpt ε hε hle] with ω hω
      rintro ⟨hωm, h1, h2, h3⟩ r hr hrd i hadm
      have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
      have hωm' : ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε := by simpa [hEdef, hle] using hωm
      exact hω hωm' h1 h2 r hr (hrd.trans (min_le_left _ _))
        (h3 r hr0 (hrd.trans (min_le_right _ _))) i hadm
    · refine Filter.Eventually.of_forall fun ω hω => ?_
      exact absurd hω.1 (by simp [hEdef, hle])
  refine ⟨fun ω => min R (dd0 ω), measurable_const.min hdd0m, fun ω => lt_min hR0 (hdd0pos ω),
    fun ω => min_le_left _ _, ?_⟩
  exact probTendsToOne_half_of_count (α := fun ε => 10 * ε ^ ω₀)
    (dd := fun ω => min R (dd0 ω)) (E := E)
    (G := goodField S Ew dd0) (R := R) (cN := countConst ζ) (q0 := q0) (ζ := ζ) hEp' hG
    (fun ε hε => by positivity) (fun ω => min_le_left _ _) hR1 hcN hq0 hq1 hRr
    (fun ε ω r i => Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i)
    (Lemma68Config.exitQ S) hpt'

/-- **`GuardProbStmt` from the CG Eps chain (q2, fp-S4S6c-cg-param).** As `guardProbStmtEps_of_chainEps`, with the chain
`ShellChainCGStmt` at `c₀(CG)`; the witness `s₁ = shellS1CG γ CG` is chosen after `CG` (inside `∀ ρ`, as in the Eps copy). -/
theorem guardProbStmtCG_of_chainCG (𝒮 : SpaceFillingSLEModel) (hMesh : MeshEventsEpsStmt 𝒮)
    (hChain : ShellChainCGStmt 𝒮) : Lemma68Uniform.GuardProbStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ζ, hζ0, hζ1, ω₀, α, hω₀, hωα, hα0, hωζ, hexp1, hexp2, hmesh⟩ := hMesh γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨CG, hCG, CE, hCE, hPH⟩ := hmesh ρ hρ0 hρ1
  obtain ⟨q0, hq0, hq1, hchain⟩ :=
    hChain γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1
  have hrA : 0 < Lemma68Cutoff.rAmp q0 ζ := Lemma68Cutoff.rAmp_pos hq0 hζ0
  have hcN : 0 < countConst ζ := countConst_pos ζ
  obtain ⟨r_amp, hra0, hra1, hbd⟩ :=
    constant_order_conclusion (c := countConst ζ * q0) (ζ := ζ) (mul_pos hcN hq0) hζ0
  obtain ⟨Rc, hRc0, hRc⟩ := exists_radius_cutoff_gap hρ0 hρ1 hζ0
  have hR0 : 0 < min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)) :=
    lt_min (by linarith) (lt_min hrA (lt_min hra0 hRc0))
  refine ⟨min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)), ζ, 2, 9 * q0, q0, hR0,
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), hζ0, hζ1, hq0, hq1,
    by ring, by linarith, by linarith, by norm_num,
    shellS1CG γ CG, shellS1CG_pos γ CG, shellS1CG_lt_one γ CG hCG, ?_⟩
  intro s₀ hs₀ hs₁ Ω _ S hS
  set R : ℝ := min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)) with hRdef
  have hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hRρ : R ≤ ρ / 4 := min_le_left _ _
  have hRr' : R ≤ r_amp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRRc : R ≤ Rc := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hR1 : R ≤ 1 := hRρ.trans (by linarith)
  have hRr : ∀ r : ℝ, 0 < r → r ≤ R →
      Real.exp (-(countConst ζ * q0 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) ≤ 1 / 2 :=
    fun r hr hrle => hbd r hr (hrle.trans hRr')
  obtain ⟨hGp, hCp, hEp⟩ := hPH Ω S hS
  obtain ⟨Ew, hEwm, hEwp, hpt⟩ :=
    hchain R hR0 hRρ hRA (hRc R hR0 hRRc) s₀ hs₀ hs₁ Ω S hS hGp hCp hEp
  obtain ⟨dd0, hdd0m, hdd0pos, _, hdd0⟩ := window_cutoff (F := S.fieldSigma) S.P Ew hEwm hEwp
  have hE : ProbTendsToOne S.P (fun ε => meshEvent S γ ω₀ ρ CG ζ α CE ε) :=
    ((probTendsToOne_of_polyHighProb hGp).inter (probTendsToOne_of_polyHighProb hCp)).inter
      (probTendsToOne_of_polyHighProb hEp)
  have hGae : ∀ᵐ ω ∂S.P, ω ∈ goodField S Ew dd0 := by
    filter_upwards [Lemma68Guard.ae_escapes_of_valid hS,
      Lemma68Guard.ae_finiteExit_of_valid hγ0 hγ2 hS, hdd0] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hG : S.P (goodField S Ew dd0)ᶜ = 0 := ae_iff.1 hGae
  have he0 : 0 < shellEps0ZCG γ α ω₀ ζ CG := shellEps0ZCG_pos γ α ω₀ ζ CG
  set e0 : ℝ := shellEps0ZCG γ α ω₀ ζ CG with he0def
  set E : ℝ → Set Ω := fun ε => if ε ≤ e0 then meshEvent S γ ω₀ ρ CG ζ α CE ε else ∅ with hEdef
  have hEp' : ProbTendsToOne S.P E :=
    probTendsToOne_congr_small he0 hE (fun ε _ hle => by simp [hEdef, hle])
  have hpt' : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε ∩ goodField S Ew dd0 →
      ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ min R (dd0 ω) → ∀ i : Lemma68Config.Config68,
        Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
          ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
            Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
    intro ε hε
    by_cases hle : ε ≤ e0
    · filter_upwards [hpt ε hε hle] with ω hω
      rintro ⟨hωm, h1, h2, h3⟩ r hr hrd i hadm
      have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
      have hωm' : ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε := by simpa [hEdef, hle] using hωm
      exact hω hωm' h1 h2 r hr (hrd.trans (min_le_left _ _))
        (h3 r hr0 (hrd.trans (min_le_right _ _))) i hadm
    · refine Filter.Eventually.of_forall fun ω hω => ?_
      exact absurd hω.1 (by simp [hEdef, hle])
  refine ⟨fun ω => min R (dd0 ω), measurable_const.min hdd0m, fun ω => lt_min hR0 (hdd0pos ω),
    fun ω => min_le_left _ _, ?_⟩
  exact probTendsToOne_half_of_count (α := fun ε => 10 * ε ^ ω₀)
    (dd := fun ω => min R (dd0 ω)) (E := E)
    (G := goodField S Ew dd0) (R := R) (cN := countConst ζ) (q0 := q0) (ζ := ζ) hEp' hG
    (fun ε hε => by positivity) (fun ω => min_le_left _ _) hR1 hcN hq0 hq1 hRr
    (fun ε ω r i => Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i)
    (Lemma68Config.exitQ S) hpt'

/-- **`GuardProbStmt` from the CG mesh-radius chain (q2, fp-S4S6c-meshEventR).** As `guardProbStmtCG_of_chainCG`, with the
chain `ShellChainCGRStmt`. The cell-size factor of `meshEventR` at `(1 + ρ)/2` is the cell-size factor of `MeshEventsEpsStmt`
instantiated once more at the mesh radius `(1 + ρ)/2` (same `ζ`, `ω₀`, `α`; its Green and exit factors are not used). -/
theorem guardProbStmtCGR_of_chainCGR (𝒮 : SpaceFillingSLEModel) (hMesh : MeshEventsEpsStmt 𝒮)
    (hChain : ShellChainCGRStmt 𝒮) : Lemma68Uniform.GuardProbStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ζ, hζ0, hζ1, ω₀, α, hω₀, hωα, hα0, hωζ, hexp1, hexp2, hmesh⟩ := hMesh γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨CG, hCG, CE, hCE, hPH⟩ := hmesh ρ hρ0 hρ1
  obtain ⟨_, _, _, _, hPHm⟩ := hmesh ((1 + ρ) / 2) (by linarith) (by linarith)
  obtain ⟨q0, hq0, hq1, hchain⟩ :=
    hChain γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1
  have hrA : 0 < Lemma68Cutoff.rAmp q0 ζ := Lemma68Cutoff.rAmp_pos hq0 hζ0
  have hcN : 0 < countConst ζ := countConst_pos ζ
  obtain ⟨r_amp, hra0, hra1, hbd⟩ :=
    constant_order_conclusion (c := countConst ζ * q0) (ζ := ζ) (mul_pos hcN hq0) hζ0
  obtain ⟨Rc, hRc0, hRc⟩ := exists_radius_cutoff_gap hρ0 hρ1 hζ0
  have hR0 : 0 < min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)) :=
    lt_min (by linarith) (lt_min hrA (lt_min hra0 hRc0))
  refine ⟨min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)), ζ, 2, 9 * q0, q0, hR0,
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), hζ0, hζ1, hq0, hq1,
    by ring, by linarith, by linarith, by norm_num,
    shellS1CG γ CG, shellS1CG_pos γ CG, shellS1CG_lt_one γ CG hCG, ?_⟩
  intro s₀ hs₀ hs₁ Ω _ S hS
  set R : ℝ := min (ρ / 4) (min (Lemma68Cutoff.rAmp q0 ζ) (min r_amp Rc)) with hRdef
  have hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hRρ : R ≤ ρ / 4 := min_le_left _ _
  have hRr' : R ≤ r_amp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRRc : R ≤ Rc := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hR1 : R ≤ 1 := hRρ.trans (by linarith)
  have hRr : ∀ r : ℝ, 0 < r → r ≤ R →
      Real.exp (-(countConst ζ * q0 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) ≤ 1 / 2 :=
    fun r hr hrle => hbd r hr (hrle.trans hRr')
  obtain ⟨hGp, _, hEp⟩ := hPH Ω S hS
  have hCpm : HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) :=
    (hPHm Ω S hS).2.1
  obtain ⟨Ew, hEwm, hEwp, hpt⟩ :=
    hchain R hR0 hRρ hRA (hRc R hR0 hRRc) s₀ hs₀ hs₁ Ω S hS hGp hCpm hEp
  obtain ⟨dd0, hdd0m, hdd0pos, _, hdd0⟩ := window_cutoff (F := S.fieldSigma) S.P Ew hEwm hEwp
  have hE : ProbTendsToOne S.P (fun ε => meshEventR S γ ω₀ ρ CG ζ α CE ε) :=
    probTendsToOne_meshEventR hGp hCpm hEp
  have hGae : ∀ᵐ ω ∂S.P, ω ∈ goodField S Ew dd0 := by
    filter_upwards [Lemma68Guard.ae_escapes_of_valid hS,
      Lemma68Guard.ae_finiteExit_of_valid hγ0 hγ2 hS, hdd0] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hG : S.P (goodField S Ew dd0)ᶜ = 0 := ae_iff.1 hGae
  have he0 : 0 < shellEps0ZCG γ α ω₀ ζ CG := shellEps0ZCG_pos γ α ω₀ ζ CG
  set e0 : ℝ := shellEps0ZCG γ α ω₀ ζ CG with he0def
  set E : ℝ → Set Ω := fun ε => if ε ≤ e0 then meshEventR S γ ω₀ ρ CG ζ α CE ε else ∅ with hEdef
  have hEp' : ProbTendsToOne S.P E :=
    probTendsToOne_congr_small he0 hE (fun ε _ hle => by simp [hEdef, hle])
  have hpt' : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε ∩ goodField S Ew dd0 →
      ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ min R (dd0 ω) → ∀ i : Lemma68Config.Config68,
        Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
          ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
            Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
    intro ε hε
    by_cases hle : ε ≤ e0
    · filter_upwards [hpt ε hε hle] with ω hω
      rintro ⟨hωm, h1, h2, h3⟩ r hr hrd i hadm
      have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
      have hωm' : ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε := by simpa [hEdef, hle] using hωm
      exact hω hωm' h1 h2 r hr (hrd.trans (min_le_left _ _))
        (h3 r hr0 (hrd.trans (min_le_right _ _))) i hadm
    · refine Filter.Eventually.of_forall fun ω hω => ?_
      exact absurd hω.1 (by simp [hEdef, hle])
  refine ⟨fun ω => min R (dd0 ω), measurable_const.min hdd0m, fun ω => lt_min hR0 (hdd0pos ω),
    fun ω => min_le_left _ _, ?_⟩
  exact probTendsToOne_half_of_count (α := fun ε => 10 * ε ^ ω₀)
    (dd := fun ω => min R (dd0 ω)) (E := E)
    (G := goodField S Ew dd0) (R := R) (cN := countConst ζ) (q0 := q0) (ζ := ζ) hEp' hG
    (fun ε hε => by positivity) (fun ω => min_le_left _ _) hR1 hcN hq0 hq1 hRr
    (fun ε ω r i => Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i)
    (Lemma68Config.exitQ S) hpt'

/-- **The counting component of the CG mesh-radius event (q2, fp-S4S6c-goodevents-cgr).** The mesh event `meshEventR`
intersected with the good counting event `countingGoodEvent` (Lemma 2.9, Berestycki-Gwynne; HoneModelInputs68.lean:48) at
the exponents `α`, `β`. Its counting component is the membership taken by `hCountGood_pw` (B1EnvPw68.lean:65); its Green
component is the lower-bound body of `greenLowEvent68` (`countingMeshEventR_green`). -/
def countingMeshEventR {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (γ ω₀ ρ CG ζ α CE β : ℝ) (ε : ℝ) :
    Set Ω :=
  meshEventR S γ ω₀ ρ CG ζ α CE ε ∩ HoneModelInputs68.countingGoodEvent S α β ρ ε

/-- The mesh component of `countingMeshEventR` (q2, fp-S4S6c-goodevents-cgr). -/
lemma countingMeshEventR_meshR {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {γ ω₀ ρ CG ζ α CE β ε : ℝ}
    {ω : Ω} (h : ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε) :
    ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε :=
  h.1

/-- The Green component of `countingMeshEventR` (q2, fp-S4S6c-goodevents-cgr): `ω ∈ greenLowEvent68 S ω₀ ρ CG ε`, the
lower Green bound of Draft Lemma 2.16. Its body is the body of `hGreen_pw` (B1EnvPw68.lean:54) at `K.ω := ω₀`, `K.C := CG`,
radius `ρ`; the conjunct `greenKernel ≤ greenFn` of `greenLowerGoodEvent` is not used by the one-test hone. -/
lemma countingMeshEventR_green {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {γ ω₀ ρ CG ζ α CE β ε : ℝ}
    {ω : Ω} (h : ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε) : ω ∈ greenLowEvent68 S ω₀ ρ CG ε :=
  h.1.1.1

/-- The counting component of `countingMeshEventR` (q2, fp-S4S6c-goodevents-cgr). -/
lemma countingMeshEventR_counting {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {γ ω₀ ρ CG ζ α CE β ε : ℝ}
    {ω : Ω} (h : ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε) :
    ω ∈ HoneModelInputs68.countingGoodEvent S α β ρ ε :=
  h.2

/-- **Probability bound of `countingMeshEventR` (q2, fp-S4S6c-goodevents-cgr).** Given the Green, cell-size (at `(1 + ρ)/2`),
exit-time and counting events with polynomially high probability, `countingMeshEventR` has `ProbTendsToOne` as `ε ↓ 0`. -/
lemma probTendsToOne_countingMeshEventR {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {γ ω₀ ρ CG ζ α CE β : ℝ}
    (hG : HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG))
    (hC : HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)))
    (hE : HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE))
    (hK : HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ)) :
    ProbTendsToOne S.P (fun ε => countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε) :=
  (probTendsToOne_meshEventR hG hC hE).inter (probTendsToOne_of_polyHighProb hK)

/-- **Named input, not a Draft statement (q2, fp-S4S6c-goodevents-cgr; for operator decision).** The counting bound at
the exit exponent. `CountingMeasureConvergenceStmt` (Draft/Section2.lean:143) gives `α`, `β` with the counting event for
all radii, and `ExitTimeUpperBoundStmt` (Draft/Section2.lean:239) gives its own `α`; the one-test hone uses one `α` for the
exit thickening and the counting thickening (`ε ^ α`). This Prop asks for one pair `(α, β)` with both. Paper: Lemma
`lemma:mu_h-convergence` (line 681, "There exists α = α(γ)") and `lemma:exit-time-upper-bound` (line 921, "There exists
deterministic α = α(γ)"); the proof at line 3820 takes `α` from the counting lemma. -/
def CountingAtExitAlphaStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ CE : ℝ, 0 < CE ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) ∧
      HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ)

/-- **`ShellChainCGRStmt` with the counting component (q2, fp-S4S6c-goodevents-cgr).** The body of `ShellChainCGRStmt`
(cell-size hypothesis at `(1 + ρ)/2`), with the counting exponent `β > 0`, the counting hypothesis
`PolyHighProb (countingGoodEvent S α β ρ)` at the chain exponent `α`, and the almost sure clause on `countingMeshEventR`. -/
def ShellChainCGRCStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE β : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE → 0 < β →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ 1 ∧ ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ) →
      ∃ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) ∧
        HarmonicBalls.PolyHighProb S.P Ew ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P,
          ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
          Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
          (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
          ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
            ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
              ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
                Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

end Lemma68Guard10

/-- **Lemma 6.8, uniform constant-order lower bound (`UniformConstantOrderLowerBoundStmt`, FirstPass/S6d.lean:95)**,
from the Draft hypotheses `GreenKernelLowerBoundStmt`, `CellSizeEstimateStmt`, `ExitTimeUpperBoundStmt` (the inputs of
q1's `draft68_uniform_events`) and the open shell chain `Lemma68Guard10.ShellChainStmt`. -/
theorem uniformConstantOrderLowerBound_of_chain (𝒮 : SpaceFillingSLEModel)
    (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hChain : Lemma68Guard10.ShellChainStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  uniformConstantOrderLowerBound_of_guard 𝒮
    (Lemma68Guard10.guardProbStmt_of_chain 𝒮 (Lemma68Guard10.meshEventsStmt_of_draft 𝒮 hG hC hE) hChain)

/-- **Lemma 6.8, uniform constant-order lower bound from the Eps chain (q2, fp-S4S6c-eps-chain).** As
`uniformConstantOrderLowerBound_of_chain`, with `ShellChainEpsStmt` and the Eps mesh events. -/
theorem uniformConstantOrderLowerBoundEps_of_chain (𝒮 : SpaceFillingSLEModel)
    (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hChain : Lemma68Guard10.ShellChainEpsStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  uniformConstantOrderLowerBound_of_guard 𝒮
    (Lemma68Guard10.guardProbStmtEps_of_chainEps 𝒮
      (Lemma68Guard10.meshEventsEpsStmt_of_draft 𝒮 hG hC hE) hChain)

/-- **Lemma 6.8, uniform constant-order lower bound from the CG Eps chain (q2, fp-S4S6c-cg-param).** As
`uniformConstantOrderLowerBoundEps_of_chain`, with `ShellChainCGStmt` (the ball ratio `c₀(CG)`). -/
theorem uniformConstantOrderLowerBoundCG_of_chain (𝒮 : SpaceFillingSLEModel)
    (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hChain : Lemma68Guard10.ShellChainCGStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  uniformConstantOrderLowerBound_of_guard 𝒮
    (Lemma68Guard10.guardProbStmtCG_of_chainCG 𝒮
      (Lemma68Guard10.meshEventsEpsStmt_of_draft 𝒮 hG hC hE) hChain)

/-- **Lemma 6.8, uniform constant-order lower bound from the CG mesh-radius chain (q2, fp-S4S6c-meshEventR).** As
`uniformConstantOrderLowerBoundCG_of_chain`, with `ShellChainCGRStmt` (the cell-size event at `(1 + ρ)/2`). -/
theorem uniformConstantOrderLowerBoundCGR_of_chain (𝒮 : SpaceFillingSLEModel)
    (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hChain : Lemma68Guard10.ShellChainCGRStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  uniformConstantOrderLowerBound_of_guard 𝒮
    (Lemma68Guard10.guardProbStmtCGR_of_chainCGR 𝒮
      (Lemma68Guard10.meshEventsEpsStmt_of_draft 𝒮 hG hC hE) hChain)

end MatedCRT

#print axioms MatedCRT.Lemma68Guard10.meshEventR_cell
#print axioms MatedCRT.Lemma68Guard10.probTendsToOne_meshEventR
#print axioms MatedCRT.Lemma68Guard10.countingMeshEventR_green
#print axioms MatedCRT.Lemma68Guard10.probTendsToOne_countingMeshEventR
#print axioms MatedCRT.Lemma68Guard10.guardProbStmtCGR_of_chainCGR
#print axioms MatedCRT.uniformConstantOrderLowerBoundCGR_of_chain

#print axioms MatedCRT.Lemma68Guard10.shellEps0_pos
#print axioms MatedCRT.Lemma68Guard10.exists_radius_cutoff_gap
#print axioms MatedCRT.Lemma68Guard10.meshEventsEpsStmt_of_draft
#print axioms MatedCRT.Lemma68Guard10.shellChainEpsStmt_of_shellChainStmt
#print axioms MatedCRT.Lemma68Guard10.probTendsToOne_congr_small
#print axioms MatedCRT.Lemma68Guard10.guardProbStmtEps_of_chainEps
#print axioms MatedCRT.uniformConstantOrderLowerBoundEps_of_chain
#print axioms MatedCRT.Lemma68Guard10.guardProbStmt_of_chain
#print axioms MatedCRT.uniformConstantOrderLowerBound_of_chain
#print axioms MatedCRT.Lemma68Guard10.shellEps0Z_pos
#print axioms MatedCRT.Lemma68Guard10.shellEps0Z_pow_le
