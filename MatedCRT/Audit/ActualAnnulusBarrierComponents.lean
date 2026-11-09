import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ActualAnnulusBarrier
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusIteration

/-! # Consumer audit: the actual one-stage barrier in the annulus survival iteration

Task `z5-steps2-actual-annulus-barrier-audit`. Source: `notes/wpn-steps2/steps2-r3.tex`, lines 695-739 (the
strong-Markov iteration over annuli with radii increasing by a factor four). Audit only: this file proves no numbered
result and no `eq:distance-tail` bound, and adds no literature input.

## Connection

* Stage input. For a good `ω`, `AnnulusStayGood` (ActualAnnulusBarrier.lean:139) gives the one-stage stay bound for every
  admissible annulus. It enters the existing finite-stage iteration `lintegral_annulusCrossings_le_pow_finite`
  (AnnulusIteration.lean:127) as its stage hypothesis, through `hit_target_before_exit_subset_stay`
  (AnnulusDisconnection.lean:208), with landing set `B i = A i`.
* No hidden premise. The consumer has no graph path (`hgeom`), no fiber connectivity and no survival law as an argument.
  The walk of `ae_outward_segment_walk` (ActualAnnulusBarrier.lean:49) and the disconnection input enter only inside
  `ae_annulus_stay_le_of_disconnection` and `stay_prob_of_GMSAnnulusDisconnectionStmt` (ActualAnnulusBarrier.lean:156).
* Literature. `hgms : GMSAnnulusDisconnectionStmt 𝒮` is the explicit printed input (Gwynne-Miller-Sheffield,
  arXiv:1807.07511v3, Lemma 3.11, (3.35), p. 31). Its exponent `α` and constant `C` appear in the probability bound.

## Exact scale quantifiers

* `AnnulusLadder ε β ρ d r V z n` carries a family `s : ℕ → ℝ`, of which only the finitely many stages `i ≤ n` are
  used. The factor-four ladder is `s i = 4 * s (i + 1)` for `i < n`. The smallest scale satisfies `ε ^ β ≤ s n`; the
  top scale satisfies `s 0 ≤ ρ` and `closedBall V (2 * s 0) ⊆ ball 0 ρ`; the separation is `5 * d < s n / 2`, with
  `r - d ≤ dist V z` and `0 ≤ d`. The window forces `4 ^ n * ε ^ β ≤ s 0 ≤ ρ`.
* Stage `i ≤ n`: start `ladderStart ε η V (s i) = V^ε(ball V (s i))`, landing and target
  `ladderTarget ε η V (s i) = V^ε(sphere V (2 * s i))`, enlarged disk `ladderDisk ε η z r d = V^ε(ball z (r + 3 * d))`.

## Named residual inputs (explicit; none is proved or assumed here)

* `AnnulusTopCellSizeGood ε η d V z r s`: cells meeting the largest annulus region `closedBall V (2 * s) \ ball z (r + 3 * d)`
  have diameter at most `d`. Its failure enters the probability bound as the term
  `S.P {ω | ¬ AnnulusTopCellSizeGood …}`, with no rate. The producer boundary is `annulusTopCellSizeGood_of_ball_diam`:
  the cell-diameter event of `cell_diam_failure_le` (UniformCellSizeProof.lean:149), on the ball `ball 0 ρ`, implies it.
  That lemma's unproved pieces are its `SegmentsContainBalls` event and its local ball-mass event; the repository gives
  no probability bound for either.
* `p < 1` for the rate exponent `ladderExponent p = -log (1 - p) / log 4 > 0` (`ladder_rate_le`). The printed GMS
  statement gives only `0 < p`, so this hypothesis is explicit there.

## Credit

Cells and cell vertices (`MatedCRT.Defs.Map`) are adapted from Leonardo Bonanno's lean-formalizations. The mated-CRT
bundle behind `MatedCRTEnv.IsValid` is Bonanno's `LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling`
(`MatedCRT.Defs.Setting`). The one-stage barrier uses Bonanno's
`LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDirectRel` through `ActualAnnulusBarrier`.
-/

namespace MatedCRT

open Set MeasureTheory Metric
open scoped ENNReal

/-- Start cells of the stage at scale `s`: the cells meeting `ball V s`. -/
abbrev ladderStart (ε : ℝ) (η : ℝ → ℂ) (V : ℂ) (s : ℝ) : Set ℤ :=
  cellVertices ε η (ball V s)

/-- Target and landing cells of the stage at scale `s`: the cells meeting the outer sphere `sphere V (2 * s)`. -/
abbrev ladderTarget (ε : ℝ) (η : ℝ → ℂ) (V : ℂ) (s : ℝ) : Set ℤ :=
  cellVertices ε η (sphere V (2 * s))

/-- The enlarged disk: the walk must stay in its cells until it reaches the outer sphere. -/
abbrev ladderDisk (ε : ℝ) (η : ℝ → ℂ) (z : ℂ) (r d : ℝ) : Set ℤ :=
  cellVertices ε η (ball z (r + 3 * d))

/-- Finite-stage scale data of the factor-four ladder (steps2-r3.tex:695-739). Only the stages `i ≤ n` are used. -/
structure AnnulusLadder (ε β ρ d r : ℝ) (V z : ℂ) (n : ℕ) where
  /-- The scale of stage `i`. -/
  s : ℕ → ℝ
  /-- Factor-four ladder: stage `i + 1` has a quarter of the scale of stage `i`. -/
  ratio : ∀ i < n, s i = 4 * s (i + 1)
  /-- Smallest scale, at least the cutoff `ε ^ β` of `AnnulusStayGood`. -/
  lower : ε ^ β ≤ s n
  /-- Top scale, at most the radius `ρ` of the environment window. -/
  upper : s 0 ≤ ρ
  /-- The top annulus lies in the window. -/
  outer_sub : closedBall V (2 * s 0) ⊆ ball (0 : ℂ) ρ
  /-- Nonnegative cell-diameter margin. -/
  nonneg : 0 ≤ d
  /-- The centre `V` is at distance at least `r - d` from the pivot `z`. -/
  near : r - d ≤ dist V z
  /-- Separation of the smallest annulus from the disk margin. -/
  separation : 5 * d < s n / 2

/-- Named residual: cells meeting the largest annulus region `closedBall V (2 * s) \ ball z (r + 3 * d)` have diameter
at most `d`. Same shape as the `hcell` hypothesis of `AnnulusStayGood`. -/
def AnnulusTopCellSizeGood (ε : ℝ) (η : ℝ → ℂ) (d : ℝ) (V z : ℂ) (r s : ℝ) : Prop :=
  ∀ i : ℤ, ((closedBall V (2 * s) \ ball z (r + 3 * d)) ∩ cell ε η i).Nonempty →
    ∀ q₁ ∈ cell ε η i, ∀ q₂ ∈ cell ε η i, dist q₁ q₂ ≤ d

/-- Crossing event of the ladder: stages `0, …, n` of the existing iteration `annulusCrossingEvent`. -/
def ladderCrossingEvent (ε : ℝ) (η : ℝ → ℂ) (V z : ℂ) (r d : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    Set (ℕ → ℤ) :=
  annulusCrossingEvent (fun i => ladderTarget ε η V (s i)) (fun _ => ladderDisk ε η z r d)
    (fun i => ladderTarget ε η V (s i)) (n + 1)

/-- Quenched survival bound of the ladder with per-stage bound `q`: every start cell of stage `n` completes the
`n + 1` crossings with probability at most `q ^ (n + 1)`. -/
def LadderSurvivalBound (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (V z : ℂ) (r d : ℝ) (s : ℕ → ℝ)
    (n : ℕ) (q : ℝ≥0∞) : Prop :=
  ∀ v ∈ ladderStart ε η V (s n), srwLaw m v (ladderCrossingEvent ε η V z r d s n) ≤ q ^ (n + 1)

/-- The rate exponent `ν = -log (1 - p) / log 4` of the factor-four ladder. -/
noncomputable def ladderExponent (p : ℝ) : ℝ :=
  -Real.log (1 - p) / Real.log 4

/-- Monotonicity of the cell-vertex map in its set argument. -/
theorem ladderCellVertices_mono {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    cellVertices ε η D ⊆ cellVertices ε η D' := by
  intro k hk
  obtain ⟨x, hx1, hx2⟩ := hk
  show (cell ε η k ∩ D').Nonempty
  exact ⟨x, hx1, h hx2⟩

theorem ladder_pos {ε β ρ d r : ℝ} {V z : ℂ} {n : ℕ} (L : AnnulusLadder ε β ρ d r V z n)
    (hε : 0 < ε) : ∀ i ≤ n, 0 < L.s i := by
  have key : ∀ k, k ≤ n → 0 < L.s (n - k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero]
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos hε β) L.lower
    | succ k ih =>
      intro hk
      have h3 := L.ratio (n - (k + 1)) (by omega)
      rw [show n - (k + 1) + 1 = n - k by omega] at h3
      rw [h3]
      exact mul_pos (by norm_num) (ih (by omega))
  intro i hi
  have h := key (n - i) (by omega)
  rwa [show n - (n - i) = i by omega] at h

theorem ladder_bottom {ε β ρ d r : ℝ} {V z : ℂ} {n : ℕ} (L : AnnulusLadder ε β ρ d r V z n)
    (hε : 0 < ε) : ∀ i ≤ n, L.s n ≤ L.s i := by
  have hpos := ladder_pos L hε
  have key : ∀ k, k ≤ n → L.s n ≤ L.s (n - k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h3 := L.ratio (n - (k + 1)) (by omega)
      rw [show n - (k + 1) + 1 = n - k by omega] at h3
      have h4 := hpos (n - k) (by omega)
      have h5 := ih (by omega)
      rw [h3]
      linarith
  intro i hi
  have h := key (n - i) (by omega)
  rwa [show n - (n - i) = i by omega] at h

theorem ladder_le_top {ε β ρ d r : ℝ} {V z : ℂ} {n : ℕ} (L : AnnulusLadder ε β ρ d r V z n)
    (hε : 0 < ε) : ∀ i ≤ n, L.s i ≤ L.s 0 := by
  have hpos := ladder_pos L hε
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ i ih =>
    intro hi
    have h3 := L.ratio i (by omega)
    have h4 := hpos (i + 1) hi
    have h5 := ih (by omega)
    linarith

theorem ladder_pow {ε β ρ d r : ℝ} {V z : ℂ} {n : ℕ} (L : AnnulusLadder ε β ρ d r V z n) :
    ∀ k, k ≤ n → L.s (n - k) = 4 ^ k * L.s n := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h3 := L.ratio (n - (k + 1)) (by omega)
    rw [show n - (k + 1) + 1 = n - k by omega] at h3
    rw [h3, ih (by omega)]
    ring

theorem ladder_top_eq {ε β ρ d r : ℝ} {V z : ℂ} {n : ℕ} (L : AnnulusLadder ε β ρ d r V z n) :
    L.s 0 = 4 ^ n * L.s n := by
  have h := ladder_pow L n le_rfl
  rwa [Nat.sub_self] at h

/-- Rate of the ladder: with `s 0 = 4 ^ n * s n` and `0 < p < 1`, the bound `(1 - p) ^ (n + 1)` is at most
`(s n / s 0) ^ ν` with `ν = -log (1 - p) / log 4 > 0`. Pure arithmetic; no probability is estimated. -/
theorem ladder_rate_le {ε β ρ d r : ℝ} {V z : ℂ} {n : ℕ} (L : AnnulusLadder ε β ρ d r V z n)
    (hε : 0 < ε) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ENNReal.ofReal (1 - p) ^ (n + 1) ≤ ENNReal.ofReal ((L.s n / L.s 0) ^ ladderExponent p) := by
  have hq0 : 0 < 1 - p := by linarith
  have hq1 : 1 - p < 1 := by linarith
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog4ne : Real.log 4 ≠ 0 := hlog4.ne'
  have hlogq : Real.log (1 - p) < 0 := Real.log_neg hq0 hq1
  have hν : ladderExponent p * Real.log 4 = -Real.log (1 - p) := by
    unfold ladderExponent
    field_simp
  have hsn : 0 < L.s n := ladder_pos L hε n le_rfl
  have hs0 : L.s 0 = 4 ^ n * L.s n := ladder_top_eq L
  have hs0pos : 0 < L.s 0 := by
    rw [hs0]
    exact mul_pos (pow_pos (by norm_num) n) hsn
  have hlog : Real.log (L.s n / L.s 0) = -((n : ℝ) * Real.log 4) := by
    rw [Real.log_div hsn.ne' hs0pos.ne', hs0, Real.log_mul (by positivity) hsn.ne', Real.log_pow]
    ring
  have hexp : -((n : ℝ) * Real.log 4) * ladderExponent p = (n : ℝ) * Real.log (1 - p) := by
    linear_combination (-(n : ℝ)) * hν
  have hpow : (1 - p) ^ n = Real.exp ((n : ℝ) * Real.log (1 - p)) := by
    rw [← Real.exp_log (pow_pos hq0 n), Real.log_pow]
  have hkey : (L.s n / L.s 0) ^ ladderExponent p = (1 - p) ^ n := by
    rw [Real.rpow_def_of_pos (div_pos hsn hs0pos), hlog, hexp, hpow]
  calc ENNReal.ofReal (1 - p) ^ (n + 1) = ENNReal.ofReal ((1 - p) ^ (n + 1)) :=
        (ENNReal.ofReal_pow hq0.le (n + 1)).symm
    _ ≤ ENNReal.ofReal ((1 - p) ^ n) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_succ n))
    _ = ENNReal.ofReal ((L.s n / L.s 0) ^ ladderExponent p) := by rw [hkey]

/-- The existing finite-stage iteration, stated for an arbitrary family of stage sets. Its stage input `hstage` is the
one-stage bound of each start cell, with landing set `B i`. This is `lintegral_annulusCrossings_le_pow_finite`
transported from the integral to the event. -/
theorem measure_annulusCrossingEvent_le_pow_finite_of_stage (m : ℤ → ℤ → ℕ) (A U B S : ℕ → Set ℤ)
    (q : ℝ≥0∞) (n : ℕ) (hnext : ∀ i < n, B (i + 1) ⊆ S i)
    (hstage : ∀ i ≤ n, ∀ v ∈ S i,
      srwLaw m v (⋃ k : ℕ, {x | vHitTime (A i ∪ (U i)ᶜ) x = k ∧ x k ∈ B i}) ≤ q)
    (v : ℤ) (hv : v ∈ S n) :
    srwLaw m v (annulusCrossingEvent A U B (n + 1)) ≤ q ^ (n + 1) := by
  rw [← lintegral_indicator_one (measurableSet_annulusCrossingEvent A U B (n + 1)),
    ← annulusCrossings_eq_indicator]
  exact lintegral_annulusCrossings_le_pow_finite m A U B S q n hnext hstage v hv

/-- Quenched consumer: on the good event `AnnulusStayGood` of the actual environment, with the top-region cell-diameter
residual `AnnulusTopCellSizeGood`, every stage-`n` start cell completes the ladder with probability at most
`(1 - p) ^ (n + 1)`. No graph path, fiber connectivity or survival law is supplied: the stage input is the one-stage
bound of `AnnulusStayGood`. -/
theorem ladder_survival_of_stay_good {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {ε ρ β p d r : ℝ} {V z : ℂ} {n : ℕ} {ω : Ω} (hε : 0 < ε)
    (L : AnnulusLadder ε β ρ d r V z n) (hω : AnnulusStayGood S ε ρ β p ω)
    (htop : AnnulusTopCellSizeGood ε (S.η ω) d V z r (L.s 0)) :
    LadderSurvivalBound (S.mult ε ω) ε (S.η ω) V z r d L.s n (ENNReal.ofReal (1 - p)) := by
  unfold AnnulusStayGood at hω
  unfold AnnulusTopCellSizeGood at htop
  have hpos := ladder_pos L hε
  have hbot := ladder_bottom L hε
  have htopb := ladder_le_top L hε
  have hVmem : V ∈ ball (0 : ℂ) ρ :=
    L.outer_sub (mem_closedBall_self (by linarith [hpos 0 (Nat.zero_le n)]))
  have hlo : ∀ i ≤ n, ε ^ β ≤ L.s i := fun i hi => L.lower.trans (hbot i hi)
  have hhi : ∀ i ≤ n, L.s i ≤ ρ := fun i hi => (htopb i hi).trans L.upper
  have hsub : ∀ i ≤ n, ball V (2 * L.s i) ⊆ ball (0 : ℂ) ρ := fun i hi =>
    (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (show 2 * L.s i ≤ 2 * L.s 0 by linarith [htopb i hi]))).trans
      L.outer_sub
  have hsep : ∀ i ≤ n, 5 * d < L.s i / 2 := fun i hi => by
    linarith [hbot i hi, L.separation]
  have hcell : ∀ i ≤ n, ∀ j : ℤ,
      ((closedBall V (2 * L.s i) \ ball z (r + 3 * d)) ∩ cell ε (S.η ω) j).Nonempty →
        ∀ q₁ ∈ cell ε (S.η ω) j, ∀ q₂ ∈ cell ε (S.η ω) j, dist q₁ q₂ ≤ d := by
    intro i hi j hj
    refine htop j (hj.mono ?_)
    intro x hx
    exact ⟨⟨closedBall_subset_closedBall
      (show 2 * L.s i ≤ 2 * L.s 0 by linarith [htopb i hi]) hx.1.1, hx.1.2⟩, hx.2⟩
  have hstage : ∀ i ≤ n, ∀ w ∈ ladderStart ε (S.η ω) V (L.s i),
      srwLaw (S.mult ε ω) w (⋃ k : ℕ, {x | vHitTime (ladderTarget ε (S.η ω) V (L.s i) ∪
        (ladderDisk ε (S.η ω) z r d)ᶜ) x = k ∧ x k ∈ ladderTarget ε (S.η ω) V (L.s i)}) ≤
        ENNReal.ofReal (1 - p) := by
    intro i hi w hw
    exact (measure_mono (hit_target_before_exit_subset_stay (ladderTarget ε (S.η ω) V (L.s i))
      (ladderDisk ε (S.η ω) z r d) (ladderTarget ε (S.η ω) V (L.s i)) subset_rfl)).trans
      (hω z V r (L.s i) d w hVmem (hlo i hi) (hhi i hi) (hsub i hi) hw L.nonneg L.near
        (hsep i hi) (hcell i hi))
  have hnext : ∀ i < n, ladderTarget ε (S.η ω) V (L.s (i + 1)) ⊆
      ladderStart ε (S.η ω) V (L.s i) := by
    intro i hi
    have hball : sphere V (2 * L.s (i + 1)) ⊆ ball V (L.s i) := by
      intro x hx
      rw [mem_sphere] at hx
      rw [mem_ball, hx, L.ratio i hi]
      linarith [hpos (i + 1) (by omega)]
    exact ladderCellVertices_mono hball
  unfold LadderSurvivalBound ladderCrossingEvent
  intro v hv
  exact measure_annulusCrossingEvent_le_pow_finite_of_stage (S.mult ε ω)
    (fun i => ladderTarget ε (S.η ω) V (L.s i)) (fun _ => ladderDisk ε (S.η ω) z r d)
    (fun i => ladderTarget ε (S.η ω) V (L.s i)) (fun i => ladderStart ε (S.η ω) V (L.s i))
    (ENNReal.ofReal (1 - p)) n hnext hstage v hv

/-- Probability form, with the GMS annulus input `hgms` explicit. For every ladder with the stated scale quantifiers,
the probability of the bad event is at most the GMS term `C ε ^ α` plus the failure probability of the residual
`AnnulusTopCellSizeGood`, which carries no rate here. The bad-event probability is an outer measure. -/
theorem MatedCRTEnv.IsValid.ladder_survival_probability {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hgms : GMSAnnulusDisconnectionStmt 𝒮) (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ p : ℝ, 0 < p ∧
      ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < 1 →
        ∀ (d r : ℝ) (V z : ℂ) (n : ℕ) (L : AnnulusLadder ε β ρ d r V z n),
          S.P {ω | ¬ LadderSurvivalBound (S.mult ε ω) ε (S.η ω) V z r d L.s n
              (ENNReal.ofReal (1 - p))} ≤
            ENNReal.ofReal (C * ε ^ α) +
              S.P {ω | ¬ AnnulusTopCellSizeGood ε (S.η ω) d V z r (L.s 0)} := by
  obtain ⟨α, β, hα, hβ, hstay⟩ := hS.stay_prob_of_GMSAnnulusDisconnectionStmt hgms hγ0 hγ2
  refine ⟨α, β, hα, hβ, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨p, hp, C, ε₀, hC, hε₀, hbound⟩ := hstay ρ hρ0 hρ1
  refine ⟨p, hp, C, ε₀, hC, hε₀, fun ε hε hεε₀ hε1 d r V z n L => ?_⟩
  calc S.P {ω | ¬ LadderSurvivalBound (S.mult ε ω) ε (S.η ω) V z r d L.s n (ENNReal.ofReal (1 - p))}
      ≤ S.P ({ω | ¬ AnnulusStayGood S ε ρ β p ω} ∪
          {ω | ¬ AnnulusTopCellSizeGood ε (S.η ω) d V z r (L.s 0)}) := by
        refine measure_mono fun ω hω => ?_
        by_cases h : AnnulusStayGood S ε ρ β p ω
        · exact Set.mem_union_right _ fun htop => hω (ladder_survival_of_stay_good hε L h htop)
        · exact Set.mem_union_left _ h
    _ ≤ S.P {ω | ¬ AnnulusStayGood S ε ρ β p ω} +
          S.P {ω | ¬ AnnulusTopCellSizeGood ε (S.η ω) d V z r (L.s 0)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C * ε ^ α) +
          S.P {ω | ¬ AnnulusTopCellSizeGood ε (S.η ω) d V z r (L.s 0)} :=
        add_le_add (hbound ε hε hεε₀ hε1) le_rfl

/-- Deterministic producer boundary: if every cell meeting the ball `ball 0 ρ` has diameter at most `D`, and the
annulus region lies in that ball, then the top-region residual holds with margin `d ≥ D`. The hypothesis `hcell` is the
good event of `cell_diam_failure_le` (UniformCellSizeProof.lean:149) with `D = 2 * δ ^ (1 - r)`. -/
theorem annulusTopCellSizeGood_of_ball_diam {ε ρ D d r s : ℝ} {η : ℝ → ℂ} {V z : ℂ}
    (hη : Continuous η) (hD : D ≤ d) (hball : closedBall V (2 * s) ⊆ ball (0 : ℂ) ρ)
    (hcell : ∀ i : ℤ, (cell ε η i ∩ ball (0 : ℂ) ρ).Nonempty → diam (cell ε η i) ≤ D) :
    AnnulusTopCellSizeGood ε η d V z r s := by
  unfold AnnulusTopCellSizeGood
  intro i hi q₁ hq₁ q₂ hq₂
  obtain ⟨x, hx⟩ := hi
  have hmeet : (cell ε η i ∩ ball (0 : ℂ) ρ).Nonempty := ⟨x, hx.2, hball hx.1.1⟩
  have hbdd : Bornology.IsBounded (cell ε η i) := by
    unfold cell
    exact (isCompact_Icc.image hη).isBounded
  calc dist q₁ q₂ ≤ diam (cell ε η i) := Metric.dist_le_diam_of_mem hbdd hq₁ hq₂
    _ ≤ D := hcell i hmeet
    _ ≤ d := hD

end MatedCRT
