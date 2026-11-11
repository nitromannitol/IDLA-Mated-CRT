import MatedCRT.Proofs.Sec3.KilledOccupation.LimClockIdentification
import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationKernelMeasurable
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# The Stieltjes kernel of the limit occupation clock

For a family `ψ` of circle averages and a path `b`, the limit clock `s ↦ limClockFun γ ε ψ σ b s` is nondecreasing and
right continuous with values in `[0, ∞]`. This file turns it into a measurable family of locally finite measures on
`ℝ≥0`, the Stieltjes measures of the clock.

* `limClockFun_mono`, `limClockFun_continuousWithinAt_Ici`: monotonicity and right continuity of the limit clock.
* `limClockTrunc`: the limit clock truncated to `0` on the set where it is infinite at some rational time. It is
  real valued, nonnegative, nondecreasing and right continuous, and it is jointly measurable in `(ψ, b)`.
* `limClockKernel`: the Stieltjes measure of `limClockTrunc` on `ℝ≥0`, with
  `limClockKernel γ ε σ p (Iic t) = ofReal (limClockTrunc γ ε σ p t - limClockTrunc γ ε σ p 0)`. This mass is finite and
  measurable in `p`, which are the hypotheses of `measurable_lintegral_setLIntegral_exitNN`.
* `limClockKernel_Iic_of_eq_clock`: when the limit clock is a time-change clock `F` stopped at `σ`, the kernel is the
  Stieltjes measure of the stopped clock, `limClockKernel γ ε σ p (Iic t) = ofReal (F (min t (σ b)))`.
* `ae_limClockKernel_Iic_cone`: on the quantum cone, the kernel is the Stieltjes measure of the clock of Liouville
  Brownian motion stopped at the exit time of the ball.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open _root_.HarmonicBalls MarkovProcess

namespace MatedCRT.KilledOccupation

section Generic

variable (γ : ℝ) (ε : ℕ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)

/-- The limit clock at time `s` is at most the limit superior of the regularized clocks at any rational time
`q > s`. -/
lemma limClockFun_le_limsup (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ) {s : ℝ≥0} {q : ℚ≥0}
    (h : s < (q : ℝ≥0)) :
    limClockFun γ ε ψ σ b s ≤ Filter.limsup (fun k => regClockFun γ (ε k) ψ σ b (q : ℝ≥0)) Filter.atTop :=
  iInf_le (fun q' : {q : ℚ≥0 // s < (q : ℝ≥0)} =>
    Filter.limsup (fun k => regClockFun γ (ε k) ψ σ b (q'.1 : ℝ≥0)) Filter.atTop) ⟨q, h⟩

/-- The limit clock is nondecreasing in time. -/
theorem limClockFun_mono (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ) :
    Monotone (limClockFun γ ε ψ σ b) := by
  intro s t hst
  refine le_iInf fun q => ?_
  exact limClockFun_le_limsup γ ε σ ψ b (lt_of_le_of_lt hst q.2)

/-- The limit clock is right continuous in time: it is the infimum over the rational times `q > s` of a function
of `q`, and it is nondecreasing. -/
theorem limClockFun_continuousWithinAt_Ici (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ) (s : ℝ≥0) :
    ContinuousWithinAt (limClockFun γ ε ψ σ b) (Ici s) s := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  have hmono := limClockFun_mono γ ε σ ψ b
  have hlim := hmono.tendsto_nhdsGT s
  have hEq : sInf (limClockFun γ ε ψ σ b '' Ioi s) = limClockFun γ ε ψ σ b s := by
    apply le_antisymm
    · refine le_iInf fun q => ?_
      obtain ⟨s', hs', hs'q⟩ := exists_between q.2
      exact (sInf_le (Set.mem_image_of_mem (limClockFun γ ε ψ σ b) (Set.mem_Ioi.2 hs'))).trans
        (limClockFun_le_limsup γ ε σ ψ b hs'q)
    · refine le_sInf ?_
      rintro _ ⟨t, ht, rfl⟩
      exact hmono (le_of_lt ht)
  rw [hEq] at hlim
  exact hlim

open Classical in
/-- The truncated limit clock `Φ̄(ψ, b)(t)`: the real value of the limit clock, set to `0` for the pairs `(ψ, b)` at
which the limit clock is infinite at some rational time. -/
def limClockTrunc (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) (t : ℝ≥0) : ℝ :=
  if (⨆ q : ℚ≥0, limClockFun γ ε p.1 σ p.2 (q : ℝ≥0)) = ∞ then 0 else (limClockFun γ ε p.1 σ p.2 t).toReal

/-- If the limit clock is finite at the rational times, uniformly, then it is finite at every time. -/
lemma limClockFun_ne_top_of_iSup_ne_top (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ)
    (h : (⨆ q : ℚ≥0, limClockFun γ ε p.1 σ p.2 (q : ℝ≥0)) ≠ ∞) (t : ℝ≥0) :
    limClockFun γ ε p.1 σ p.2 t ≠ ∞ := by
  obtain ⟨q, hq, -⟩ := exists_nnrat_btwn_nnreal (lt_add_one t)
  exact ne_top_of_le_ne_top h ((limClockFun_mono γ ε σ p.1 p.2 hq.le).trans
    (le_iSup (fun q : ℚ≥0 => limClockFun γ ε p.1 σ p.2 (q : ℝ≥0)) q))

lemma limClockTrunc_of_iSup_eq_top (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ)
    (h : (⨆ q : ℚ≥0, limClockFun γ ε p.1 σ p.2 (q : ℝ≥0)) = ∞) :
    limClockTrunc γ ε σ p = fun _ => 0 := by
  funext t
  unfold limClockTrunc
  split_ifs
  rfl

lemma limClockTrunc_of_iSup_ne_top (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ)
    (h : (⨆ q : ℚ≥0, limClockFun γ ε p.1 σ p.2 (q : ℝ≥0)) ≠ ∞) :
    limClockTrunc γ ε σ p = fun t => (limClockFun γ ε p.1 σ p.2 t).toReal := by
  funext t
  unfold limClockTrunc
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-- The truncated limit clock is nonnegative. -/
theorem limClockTrunc_nonneg (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) (t : ℝ≥0) :
    0 ≤ limClockTrunc γ ε σ p t := by
  by_cases h : (⨆ q : ℚ≥0, limClockFun γ ε p.1 σ p.2 (q : ℝ≥0)) = ∞
  · rw [limClockTrunc_of_iSup_eq_top γ ε σ p h]
  · rw [limClockTrunc_of_iSup_ne_top γ ε σ p h]
    exact ENNReal.toReal_nonneg

/-- The truncated limit clock is nondecreasing in time. -/
theorem limClockTrunc_mono (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) :
    Monotone (limClockTrunc γ ε σ p) := by
  by_cases h : (⨆ q : ℚ≥0, limClockFun γ ε p.1 σ p.2 (q : ℝ≥0)) = ∞
  · rw [limClockTrunc_of_iSup_eq_top γ ε σ p h]
    exact monotone_const
  · rw [limClockTrunc_of_iSup_ne_top γ ε σ p h]
    intro s t hst
    exact ENNReal.toReal_mono (limClockFun_ne_top_of_iSup_ne_top γ ε σ p h t)
      (limClockFun_mono γ ε σ p.1 p.2 hst)

/-- The truncated limit clock is right continuous in time. -/
theorem limClockTrunc_continuousWithinAt_Ici (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) (s : ℝ≥0) :
    ContinuousWithinAt (limClockTrunc γ ε σ p) (Ici s) s := by
  by_cases h : (⨆ q : ℚ≥0, limClockFun γ ε p.1 σ p.2 (q : ℝ≥0)) = ∞
  · rw [limClockTrunc_of_iSup_eq_top γ ε σ p h]
    exact continuousWithinAt_const
  · rw [limClockTrunc_of_iSup_ne_top γ ε σ p h]
    exact ContinuousAt.comp_continuousWithinAt (g := ENNReal.toReal)
      (ENNReal.tendsto_toReal (limClockFun_ne_top_of_iSup_ne_top γ ε σ p h s))
      (limClockFun_continuousWithinAt_Ici γ ε σ p.1 p.2 s)

/-- Joint measurability of the truncated limit clock in the pair `(ψ, b)`, for a measurable exit time `σ`. -/
theorem measurable_limClockTrunc (hσ : Measurable σ) (t : ℝ≥0) :
    Measurable fun p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ => limClockTrunc γ ε σ p t := by
  have hsup : Measurable fun p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ =>
      ⨆ q : ℚ≥0, limClockFun γ ε p.1 σ p.2 (q : ℝ≥0) :=
    Measurable.iSup fun q : ℚ≥0 => measurable_limClockFun γ ε σ hσ (q : ℝ≥0)
  unfold limClockTrunc
  exact Measurable.ite (measurableSet_eq_fun hsup measurable_const) measurable_const
    (measurable_limClockFun γ ε σ hσ t).ennreal_toReal

/-- The truncated limit clock as a Stieltjes function on `ℝ≥0`. -/
def limClockStieltjes (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) : StieltjesFunction ℝ≥0 where
  toFun := limClockTrunc γ ε σ p
  mono' := limClockTrunc_mono γ ε σ p
  right_continuous' := limClockTrunc_continuousWithinAt_Ici γ ε σ p

/-- The Stieltjes kernel of the limit clock: for each pair `p = (ψ, b)`, the Stieltjes measure on `ℝ≥0` of the
truncated limit clock `limClockTrunc γ ε σ p`. -/
def limClockKernel (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) : Measure ℝ≥0 :=
  (limClockStieltjes γ ε σ p).measure

/-- The mass of `[0, t]` under the Stieltjes kernel of the limit clock. -/
theorem limClockKernel_Iic (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) (t : ℝ≥0) :
    limClockKernel γ ε σ p (Iic t) =
      ENNReal.ofReal (limClockTrunc γ ε σ p t - limClockTrunc γ ε σ p 0) := by
  have h0 : IsBot (0 : ℝ≥0) := fun x => by simp
  have hf : Tendsto (limClockStieltjes γ ε σ p) atBot (𝓝 (limClockTrunc γ ε σ p 0)) := by
    rw [atBot_eq_pure_of_isBot h0]
    exact tendsto_pure_nhds _ _
  exact (limClockStieltjes γ ε σ p).measure_Iic hf t

/-- The Stieltjes kernel of the limit clock gives finite mass to bounded intervals. -/
theorem limClockKernel_Iic_ne_top (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) (t : ℝ≥0) :
    limClockKernel γ ε σ p (Iic t) ≠ ∞ := by
  rw [limClockKernel_Iic]
  exact ENNReal.ofReal_ne_top

/-- Measurability in `p = (ψ, b)` of the mass of `[0, t]` under the Stieltjes kernel of the limit clock. -/
theorem measurable_limClockKernel_Iic (hσ : Measurable σ) (t : ℝ≥0) :
    Measurable fun p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ => limClockKernel γ ε σ p (Iic t) := by
  simp_rw [limClockKernel_Iic]
  exact ((measurable_limClockTrunc γ ε σ hσ t).sub (measurable_limClockTrunc γ ε σ hσ 0)).ennreal_ofReal

/-- Measurability in the circle averages `ψ` of the occupation functional of the limit clock: the integral over the
path `b` of the integral of `q (b u)` over `u ∈ [0, σ(b)]` against the Stieltjes kernel of the limit clock, where
`σ = exitNN z r` is the exit time of `ball z r`. -/
theorem measurable_limClockOccupation (z : ℂ) (r : ℝ) (μ : Measure (ContinuousPath ℂ)) [SFinite μ]
    (q : ℂ → ℝ≥0∞) (hq : Measurable q) :
    Measurable fun ψ : UnitDiskCircleIndex → ℝ =>
      ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(limClockKernel γ ε (exitNN z r) (ψ, b)) ∂μ :=
  measurable_lintegral_setLIntegral_exitNN (fun p => limClockKernel γ ε (exitNN z r) p)
    (fun p t => limClockKernel_Iic_ne_top γ ε (exitNN z r) p t)
    (fun t => measurable_limClockKernel_Iic γ ε (exitNN z r) (measurable_exitNN z r) t) μ z r q hq

/-- If the limit clock at `p = (ψ, b)` is a time-change clock `F` stopped at `σ(b)`, the truncated limit clock is the
stopped clock. -/
theorem limClockTrunc_eq_of_eq_clock {p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ} {F : ℝ≥0 → ℝ}
    (hF : IsTimeChangeClock F)
    (h : ∀ s : ℝ≥0, limClockFun γ ε p.1 σ p.2 s = ENNReal.ofReal (F (min s (σ p.2)))) (t : ℝ≥0) :
    limClockTrunc γ ε σ p t = F (min t (σ p.2)) := by
  have hsup : (⨆ q : ℚ≥0, limClockFun γ ε p.1 σ p.2 (q : ℝ≥0)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := F (σ p.2))) (iSup_le fun q => ?_)
    rw [h]
    exact ENNReal.ofReal_le_ofReal (hF.strictMono.monotone (min_le_right _ _))
  have hnn : 0 ≤ F (min t (σ p.2)) := by
    have h0 : F 0 ≤ F (min t (σ p.2)) := hF.strictMono.monotone (by simp)
    rwa [hF.map_zero] at h0
  rw [limClockTrunc_of_iSup_ne_top γ ε σ p hsup]
  show (limClockFun γ ε p.1 σ p.2 t).toReal = F (min t (σ p.2))
  rw [h t, ENNReal.toReal_ofReal hnn]

/-- If the limit clock at `p = (ψ, b)` is a time-change clock `F` stopped at `σ(b)`, the Stieltjes kernel of the limit
clock is the Stieltjes measure of the stopped clock: the mass of `[0, t]` is `F (min t (σ b))`. -/
theorem limClockKernel_Iic_of_eq_clock {p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ} {F : ℝ≥0 → ℝ}
    (hF : IsTimeChangeClock F)
    (h : ∀ s : ℝ≥0, limClockFun γ ε p.1 σ p.2 s = ENNReal.ofReal (F (min s (σ p.2)))) (t : ℝ≥0) :
    limClockKernel γ ε σ p (Iic t) = ENNReal.ofReal (F (min t (σ p.2))) := by
  have h0 : min (0 : ℝ≥0) (σ p.2) = 0 := min_eq_left (by simp)
  rw [limClockKernel_Iic, limClockTrunc_eq_of_eq_clock γ ε σ hF h t, limClockTrunc_eq_of_eq_clock γ ε σ hF h 0,
    h0, hF.map_zero, sub_zero]

end Generic

/-- On the quantum cone, the Stieltjes kernel of the limit clock is the Stieltjes measure of the clock of Liouville
Brownian motion stopped at the exit time of `ball z r`: for almost every `ω` and almost every Brownian path `b` from
`y`, the mass of `[0, t]` is `S.clock ω b (min t (exitNN z r b))` for every `t`. The hypothesis `hid` is the
identification of the limit clock along the scales `n` (`exists_strictMono_ae_limClockFun_eq_clock_cone`). -/
theorem ae_limClockKernel_Iic_cone {Ω : Type} [MeasurableSpace Ω] (𝒮 : SpaceFillingSLEModel) (γ : ℝ) (z y : ℂ)
    (r : ℝ) (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (n : ℕ → ℕ)
    (hid : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, ∀ s : ℝ≥0,
      limClockFun γ (fun k => dyadicScale (n k)) (clockPsi S.hcirc ω) (exitNN z r) b s =
        ENNReal.ofReal (S.clock ω b (min s (exitNN z r b)))) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, ∀ t : ℝ≥0,
      limClockKernel γ (fun k => dyadicScale (n k)) (exitNN z r) (clockPsi S.hcirc ω, b) (Iic t) =
        ENNReal.ofReal (S.clock ω b (min t (exitNN z r b))) := by
  filter_upwards [hid, hS.isLQGClock] with ω hω hclk
  filter_upwards [hω, (hclk y).2] with b hb hT
  intro t
  exact limClockKernel_Iic_of_eq_clock γ (fun k => dyadicScale (n k)) (exitNN z r)
    (p := (clockPsi S.hcirc ω, b)) hT hb t

end MatedCRT.KilledOccupation
