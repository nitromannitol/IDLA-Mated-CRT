import MatedCRT.FirstPass.Derived.PlanarBrownianVisitTrials
import MatedCRT.FirstPass.Derived.PlanarBrownianUniformShiftBound

/-!
# Divergence of an additive clock along planar Brownian motion

Let `F b t` be a nondecreasing clock of the continuous path `b`, additive under the time shift
`θ_s` (`F (θ_s b) t = F b (s + t) - F b s`), whose value at time `1/2` is determined by the path up
to time `1/2` and is almost surely positive under planar Brownian motion started from
Lebesgue-almost every point. Then `F b t → ∞` as `t → ∞`, almost surely under planar Brownian
motion from any start at which monotonicity and additivity hold almost surely.

This is the geometric-trials argument: with `σ_j` the successive visit times of the closed unit
disc `K` (each at least one unit of time after the previous one), the clock gains more than a
fixed `c > 0` during `[σ_j, σ_j + 1]` with conditional probability at least `p > 0` given the past
at `σ_j`:

* the fixed-time Markov property at time `1/2` and the Gaussian lower bound of the transition
  density on `K` give `c` and `p` uniformly over starts in `K`
  (`exists_pos_forall_closedBall_le_planarBrownianMotion_shift`);
* the strong Markov property at `σ_j`, neighbourhood recurrence, and the geometric-trials bound
  give infinitely many such gains (`planarBrownianMotion_ae_frequently_shift_visitTime_closedBall_mem`);
* additivity turns a gain of the shifted clock into an increment of `F b` over `[σ_j, σ_j + 1]`, and
  `LatticeProb.tendsto_atTop_of_frequently_lt_increment` concludes.

## Main results

* `planarBrownianMotion_ae_tendsto_atTop_of_additive`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

open _root_.HarmonicBalls

/-- **Divergence of an additive clock along planar Brownian motion.** Let `F b t` be a clock of
continuous paths whose value at time `1/2` is measurable for the canonical filtration at time
`1/2` and positive almost surely under planar Brownian motion from Lebesgue-almost every start.
If, almost surely under planar Brownian motion from `z`, `F b` is nondecreasing and additive under
the time shift (`F (θ_s b) t = F b (s + t) - F b s` for all `s, t`), then almost surely
`F b t → ∞` as `t → ∞`. -/
theorem planarBrownianMotion_ae_tendsto_atTop_of_additive {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hFm : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) 2⁻¹] fun b => F b 2⁻¹)
    (hpos : ∀ᵐ w ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion w), 0 < F b 2⁻¹)
    (z : ℂ)
    (hadd : ∀ᵐ b ∂(planarBrownianMotion z), Monotone (F b) ∧
      ∀ s t, F (ContinuousPath.shift s b) t = F b (s + t) - F b s) :
    ∀ᵐ b ∂(planarBrownianMotion z), Tendsto (F b) atTop atTop := by
  have h1 : (2⁻¹ : ℝ≥0) + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ two_ne_zero]
  set E : ℕ → Set (ContinuousPath ℂ) := fun m => {b | 1 / ((m : ℝ) + 1) < F b 2⁻¹} with hE_def
  have hE2 : ∀ m, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) 2⁻¹] (E m) :=
    fun m => measurableSet_lt measurable_const hFm
  have hEm : ∀ m, MeasurableSet (E m) :=
    fun m => (ContinuousPath.canonicalFiltration (alpha := ℂ)).le 2⁻¹ _ (hE2 m)
  have hmono : Monotone E := fun m n hmn b (hb : 1 / ((m : ℝ) + 1) < F b 2⁻¹) =>
    show 1 / ((n : ℝ) + 1) < F b 2⁻¹ from lt_of_le_of_lt (Nat.one_div_le_one_div hmn) hb
  have hfull : ∀ᵐ w ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion w), b ∈ ⋃ m, E m :=
    hpos.mono fun w hw => hw.mono fun b hb => mem_iUnion.2 (exists_nat_one_div_lt hb)
  obtain ⟨p, hp0, m, hp⟩ :=
    exists_pos_forall_closedBall_le_planarBrownianMotion_shift hEm hmono hfull
      (s := 2⁻¹) (inv_ne_zero two_ne_zero)
  have hΓ : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) 1]
      (ContinuousPath.shift 2⁻¹ ⁻¹' E m) := by
    have := ContinuousPath.measurable_shift_canonicalFiltration (alpha := ℂ) 2⁻¹ 2⁻¹ (hE2 m)
    rwa [h1] at this
  filter_upwards [planarBrownianMotion_ae_frequently_shift_visitTime_closedBall_mem z 0
      one_pos hΓ hp0 hp, planarBrownianMotion_ae_forall_exists_le_norm_sub_lt z, hadd]
    with b hb hr hFb
  obtain ⟨hFmono, hshift⟩ := hFb
  have hrec : ∀ a : ℝ≥0, ∃ s : ℝ≥0, a ≤ s ∧ b s ∈ closedBall (0 : ℂ) 1 := fun a => by
    obtain ⟨s, has, hs⟩ := hr 0 1 one_pos a
    exact ⟨s, has, by rw [mem_closedBall, dist_eq_norm]; exact hs.le⟩
  refine LatticeProb.tendsto_atTop_of_frequently_lt_increment hFmono
    (untopD_visitTime_add_one_le isClosed_closedBall b hrec) (c := 1 / ((m : ℝ) + 1))
    (by positivity) (hb.mono fun j hj => ?_)
  set σ : ℝ≥0 := (visitTime (closedBall (0 : ℂ) 1) j b).untopD 0
  have hj' : 1 / ((m : ℝ) + 1) < F (ContinuousPath.shift (σ + 2⁻¹) b) 2⁻¹ := by
    have : 1 / ((m : ℝ) + 1) < F (ContinuousPath.shift 2⁻¹ (ContinuousPath.shift σ b)) 2⁻¹ := hj
    rwa [ContinuousPath.shift_add] at this
  rw [hshift, add_assoc, h1] at hj'
  have hle : F b σ ≤ F b (σ + 2⁻¹) := hFmono le_self_add
  linarith

end MatedCRT.KilledOccupation
