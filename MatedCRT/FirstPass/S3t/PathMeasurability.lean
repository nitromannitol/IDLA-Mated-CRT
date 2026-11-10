import MatedCRT.FirstPass.S3t.Defs
import MarkovProcess.Path.ExitTimeShift
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkContinuity

/-!
# Stopped occupation on the continuous-path carrier (fp-S3t-four-binder, z8)

Answer 46(a3) of `notes/fp-gaps/CHATGPT-216-idla-hdet-truncated-gaps-PRO.md` (sections 1 and 2, lines 423-549): the stopped
occupation `∫_{(0, min (T, τ_D)]} g(w_t) dt` is Borel on the path space `ContinuousPath ℂ = C(ℝ≥0, ℂ)`, with its Borel
σ-algebra `MarkovProcess.ContinuousPath.instMeasurableSpace`, where `τ_D` is the exit time of the open set `D`
(Duplantier–Sheffield truncated occupation; potential-theoretic exit time of Armitage–Gardiner).
The exit time is Borel on path space by `MarkovProcess.ContinuousPath.measurable_exitTime`.
-/

open MeasureTheory Set Filter Topology MarkovProcess
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.TruncatedLaws

/-- The stopped occupation `∫_{(0, min (T, τ_D)]} g(w_t) dt` of a continuous path `w : ContinuousPath ℂ`
(the carrier on which the Brownian side `planarBrownianMotion` is a measure). -/
noncomputable def stoppedOccupationC (D : Set ℂ) (T : ℝ) (g : ℂ → ℝ) (w : ContinuousPath ℂ) : ℝ :=
  stoppedOccupation D T g w

/-- On `ContinuousPath ℂ` the Harmonic-Balls exit time `pathExitTime` is MarkovProcess's `ContinuousPath.exitTime`. -/
theorem pathExitTime_coe_eq_exitTime (D : Set ℂ) (w : ContinuousPath ℂ) :
    pathExitTime D (w : ℝ≥0 → ℂ) = MarkovProcess.ContinuousPath.exitTime D w := rfl

/-- The exit time of an open set is a Borel function on the continuous-path carrier
(`MarkovProcess.ContinuousPath.measurable_exitTime`, `Path/ExitTimeShift.lean:115`). -/
theorem measurable_pathExitTime_continuousPath {D : Set ℂ} (hD : IsOpen D) :
    Measurable (fun w : ContinuousPath ℂ => pathExitTime D (w : ℝ≥0 → ℂ)) :=
  MarkovProcess.ContinuousPath.measurable_exitTime D hD

/-- Borel measurability of the stopped occupation of an open set `D` on the continuous-path carrier, for a continuous
integrand `g`. Proof as `MatedCRT.TruncatedLaws.measurable_stoppedOccupation_interpolatedWalk` (Integrate.lean:112):
Carathéodory (continuity in the time variable, measurability in the path) and Fubini on `ℝ × ContinuousPath ℂ`. -/
theorem measurable_stoppedOccupationC {D : Set ℂ} (hD : IsOpen D) {g : ℂ → ℝ} (hg : Continuous g) (T : ℝ) :
    Measurable (stoppedOccupationC D T g) := by
  have hu : Measurable (fun w : ContinuousPath ℂ =>
      (min (ENNReal.ofReal T) (pathExitTime D (w : ℝ≥0 → ℂ))).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_const.min (measurable_pathExitTime_continuousPath hD))
  have hG : Measurable (Function.uncurry fun (t : ℝ) (w : ContinuousPath ℂ) => g (w t.toNNReal)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun w => hg.comp (w.continuous.comp continuous_real_toNNReal))
      (fun t => hg.measurable.comp (continuous_eval_const t.toNNReal).measurable)
  set E : Set (ℝ × ContinuousPath ℂ) :=
    {q | 0 < q.1} ∩ {q | q.1 ≤ (min (ENNReal.ofReal T) (pathExitTime D (q.2 : ℝ≥0 → ℂ))).toReal} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (hu.comp measurable_snd))
  have hsm : StronglyMeasurable (fun w : ContinuousPath ℂ => ∫ t : ℝ,
      E.indicator (Function.uncurry fun (t : ℝ) (w : ContinuousPath ℂ) => g (w t.toNNReal)) (t, w)) :=
    StronglyMeasurable.integral_prod_left' (hG.indicator hEm).stronglyMeasurable
  have heq : stoppedOccupationC D T g = fun w : ContinuousPath ℂ => ∫ t : ℝ,
      E.indicator (Function.uncurry fun (t : ℝ) (w : ContinuousPath ℂ) => g (w t.toNNReal)) (t, w) := by
    funext w
    unfold stoppedOccupationC stoppedOccupation
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
  rw [heq]
  exact hsm.measurable

/-- The interpolated walk of a lattice configuration `q : ℕ → ℤ`, packaged as a continuous path `ℝ≥0 → ℂ`. -/
noncomputable def interpolatedWalkC (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) (q : ℕ → ℤ) : ContinuousPath ℂ :=
  ⟨interpolatedWalk ε η m q, MatedCRT.continuous_interpolatedWalk ε m η q⟩

/-- Up to time `K`, the interpolated walk reads the lattice coordinates `q k` only for `k ≤ ⌊|m| K⌋₊ + 1`
(the floor of `m t` is monotone in `t`, Nat.floor_le_floor). -/
theorem interpolatedWalk_eq_of_agree (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) {K : ℝ} {q q' : ℕ → ℤ}
    (hqq : ∀ k : ℕ, k ≤ ⌊|m| * K⌋₊ + 1 → q k = q' k) {t : ℝ≥0} (ht : (t : ℝ) ≤ K) :
    interpolatedWalk ε η m q t = interpolatedWalk ε η m q' t := by
  have hn : ⌊m * (t : ℝ)⌋₊ ≤ ⌊|m| * K⌋₊ := by
    apply Nat.floor_le_floor
    calc m * (t : ℝ) ≤ |m| * (t : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self m) t.2
      _ ≤ |m| * K := mul_le_mul_of_nonneg_left ht (abs_nonneg m)
  unfold interpolatedWalk
  dsimp only
  rw [hqq _ (by omega), hqq (⌊m * (t : ℝ)⌋₊ + 1) (by omega)]

/-- Joint continuity in (lattice configuration, time) of the interpolated walk, for the product topology on `ℕ → ℤ`
(finitely many coordinates control the walk on each compact time interval). -/
theorem continuous_uncurry_interpolatedWalk (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) :
    Continuous (Function.uncurry fun (q : ℕ → ℤ) (t : ℝ≥0) => interpolatedWalk ε η m q t) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨q0, t0⟩
  set K : ℝ := (t0 : ℝ) + 1 with hK
  set N : ℕ := ⌊|m| * K⌋₊ + 1 with hN
  have hV : ∀ᶠ q in 𝓝 q0, ∀ k ∈ Finset.range (N + 1), q k = q0 k := by
    rw [Filter.eventually_all_finset]
    intro k _
    have hc : Continuous (fun q : ℕ → ℤ => q k) := continuous_apply k
    have hopen : IsOpen {q : ℕ → ℤ | q k = q0 k} := (isOpen_discrete ({q0 k} : Set ℤ)).preimage hc
    exact hopen.mem_nhds rfl
  have ht : ∀ᶠ t : ℝ≥0 in 𝓝 t0, (t : ℝ) ≤ K := by
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ) < K} :=
      isOpen_lt NNReal.continuous_coe continuous_const
    filter_upwards [hopen.mem_nhds (show (t0 : ℝ) < K by linarith)] with t ht'
    exact ht'.le
  have hG : ContinuousAt (fun p : (ℕ → ℤ) × ℝ≥0 => interpolatedWalk ε η m q0 p.2) (q0, t0) :=
    ((MatedCRT.continuous_interpolatedWalk ε m η q0).comp continuous_snd).continuousAt
  have hVp : ∀ᶠ p : (ℕ → ℤ) × ℝ≥0 in 𝓝 (q0, t0), ∀ k ∈ Finset.range (N + 1), p.1 k = q0 k :=
    (continuous_fst.tendsto (q0, t0)).eventually hV
  have htp : ∀ᶠ p : (ℕ → ℤ) × ℝ≥0 in 𝓝 (q0, t0), (p.2 : ℝ) ≤ K :=
    (continuous_snd.tendsto (q0, t0)).eventually ht
  refine hG.congr ?_
  filter_upwards [hVp, htp] with p hp1 hp2
  exact (interpolatedWalk_eq_of_agree ε η m (K := K) (q := p.1) (q' := q0) (fun k hk => hp1 k
    (Finset.mem_range.2 (by omega))) hp2).symm

/-- The path-valued interpolated walk `q ↦ interpolatedWalkC ε η m q` is continuous into `ContinuousPath ℂ`
(compact-open topology on `C(ℝ≥0, ℂ)`), hence Borel. No assumption on `η` is needed. -/
theorem continuous_interpolatedWalkC (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) :
    Continuous (interpolatedWalkC ε η m) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_uncurry_interpolatedWalk ε η m)

/-- Measurability of the path-valued interpolated walk on `ContinuousPath ℂ` (answer 46(a3), section 2). -/
theorem measurable_interpolatedWalkC (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) :
    Measurable (interpolatedWalkC ε η m) :=
  (continuous_interpolatedWalkC ε η m).measurable

/-- Measurability in the lattice configuration of the stopped occupation of the interpolated walk, on the
continuous-path carrier. Named `…C` because `MatedCRT.TruncatedLaws.measurable_stoppedOccupation_interpolatedWalk`
(Integrate.lean:112) already states the same walk-side measurability for the ball `ball z r` on `ℕ → ℤ`. -/
theorem measurable_stoppedOccupation_interpolatedWalkC {D : Set ℂ} (hD : IsOpen D) {g : ℂ → ℝ} (hg : Continuous g)
    (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) (T : ℝ) :
    Measurable (fun q : ℕ → ℤ => stoppedOccupationC D T g (interpolatedWalkC ε η m q)) :=
  (measurable_stoppedOccupationC hD hg T).comp (measurable_interpolatedWalkC ε η m)

#print axioms measurable_stoppedOccupationC
#print axioms measurable_interpolatedWalkC
#print axioms measurable_stoppedOccupation_interpolatedWalkC

end MatedCRT.TruncatedLaws
