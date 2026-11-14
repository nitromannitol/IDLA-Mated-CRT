import MatedCRT.FirstPass.Derived.MarkovTimeChangeTransfer
import MatedCRT.FirstPass.Derived.RevuzRegularize
import LatticeProb.Analysis.NNRatRightInfValues

/-!
# The half-clock of a Markovian time-changed planar Brownian motion is a positive continuous additive functional

For a family of measurable functionals `F_s` of the clock-read path with the shift identity of the inverse
crossing clock, the half-clock `A_t = F_{2t} / 2` of the planar Brownian path, regularized along the nonnegative
rationals (`MatedCRT.regularize`), is a positive continuous additive functional of planar Brownian motion
(`IsPCAF`).  This identifies the time change of the Markov process of Berestycki-Gwynne Proposition 7.10 as
the time change by a positive continuous additive functional.

* `rawClock F`: the raw half-clock `t ↦ (1/2) F_{2t} (halfRead ·)`, cut to `ℝ≥0`;
* `tset F s`, `rset F t s`: the sets of clock-read paths on which the right limit of the rational skeleton at
  `s` equals the raw value, resp. the raw additivity holds at `(t, s)`;
* `ae_shift_mem_tset`, `ae_mem_rset`: these hold almost surely for a measure with good inverse crossing clock
  and the shift identity;
* `isPCAF_regularize_rawClock`: the assembly of the fields `meas`, `adapted`, `path`, `add` of `IsPCAF`.
-/

open MeasureTheory MarkovProcess Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open PlanarBrownianSpace

/-- The raw half-clock: `t ↦ (1/2) F_{2t} (halfRead ω)`, negative values cut to `0`. -/
noncomputable def rawClock (F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ) (t : ℝ≥0)
    (ω : ContinuousPath ℂ) : ℝ≥0 :=
  Real.toNNReal (2⁻¹ * F (2 * t) (halfRead ω))

/-- The clock-read paths whose rational skeleton is nondecreasing and whose right limit at `s` along the
rationals is the raw value at `s`. -/
def tset (F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ) (s : ℝ≥0) :
    Set (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) :=
  {f | (∀ p q : ℚ≥0, p ≤ q → clockSkel F f p ≤ clockSkel F f q) ∧
    (⨅ q : {q : ℚ≥0 // s < (q : ℝ≥0)}, clockSkel F f q.1) = Real.toNNReal (2⁻¹ * F (2 * s) f)}

/-- The clock-read paths at which the raw additivity `A (t + s) = A t + A s ∘ θ_t` holds, with nonnegative
increments. -/
def rset (F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ) (t s : ℝ≥0) :
    Set (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) :=
  {f | 0 ≤ F (2 * t) f ∧ 0 ≤ F (2 * s) (fun q => f (2 * t + q)) ∧
    F (2 * (t + s)) f = F (2 * t) f + F (2 * s) (fun q => f (2 * t + q))}

theorem measurable_rawClock {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hF : ∀ s, Measurable (F s)) (t : ℝ≥0) : Measurable (rawClock F t) :=
  measurable_real_toNNReal.comp (((hF _).comp measurable_halfRead).const_mul _)

theorem measurableSet_tset {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hF : ∀ s, Measurable (F s)) (s : ℝ≥0) : MeasurableSet (tset F s) := by
  have hm : ∀ q : ℚ≥0, Measurable fun f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) => clockSkel F f q :=
    fun q => measurable_real_toNNReal.comp ((hF _).const_mul _)
  have h1 : MeasurableSet {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) |
      ∀ p q : ℚ≥0, p ≤ q → clockSkel F f p ≤ clockSkel F f q} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
      measurableSet_le (hm p) (hm q)
  have h2 : MeasurableSet {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) |
      (⨅ q : {q : ℚ≥0 // s < (q : ℝ≥0)}, clockSkel F f q.1) =
        Real.toNNReal (2⁻¹ * F (2 * s) f)} :=
    measurableSet_eq_fun (Measurable.iInf fun q => hm q.1)
      (measurable_real_toNNReal.comp ((hF _).const_mul _))
  exact h1.inter h2

theorem measurableSet_rset {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hF : ∀ s, Measurable (F s)) (t s : ℝ≥0) : MeasurableSet (rset F t s) := by
  have hsh : Measurable fun f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) => fun q => f (2 * t + q) :=
    measurable_pi_iff.2 fun q => measurable_pi_apply _
  have h1 : MeasurableSet {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) | 0 ≤ F (2 * t) f} :=
    measurableSet_le measurable_const (hF _)
  have h2 : MeasurableSet {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) | 0 ≤ F (2 * s) (fun q => f (2 * t + q))} :=
    measurableSet_le measurable_const ((hF _).comp hsh)
  have h3 : MeasurableSet {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) |
      F (2 * (t + s)) f = F (2 * t) f + F (2 * s) (fun q => f (2 * t + q))} :=
    measurableSet_eq_fun (hF _) ((hF _).add ((hF _).comp hsh))
  exact h1.inter (h2.inter h3)

/-- **Almost surely every shifted clock-read path has the right limit of its skeleton equal to the raw
value.**  For a measure `μ` on paths such that almost surely the crossing clock is good, and the shift identity
holds for the functionals `F`, almost surely, for every shift `T` and level `s`, the path
`q ↦ (clock-read path) (T + q)` lies in `tset F s`. -/
theorem ae_shift_mem_tset {μ : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))} {m : ℝ≥0∞}
    {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hgood : ∀ᵐ x ∂μ, LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hS : ∀ t s : ℝ≥0, ∀ᵐ x ∂μ, (LatticeProb.pathClockInv m x (t + s)).toReal =
      (LatticeProb.pathClockInv m x t).toReal +
        F s fun q => LatticeProb.clockPath m (fun u => x u) (t + q)) (T s : ℝ≥0) :
    ∀ᵐ x ∂μ, (fun q => LatticeProb.clockRead m x (T + q)) ∈ tset F s := by
  have hq : ∀ᵐ x ∂μ, ∀ q : ℚ≥0, (LatticeProb.pathClockInv m x (T + 2 * (q : ℝ≥0))).toReal =
      (LatticeProb.pathClockInv m x T).toReal +
        F (2 * (q : ℝ≥0)) fun r => LatticeProb.clockPath m (fun u => x u) (T + r) :=
    ae_all_iff.2 fun q => hS T (2 * (q : ℝ≥0))
  filter_upwards [hgood, hq, hS T (2 * s)] with x hg hx hxs
  have hAmono : Monotone fun u : ℝ≥0 => (LatticeProb.pathClockInv m x u).toReal :=
    fun u v h => NNReal.coe_le_coe.2 (hg.monotone_clockInv_toNNReal h)
  have hAcont : Continuous fun u : ℝ≥0 => (LatticeProb.pathClockInv m x u).toReal :=
    hg.continuous_clockInv_toReal (LatticeProb.crossClock_mono m _)
  set b : ℝ≥0 → ℝ := fun u => (LatticeProb.pathClockInv m x (T + u)).toReal -
    (LatticeProb.pathClockInv m x T).toReal with hb
  have hbm : Monotone b := fun u v h => sub_le_sub_right (hAmono (add_le_add le_rfl h)) _
  have hbc : Continuous b := (hAcont.comp (continuous_const.add continuous_id)).sub continuous_const
  set g : ℝ≥0 → ℝ≥0 := fun u => Real.toNNReal (2⁻¹ * b (2 * u)) with hg'
  have hgc : Continuous g :=
    continuous_real_toNNReal.comp
      (continuous_const.mul (hbc.comp (continuous_const.mul continuous_id)))
  have hgm : Monotone g := fun u v h =>
    Real.toNNReal_le_toNNReal
      (mul_le_mul_of_nonneg_left (hbm (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ≥0) ≤ 2)))
        (by norm_num : (0 : ℝ) ≤ 2⁻¹))
  have hsk : ∀ q : ℚ≥0, clockSkel F (fun r => LatticeProb.clockRead m x (T + r)) q = g q := by
    intro q
    have := hx q
    change clockSkel F (fun r => LatticeProb.clockPath m (fun u => x u) (T + r)) q = g q
    unfold clockSkel
    simp only [hg', hb]
    congr 2
    linarith
  have hs : Real.toNNReal (2⁻¹ * F (2 * s) fun r => LatticeProb.clockRead m x (T + r)) = g s := by
    change Real.toNNReal (2⁻¹ * F (2 * s) fun r => LatticeProb.clockPath m (fun u => x u) (T + r)) = g s
    simp only [hg', hb]
    congr 2
    linarith
  show _ ∧ _
  refine ⟨fun p q hpq => ?_, ?_⟩
  · rw [hsk p, hsk q]
    exact hgm (by exact_mod_cast hpq)
  · have hfun : (fun q : ℚ≥0 => clockSkel F (fun r => LatticeProb.clockRead m x (T + r)) q) =
        fun q : ℚ≥0 => g q := funext hsk
    have h1 : LatticeProb.nnratRightInf
        (fun q : ℚ≥0 => clockSkel F (fun r => LatticeProb.clockRead m x (T + r)) q) s = g s := by
      rw [hfun]
      exact LatticeProb.nnratRightInf_eq_of_continuous hgc hgm s
    exact h1.trans hs.symm

/-- **Almost surely the raw additivity holds at every pair `(t, s)`** (for each fixed pair), for a measure with
good inverse crossing clock and the shift identity. -/
theorem ae_mem_rset {μ : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))} {m : ℝ≥0∞}
    {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hgood : ∀ᵐ x ∂μ, LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hS : ∀ t s : ℝ≥0, ∀ᵐ x ∂μ, (LatticeProb.pathClockInv m x (t + s)).toReal =
      (LatticeProb.pathClockInv m x t).toReal +
        F s fun q => LatticeProb.clockPath m (fun u => x u) (t + q)) (t s : ℝ≥0) :
    ∀ᵐ x ∂μ, LatticeProb.clockRead m x ∈ rset F t s := by
  filter_upwards [hgood, hS 0 (2 * t), hS 0 (2 * (t + s)), hS (2 * t) (2 * s)] with x hg h1 h2 h3
  have hAmono : Monotone fun u : ℝ≥0 => (LatticeProb.pathClockInv m x u).toReal :=
    fun u v h => NNReal.coe_le_coe.2 (hg.monotone_clockInv_toNNReal h)
  have e0 : (fun q : ℝ≥0 => LatticeProb.clockPath m (fun u => x u) (0 + q)) =
      LatticeProb.clockRead m x := by
    funext q
    rw [zero_add]
    rfl
  rw [zero_add, e0] at h1 h2
  have h3' : (LatticeProb.pathClockInv m x (2 * t + 2 * s)).toReal =
      (LatticeProb.pathClockInv m x (2 * t)).toReal +
        F (2 * s) (fun q => LatticeProb.clockRead m x (2 * t + q)) := h3
  have h0 : (LatticeProb.pathClockInv m x 0).toReal ≤ (LatticeProb.pathClockInv m x (2 * t)).toReal :=
    hAmono (by positivity : (0 : ℝ≥0) ≤ 2 * t)
  have h4 : (LatticeProb.pathClockInv m x (2 * t)).toReal ≤
      (LatticeProb.pathClockInv m x (2 * t + 2 * s)).toReal :=
    hAmono (le_add_of_nonneg_right (by positivity : (0 : ℝ≥0) ≤ 2 * s))
  rw [mul_add] at h2
  show 0 ≤ F (2 * t) (LatticeProb.clockRead m x) ∧
    0 ≤ F (2 * s) (fun q => LatticeProb.clockRead m x (2 * t + q)) ∧
    F (2 * (t + s)) (LatticeProb.clockRead m x) = F (2 * t) (LatticeProb.clockRead m x) +
      F (2 * s) (fun q => LatticeProb.clockRead m x (2 * t + q))
  rw [mul_add]
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Along a path whose half-reading is in `tset F s`, the regularization of the raw half-clock at `s` is the raw
half-clock at `s`. -/
theorem regularize_rawClock_eq {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ} {ω : ContinuousPath ℂ}
    {s : ℝ≥0} (h : halfRead ω ∈ tset F s) : regularize (rawClock F) s ω = rawClock F s ω := by
  obtain ⟨h1, h2⟩ := h
  unfold regularize
  split_ifs with hc
  · exact h2
  · exact absurd (fun p q hpq => h1 p q hpq) hc

theorem halfRead_pathShift_zero (ω : ContinuousPath ℂ) :
    halfRead (LatticeProb.pathShift ω 0) = halfRead ω := by
  rw [halfRead_pathShift]
  funext u
  simp

/-- **The transfer of the almost-sure skeleton property to the planar Brownian path.** -/
theorem ae_halfRead_pathShift_mem_tset {μ : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))}
    {ν : Measure (ContinuousPath ℂ)} {m : ℝ≥0∞}
    {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ} (hF : ∀ s, Measurable (F s))
    (hmap : μ.map (LatticeProb.clockRead m) = ν.map halfRead)
    (hgood : ∀ᵐ x ∂μ, LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hS : ∀ t s : ℝ≥0, ∀ᵐ x ∂μ, (LatticeProb.pathClockInv m x (t + s)).toReal =
      (LatticeProb.pathClockInv m x t).toReal +
        F s fun q => LatticeProb.clockPath m (fun u => x u) (t + q)) (t s : ℝ≥0) :
    ∀ᵐ w ∂ν, halfRead (LatticeProb.pathShift w t) ∈ tset F s := by
  have hset : MeasurableSet
      {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) | (fun q => f (2 * t + q)) ∈ tset F s} :=
    (measurableSet_tset hF s).preimage (measurable_pi_iff.2 fun q => measurable_pi_apply _)
  have h := ae_shift_mem_tset hgood hS (2 * t) s
  filter_upwards [ae_halfRead_mem_of_ae_clockRead hmap hset h] with w hw
  rw [halfRead_pathShift]
  exact hw

/-- **The transfer of the almost-sure raw additivity to the planar Brownian path.** -/
theorem ae_halfRead_mem_rset {μ : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))}
    {ν : Measure (ContinuousPath ℂ)} {m : ℝ≥0∞}
    {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ} (hF : ∀ s, Measurable (F s))
    (hmap : μ.map (LatticeProb.clockRead m) = ν.map halfRead)
    (hgood : ∀ᵐ x ∂μ, LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hS : ∀ t s : ℝ≥0, ∀ᵐ x ∂μ, (LatticeProb.pathClockInv m x (t + s)).toReal =
      (LatticeProb.pathClockInv m x t).toReal +
        F s fun q => LatticeProb.clockPath m (fun u => x u) (t + q)) (t s : ℝ≥0) :
    ∀ᵐ w ∂ν, halfRead w ∈ rset F t s :=
  ae_halfRead_mem_of_ae_clockRead hmap (measurableSet_rset hF t s) (ae_mem_rset hgood hS t s)

/-- **The regularized half-clock is a positive continuous additive functional.**  The hypotheses are the
almost-sure properties of the half-reading of the planar path established above (`hgood`, `htset`, `hrset`),
and the adaptedness of `F_s ∘ halfRead`. -/
theorem isPCAF_regularize_rawClock {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hF : ∀ s, Measurable (F s))
    (hgood : ∀ z (t : ℝ≥0), ∀ᵐ w ∂planarLaw z, halfRead (LatticeProb.pathShift w t) ∈ clockGoodSet F)
    (htset : ∀ z (t s : ℝ≥0), ∀ᵐ w ∂planarLaw z, halfRead (LatticeProb.pathShift w t) ∈ tset F s)
    (hrset : ∀ z (t s : ℝ≥0), ∀ᵐ w ∂planarLaw z, halfRead w ∈ rset F t s)
    (hadapt : ∀ z (s : ℝ≥0), ∃ g : ContinuousPath ℂ → ℝ≥0, Measurable[pathFiltration (2⁻¹ * s)] g ∧
      (fun ω => Real.toNNReal (F s (halfRead ω))) =ᵐ[planarLaw z] g) :
    IsPCAF planarLaw (regularize (rawClock F)) := by
  have hreg : ∀ z (t : ℝ≥0), ∀ᵐ w ∂planarLaw z, regularize (rawClock F) t w = rawClock F t w := by
    intro z t
    filter_upwards [htset z 0 t] with w hw
    rw [halfRead_pathShift_zero] at hw
    exact regularize_rawClock_eq hw
  refine ⟨fun t => measurable_regularize (measurable_rawClock hF) t, ?_, ?_, ?_⟩
  · intro z t
    obtain ⟨g, hg, hae⟩ := hadapt z (2 * t)
    have e : (2⁻¹ : ℝ≥0) * (2 * t) = t := by
      rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
    rw [e] at hg
    refine ⟨fun w => Real.toNNReal 2⁻¹ * g w, hg.const_mul _, ?_⟩
    filter_upwards [hreg z t, hae] with w h1 h3
    have h3' : Real.toNNReal (F (2 * t) (halfRead w)) = g w := h3
    rw [h1]
    unfold rawClock
    rw [Real.toNNReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹), h3']
  · intro z
    filter_upwards [hgood z 0] with w hw
    rw [halfRead_pathShift_zero] at hw
    obtain ⟨h0, hmono, hmod⟩ := hw
    have hmono' : Monotone (clockSkel F (halfRead w)) := fun p q hpq => hmono p q hpq
    have hfun : ∀ t, regularize (rawClock F) t w =
        LatticeProb.nnratRightInf (clockSkel F (halfRead w)) t := by
      intro t
      unfold regularize
      split_ifs with hc
      · rfl
      · exact absurd (fun p q hpq => hmono p q hpq) hc
    refine ⟨?_, ?_, ?_⟩
    · rw [hfun]
      have := LatticeProb.nnratRightInf_nnrat (clockSkel F (halfRead w)) hmono' hmod 0
      simpa [h0] using this
    · have hc := LatticeProb.continuous_nnratRightInf (clockSkel F (halfRead w)) hmono' hmod
      simpa only [hfun] using hc
    · exact regularize_monotone (rawClock F) w
  · intro z s t
    filter_upwards [hrset z t s, hreg z (t + s), hreg z t, htset z t s] with w h1 h2 h3 h4
    have h5 : regularize (rawClock F) s (LatticeProb.pathShift w t) =
        rawClock F s (LatticeProb.pathShift w t) := regularize_rawClock_eq h4
    rw [h2, h3, h5]
    obtain ⟨a1, a2, a3⟩ := h1
    unfold rawClock
    rw [halfRead_pathShift, a3, mul_add,
      Real.toNNReal_add (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) a1)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) a2)]

end MatedCRT
