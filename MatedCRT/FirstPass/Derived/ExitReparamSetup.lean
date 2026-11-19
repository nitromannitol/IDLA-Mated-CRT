import MatedCRT.FirstPass.Derived.ExitReparamClass
import MatedCRT.Proofs.LBM.BrownianExitBall

/-!
# Set-up facts for the exact-reparametrization argument

Three elementary pieces used to identify a path law `P` with a time change of planar Brownian
motion once the stopped curve classes of `P` and of Brownian motion have the same laws at a
sequence of radii:

* `exists_radii_seq`: from an almost-everywhere statement in the radius one extracts a strictly
  increasing sequence of good radii tending to infinity, the `k`-th in `(c + k, c + k + 1)`;
* `planarBrownianMotion_noFlat`: planar Brownian motion almost surely has no interval of
  constancy;
* `ae_pathExitTime_lt_top_of_map_eq`: if the law of the stopped curve class at exit from the ball
  of radius `r > ‖z‖` is the Brownian one, then almost every path leaves the ball.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
  LatticeProb LatticeProb.CurveSpaceComparison
open scoped ENNReal NNReal

namespace MatedCRT.ExitReparamSetup

/-- A strictly increasing sequence of good radii tending to infinity, the `k`-th in
`(c + k, c + k + 1)`. -/
theorem exists_radii_seq {c : ℝ} {p : ℝ → Prop}
    (h : ∀ᵐ r ∂(volume : Measure ℝ), c < r → p r) :
    ∃ r : ℕ → ℝ, StrictMono r ∧ c < r 0 ∧ Tendsto r atTop atTop ∧ ∀ k, p (r k) := by
  have hk : ∀ k : ℕ, ∃ x ∈ Ioo (c + k) (c + k + 1), p x := by
    intro k
    have hne : (volume.restrict (Ioo (c + k) (c + k + 1)) : Measure ℝ) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero]
      simp
    have : (ae (volume.restrict (Ioo (c + k) (c + k + 1)))).NeBot := ae_neBot.2 hne
    have h1 := ae_restrict_of_ae (s := Ioo (c + k) (c + k + 1)) h
    have h2 := ae_restrict_mem (μ := (volume : Measure ℝ))
      (measurableSet_Ioo (a := c + k) (b := c + k + 1))
    obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
    exact ⟨x, hx2, hx1 (by linarith [hx2.1, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])⟩
  choose r hr hp using hk
  refine ⟨r, ?_, ?_, ?_, hp⟩
  · refine strictMono_nat_of_lt_succ fun k => ?_
    have h1 := (hr k).2
    have h2 := (hr (k + 1)).1
    push_cast at h2
    linarith
  · simpa using (hr 0).1
  · exact tendsto_atTop_mono (fun k => (hr k).1.le)
      (tendsto_atTop_add_const_left _ c tendsto_natCast_atTop_atTop)

/-- Planar Brownian motion has almost surely no interval of constancy. -/
theorem planarBrownianMotion_noFlat (z : ℂ) :
    planarBrownianMotion z
      {f : ContinuousPath ℂ | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s} = 0 := by
  let D : ℕ → ℝ≥0 := TopologicalSpace.denseSeq ℝ≥0
  have hD : Dense (range D) := TopologicalSpace.denseRange_denseSeq ℝ≥0
  have hnull : ∀ p : ℕ × ℕ, planarBrownianMotion z
      {f : ContinuousPath ℂ | D p.1 < D p.2 ∧ (f (D p.2)).re = (f (D p.1)).re} = 0 := by
    intro p
    by_cases hlt : D p.1 < D p.2
    · have hv : D p.2 - D p.1 ≠ 0 := (tsub_pos_of_lt hlt).ne'
      have hre : AEMeasurable (fun ω : ContinuousPath ℂ => (reImPath ω).1) (planarBrownianMotion z) :=
        (measurable_fst.comp measurable_reImPath).aemeasurable
      have hincr : AEMeasurable (fun ω : ContinuousPath ℝ => ω (D p.2) - ω (D p.1))
          (brownianMotion z.re) :=
        ((ContinuousPath.measurable_coordinateProcess (D p.2)).sub
          (ContinuousPath.measurable_coordinateProcess (D p.1))).aemeasurable
      refine le_antisymm ?_ bot_le
      calc planarBrownianMotion z {f : ContinuousPath ℂ | D p.1 < D p.2 ∧
              (f (D p.2)).re = (f (D p.1)).re}
          ≤ planarBrownianMotion z ((fun ω : ContinuousPath ℂ => (reImPath ω).1) ⁻¹'
              {ω' : ContinuousPath ℝ | ω' (D p.2) - ω' (D p.1) = 0}) := by
            refine measure_mono fun f hf => ?_
            simp only [mem_preimage, mem_ofPred_eq, reImPath_fst_apply]
            exact sub_eq_zero.2 hf.2
        _ ≤ (brownianMotion z.re) {ω' : ContinuousPath ℝ | ω' (D p.2) - ω' (D p.1) = 0} := by
            rw [← planarBrownianMotion_map_re z]
            exact Measure.le_map_apply hre _
        _ ≤ ((brownianMotion z.re).map (fun ω : ContinuousPath ℝ => ω (D p.2) - ω (D p.1))) {0} :=
            Measure.le_map_apply hincr {0}
        _ = 0 := by
            rw [brownianMotion_map_increment z.re _ _ hlt.le]
            exact gaussianReal_absolutelyContinuous 0 hv Real.volume_singleton
    · have : {f : ContinuousPath ℂ | D p.1 < D p.2 ∧ (f (D p.2)).re = (f (D p.1)).re} = ∅ := by
        ext f
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hlt
      rw [this, measure_empty]
  refine measure_mono_null (fun f hf => ?_) (measure_iUnion_null hnull)
  obtain ⟨s, t, hst, hconst⟩ := hf
  obtain ⟨_, ⟨m, rfl⟩, hm⟩ := hD.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 hst)
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hD.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 hm.2)
  refine mem_iUnion.2 ⟨(m, n), hn.1, ?_⟩
  rw [hconst _ (hm.1.le.trans hn.1.le) hn.2.le, hconst _ hm.1.le hm.2.le]

/-- The endpoint of the Euclidean curve class of a prefix is the value of the path at the
duration (the same statement as `LatticeProb.normalizedPrefixCurve_endPoint`, read in the source
curve space). -/
theorem endPoint_isometryEquiv (q : LatticeProb.CurveSpace 2) :
    BouRabeeGwynne.CurveSpace.endPoint (isometryEquiv 2 q) = LatticeProb.CurveSpace.endPoint q := by
  obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk q
  rfl

/-- The endpoint of the stopped exit curve is the value of the path at its exit time (at time `0`
if it never exits), in Euclidean coordinates. -/
theorem endPoint_stoppedExitCurve (U : Set ℂ) (b : ContinuousPath ℂ) :
    BouRabeeGwynne.CurveSpace.endPoint (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve U b) =
      Complex.orthonormalBasisOneI.repr (b (pathExitTime U b).toNNReal) := by
  unfold MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve
  rw [endPoint_isometryEquiv, normalizedPrefixCurve_endPoint]
  rfl

/-- A continuous path that starts in the open ball of radius `r` and leaves it does so on the
sphere: the exit point has norm `r`. -/
theorem norm_exit_point_eq {r : ℝ} {f : ContinuousPath ℂ} (h0 : ‖f 0‖ < r)
    (hlt : pathExitTime (ball (0 : ℂ) r) f < ⊤) :
    ‖f (pathExitTime (ball (0 : ℂ) r) f).toNNReal‖ = r := by
  obtain ⟨m, hm, hfm⟩ := MatedCRT.M0Cdf.exists_exit_eq isOpen_ball f hlt
  rw [hm, ENNReal.toNNReal_coe]
  have hge : r ≤ ‖f m‖ := by
    simpa only [mem_ball_zero_iff, not_lt] using hfm
  refine le_antisymm ?_ hge
  rcases eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    exact absurd h0 (not_lt.2 hge)
  · have hcl : IsClosed {t : ℝ≥0 | ‖f t‖ ≤ r} :=
      isClosed_le (continuous_norm.comp f.continuous) continuous_const
    have hsub : Iio m ⊆ {t : ℝ≥0 | ‖f t‖ ≤ r} := fun t ht => by
      have hmem : f t ∈ ball (0 : ℂ) r := by
        by_contra hn
        have h1 := MatedCRT.M0Cdf.pathExitTime_le_of_not_mem hn
        rw [hm] at h1
        exact absurd (ENNReal.coe_le_coe.1 h1) (not_le.2 ht)
      exact (mem_ball_zero_iff.1 hmem).le
    have hcm : m ∈ closure (Iio m) := by
      rw [closure_Iio' (a := m) ⟨0, hm0⟩]
      exact Set.mem_Iic.2 le_rfl
    exact closure_minimal hsub hcl hcm

/-- If the stopped curve class at exit from the ball of radius `r > ‖z‖` has under `P` the law it
has under planar Brownian motion from `z`, then `P`-almost every path leaves the ball. -/
theorem ae_pathExitTime_lt_top_of_map_eq {z : ℂ} {r : ℝ} (hr : ‖z‖ < r)
    {P : Measure (ContinuousPath ℂ)}
    (hb : P.map (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) =
      (planarBrownianMotion z).map
        (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r))) :
    ∀ᵐ f : ContinuousPath ℂ ∂P, pathExitTime (ball (0 : ℂ) r) f < ⊤ := by
  set c := MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r) with hc
  have hcm : Measurable c := MatedCRT.StopAtExitLevyProkhorov.measurable_stoppedExitCurve _
    isOpen_ball
  set E : Set (BouRabeeGwynne.CurveSpace 2) :=
    {q | ‖BouRabeeGwynne.CurveSpace.endPoint q‖ = r} with hE
  have hEm : MeasurableSet E :=
    (isClosed_eq (continuous_norm.comp BouRabeeGwynne.CurveSpace.continuous_endPoint)
      continuous_const).measurableSet
  have hW : ∀ᵐ f ∂(planarBrownianMotion z), c f ∈ E := by
    filter_upwards [ae_planarBrownianMotion_eval_zero z,
      ae_planarBrownianMotion_exit_any_ball_lt_top z 0 r] with f hf0 hfin
    have hlt : pathExitTime (ball (0 : ℂ) r) f < ⊤ := by
      obtain ⟨t, ht⟩ := (ContinuousPath.exitTime_lt_top_iff _ _).1 hfin
      exact lt_of_le_of_lt (MatedCRT.M0Cdf.pathExitTime_le_of_not_mem ht) ENNReal.coe_lt_top
    show ‖BouRabeeGwynne.CurveSpace.endPoint (c f)‖ = r
    rw [hc, endPoint_stoppedExitCurve, LinearIsometryEquiv.norm_map]
    exact norm_exit_point_eq (by rw [hf0]; exact hr) hlt
  have hP : ∀ᵐ f ∂P, c f ∈ E := by
    have h1 : (P.map c) Eᶜ = 0 := by
      rw [hb, Measure.map_apply hcm hEm.compl]
      exact ae_iff.1 hW
    rw [Measure.map_apply hcm hEm.compl] at h1
    exact ae_iff.2 h1
  filter_upwards [hP] with f hf
  by_contra hnot
  have htop : pathExitTime (ball (0 : ℂ) r) f = ⊤ := not_lt_top_iff.1 hnot
  have hin : ∀ t : ℝ≥0, f t ∈ ball (0 : ℂ) r := fun t => by
    by_contra hn
    have := MatedCRT.M0Cdf.pathExitTime_le_of_not_mem hn
    rw [htop] at this
    exact absurd this (not_le.2 ENNReal.coe_lt_top)
  have hf' : ‖BouRabeeGwynne.CurveSpace.endPoint (c f)‖ = r := hf
  rw [hc, endPoint_stoppedExitCurve, LinearIsometryEquiv.norm_map, htop,
    ENNReal.toNNReal_top] at hf'
  have := mem_ball_zero_iff.1 (hin 0)
  linarith

end MatedCRT.ExitReparamSetup
