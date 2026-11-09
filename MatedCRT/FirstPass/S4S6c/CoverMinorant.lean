import MatedCRT.Draft.Section6

/-!
# Lemma 2, eq (9): a dense-centre minorant of the good-annulus cover (q2, task fp-S4S6c; LEMMA68 gap G9)

`IsGoodAnnulusEvent μ c r z` (Defs/Setting.lean:333) compares the supremum over the open annulus `A = HarmonicBalls.annulus z r (2r)` of the
log potential `v ↦ ∫⁻_A (log (r/|u-v|) + 1)^+ dμ(u)` with `C` times the infimum over `A` of the ball masses `μ(B(w, c r))`.
Two deterministic facts reduce this to countably many centres, at the cost of halving the radius in the ball masses:

* `logKernel_liminf_ge`, `lintegral_annulus_le_dense`: the log potential is lower semicontinuous in its centre (Fatou; the
  diagonal value `1` of the Lean convention `log 0 = 0` is below the liminf), so its supremum over `A` is attained on a
  countable dense subset `D ∩ A` (`D` dense in `ℂ`).
* `good_of_dense`: for `w ∈ A`, the open set `A ∩ B(w, c₀ r / 2)` meets `D`, and `B(q, c₀ r / 2) ⊆ B(w, c₀ r)`; so the dense
  event with radius `c₀ / 2` and constant `C` implies `IsGoodAnnulusEvent μ c₀ C r z`.
* `dense_of_good`: conversely, `IsGoodAnnulusEvent μ c' C r z` implies the dense event with radius `c'`, since `D ∩ A ⊆ A`.

Hence the dense event at radius `c₀/2` lies between the printed cover at radius `c₀` and the `GoodAnnulusPrevalenceStmt`
event at radius `c₀/2`, and so inherits its polynomial failure bound.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRT

namespace CoverMinorant

/-- Lower semicontinuity of the log kernel of `IsGoodAnnulusEvent` in its centre: the value at `u` is at most the liminf of the
values at any sequence `d k → v`. -/
theorem logKernel_liminf_ge {r : ℝ} (hr : 0 < r) {d : ℕ → ℂ} {v u : ℂ} (hd : Tendsto d atTop (𝓝 v)) :
    ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ≤
      liminf (fun k => ENNReal.ofReal (Real.log (r / ‖u - d k‖) + 1)) atTop := by
  by_cases huv : v = u
  · subst huv
    have hev : ∀ᶠ k in atTop, ‖v - d k‖ < r := by
      have h0 : Tendsto (fun k => ‖v - d k‖) atTop (𝓝 ‖v - v‖) := (tendsto_const_nhds.sub hd).norm
      rw [sub_self, norm_zero] at h0
      exact h0.eventually (gt_mem_nhds hr)
    have h1 : (1 : ℝ≥0∞) ≤ liminf (fun k => ENNReal.ofReal (Real.log (r / ‖v - d k‖) + 1)) atTop := by
      refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hev] with k hk
      rcases eq_or_ne (‖v - d k‖) 0 with h0 | h0
      · rw [h0, div_zero, Real.log_zero, zero_add, ENNReal.ofReal_one]
      · apply ENNReal.one_le_ofReal.2
        have := Real.log_nonneg ((one_le_div (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))).2 hk.le)
        linarith
    simpa [sub_self, norm_zero, div_zero, Real.log_zero] using h1
  · have hne : u - v ≠ 0 := sub_ne_zero.2 (Ne.symm huv)
    have hnorm : ‖u - v‖ ≠ 0 := norm_ne_zero_iff.2 hne
    have hg1 : ContinuousAt (fun t : ℝ => Real.log (r / t) + 1) ‖u - v‖ :=
      ((continuousAt_const.div continuousAt_id hnorm).log (div_ne_zero hr.ne' hnorm)).add continuousAt_const
    have hg : ContinuousAt (fun t : ℝ => ENNReal.ofReal (Real.log (r / t) + 1)) ‖u - v‖ :=
      ENNReal.continuous_ofReal.continuousAt.comp hg1
    have ht : Tendsto (fun k => ‖u - d k‖) atTop (𝓝 ‖u - v‖) := (tendsto_const_nhds.sub hd).norm
    have hT := hg.tendsto.comp ht
    exact le_of_eq hT.liminf_eq.symm

/-- The supremum over the annulus of the log potential is at most its supremum over a dense subset of the annulus
(Fatou for the lower semicontinuous log kernel, `logKernel_liminf_ge`). -/
theorem lintegral_annulus_le_dense {D A : Set ℂ} (hD : Dense D) (hA : IsOpen A) {r : ℝ} (hr : 0 < r)
    (ν : Measure ℂ) {v : ℂ} (hv : v ∈ A) :
    ∫⁻ u in A, ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂ν ≤
      ⨆ d ∈ D ∩ A, ∫⁻ u in A, ENNReal.ofReal (Real.log (r / ‖u - d‖) + 1) ∂ν := by
  have hex : ∀ k : ℕ, ∃ d ∈ D ∩ A, dist d v < 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨d, hdD, hdU⟩ := hD.exists_mem_open (hA.inter isOpen_ball) ⟨v, hv, mem_ball_self hpos⟩
    exact ⟨d, ⟨hdD, hdU.1⟩, mem_ball.1 hdU.2⟩
  choose d hdmem hdist using hex
  have hdt : Tendsto d atTop (𝓝 v) :=
    tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero (fun k => dist_nonneg) (fun k => (hdist k).le) tendsto_one_div_add_atTop_nhds_zero_nat)
  have hmeas : ∀ k : ℕ, Measurable fun u : ℂ => ENNReal.ofReal (Real.log (r / ‖u - d k‖) + 1) := fun k =>
    ((measurable_const.div ((measurable_id.sub measurable_const).norm)).log.add_const 1).ennreal_ofReal
  calc ∫⁻ u in A, ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂ν
      ≤ ∫⁻ u in A, liminf (fun k => ENNReal.ofReal (Real.log (r / ‖u - d k‖) + 1)) atTop ∂ν :=
        lintegral_mono fun u => logKernel_liminf_ge hr hdt
    _ ≤ liminf (fun k => ∫⁻ u in A, ENNReal.ofReal (Real.log (r / ‖u - d k‖) + 1) ∂ν) atTop :=
        lintegral_liminf_le hmeas
    _ ≤ ⨆ d ∈ D ∩ A, ∫⁻ u in A, ENNReal.ofReal (Real.log (r / ‖u - d‖) + 1) ∂ν :=
        le_trans (Filter.liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault))
          (Filter.limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun k =>
            le_iSup₂ (f := fun d (_ : d ∈ D ∩ A) => ∫⁻ u in A, ENNReal.ofReal (Real.log (r / ‖u - d‖) + 1) ∂ν)
              (d k) (hdmem k)))

/-- **Dense-centre sufficient condition** (eq (9) minorant, deterministic): the supremum over the dense subset of the annulus,
with the ball masses of radius `c₀/2 · r` at dense centres, implies `IsGoodAnnulusEvent μ c₀ C r z`. -/
theorem good_of_dense {D : Set ℂ} (hD : Dense D) {z : ℂ} {r c₀ C : ℝ} (hr : 0 < r) (hc₀ : 0 < c₀) (μ : Measure ℂ)
    (h : (⨆ d ∈ D ∩ HarmonicBalls.annulus z r (2 * r),
        ∫⁻ u in HarmonicBalls.annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - d‖) + 1) ∂μ) ≤
      ENNReal.ofReal C * ⨅ q ∈ D ∩ HarmonicBalls.annulus z r (2 * r), μ (ball q (c₀ / 2 * r))) :
    IsGoodAnnulusEvent μ c₀ C r z := by
  unfold IsGoodAnnulusEvent
  have hA : IsOpen (HarmonicBalls.annulus z r (2 * r)) := isOpen_ball.sdiff isClosed_closedBall
  refine le_trans (iSup₂_le fun v hv => lintegral_annulus_le_dense hD hA hr μ hv) (h.trans ?_)
  refine mul_le_mul_of_nonneg_left (le_iInf₂ fun w hw => ?_) (by positivity)
  have hpos : (0 : ℝ) < c₀ / 2 * r := by positivity
  obtain ⟨q, hqD, hqU⟩ := hD.exists_mem_open (hA.inter (isOpen_ball (x := w) (ε := c₀ / 2 * r)))
    ⟨w, hw, mem_ball_self hpos⟩
  refine (iInf₂_le q ⟨hqD, hqU.1⟩).trans (measure_mono ?_)
  intro x hx
  have h2 : dist q w < c₀ / 2 * r := mem_ball.1 hqU.2
  rw [mem_ball] at hx ⊢
  have h1 := dist_triangle x q w
  linarith

/-- **Dense-centre necessary consequence** (deterministic): `IsGoodAnnulusEvent μ c' C r z` implies the dense event at radius
`c'`, since the dense centres lie in the annulus. -/
theorem dense_of_good {D : Set ℂ} {z : ℂ} {r c C : ℝ} (μ : Measure ℂ)
    (h : IsGoodAnnulusEvent μ c C r z) :
    (⨆ d ∈ D ∩ HarmonicBalls.annulus z r (2 * r),
        ∫⁻ u in HarmonicBalls.annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - d‖) + 1) ∂μ) ≤
      ENNReal.ofReal C * ⨅ q ∈ D ∩ HarmonicBalls.annulus z r (2 * r), μ (ball q (c * r)) := by
  unfold IsGoodAnnulusEvent at h
  refine le_trans (iSup₂_le fun d hd => le_iSup₂
    (f := fun v (_ : v ∈ HarmonicBalls.annulus z r (2 * r)) =>
      ∫⁻ u in HarmonicBalls.annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂μ) d hd.2) (h.trans ?_)
  exact mul_le_mul_of_nonneg_left (le_iInf₂ fun q hq => iInf₂_le q hq.2) (by positivity)

end CoverMinorant

end MatedCRT

#print axioms MatedCRT.CoverMinorant.logKernel_liminf_ge
#print axioms MatedCRT.CoverMinorant.lintegral_annulus_le_dense
#print axioms MatedCRT.CoverMinorant.good_of_dense
#print axioms MatedCRT.CoverMinorant.dense_of_good
