import MatedCRT.FirstPass.Derived.WindowChartBGJointConvergence
import HarmonicBalls.Proofs.Sec6.ShrinkingBrownianExit
import LatticeProb.Topology.EmbeddedClosedDiskExterior
import LatticeProb.Topology.PlanarInvarianceOfDomain

/-!
# Exterior regularity of the windows of Berestycki–Gwynne (2020), Lemma 7.21

This file proves `JordanDomainExteriorRegularity`: planar Brownian motion started at a frontier point `y` of a bounded
window `U` with an inverse chart leaves `closure U` at once. The only analytic input is the Beurling estimate for planar
Brownian motion (`BrownianBeurlingEstimate`; Lawler, *Conformally Invariant Processes in the Plane*, Theorem 3.76).

* **The exterior domain.** The inverse chart `ψ` maps `closure U = U ∪ ∂U` continuously and injectively onto the closed
  unit disc, hence homeomorphically. The complement `E` of an embedded closed disc is connected and unbounded
  (Jordan curve theorem; `LatticeProb.complex_embedded_closed_disk_compl_preconnected_unbounded`), hence path connected
  as an open set. Every frontier point `y` of `U` lies in `closure E`: otherwise `y` is interior to `closure U`, and by
  invariance of domain `ψ` maps a neighbourhood of `y` onto an open subset of the closed disc containing the point
  `ψ y` of the unit circle.
* **Brownian motion meets the exterior at once.** For `r_n = 2^{-(n+1)}` take `w_n ∈ E` with `|y - w_n| < r_n^3` and a
  path `γ_n` in `E` from `w_n` to a point at distance at least `r_n` from `w_n`. By the Beurling estimate, Brownian
  motion from `y` leaves `B(w_n, r_n)` before hitting `γ_n` with probability at most `C r_n`, so almost surely it hits
  `γ_n` before leaving `B(w_n, r_n) ⊆ B(y, 2 r_n)` for infinitely many `n`. Since the exit times of `B(y, 2 r_n)` tend to
  `0` almost surely, the exit time of `closure U ⊆ γ_nᶜ` is `0`.

## Main statements

* `MatedCRT.BrownianBeurlingEstimate`: the Beurling estimate for planar Brownian motion, proved as
  `MatedCRT.BrownianBeurling.brownianBeurlingEstimate` (`BrownianBeurling/BrownianBeurlingEstimateProof.lean`).
* `MatedCRT.IsInverseChart.frontier_subset_closure_compl_closure`: the exterior of a bounded window is open, path
  connected and unbounded, and its closure contains the frontier of the window.
* `MatedCRT.ae_exitTime_eq_zero_of_mem_closure_compl`: instant exit at a point of the closure of a path connected
  unbounded complement.
* `MatedCRT.jordanDomainExteriorRegularity`: `JordanDomainExteriorRegularity` from the Beurling estimate.
* `MatedCRT.bg20WindowJointConvergenceInput_proved`: `BG20WindowJointConvergenceInput 𝒮` from the Beurling estimate.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

/-! ### The named input -/

/-- **The Beurling estimate for planar Brownian motion.** There is a constant `C ≥ 0` such that for every curve `γ`
from `w = γ 0` to a point `γ 1` at distance at least `R` from `w`, planar Brownian motion started at `y` with
`|y - w| < R` leaves the disc `B(w, R)` before hitting `γ` with probability at most `C (|y - w| / R)^{1/2}`.

Source: Lawler, *Conformally Invariant Processes in the Plane*, AMS 2005, Theorem 3.76 (after translation by `w` and
scaling by `R`; the curve may be stopped at its first visit to the circle `∂B(w, R)`, which only enlarges the event);
Lawler–Limic (arXiv:math/0403309), Section 1. It is proved as `MatedCRT.BrownianBeurling.brownianBeurlingEstimate`
(`BrownianBeurling/BrownianBeurlingEstimateProof.lean`), from the analytic Beurling estimate for harmonic majorants of
Lattice-Probability. -/
def BrownianBeurlingEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : C(unitInterval, ℂ)) (y : ℂ) (R : ℝ), R ≤ dist (γ 1) (γ 0) →
    dist y (γ 0) < R →
    planarBrownianMotion y
        {b | ContinuousPath.exitTime (ball (γ 0) R) b < ContinuousPath.exitTime (range γ)ᶜ b} ≤
      ENNReal.ofReal (C * Real.sqrt (dist y (γ 0) / R))

/-! ### The exterior of a window -/

/-- An inverse chart maps the closure of its window onto the closed unit disc. -/
theorem IsInverseChart.image_closure_eq_closedBall {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}
    (h : IsInverseChart U z ψ) : ψ '' closure U = closedBall 0 1 := by
  rw [closure_eq_self_union_frontier, image_union, h.image_eq, h.image_frontier, ball_union_sphere]

/-- The closure of a bounded window is an embedded closed disc. -/
theorem IsInverseChart.nonempty_homeomorph_closure {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}
    (hb : Bornology.IsBounded U) (h : IsInverseChart U z ψ) :
    Nonempty (closedBall (0 : ℂ) 1 ≃ₜ closure U) := by
  have : CompactSpace (closure U) := isCompact_iff_compactSpace.mp hb.isCompact_closure
  have hmem : ∀ x ∈ closure U, ψ x ∈ closedBall (0 : ℂ) 1 := fun x hx => by
    rw [← h.image_closure_eq_closedBall]
    exact mem_image_of_mem ψ hx
  let f : closure U → closedBall (0 : ℂ) 1 := fun x => ⟨ψ x, hmem x x.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x x' hxx' => Subtype.ext (h.injOn x.2 x'.2 (congrArg Subtype.val hxx')), ?_⟩
    intro p
    have hp : (p : ℂ) ∈ ψ '' closure U := by
      rw [h.image_closure_eq_closedBall]
      exact p.2
    obtain ⟨x, hx, hxp⟩ := hp
    exact ⟨⟨x, hx⟩, Subtype.ext hxp⟩
  have hcont : Continuous f := (ψ.continuous.comp continuous_subtype_val).subtype_mk _
  exact ⟨(Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf) hcont).symm⟩

/-- **The exterior of a bounded window.** The complement of the closure of a bounded window with an inverse chart is
open, path connected and unbounded, and its closure contains the frontier of the window. -/
theorem IsInverseChart.frontier_subset_closure_compl_closure {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}
    (hb : Bornology.IsBounded U) (h : IsInverseChart U z ψ) :
    IsOpen (closure U)ᶜ ∧ IsPathConnected (closure U)ᶜ ∧ ¬ Bornology.IsBounded (closure U)ᶜ ∧
      frontier U ⊆ closure (closure U)ᶜ := by
  obtain ⟨e⟩ := h.nonempty_homeomorph_closure hb
  obtain ⟨hpre, hunb⟩ := LatticeProb.complex_embedded_closed_disk_compl_preconnected_unbounded e
  have hopen : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
  have hne : ((closure U)ᶜ).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    exact hunb (hne ▸ Bornology.isBounded_empty)
  refine ⟨hopen, hopen.isConnected_iff_isPathConnected.mp ⟨hne, hpre⟩, hunb, ?_⟩
  intro y hy
  rw [closure_compl]
  intro hint
  have hO : IsOpen (ψ '' interior (closure U)) :=
    LatticeProb.isOpen_image_of_continuousOn_injOn isOpen_interior ψ.continuous.continuousOn
      (h.injOn.mono interior_subset)
  have hsub : ψ '' interior (closure U) ⊆ ball (0 : ℂ) 1 := by
    rw [← interior_closedBall (0 : ℂ) one_ne_zero]
    exact interior_maximal ((image_mono interior_subset).trans h.image_closure_eq_closedBall.subset) hO
  exact h.mapsTo_frontier hy (hsub (mem_image_of_mem ψ hint))

/-! ### Instant exit -/

/-- **Brownian motion meets a path connected unbounded exterior at once.** If the complement of `F` is path connected
and unbounded, planar Brownian motion started at a point of the closure of the complement leaves `F` at once, given the
Beurling estimate. -/
theorem ae_exitTime_eq_zero_of_mem_closure_compl (hB : BrownianBeurlingEstimate) {F : Set ℂ}
    (hE : IsPathConnected Fᶜ) (hunb : ¬ Bornology.IsBounded Fᶜ) {y : ℂ} (hy : y ∈ closure Fᶜ) :
    ∀ᵐ b ∂planarBrownianMotion y, ContinuousPath.exitTime F b = 0 := by
  obtain ⟨C, hC0, hC⟩ := hB
  let r : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 1)
  have hr0 : ∀ n, 0 < r n := fun n => by positivity
  have hr1 : ∀ n, r n ≤ 1 := fun n => pow_le_one₀ (by norm_num) (by norm_num)
  have hrlim : Tendsto r atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  have hr3 : ∀ n, r n ^ 3 ≤ r n := fun n => by
    calc r n ^ 3 ≤ r n ^ 1 := pow_le_pow_of_le_one (hr0 n).le (hr1 n) (by norm_num)
      _ = r n := pow_one _
  -- the exterior curves
  have hex : ∀ n, ∃ γ : C(unitInterval, ℂ), dist y (γ 0) < r n ^ 3 ∧ r n ≤ dist (γ 1) (γ 0) ∧
      range γ ⊆ Fᶜ := by
    intro n
    obtain ⟨w, hwE, hwy⟩ := Metric.mem_closure_iff.mp hy (r n ^ 3) (pow_pos (hr0 n) 3)
    obtain ⟨v, hvE, hvw⟩ : ∃ v ∈ Fᶜ, r n ≤ dist v w := by
      by_contra hcon
      exact hunb (isBounded_ball.subset fun v hv => mem_ball.mpr (not_le.mp fun hle => hcon ⟨v, hv, hle⟩))
    let hJ := hE.joinedIn w hwE v hvE
    refine ⟨hJ.somePath.toContinuousMap, ?_, ?_, ?_⟩
    · rw [show hJ.somePath.toContinuousMap 0 = w from hJ.somePath.source]
      exact hwy
    · rw [show hJ.somePath.toContinuousMap 0 = w from hJ.somePath.source,
        show hJ.somePath.toContinuousMap 1 = v from hJ.somePath.target]
      exact hvw
    · rintro _ ⟨t, rfl⟩
      exact hJ.somePath_mem t
  choose γ hγy hγR hγE using hex
  have hdr : ∀ n, dist y (γ n 0) < r n := fun n => (hγy n).trans_le (hr3 n)
  -- the Beurling events
  let G : ℕ → Set (ContinuousPath ℂ) := fun n =>
    {b | ContinuousPath.exitTime (ball (γ n 0) (r n)) b < ContinuousPath.exitTime (range (γ n))ᶜ b}
  have hG : ∀ n, planarBrownianMotion y (G n) ≤ ENNReal.ofReal (C * r n) := by
    intro n
    refine (hC (γ n) y (r n) (hγR n) (hdr n)).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hC0
    have h3 : r n ^ 2 * r n = r n ^ 3 := by ring
    calc Real.sqrt (dist y (γ n 0) / r n) ≤ Real.sqrt (r n ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_le_iff₀ (hr0 n), h3]
          exact (hγy n).le
      _ = r n := Real.sqrt_sq (hr0 n).le
  have hfreq : ∀ᵐ b ∂planarBrownianMotion y, ∃ᶠ n in atTop, b ∉ G n := by
    rw [ae_iff]
    refine measure_mono_null (?_ : _ ⊆ ⋃ N : ℕ, ⋂ n ≥ N, G n) (measure_iUnion_null fun N => ?_)
    · intro b hb
      simp only [mem_ofPred_eq, not_frequently, not_not] at hb
      obtain ⟨N, hN⟩ := eventually_atTop.mp hb
      exact mem_iUnion.mpr ⟨N, mem_iInter₂.mpr hN⟩
    · refine le_antisymm ?_ bot_le
      have hlim : Tendsto (fun n => ENNReal.ofReal (C * r n)) atTop (𝓝 0) := by
        have h0 := (hrlim.const_mul C)
        rw [mul_zero] at h0
        simpa using ENNReal.tendsto_ofReal h0
      refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (measure_mono (iInter₂_subset n hn)).trans (hG n)
  have hball : ∀ᵐ b ∂planarBrownianMotion y,
      Tendsto (fun n => ContinuousPath.exitTime (ball y (2 * r n)) b) atTop (𝓝 0) := by
    have h2 := hrlim.const_mul 2
    rw [mul_zero] at h2
    exact Section6.ae_tendsto_exitTime_ball_zero y h2
  filter_upwards [hfreq, hball] with b hbf hbt
  obtain ⟨φ, hφ, hφG⟩ := extraction_of_frequently_atTop hbf
  have hle : ∀ n, ContinuousPath.exitTime F b ≤ ContinuousPath.exitTime (ball y (2 * r (φ n))) b := by
    intro n
    have h1 : ContinuousPath.exitTime F b ≤ ContinuousPath.exitTime (range (γ (φ n)))ᶜ b :=
      ContinuousPath.exitTime_mono (fun x hx hxr => hγE (φ n) hxr hx) b
    have h2 : ContinuousPath.exitTime (range (γ (φ n)))ᶜ b ≤
        ContinuousPath.exitTime (ball (γ (φ n) 0) (r (φ n))) b := by
      have hn := hφG n
      simp only [G, mem_ofPred_eq, not_lt] at hn
      exact hn
    have h3 : ContinuousPath.exitTime (ball (γ (φ n) 0) (r (φ n))) b ≤
        ContinuousPath.exitTime (ball y (2 * r (φ n))) b := by
      refine ContinuousPath.exitTime_mono (ball_subset_ball' ?_) b
      rw [dist_comm]
      linarith [hdr (φ n)]
    exact h1.trans (h2.trans h3)
  exact le_antisymm (ge_of_tendsto (hbt.comp hφ.tendsto_atTop) (Eventually.of_forall hle)) bot_le

/-! ### The named input of the joint convergence -/

/-- **`JordanDomainExteriorRegularity` from the Beurling estimate.** Planar Brownian motion started at a frontier point
of a bounded window with an inverse chart leaves the closure of the window at once. -/
theorem jordanDomainExteriorRegularity (hB : BrownianBeurlingEstimate) : JordanDomainExteriorRegularity := by
  intro U z ψ hb h y hy
  obtain ⟨-, hpath, hunb, hfr⟩ := h.frontier_subset_closure_compl_closure hb
  exact ae_exitTime_eq_zero_of_mem_closure_compl hB hpath hunb (hfr hy)

/-- **`BG20WindowJointConvergenceInput` from the Beurling estimate** (the replacement step (7.36) of the proof of
Lemma 7.21 of Berestycki–Gwynne, arXiv:2003.10320). -/
theorem bg20WindowJointConvergenceInput_proved {𝒮 : SpaceFillingSLEModel} (hB : BrownianBeurlingEstimate) :
    BG20WindowJointConvergenceInput 𝒮 :=
  bg20WindowJointConvergenceInput (jordanDomainExteriorRegularity hB)

end MatedCRT
