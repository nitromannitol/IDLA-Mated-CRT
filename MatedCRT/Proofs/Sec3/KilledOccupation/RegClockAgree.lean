import MatedCRT.Proofs.Sec3.KilledOccupation.CircleAverageRepAgree
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockIdentificationConcrete

/-!
# Regularized clock of the shifted field equals the circle-average clock (step B1 of the transfer of thm:occ-main)

The field of the quantum cone on the unit disk is `h = g − γ log|·|` with `g` the whole-plane GFF (eq:occ-field of
`paper/appendix-occupation-C16.tex`). Its circle averages are `HarmonicBalls.fieldCircleAverage γ hc ε x =
hc ε x − γ · circleAverage (log ‖·‖) x ε`. The regularized clock `regClock` of `ClockIdentificationConcrete` uses these
circle averages in its density `regDensity`, while `regClockFun` of `RegClockFun` takes the family `ψ` directly.

This file proves:
* the circle averages of the shifted field are continuous on the positive radii whenever the GFF circle averages
  are (Jensen's formula for the logarithmic potential, `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`);
* the regularized clock `regClockFun` built from the family of circle averages of the shifted field coincides with
  `regClock`, the clock of the Dirichlet Green function identification;
* the same identity under the continuity of the GFF circle averages on `ℝ_{>0} × ℂ`, the form given by the a.s.
  continuity of the whole-plane GFF (`IsWholePlaneGFF.ae_continuousOn_circle`).

Terminology: Jensen's formula and the logarithmic potential as in Armitage-Gardiner; circle averages of the
Gaussian free field as in Duplantier-Sheffield.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- **Step B1 (continuity of the shifted-field circle averages).** If the circle averages `hc r z` of the whole-plane
GFF are continuous on `ℝ_{>0} × ℂ`, then so are the circle averages `fieldCircleAverage α₀ hc r z` of the shifted
field `h = g − α₀ log|·|`. The proof uses the closed form `circleAverage (log ‖·‖) z r = log r + log⁺(‖z‖ / r)` for
`r ≠ 0` (Jensen's formula with centre `0`). -/
theorem continuousOn_fieldCircleAverage {α₀ : ℝ} {hc : ℝ → ℂ → ℝ}
    (h : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × ℂ => HarmonicBalls.fieldCircleAverage α₀ hc p.1 p.2) (Ioi 0 ×ˢ univ) := by
  have hform : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ univ : Set (ℝ × ℂ)),
      HarmonicBalls.fieldCircleAverage α₀ hc p.1 p.2
        = hc p.1 p.2 - α₀ * (Real.log p.1 + Real.posLog (p.1⁻¹ * ‖p.2‖)) := by
    intro p hp
    have hr : p.1 ≠ 0 := (mem_Ioi.1 hp.1).ne'
    have h1 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := p.2) hr
    simp only [sub_zero] at h1
    unfold HarmonicBalls.fieldCircleAverage
    rw [h1]
  have hlog : ContinuousOn (fun p : ℝ × ℂ => Real.log p.1) (Ioi 0 ×ˢ univ) :=
    ContinuousOn.log continuousOn_fst (fun p hp => (mem_Ioi.1 hp.1).ne')
  have hposlog : ContinuousOn (fun p : ℝ × ℂ => Real.posLog (p.1⁻¹ * ‖p.2‖)) (Ioi 0 ×ˢ univ) :=
    Real.continuous_posLog.comp_continuousOn
      ((ContinuousOn.inv₀ continuousOn_fst (fun p hp => (mem_Ioi.1 hp.1).ne')).mul
        continuousOn_snd.norm)
  refine ContinuousOn.congr ?_ hform
  exact ContinuousOn.sub h (ContinuousOn.mul continuousOn_const (ContinuousOn.add hlog hposlog))

/-- **Step B2 (regularized clock of the shifted field).** For the family of circle averages of the shifted field
`h = g − γ log|·|`, the clock `regClockFun` of `RegClockFun` equals the clock `regClock` of
`ClockIdentificationConcrete`, under the continuity of that family on the index set `UnitDiskCircleIndex`, and the
path `b` stays in the index set up to the exit time. The time measures `timeLeb` and `lebNN` coincide. -/
theorem regClockFun_eq_regClock (γ ε : ℝ) (hc : ℝ → ℂ → ℝ)
    (hψ : Continuous fun q : UnitDiskCircleIndex => HarmonicBalls.fieldCircleAverage γ hc q.1.1 q.1.2)
    (σ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) (s : ℝ≥0)
    (hb : ∀ u ∈ Set.Icc (0 : ℝ≥0) (min s (σ b)), (ε, b u) ∈ UnitDiskCircleIndex) :
    regClockFun γ ε (fun q : UnitDiskCircleIndex => HarmonicBalls.fieldCircleAverage γ hc q.1.1 q.1.2) σ b s
      = regClock γ ε hc (σ b) ⇑b s := by
  unfold regClockFun regClock
  have htl : timeLeb = lebNN := rfl
  rw [htl]
  refine setLIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
  have hcirc := circleAverageRep_eq_of_continuous hψ (hb u hu)
  simp only [regDensity]
  rw [hcirc]

/-- **Step B3 (regularized clock from continuity on the positive radii).** The conclusion of `regClockFun_eq_regClock`
under the hypothesis that the whole-plane GFF circle averages `hc` are continuous on `ℝ_{>0} × ℂ`, the form given by
the a.s. continuity of the GFF circle averages (`IsWholePlaneGFF.ae_continuousOn_circle`). -/
theorem regClockFun_eq_regClock_of_continuousOn (γ ε : ℝ) (hc : ℝ → ℂ → ℝ)
    (h : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Ioi 0 ×ˢ univ))
    (σ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) (s : ℝ≥0)
    (hb : ∀ u ∈ Set.Icc (0 : ℝ≥0) (min s (σ b)), (ε, b u) ∈ UnitDiskCircleIndex) :
    regClockFun γ ε (fun q : UnitDiskCircleIndex => HarmonicBalls.fieldCircleAverage γ hc q.1.1 q.1.2) σ b s
      = regClock γ ε hc (σ b) ⇑b s := by
  have hF := continuousOn_fieldCircleAverage (α₀ := γ) h
  have hsub : (UnitDiskCircleIndex : Set (ℝ × ℂ)) ⊆ Ioi 0 ×ˢ univ := fun q hq => ⟨hq.1, mem_univ _⟩
  have hψ : Continuous fun q : UnitDiskCircleIndex => HarmonicBalls.fieldCircleAverage γ hc q.1.1 q.1.2 :=
    continuousOn_iff_continuous_domRestrict.1 (hF.mono hsub)
  exact regClockFun_eq_regClock γ ε hc hψ σ b s hb

end MatedCRT.KilledOccupation
