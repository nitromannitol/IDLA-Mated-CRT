import MatedCRT.FirstPass.Derived.WindowChartBGJointConvergence

/-!
# Time-changed Brownian paths cross the window

A family of path laws that defines a time-changed Brownian motion (Definition 7.2 of Berestycki–Gwynne (2020)) runs a
planar Brownian path `B` with a continuous strictly increasing clock `τ` with `τ 0 = 0`. Such a clock preserves the
order of any two exit times, so the paths leave the closure of a Jordan domain as soon as they leave the domain. This
is the crossing used in the proof of Berestycki–Gwynne (2020), Lemma 7.21 (in a
bounded Jordan domain the limiting path visits the open exterior arbitrarily soon after its exit).

* `MatedCRT.FrozenPath.pathExitTime_comp_le`: a continuous strictly increasing time change preserves `≤` between
  two exit times.
* `MatedCRT.FrozenPath.crossing_of_timeChange`: the time-changed path leaves `{D ≥ 0}` no later than `{D > 0}`.
* `MatedCRT.FrozenPath.ae_crossing_of_definesTimeChangedBM`: almost every path from `z` crosses a bounded open set
  `{D > 0}` whose frontier points are regular for the exterior.
* `MatedCRT.FrozenPath.ae_windowGap_crossing_of_definesTimeChangedBM`: the same for the window of any curve.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

namespace FrozenPath

/-- A continuous strictly increasing time change `τ` with `τ 0 = 0` preserves the order of two exit times. -/
theorem pathExitTime_comp_le {α : Type*} {O O' : Set α} {g : ℝ≥0 → α} {τ : ℝ≥0 → ℝ≥0}
    (hτc : Continuous τ) (hτm : StrictMono τ) (hτ0 : τ 0 = 0)
    (h : pathExitTime O g ≤ pathExitTime O' g) :
    pathExitTime O (g ∘ τ) ≤ pathExitTime O' (g ∘ τ) := by
  refine le_sInf ?_
  rintro _ ⟨u, rfl, hu⟩
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hlt : pathExitTime O g < (τ (u + ε) : ℝ≥0∞) :=
    (h.trans (GapExit.pathExitTime_le_of_notMem (f := g) (t := τ u) hu)).trans_lt
      (ENNReal.coe_lt_coe.2 (hτm (lt_add_of_pos_right u hε)))
  obtain ⟨_, ⟨t, rfl, ht⟩, htlt⟩ := sInf_lt_iff.1 hlt
  have htlt' : t ≤ τ (u + ε) := (ENNReal.coe_lt_coe.1 htlt).le
  have h0t : τ 0 ≤ t := by
    rw [hτ0]
    exact zero_le
  obtain ⟨v, hv, hvt⟩ : t ∈ τ '' Icc 0 (u + ε) :=
    intermediate_value_Icc zero_le hτc.continuousOn ⟨h0t, htlt'⟩
  have hgv : (g ∘ τ) v ∉ O := by
    simp only [Function.comp_apply, hvt]
    exact ht
  calc pathExitTime O (g ∘ τ) ≤ (v : ℝ≥0∞) := GapExit.pathExitTime_le_of_notMem hgv
    _ ≤ (u : ℝ≥0∞) + ε := by exact_mod_cast hv.2

/-- **Crossing of a time-changed path.** If the path `B` leaves `closure {D > 0}` when it leaves `{D > 0}`, then the
path `X = B ∘ τ`, for a continuous strictly increasing clock `τ` with `τ 0 = 0`, leaves `{D ≥ 0} ⊆ closure {D > 0}` no
later than `{D > 0}`. -/
theorem crossing_of_timeChange {D : C(ℂ, ℝ)} {B X : ContinuousPath ℂ} {τ : ℝ≥0 → ℝ≥0}
    (hτc : Continuous τ) (hτm : StrictMono τ) (hτ0 : τ 0 = 0) (hX : ∀ u, X u = B (τ u))
    (hsub : {w | 0 ≤ D w} ⊆ closure (gapDomain D))
    (hB : ContinuousPath.exitTime (closure (gapDomain D)) B = ContinuousPath.exitTime (gapDomain D) B) :
    ContinuousPath.exitTime {w | 0 ≤ D w} X ≤ ContinuousPath.exitTime (gapDomain D) X := by
  have hXe : (⇑X : ℝ≥0 → ℂ) = ⇑B ∘ τ := funext hX
  have h1 : pathExitTime {w | 0 ≤ D w} (⇑X : ℝ≥0 → ℂ) ≤ pathExitTime (closure (gapDomain D)) (⇑X : ℝ≥0 → ℂ) :=
    GapExit.pathExitTime_mono hsub _
  have h2 : pathExitTime (closure (gapDomain D)) (⇑X : ℝ≥0 → ℂ) ≤ pathExitTime (gapDomain D) (⇑X : ℝ≥0 → ℂ) := by
    rw [hXe]
    exact pathExitTime_comp_le hτc hτm hτ0 (le_of_eq hB)
  exact h1.trans h2

theorem measurableSet_crossing (D : C(ℂ, ℝ)) : MeasurableSet {f : ContinuousPath ℂ |
    ContinuousPath.exitTime {w | 0 ≤ D w} f ≤ ContinuousPath.exitTime (gapDomain D) f} :=
  measurableSet_le (measurable_exitTime_setOf_nonneg.comp (measurable_const.prodMk measurable_id))
    (measurable_exitTime_gapDomain.comp (measurable_const.prodMk measurable_id))

/-- **Crossing for a time-changed Brownian motion.** If `P` defines a time-changed Brownian motion, then for every
bounded open set `{D > 0}` containing `z`, whose frontier points are regular for its exterior and whose closure
contains `{D ≥ 0}`, almost every path under `P z` leaves `{D ≥ 0}` no later than `{D > 0}`. -/
theorem ae_crossing_of_definesTimeChangedBM {P : PathLawFamily} (hP : DefinesTimeChangedBM P) {z : ℂ}
    {D : C(ℂ, ℝ)} (hDb : Bornology.IsBounded (gapDomain D)) (hzD : z ∈ gapDomain D)
    (hreg : ∀ y ∈ frontier (gapDomain D), ∀ᵐ b ∂planarBrownianMotion y,
      ContinuousPath.exitTime (closure (gapDomain D)) b = 0)
    (hsub : {w | 0 ≤ D w} ⊆ closure (gapDomain D)) :
    ∀ᵐ f ∂(P z : Measure (ContinuousPath ℂ)),
      ContinuousPath.exitTime {w | 0 ≤ D w} f ≤ ContinuousPath.exitTime (gapDomain D) f := by
  obtain ⟨Ω, _, Q, _, B, X, τ, hB, hX, hlaw, hae, hPz⟩ := hP z
  rw [hPz]
  refine (ae_map_iff hX (measurableSet_crossing D)).2 ?_
  have hbm : ∀ᵐ b ∂(Q.map B), ContinuousPath.exitTime (closure (gapDomain D)) b =
      ContinuousPath.exitTime (gapDomain D) b := by
    rw [hlaw]
    exact HarmonicBalls.Section6.ae_exitTime_closure_eq_of_boundary_instant_exit (isOpen_gapDomain D) hDb hzD hreg
  filter_upwards [hae, ae_of_ae_map hB hbm] with ω hω hb
  obtain ⟨hc, hm, h0, hXB⟩ := hω
  exact crossing_of_timeChange hc hm h0 hXB hsub hb

/-- **Crossing of the window for a time-changed Brownian motion.** If `P` defines a time-changed Brownian motion,
then for every curve `η` almost every path under `P (η u)` leaves `{windowGapBG ≥ 0}` no later than the window
`{windowGapBG > 0}`. -/
theorem ae_windowGap_crossing_of_definesTimeChangedBM {P : PathLawFamily} (hP : DefinesTimeChangedBM P)
    (hJ : JordanDomainExteriorRegularity) (a u b : ℝ) (η : C(ℝ, ℂ)) :
    ∀ᵐ f ∂(P (η u) : Measure (ContinuousPath ℂ)),
      ContinuousPath.exitTime {w | 0 ≤ windowGapBG a u b η w} f ≤
        ContinuousPath.exitTime (gapDomain (windowGapBG a u b η)) f := by
  by_cases hη : η ∈ windowChartCurves a u b
  · obtain ⟨ψ, hψ⟩ := id hη
    have hU := gapDomain_windowGapBG_of_mem hη
    have hb := isBounded_windowDomain η a u b
    have hb' : Bornology.IsBounded (gapDomain (windowGapBG a u b η)) := by
      rw [hU]
      exact hb
    have hz' : η u ∈ gapDomain (windowGapBG a u b η) := by
      rw [hU]
      exact hψ.mem
    have hreg : ∀ y ∈ frontier (gapDomain (windowGapBG a u b η)), ∀ᵐ β ∂planarBrownianMotion y,
        ContinuousPath.exitTime (closure (gapDomain (windowGapBG a u b η))) β = 0 := by
      rw [hU]
      exact hJ _ _ ψ hb hψ
    have hsub : {w | 0 ≤ windowGapBG a u b η w} ⊆ closure (gapDomain (windowGapBG a u b η)) := by
      rw [hU]
      exact setOf_nonneg_windowGapBG_subset hη
    exact ae_crossing_of_definesTimeChangedBM hP hb' hz' hreg hsub
  · exact ae_of_all _ fun f => crossing_windowGapBG_of_not_mem hη f

end FrozenPath

end MatedCRT
