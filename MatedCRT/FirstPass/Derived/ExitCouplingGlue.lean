import MatedCRT.FirstPass.Derived.ExitCoupling
import MatedCRT.FirstPass.Derived.ExitCouplingPath
import MatedCRT.FirstPass.Derived.ExitCouplingEvents
import LatticeProb.Prob.StoppedPathCoupling
import LatticeProb.Prob.StopPathMeasurable

/-!
# Lévy–Prokhorov distance between the stopped interpolated walks from two nearby vertices

Let `A' ⊆ A` be vertex sets with `A'` a finite exit datum, and `x, y ∈ A'`.  Suppose the exit
positions from `A'` of the walks from `x` and from `y` are within `a` in the one-sided total
variation sense of `srwLaw_exit_coupling`.  The coupling of that statement makes the two walks agree
after their exit times from `A'`, up to an event of probability at most `a`; the interpolated walks
of speed `m`, stopped at their exit times from `A`, are then equal after the time shifts
(`interpPathFn_coupled_of_postExit_eq`).  If both walks are, outside events of probability at most `p`,
quickly out of `A'`, started at `x` (resp. `y`) and of small oscillation up to their exit time from `A`,
then the Lévy–Prokhorov edistance of the laws of the two stopped interpolated paths, for the local
uniform metric, is at most `r` as soon as `a + p + p ≤ r` and `T0 (2 ε + η) + exp (-T0) < r`
(Berestycki–Gwynne (2020), Proposition 6.12, Step 2).
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingGlue

open MeasureTheory Set LatticeProb
open scoped ENNReal NNReal
open MatedCRT.ExitDecomposition MatedCRT.ExitCoupling MatedCRT.ExitCouplingPath
open MatedCRT.ExitCouplingEvents
open MatedCRT.FirstPass36 (FiniteExitData)

/-- The interpolated walk of speed `m`, stopped at its exit time from `A` (in the rescaled time). -/
noncomputable def stoppedInterp (v : ℤ → ℂ) (m : ℝ≥0) (A : Set ℤ) (X : ℕ → ℤ) : C(ℝ≥0, ℂ) :=
  stopPath (interpPathCM v m.coe_nonneg X) (((vExitTime A X).toNat : ℝ≥0) / m)

lemma measurable_stoppedInterp (v : ℤ → ℂ) (m : ℝ≥0) (A : Set ℤ) :
    Measurable (stoppedInterp v m A) :=
  measurable_stopPath (measurable_interpPathCM v m.coe_nonneg) (measurable_exitTimeScaled A m)

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **Coupling of the stopped interpolated walks from two nearby vertices.**  The Lévy–Prokhorov
edistance, for the local uniform metric on `C(ℝ≥0, ℂ)`, between the laws of the interpolated walks
from `x` and from `y` stopped at their exit time from `A` is at most `r`. -/
theorem levyProkhorovEDist_stoppedInterp_le {mult : ℤ → ℤ → ℕ} {A' A : Set ℤ}
    (hA' : FiniteExitData mult A') (hAA : A' ⊆ A) {x y : ℤ} (hx : x ∈ A') (hy : y ∈ A')
    {a p : ℝ≥0∞}
    (hTV : ∀ S : Set ℤ, srwLaw mult x (vExitPosition A' ⁻¹' S) ≤
      srwLaw mult y (vExitPosition A' ⁻¹' S) + a)
    (v : ℤ → ℂ) {m : ℝ≥0} (hm : 0 < m) (ρ : ℝ≥0) {ε η : ℝ} (hη : dist (v x) (v y) ≤ η)
    (T0 r : ℝ≥0) (hr : T0 * (2 * ε + η) + Real.exp (-(T0 : ℝ)) < r)
    (hbx : srwLaw mult x (walkGood v m A' A ρ ε x)ᶜ ≤ p)
    (hby : srwLaw mult y (walkGood v m A' A ρ ε y)ᶜ ≤ p) (hap : a + p + p ≤ r) :
    levyProkhorovEDist ((srwLaw mult x).map (stoppedInterp v m A))
      ((srwLaw mult y).map (stoppedInterp v m A)) ≤ r := by
  obtain ⟨π, hπ1, hπ2, hπbad⟩ := srwLaw_exit_coupling hA' hx hy hTV
  have hmeas := measurable_stoppedInterp v m A
  have e1 : (srwLaw mult x).map (stoppedInterp v m A) = π.map fun w => stoppedInterp v m A w.1 := by
    rw [← hπ1, Measure.map_map hmeas measurable_fst]; rfl
  have e2 : (srwLaw mult y).map (stoppedInterp v m A) = π.map fun w => stoppedInterp v m A w.2 := by
    rw [← hπ2, Measure.map_map hmeas measurable_snd]; rfl
  rw [e1, e2]
  refine levyProkhorovEDist_stopPath_le π (fun w => interpPathCM v m.coe_nonneg w.1)
    (fun w => interpPathCM v m.coe_nonneg w.2) (fun w => ((vExitTime A w.1).toNat : ℝ≥0) / m)
    (fun w => ((vExitTime A w.2).toNat : ℝ≥0) / m) (fun w => ((vExitTime A' w.1).toNat : ℝ≥0) / m)
    (fun w => ((vExitTime A' w.2).toNat : ℝ≥0) / m) (hmeas.comp measurable_fst)
    (hmeas.comp measurable_snd) ρ T0 r hr
    (exitContinuationEvent A' ∩ Prod.fst ⁻¹' walkGood v m A' A ρ ε x ∩
      Prod.snd ⁻¹' walkGood v m A' A ρ ε y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro w hw
    exact hw.1.2.2.2.1
  · intro w hw
    exact hw.2.2.2.1
  · intro w hw s t hs ht hst
    exact hw.1.2.2.2.2 s t hs ht hst
  · intro w hw s t hs ht hst
    exact hw.2.2.2.2 s t hs ht hst
  · intro w hw
    have h1 : interpPathFn v m w.1 0 = v x := by rw [interpPathFn_zero, hw.1.2.1]
    have h2 : interpPathFn v m w.2 0 = v y := by rw [interpPathFn_zero, hw.2.1]
    simp only [interpPathCM_apply]
    rw [h1, h2]
    exact hη
  · intro w hw t
    have hpost : postExit A' w.1 = postExit A' w.2 := hw.1.1
    have he : vExitTime A (postExit A' w.1) ≠ ⊤ :=
      vExitTime_postExit_ne_top hAA hw.1.2.2.1
    exact interpPathFn_coupled_of_postExit_eq v hm hAA hpost he t
  · have hsub : (exitContinuationEvent A' ∩ Prod.fst ⁻¹' walkGood v m A' A ρ ε x ∩
        Prod.snd ⁻¹' walkGood v m A' A ρ ε y)ᶜ ⊆
        (exitContinuationEvent A')ᶜ ∪ Prod.fst ⁻¹' (walkGood v m A' A ρ ε x)ᶜ ∪
          Prod.snd ⁻¹' (walkGood v m A' A ρ ε y)ᶜ := by
      intro w hw
      simp only [mem_compl_iff, mem_inter_iff, mem_preimage, not_and_or] at hw
      simp only [mem_union, mem_compl_iff, mem_preimage]
      tauto
    have hfx : π (Prod.fst ⁻¹' (walkGood v m A' A ρ ε x)ᶜ) ≤ p :=
      (Measure.le_map_apply measurable_fst.aemeasurable _).trans (hπ1 ▸ hbx)
    have hfy : π (Prod.snd ⁻¹' (walkGood v m A' A ρ ε y)ᶜ) ≤ p :=
      (Measure.le_map_apply measurable_snd.aemeasurable _).trans (hπ2 ▸ hby)
    calc π _ ≤ π ((exitContinuationEvent A')ᶜ ∪ Prod.fst ⁻¹' (walkGood v m A' A ρ ε x)ᶜ ∪
          Prod.snd ⁻¹' (walkGood v m A' A ρ ε y)ᶜ) := measure_mono hsub
      _ ≤ π (exitContinuationEvent A')ᶜ + π (Prod.fst ⁻¹' (walkGood v m A' A ρ ε x)ᶜ) +
          π (Prod.snd ⁻¹' (walkGood v m A' A ρ ε y)ᶜ) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ a + p + p := add_le_add (add_le_add hπbad hfx) hfy
      _ ≤ r := hap

end ExitCouplingGlue
end MatedCRT
