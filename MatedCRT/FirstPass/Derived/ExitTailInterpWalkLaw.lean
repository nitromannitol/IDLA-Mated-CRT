import MatedCRT.FirstPass.Derived.ExitTailClock
import MatedCRT.FirstPass.Derived.StickyWindowKernel

/-!
# The quenched interpolated walk laws rarely stay in a ball for a long time

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Section 6.4, the last step before the passage to the limit in Lemma 7.4.

`exitTail_clock`: outside an event of probability at most `2 θ`, from every vertex of `B_r` the
walk stays in `B_r` up to time `N` with probability at most `θ`.  The interpolated walk law `P̃^ε(ω)(z)` from an
arbitrary point `z` is a mixture over the vertices whose cell meets `B_r` of the walk laws from these vertices
(`StickyWindowKernel.interpWalkLaw_apply_le_of_start`); a vertex whose own position is outside `B_r` contributes
nothing to the set of paths that stay in `B_r` (their starting point is that position).  Hence, outside the same
event, `P̃^ε(ω)(z)` gives mass at most `θ` to the open set of paths that stay in `B_r` up to time `N`, for all `z`.

* `stayOpen`, `isOpen_stayOpen`: the set of paths that stay in `B_r` up to time `T` is open.
* `exitTail_interpWalkLaw`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter HarmonicBalls LatticeProb
open MarkovProcess (ContinuousPath)
open scoped ENNReal Topology NNReal
open MatedCRT.FirstPass.Derived MatedCRT.StickyWindowKernel

namespace MatedCRT
namespace ExitTailInterpWalkLaw

variable {Ω : Type} [MeasurableSpace Ω]

/-- The continuous paths that stay in the open ball `B(0, r)` up to time `T`. -/
def stayOpen (r : ℝ) (T : ℝ≥0) : Set (ContinuousPath ℂ) :=
  {f | ∀ t : ℝ≥0, t ≤ T → f t ∈ ball (0 : ℂ) r}

theorem isOpen_stayOpen (r : ℝ) (T : ℝ≥0) : IsOpen (stayOpen r T) := by
  have h : stayOpen r T = {f : C(ℝ≥0, ℂ) | MapsTo f (Icc 0 T) (ball (0 : ℂ) r)} := by
    ext f
    exact ⟨fun hf t ht => hf t ht.2, fun hf t ht => hf ⟨zero_le, ht⟩⟩
  rw [h]
  exact ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc isOpen_ball

theorem measurableSet_stayOpen (r : ℝ) (T : ℝ≥0) : MeasurableSet (stayOpen r T) :=
  (isOpen_stayOpen r T).measurableSet

theorem stayOpen_start (r : ℝ) (T : ℝ≥0) : ∀ f ∈ stayOpen r T, f 0 ∈ ball (0 : ℂ) r :=
  fun _ hf => hf 0 zero_le

/-- **Step E4.**  Outside an event of probability at most `2 θ`, every interpolated walk law `P̃^ε(ω)(z)` gives
mass at most `θ` to the paths that stay in `B_r` up to time `N`. -/
theorem exitTail_interpWalkLaw {𝒮 : SpaceFillingSLEModel} (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (h214 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {θ : ℝ} (hθ : 0 < θ) {r : ℝ} (hr : 0 < r) (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (η' : Ω → C(ℝ, ℂ)) (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    (hc0 : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → c₀ ≤ ε * S.mε ε) :
    ∃ N : ℕ, ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₂ →
      S.P {ω | ∃ z : ℂ, ENNReal.ofReal θ <
        ((interpWalkLaw S η' ε ω z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
          (stayOpen r N)} ≤ ENNReal.ofReal (2 * θ) := by
  obtain ⟨N, ε₂, hε₂, hmain⟩ := exitTail_clock hEnvS h214 h217 hγ hγ2 hθ hr Ω S hS hc0
  refine ⟨N, ε₂, hε₂, fun ε hε hεlt => le_trans (measure_mono_ae ?_) (hmain ε hε hεlt)⟩
  filter_upwards [hS.ae_interpWeight_good hae hε, hae] with ω hgood hηω hω
  obtain ⟨z, hz⟩ := hω
  by_contra hnot
  have hnot' : ∀ k : ℤ, vertexPoint ε (S.η ω) k ∈ ball (0 : ℂ) r →
      srwLaw (S.mult ε ω) k {x | ∀ t : ℝ≥0, t ≤ (N : ℝ≥0) →
        interpolatedWalk ε (S.η ω) (S.mε ε) x t ∈ ball (0 : ℂ) r} ≤ ENNReal.ofReal θ := by
    intro k hk
    by_contra hlt
    exact hnot ⟨k, hk, not_le.1 hlt⟩
  refine absurd hz (not_lt.2 ?_)
  refine interpWalkLaw_apply_le_of_start S η' hε hgood.1 hgood.2 z (measurableSet_stayOpen r N)
    (stayOpen_start r N) ?_
  intro k hk
  have hcoe : ((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω :
      ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) =
      Measure.map (interpPathCM (vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε)) (srwLaw (S.mult ε ω) k) := rfl
  by_cases hv : vertexPoint ε (⇑(η' ω)) k ∈ ball (0 : ℂ) r
  · have hv' : vertexPoint ε (S.η ω) k ∈ ball (0 : ℂ) r := by rw [← hηω]; exact hv
    rw [hcoe, Measure.map_apply (measurable_interpPathCM _ _) (measurableSet_stayOpen r N)]
    refine le_trans (le_of_eq ?_) (hnot' k hv')
    congr 1
    ext x
    simp only [mem_preimage, stayOpen, mem_ofPred_eq, interpPathCM_vertexPoint, hηω]
  · have hnull := walkPathLaw_start_null S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω
      (z := vertexPoint ε (⇑(η' ω)) k) (r := 0) (by simp)
    refine le_trans (measure_mono ?_) (hnull.le.trans zero_le)
    intro f hf
    have h0 := stayOpen_start r N f hf
    show 0 < dist (f 0) (vertexPoint ε (⇑(η' ω)) k)
    refine dist_pos.2 fun heq => hv ?_
    rw [← heq]
    exact h0

end ExitTailInterpWalkLaw
end MatedCRT
