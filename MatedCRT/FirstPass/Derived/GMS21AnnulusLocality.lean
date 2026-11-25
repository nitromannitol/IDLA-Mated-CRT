import MatedCRT.FirstPass.Derived.GMS21AnnulusStoppedCurve
import MatedCRT.FirstPass.Derived.StopAtExitLocalUniform
import MatedCRT.FirstPass.Derived.InterpolatedWalkPrefix
import MatedCRT.FirstPass.Derived.AreaCellStoppedTrajectory
import MatedCRT.FirstPass.Derived.SrwRelabelLaw

/-!
# Locality of the walk stopped at its exit from a domain

In the proof of Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, case 1, the comparison of the embedded walk
with Brownian motion on an annulus `V` avoiding the origin is transferred from the `0`-quantum cone to the
`γ`-quantum cone by Lemma 3.3: the laws of the cell configurations near `V` are uniformly mutually absolutely
continuous. This uses that the law of the embedded walk stopped at its exit from `V` is determined by the cell
configuration near `V`. This file proves the walk part of that statement:

* the curve class of a path stopped at its exit from `U` only depends on the path up to any time at which it is
  outside `U`;
* the interpolated embedded walk stopped at its exit from `V` only depends on the discrete walk stopped at its first
  exit from the set of vertices embedded in `V`;
* hence the law of the stopped interpolated walk only depends on the rows `m x ·` of the edge multiplicities at the
  vertices `x` embedded in `V`, and it is invariant under relabelling the vertices.

## Main results

* `stoppedExitCurve_eq_of_eqOn_of_not_mem`
* `stoppedExitCurve_interpPathCM_stoppedPath`
* `srwLaw_map_stoppedPath_eq_of_rows`
* `map_stoppedExitCurve_interpPathCM_eq_of_rows`
* `map_stoppedExitCurve_interpPathCM_relabel`
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open StopAtExitLevyProkhorov ExitDecomposition

/-- Two continuous paths that agree up to a time `T` by which the first has left `U` have the same curve class
stopped at the exit from `U`. -/
theorem stoppedExitCurve_eq_of_eqOn_of_not_mem {U : Set ℂ} {b b' : ContinuousPath ℂ} {T t₀ : ℝ≥0}
    (hbb : ∀ t ≤ T, b t = b' t) (ht₀ : t₀ ≤ T) (hb : b t₀ ∉ U) :
    stoppedExitCurve U b = stoppedExitCurve U b' := by
  have he : pathExitTime U ⇑b = pathExitTime U ⇑b' :=
    StopAtExitCmp.pathExitTime_eq_of_eqOn_of_not_mem hbb ht₀ hb
  have h0 : pathExitTime U ⇑b ≤ (t₀ : ℝ≥0∞) := sInf_le ⟨t₀, rfl, hb⟩
  have hle : pathExitTime U ⇑b ≤ (T : ℝ≥0∞) := h0.trans (by exact_mod_cast ht₀)
  have hT : (pathExitTime U ⇑b).toNNReal ≤ T := by
    simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top hle
  have hpre : LatticeProb.normalizedPathPrefix
      (LatticeProb.ReparamDistanceIsometry.complexToEuclideanPath b) (pathExitTime U ⇑b).toNNReal =
      LatticeProb.normalizedPathPrefix
        (LatticeProb.ReparamDistanceIsometry.complexToEuclideanPath b') (pathExitTime U ⇑b).toNNReal := by
    ext u : 1
    rw [LatticeProb.normalizedPathPrefix_apply, LatticeProb.normalizedPathPrefix_apply]
    change Complex.orthonormalBasisOneI.repr (b _) = Complex.orthonormalBasisOneI.repr (b' _)
    refine congrArg _ (hbb _ ?_)
    have h3 : (u : ℝ) * ((pathExitTime U ⇑b).toNNReal : ℝ) ≤ (T : ℝ) :=
      le_trans (mul_le_of_le_one_left (NNReal.coe_nonneg _) u.2.2) (NNReal.coe_le_coe.2 hT)
    exact NNReal.coe_le_coe.1 h3
  have hcurve : LatticeProb.normalizedPrefixCurve
      (LatticeProb.ReparamDistanceIsometry.complexToEuclideanPath b) (pathExitTime U ⇑b).toNNReal =
      LatticeProb.normalizedPrefixCurve
        (LatticeProb.ReparamDistanceIsometry.complexToEuclideanPath b') (pathExitTime U ⇑b).toNNReal := by
    unfold LatticeProb.normalizedPrefixCurve
    rw [hpre]
  simp only [stoppedExitCurve]
  rw [← he, hcurve]

/-- The interpolated embedded walk (unit speed) stopped at its exit from `V` only depends on the discrete walk stopped
at its first exit from the set `{x | p x ∈ V}` of vertices embedded in `V`. -/
theorem stoppedExitCurve_interpPathCM_stoppedPath (V : Set ℂ) (p : ℤ → ℂ) (w : ℕ → ℤ) :
    stoppedExitCurve V (interpPathCM p zero_le_one (stoppedPath {x | p x ∈ V} w)) =
      stoppedExitCurve V (interpPathCM p zero_le_one w) := by
  by_cases ht : vExitTime {x | p x ∈ V} w = ⊤
  · rw [stoppedPath_of_top ht]
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp ht
  have hk' : vExitTime {x | p x ∈ V} w = (k : ℕ∞) := hk.symm
  have hout : w k ∉ {x | p x ∈ V} :=
    ((FirstPass36.H2.vExitTime_eq_coe_iff_spec {x | p x ∈ V} w k).mp hk').1
  have hagree : ∀ j ≤ k, stoppedPath {x | p x ∈ V} w j = w j := fun j hj => stoppedPath_of_le hk' hj
  have h1 := stopPath_interpPathCM_congr p (zero_lt_one : (0 : ℝ) < 1) k hagree
  have hT : ∀ t ≤ (((k : ℝ) / 1).toNNReal),
      interpPathCM p zero_le_one (stoppedPath {x | p x ∈ V} w) t = interpPathCM p zero_le_one w t := by
    intro t ht'
    have h2 := congrArg (fun f => f t) h1
    simp only [LatticeProb.stopPath_apply, min_eq_left ht'] at h2
    exact h2
  refine stoppedExitCurve_eq_of_eqOn_of_not_mem hT le_rfl ?_
  rw [hT _ le_rfl, interpPathCM_at_stepTime p (zero_lt_one : (0 : ℝ) < 1) w k]
  exact hout

/-- **Locality of the stopped walk.** The law of simple random walk on the multigraph `m` stopped at its first exit
from `A` only depends on the rows `m x ·` for `x ∈ A`. -/
theorem srwLaw_map_stoppedPath_eq_of_rows {A : Set ℤ} {m m' : ℤ → ℤ → ℕ} (h : ∀ x ∈ A, m x = m' x) (a : ℤ) :
    (srwLaw m a).map (stoppedPath A) = (srwLaw m' a).map (stoppedPath A) := by
  have hk : absorbedSrwKernel m A = absorbedSrwKernel m' A := by
    ext x : 1
    simp only [absorbedSrwKernel, Kernel.piecewise_apply]
    split_ifs with hx
    · change srwStep m x = srwStep m' x
      unfold srwStep edgeMeasure
      rw [h x hx]
    · rfl
  have key : ∀ κ₁ κ₂ : Kernel ℤ ℤ, κ₁ = κ₂ → ∀ [IsMarkovKernel κ₁] [IsMarkovKernel κ₂],
      (Kernel.trajMeasure (Measure.dirac a) (fun n => κ₁.comap
        (fun h : Finset.Iic n → ℤ => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _))).map (stoppedPath A) =
      (Kernel.trajMeasure (Measure.dirac a) (fun n => κ₂.comap
        (fun h : Finset.Iic n → ℤ => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _))).map (stoppedPath A) := by
    intro κ₁ κ₂ hκ _ _
    subst hκ
    rfl
  rw [← absorbedSrwKernel_stopped_trajectoryLaw m A a, ← absorbedSrwKernel_stopped_trajectoryLaw m' A a]
  exact key _ _ hk

/-- **Locality of the stopped interpolated walk.** For an open set `V` and vertex positions `p`, the law of the curve
class of the interpolated embedded walk stopped at its exit from `V` only depends on the rows `m x ·` of the edge
multiplicities at the vertices `x` with `p x ∈ V`. -/
theorem map_stoppedExitCurve_interpPathCM_eq_of_rows {V : Set ℂ} (hV : IsOpen V) (p : ℤ → ℂ)
    {m m' : ℤ → ℤ → ℕ} (h : ∀ x, p x ∈ V → m x = m' x) (a : ℤ) :
    (srwLaw m a).map (fun w => stoppedExitCurve V (interpPathCM p zero_le_one w)) =
      (srwLaw m' a).map (fun w => stoppedExitCurve V (interpPathCM p zero_le_one w)) := by
  have hF : Measurable (fun w : ℕ → ℤ => stoppedExitCurve V (interpPathCM p zero_le_one w)) :=
    (measurable_stoppedExitCurve V hV).comp (measurable_interpPathCM p zero_le_one)
  have key : ∀ μ : Measure (ℕ → ℤ),
      μ.map (fun w => stoppedExitCurve V (interpPathCM p zero_le_one w)) =
        (μ.map (stoppedPath {x | p x ∈ V})).map
          (fun w => stoppedExitCurve V (interpPathCM p zero_le_one w)) := by
    intro μ
    rw [Measure.map_map hF (measurable_stoppedPath _)]
    congr 1
    funext w
    exact (stoppedExitCurve_interpPathCM_stoppedPath V p w).symm
  rw [key (srwLaw m a), key (srwLaw m' a), srwLaw_map_stoppedPath_eq_of_rows (A := {x | p x ∈ V}) (fun x hx => h x hx) a]

/-- **Relabelling invariance of the stopped interpolated walk.** Relabelling the vertices by a bijection `e` of `ℤ`
(multiplicities `m (e x) (e y)`, positions `p (e x)`) does not change the law of the curve class of the stopped
interpolated walk. -/
theorem map_stoppedExitCurve_interpPathCM_relabel {V : Set ℂ} (hV : IsOpen V) (p : ℤ → ℂ)
    (m : ℤ → ℤ → ℕ) (e : ℤ ≃ ℤ) (a : ℤ) :
    (srwLaw (fun x y => m (e x) (e y)) a).map
        (fun w => stoppedExitCurve V (interpPathCM (fun x => p (e x)) zero_le_one w)) =
      (srwLaw m (e a)).map (fun w => stoppedExitCurve V (interpPathCM p zero_le_one w)) := by
  have hF : Measurable (fun w : ℕ → ℤ => stoppedExitCurve V (interpPathCM p zero_le_one w)) :=
    (measurable_stoppedExitCurve V hV).comp (measurable_interpPathCM p zero_le_one)
  have hf : Measurable (fun ω : ℕ → ℤ => fun n => e (ω n)) :=
    Measurable.of_eval fun n => measurable_of_countable _ |>.comp (measurable_pi_apply n)
  rw [← srwLaw_map_relabel m e a, Measure.map_map hF hf]
  rfl

end MatedCRT
