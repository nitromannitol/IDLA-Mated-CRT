import MatedCRT.FirstPass.Derived.DMSWilliamsPostLastPath
import MatedCRT.FirstPass.Derived.CanonicalBrownianPathLaw
import LatticeProb.Prob.BrownianPathCoords
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W6Meas

/-! # Canonical law of the post-last-zero path -/

open MeasureTheory ProbabilityTheory LatticeProb
open scoped NNReal

noncomputable section

namespace MatedCRT.Proposed

open QuantumZipper.Williams

/-- Remove the drift from a continuous path viewed after its last zero. -/
def postLastPathMap (d : ℝ) (w : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun t => postLast (fun s => w s + d * s) 0 t - d * t,
    (continuous_postLast_gen (f := fun w : C(ℝ≥0, ℝ) => fun s => w s + d * s)
      (fun w => w.continuous.add (continuous_const.mul continuous_subtype_val)) w).sub
      (continuous_const.mul continuous_subtype_val)⟩

/-- The post-last-zero transformation is measurable on continuous path space. -/
theorem measurable_postLastPathMap (d : ℝ) : Measurable (postLastPathMap d) := by
  apply ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2
  intro t
  exact (measurable_postLast_gen
    (f := fun w : C(ℝ≥0, ℝ) => fun s => w s + d * s)
    (fun w => w.continuous.add (continuous_const.mul continuous_subtype_val))
    (fun s => (ContinuousMap.measurable_eval s).add measurable_const)
    (s := fun _ => t) measurable_const).sub measurable_const

/-- Any continuous version of the post-last-zero Brownian path has
    the pushforward of canonical Brownian motion as its law. -/
theorem map_dmsPostLastZeroPath_eq_canonical
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (d : ℝ) {F : Ω → C(ℝ≥0, ℝ)}
    (hpath : ∀ᵐ ω ∂P, ∀ t, F ω t = dmsPostLastZeroPath d (fun s => B s ω) t) :
    P.map F = (MarkovProcess.brownianMotion 0).map (postLastPathMap d) := by
  obtain ⟨D, hDm, hD, hBD, hDc⟩ := LatticeProb.IsBrownianReal.exists_continuous_indistinguishable hB
  have heq : F =ᵐ[P] (postLastPathMap d) ∘ LatticeProb.pathMap D hDc := by
    filter_upwards [hpath, hBD] with ω hFω hBDω
    ext t
    rw [hFω t]
    have hpaths : (fun s => B s ω) = fun s => D s ω := funext hBDω
    rw [hpaths, dmsPostLastZeroPath_eq_postLast]
    rfl
  rw [Measure.map_congr heq, ← Measure.map_map (measurable_postLastPathMap d)
    (LatticeProb.measurable_pathMap D hDm hDc),
    MatedCRT.map_pathMap_eq_brownianMotion_zero hD hDm hDc]

end MatedCRT.Proposed
