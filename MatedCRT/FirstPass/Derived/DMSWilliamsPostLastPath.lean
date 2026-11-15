import MatedCRT.Proposed.DuplantierMillerSheffieldCone2014
import LatticeProb.Prob.WilliamsPostLastPath
import LatticeProb.Prob.BrownianRestartPath
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W0

/-! # The post-last-zero path in real and nonnegative time -/

open MeasureTheory
open scoped NNReal

noncomputable section

namespace MatedCRT.Proposed

open QuantumZipper.Williams

/-- The real-time post-last-zero path agrees with the nonnegative-time path,
with the drift removed. -/
theorem dmsPostLastZeroPath_eq_postLast (d : ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) :
    dmsPostLastZeroPath d b t =
      postLast (fun s : ℝ≥0 => b s + d * s) 0 t - d * t := by
  let c : ℝ → ℝ := fun s => b s.toNNReal + d * s
  let w : ℝ≥0 → ℝ := fun s => b s + d * s
  have hlast : MatedCRTHarmonic.MatedCRT.lastZeroR c = (lastPass w 0 : ℝ) := by
    change QuantumZipper.lastZero c = (lastPass w 0 : ℝ)
    apply lastZero_eq_lastPass
    intro s hs
    simp only [c, w, Real.coe_toNNReal s hs]
  unfold dmsPostLastZeroPath
  change c (MatedCRTHarmonic.MatedCRT.lastZeroR c + t) - d * t = _
  rw [hlast]
  simp only [c, w, postLast, sub_zero, ← NNReal.coe_add, Real.toNNReal_coe]

/-- The Williams continuous path with its drift removed has the paper's
post-last-zero coordinates. -/
theorem dmsPostLastZeroPath_eq_williams {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P)
    (d : ℝ) (ω : Ω) (t : ℝ≥0) :
    dmsPostLastZeroPath d (fun s => b s ω) t =
      LatticeProb.driftMap (-d) (LatticeProb.williamsPostLastPath hb 1 d ω) t := by
  rw [dmsPostLastZeroPath_eq_postLast]
  have hpath : (fun s : ℝ≥0 => b s ω + d * s) = dpath 1 d b ω := by
    funext s
    simp only [dpath, one_mul]
  rw [hpath]
  change postLast (dpath 1 d b ω) 0 t - d * t =
    postLast (dpath 1 d b ω) 0 t + (-d) * t
  ring

end MatedCRT.Proposed
