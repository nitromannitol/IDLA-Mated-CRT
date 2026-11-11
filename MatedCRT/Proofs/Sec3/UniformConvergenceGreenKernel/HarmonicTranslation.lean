import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.ContinuumBoundary
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.HarmonicTranslation
import LatticeProb.Analysis.LaplacianCalculus

/-! # Translation of harmonic functions

`harmonicAt_comp_add_const` (translation of harmonic functions) is imported from
`Proofs/Sec3/ConvergenceNormalizedExitTime/HarmonicTranslation` (Lemma 3.7), so that Lemmas 3.3
and 3.7 import together (F12). -/

open Filter InnerProductSpace
open scoped Topology Laplacian

namespace MatedCRT

/-- The Laplacian commutes with translation of the argument. -/
theorem laplacian_comp_add_const (f : ℂ → ℝ) (a x : ℂ) :
    Δ (fun z => f (z + a)) x = Δ f (x + a) :=
  LatticeProb.LaplacianCalculus.laplacian_comp_add_right f a x

/-- Translating a harmonic minorant preserves the minorant relation. -/
theorem isHarmonicMinorant_comp_add_const {O : Set ℂ} {u : ℂ → EReal} {h : ℂ → ℝ}
    (hh : HarmonicBalls.IsHarmonicMinorant O u h) (a : ℂ) :
    HarmonicBalls.IsHarmonicMinorant ((fun z : ℂ => z + a) ⁻¹' O)
      (fun z => u (z + a)) (fun z => h (z + a)) := by
  constructor
  · intro z hz
    exact harmonicAt_comp_add_const (hh.1 (z + a) hz)
  · intro z hz
    exact hh.2 (z + a) hz

/-- The greatest harmonic minorant commutes with translation of the domain and
the obstacle. -/
theorem greatestHarmonicMinorant_comp_add_const (O : Set ℂ) (u : ℂ → EReal) (a y : ℂ) :
    HarmonicBalls.greatestHarmonicMinorant ((fun z : ℂ => z + a) ⁻¹' O)
      (fun z => u (z + a)) y = HarmonicBalls.greatestHarmonicMinorant O u (y + a) := by
  unfold HarmonicBalls.greatestHarmonicMinorant
  apply le_antisymm
  · refine iSup_le fun h => iSup_le fun hh => ?_
    let g : ℂ → ℝ := fun z => h (z - a)
    have hg : HarmonicBalls.IsHarmonicMinorant O u g := by
      have h' := isHarmonicMinorant_comp_add_const hh (-a)
      simpa [g, sub_eq_add_neg, Set.preimage_preimage, Function.comp_def, add_assoc] using h'
    calc
      (h y : EReal) = (g (y + a) : EReal) := by simp [g]
      _ ≤ ⨆ (f : ℂ → ℝ) (_ : HarmonicBalls.IsHarmonicMinorant O u f), (f (y + a) : EReal) :=
        le_iSup_of_le g (le_iSup_of_le hg le_rfl)
  · refine iSup_le fun h => iSup_le fun hh => ?_
    have hg := isHarmonicMinorant_comp_add_const hh a
    exact le_iSup_of_le (fun z => h (z + a)) (le_iSup_of_le hg le_rfl)

/-- The Green function is invariant under simultaneous translations of the
domain, pole and evaluation point. -/
theorem greenFunction_comp_add_const (O : Set ℂ) (a x y : ℂ) :
    HarmonicBalls.greenFunction ((fun z : ℂ => z + a) ⁻¹' O) x y =
      HarmonicBalls.greenFunction O (x + a) (y + a) := by
  classical
  have hk : (fun z => HarmonicBalls.newtonKernelEReal (x + a) (z + a)) =
      HarmonicBalls.newtonKernelEReal x := by
    funext z
    simp [HarmonicBalls.newtonKernelEReal, HarmonicBalls.newtonKernel]
  have hgm := greatestHarmonicMinorant_comp_add_const O
    (HarmonicBalls.newtonKernelEReal (x + a)) a y
  rw [hk] at hgm
  unfold HarmonicBalls.greenFunction
  change (if x + a ∈ O ∧ y + a ∈ O ∧ x ≠ y then
    HarmonicBalls.newtonKernel x y -
      (HarmonicBalls.greatestHarmonicMinorant ((fun z : ℂ => z + a) ⁻¹' O)
        (HarmonicBalls.newtonKernelEReal x) y).toReal else 0) = _
  have heq : (x + a ≠ y + a) ↔ x ≠ y := by
    constructor
    · intro h hxy
      exact h (by rw [hxy])
    · intro h hxy
      exact h (add_right_cancel hxy)
  simp only [hgm, HarmonicBalls.newtonKernel, add_sub_add_right_eq_sub]
  by_cases hxy : x = y
  · subst y
    simp
  · have hxy' : x + a ≠ y + a := heq.mpr hxy
    simp [hxy, hxy']

/-- The Green function of a translated ball reduces to the centered case. -/
theorem greenFunction_ball_eq_centered (z y x : ℂ) (r : ℝ) :
    HarmonicBalls.greenFunction (Metric.ball z r) y x =
      HarmonicBalls.greenFunction (Metric.ball 0 r) (y - z) (x - z) := by
  have hpre : (fun w : ℂ => w + z) ⁻¹' Metric.ball z r = Metric.ball 0 r := by
    ext w
    simp [Metric.mem_ball, dist_eq_norm]
  have h := greenFunction_comp_add_const (Metric.ball z r) z (y - z) (x - z)
  rw [hpre] at h
  simpa using h.symm

/-- The Green function of any ball is uniformly small near its boundary. -/
theorem greenFunction_ball_boundary_small {r : ℝ} {z y : ℂ}
    (hy : y ∈ Metric.ball z r) (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      ∀ x ∈ Metric.closedBall z r \ Metric.closedBall z r',
        |c * HarmonicBalls.greenFunction (Metric.ball z r) y x| < δ := by
  have hy' : y - z ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  obtain ⟨r', hr'0, hr'r, hb⟩ := greenFunction_centered_ball_boundary_small hy' c hδ
  refine ⟨r', hr'0, hr'r, fun x hx => ?_⟩
  have hx' : x - z ∈ Metric.closedBall (0 : ℂ) r \ Metric.closedBall 0 r' := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  simpa [greenFunction_ball_eq_centered] using hb (x - z) hx'

end MatedCRT
