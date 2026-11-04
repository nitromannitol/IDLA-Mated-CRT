import HarmonicBalls.Defs.Green
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-! Translation invariance of planar harmonic functions. -/

namespace MatedCRT

open Set Metric Filter Topology InnerProductSpace

/-- A translated planar harmonic function is harmonic. -/
theorem harmonicAt_comp_add_const {f : ℂ → ℝ} {x z : ℂ}
    (hf : HarmonicAt f (x + z)) : HarmonicAt (fun w => f (w + z)) x := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hf.eventually
  have hh : HarmonicOnNhd f (ball (x + z) r) := fun y hy => hball hy
  obtain ⟨F, hF, heq⟩ := hh.exists_analyticOnNhd_ball_re_eq
  have hF₀ : AnalyticAt ℂ F (x + z) := hF (x + z) (mem_ball_self hr)
  have ha : AnalyticAt ℂ (fun w : ℂ => w + z) x := by fun_prop
  have htrans : AnalyticAt ℂ (fun w => F (w + z)) x :=
    AnalyticAt.comp (f := fun w : ℂ => w + z) (x := x) hF₀ ha
  apply (harmonicAt_congr_nhds ?_).mp htrans.harmonicAt_re
  have hnear : ∀ᶠ w : ℂ in 𝓝 x, w + z ∈ ball (x + z) r :=
    (continuousAt_id.add continuousAt_const).eventually (ball_mem_nhds (x + z) hr)
  filter_upwards [hnear] with w hw
  exact heq hw

/-- The Newtonian kernel is invariant under simultaneous translations. -/
theorem newtonKernelEReal_add_right (x y z : ℂ) :
    HarmonicBalls.newtonKernelEReal (x + z) (y + z) =
      HarmonicBalls.newtonKernelEReal x y := by
  simp [HarmonicBalls.newtonKernelEReal, HarmonicBalls.newtonKernel]

/-- Translation preserves the greatest harmonic minorant of the Newtonian kernel. -/
theorem greatestHarmonicMinorant_translate (O : Set ℂ) (x y z : ℂ) :
    HarmonicBalls.greatestHarmonicMinorant O
        (HarmonicBalls.newtonKernelEReal (x + z)) (y + z) =
      HarmonicBalls.greatestHarmonicMinorant ((fun w : ℂ => w + z) ⁻¹' O)
        (HarmonicBalls.newtonKernelEReal x) y := by
  apply le_antisymm
  · apply iSup₂_le
    intro h hh
    have hm : HarmonicBalls.IsHarmonicMinorant ((fun w : ℂ => w + z) ⁻¹' O)
        (HarmonicBalls.newtonKernelEReal x) (fun w => h (w + z)) := by
      constructor
      · intro w hw
        exact harmonicAt_comp_add_const (hh.1 (w + z) hw)
      · intro w hw
        simpa only [newtonKernelEReal_add_right] using hh.2 (w + z) hw
    exact hm.le_greatestHarmonicMinorant y
  · apply iSup₂_le
    intro h hh
    have hm : HarmonicBalls.IsHarmonicMinorant O
        (HarmonicBalls.newtonKernelEReal (x + z)) (fun w => h (w - z)) := by
      constructor
      · intro w hw
        have hw' : w - z ∈ (fun w : ℂ => w + z) ⁻¹' O := by simpa using hw
        have ht : HarmonicAt h (w + -z) := by
          simpa only [← sub_eq_add_neg] using hh.1 (w - z) hw'
        simpa only [← sub_eq_add_neg] using harmonicAt_comp_add_const ht
      · intro w hw
        have hw' : w - z ∈ (fun w : ℂ => w + z) ⁻¹' O := by simpa using hw
        have hk := newtonKernelEReal_add_right x (w - z) z
        simp only [sub_add_cancel] at hk
        rw [hk]
        exact hh.2 (w - z) hw'
    simpa using hm.le_greatestHarmonicMinorant (y + z)

/-- The Green function is invariant under simultaneous translation of its
domain and arguments. -/
theorem greenFunction_translate (O : Set ℂ) (x y z : ℂ) :
    HarmonicBalls.greenFunction O (x + z) (y + z) =
      HarmonicBalls.greenFunction ((fun w : ℂ => w + z) ⁻¹' O) x y := by
  have heq : x + z ≠ y + z ↔ x ≠ y := by
    constructor
    · intro h hxy
      exact h (congrArg (fun w : ℂ => w + z) hxy)
    · intro h hxy
      exact h (add_right_cancel hxy)
  simp only [HarmonicBalls.greenFunction, greatestHarmonicMinorant_translate,
    show (x ∈ (fun w : ℂ => w + z) ⁻¹' O) ↔ x + z ∈ O from Iff.rfl,
    show (y ∈ (fun w : ℂ => w + z) ⁻¹' O) ↔ y + z ∈ O from Iff.rfl, heq]
  simp only [HarmonicBalls.newtonKernel, add_sub_add_right_eq_sub]
  split <;> split <;> simp_all [Set.mem_preimage]

end MatedCRT
