import HarmonicBalls.Defs.Green

/-!
Domain monotonicity of the Green function, with the diagonal convention used by
`HarmonicBalls`. This follows directly from restriction of harmonic minorants.
-/

open Set Metric

namespace HarmonicBalls

/-- The Green function increases when a bounded domain is enlarged. -/
theorem greenFunction_le_of_subset {O U : Set ℂ} (hU : Bornology.IsBounded U)
    (hsub : O ⊆ U) (x y : ℂ) : greenFunction O x y ≤ greenFunction U x y := by
  classical
  by_cases h : x ∈ O ∧ y ∈ O ∧ x ≠ y
  · have hUxy : x ∈ U ∧ y ∈ U ∧ x ≠ y := ⟨hsub h.1, hsub h.2.1, h.2.2⟩
    have hminor : greatestHarmonicMinorant U (newtonKernelEReal x) y ≤
        greatestHarmonicMinorant O (newtonKernelEReal x) y := by
      apply iSup₂_le
      intro f hf
      exact (show IsHarmonicMinorant O (newtonKernelEReal x) f from
        ⟨hf.1.mono hsub, fun z hz => hf.2 z (hsub hz)⟩).le_greatestHarmonicMinorant y
    obtain ⟨r, hr⟩ := hU.subset_closedBall x
    have hlow := (isHarmonicMinorant_const_newtonKernelEReal hr).le_greatestHarmonicMinorant y
    have hbot : greatestHarmonicMinorant U (newtonKernelEReal x) y ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
    have hup : greatestHarmonicMinorant O (newtonKernelEReal x) y ≤
        (newtonKernel x y : EReal) := by
      simpa [newtonKernelEReal, Ne.symm h.2.2] using
        greatestHarmonicMinorant_le (u := newtonKernelEReal x) h.2.1
    have htop : greatestHarmonicMinorant O (newtonKernelEReal x) y ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) hup
    have hreal := EReal.toReal_le_toReal hminor hbot htop
    simpa [greenFunction, h.1, h.2.1, h.2.2, hUxy.1, hUxy.2.1] using
      (sub_le_sub_left hreal (newtonKernel x y))
  · simpa only [greenFunction, h, ↓reduceIte] using greenFunction_nonneg hU x y

end HarmonicBalls
