import MatedCRT.Defs.Map
import LatticeProb.Topology.FiberIntersectionComponentCount

/-! # Cell multiplicities determined by curve fibers -/

set_option autoImplicit false

open Function Set TopologicalSpace Topology

namespace MatedCRT

/-- Quotient curves with the same fibers have the same cell multiplicities. -/
theorem cellMult_eq_of_quotient_maps_same_fibers
    (f g : ℝ → ℂ) (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (hfg : ∀ s t, f s = f t ↔ g s = g t) (ε : ℝ) (j k : ℤ) :
    cellMult ε f j k = cellMult ε g j k := by
  classical
  by_cases h : j = k
  · simp [cellMult, h]
  · simpa only [cellMult, h, ite_false, cell, HarmonicBalls.connectedComponentsIn] using
      LatticeProb.ncard_inter_components_of_quotient_maps_same_fibers f g hf hg hfg
        (Icc (ε * (j - 1)) (ε * j)) (Icc (ε * (k - 1)) (ε * k))

/-- Proper surjective curves with the same fibers have the same cell multiplicities. -/
theorem cellMult_eq_of_proper_maps_same_fibers
    (f g : ℝ → ℂ) (hf : IsProperMap f) (hg : IsProperMap g)
    (hfs : Surjective f) (hgs : Surjective g)
    (hfg : ∀ s t, f s = f t ↔ g s = g t) (ε : ℝ) (j k : ℤ) :
    cellMult ε f j k = cellMult ε g j k :=
  cellMult_eq_of_quotient_maps_same_fibers f g
    (hf.isClosedMap.isQuotientMap hf.continuous hfs)
    (hg.isClosedMap.isQuotientMap hg.continuous hgs) hfg ε j k

end MatedCRT
