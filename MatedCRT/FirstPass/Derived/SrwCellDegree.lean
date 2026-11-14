import MatedCRT.Proofs.Infra.DiscretePotential
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement

/-! # Multigraph degree and cell conductance -/

set_option autoImplicit false

namespace MatedCRT

open ReflectedGMS.GMS

/-- Under a conductance-preserving relabelling, total cell conductance is the multigraph degree. -/
theorem cell_pi_eq_mdeg (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m)
    (H : CellConfig) (e : ℤ ≃ H.cells) (a : ℤ)
    (hc : ∀ b, H.c (e a) (e b) = (m a b : ℝ)) :
    H.pi (e a) = (mdeg m a : ℝ) := by
  classical
  rw [CellConfig.pi, ← e.tsum_eq, mdeg_cast_eq hlf]
  simp_rw [hc]
  apply tsum_eq_sum
  intro b hb
  have : m a b = 0 := by
    by_contra h
    exact hb ((mem_nbrs hlf).2 h)
  simp [this]

end MatedCRT
