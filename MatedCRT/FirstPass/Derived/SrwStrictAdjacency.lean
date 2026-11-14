import MatedCRT.FirstPass.Derived.SrwReversibleSteps
import MatedCRT.FirstPass.Derived.SrwGraphAdjBridge
import MatedCRT.FirstPass.Derived.AreaCellTransition

/-! # Adjacent steps of simple random walk -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

/-- On a locally finite loopless multigraph of positive degree, every step follows an edge. -/
theorem srwLaw_ae_adj (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m)
    (hpos : ∀ x, 0 < mdeg m x) (hloop : ∀ x, m x x = 0) (a : ℤ) :
    ∀ᵐ ξ ∂srwLaw m a, ∀ n, (srwGraph m).Adj (ξ n) (ξ (n + 1)) := by
  classical
  have hstep (x : ℤ) : srwKernel m x {y | ¬ (srwGraph m).Adj x y} = 0 := by
    rw [srwKernel_apply]
    apply measure_mono_null (t := ⋃ y : ℤ, if (srwGraph m).Adj x y then ∅ else {y})
    · intro y hy
      change ¬ (srwGraph m).Adj x y at hy
      exact mem_iUnion.mpr ⟨y, by simp [hy]⟩
    · apply measure_iUnion_null
      intro y
      by_cases hxy : (srwGraph m).Adj x y
      · simp [hxy]
      · simp only [hxy, ↓reduceIte]
        have hm : m x y = 0 := by
          by_cases he : x = y
          · subst y
            exact hloop x
          · by_contra hn
            exact hxy ⟨he, Or.inl hn⟩
        have hp : (mdeg m x : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (hpos x))
        have hz := FirstPass.Derived.mdeg_mul_srwStep_singleton hlf x y
        rw [hm, Nat.cast_zero] at hz
        exact (mul_eq_zero.mp hz).resolve_left hp
  have h := MatedCRTHarmonic.Harmonic.ae_forall_succ_mem (srwKernel m) a
    (fun x => {y | (srwGraph m).Adj x y}) hstep
  simpa only [chainLaw_srwKernel, mem_ofPred_eq] using h

/-- The simple random walk on the mated-CRT map traverses an edge at each step almost surely. -/
theorem MatedCRTEnv.srwLaw_ae_graph_adj {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ε : ℝ} (hε : 0 ≤ ε) (ω : Ω)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (a : ℤ) :
    ∀ᵐ ξ ∂srwLaw (S.mult ε ω) a, ∀ n,
      (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Adj (ξ n) (ξ (n + 1)) := by
  rw [graph_adj_eq_srwGraph hlf hε]
  have hm : IsLocallyFiniteMult (S.mult ε ω) :=
    FirstPass.Derived.isLocallyFiniteMult_bmEdgeCount hlf hε
  exact srwLaw_ae_adj _ hm (S.mult_mdeg_pos hε ω hm) (S.mult_self ε ω) a

end MatedCRT
