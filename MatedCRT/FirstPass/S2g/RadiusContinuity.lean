import MatedCRT.Defs.Setting
import MatedCRT.FirstPass.S2g.ClosureRadius

/-! # Continuity of the closure radius under Hausdorff continuity (fp-S2g, q1; CHATGPT-q1-open-steps.md H5, step P2)

If `t ↦ Λ_t` is Hausdorff continuous on a set `S` (the closure-continuity field of Theorem 1.1, HB
`HarmonicBalls.HausdorffContinuousOn`) and every `Λ_t` is bounded, then `t ↦ closureRadius (Λ_t)` is continuous on `S`.
Deterministic: the norm is 1-Lipschitz, so a Hausdorff perturbation moves the supremum of the norms by at most the
perturbation. -/

namespace MatedCRT

open Set Filter Topology Metric HarmonicBalls
open scoped ENNReal

/-- A Hausdorff perturbation of `M` by `ε` moves the closure radius by at most `ε`:
`closureRadius L ≤ closureRadius M + ε` when `hausdorffEDist L M < ε` and `M` is bounded. -/
theorem closureRadius_le_add_of_hausdorffEDist {L M : Set ℂ} (hMb : Bornology.IsBounded M) {ε : ℝ} (hε : 0 ≤ ε)
    (hd : hausdorffEDist L M < ENNReal.ofReal ε) :
    closureRadius L ≤ closureRadius M + ε := by
  have hM0 : 0 ≤ closureRadius M :=
    Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)
  have hbdd : BddAbove ((fun x : ℂ => ‖x‖) '' closure M) :=
    ((hMb.isCompact_closure).image continuous_norm).bddAbove
  have hcl : hausdorffEDist (closure L) (closure M) < ENNReal.ofReal ε := by
    rw [hausdorffEDist_closure]
    exact hd
  unfold closureRadius
  refine Real.sSup_le ?_ (add_nonneg hM0 hε)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hx hcl
  have hdist : dist x y < ε := edist_lt_ofReal.mp hxy
  have hyle : ‖y‖ ≤ sSup ((fun x : ℂ => ‖x‖) '' closure M) :=
    le_csSup hbdd ⟨y, hy, rfl⟩
  have htri : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
  rw [← dist_eq_norm] at htri
  linarith

/-- **Continuity of the closure radius (P2, q1).** If `t ↦ Λ_t` is Hausdorff continuous on `S` and each `Λ_t` is
bounded, then `t ↦ closureRadius (Λ_t)` is continuous on `S`. -/
theorem continuousOn_closureRadius_of_hausdorffContinuousOn {Λ : ℝ → Set ℂ} {S : Set ℝ}
    (hH : HausdorffContinuousOn Λ S) (hb : ∀ t, Bornology.IsBounded (Λ t)) :
    ContinuousOn (fun t => closureRadius (Λ t)) S := by
  intro t ht
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hev := hH t ht (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (by linarith))
  filter_upwards [hev] with s hs
  have h1 := closureRadius_le_add_of_hausdorffEDist (hb t) (by linarith : (0 : ℝ) ≤ ε / 2) hs
  have h2 := closureRadius_le_add_of_hausdorffEDist (hb s) (by linarith : (0 : ℝ) ≤ ε / 2)
    (by rw [hausdorffEDist_comm]; exact hs)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end MatedCRT
