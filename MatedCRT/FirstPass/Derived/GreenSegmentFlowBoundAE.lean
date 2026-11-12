import MatedCRT.FirstPass.Derived.GreenSegmentFlowBound
import LatticeProb.Network.SegmentPathFlowAE

/-!
# The Green kernel on the inner boundary through segment paths of almost every direction

The statement of `exists_mem_innerBoundary_greenKernel_le_segmentPaths` with the self-avoiding,
chain and reachability properties of the segment paths required for almost every direction only.

## Main statement

* `MatedCRT.exists_mem_innerBoundary_greenKernel_le_segmentPaths_ae`.
-/

namespace MatedCRT

open Finset Metric Set LatticeProb

variable {m : ℤ → ℤ → ℕ}

/-- **The Green kernel on the inner boundary through the segment-path flow, almost every
direction.** For finite `x ∈ A ⊆ B ⊆ S`, cells `H` and the expected flow of self-avoiding paths
through the cells met by the segment from `z`, starting at `x`, staying in `S` and ending outside
`B` for almost every direction: some `y ∈ A` with a neighbour outside `A`, minimal for
`v ↦ G_B(v, x)` on `A`, satisfies `g_B(y, x) ≤ ∑_{a ∈ S \ A} deg(a) (diam H_a / dist(z, H_a))²`. -/
theorem exists_mem_innerBoundary_greenKernel_le_segmentPaths_ae
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hsymm : ∀ a b, m a b = m b a) {B A S : Finset ℤ} (hBS : B ⊆ S) (hAB : A ⊆ B)
    (hS : ∀ a ∈ B, ∀ b, m a b ≠ 0 → b ∈ S) {x : ℤ} (hx : x ∈ A)
    {H : ℤ → Set ℂ} {z : ℂ} {ℓ : ℝ} {Y : Finset ℤ} {F : Finset ℤ → List ℤ}
    (hF : ∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) (hHc : ∀ y ∈ Y, IsClosed (H y))
    (hnd : ∀ᵐ θ ∂uniformDirection, (segmentPath z ℓ H Y F θ).Nodup)
    (hchain : ∀ᵐ θ ∂uniformDirection, (segmentPath z ℓ H Y F θ).IsChain fun a b => m a b ≠ 0)
    (hpath : ∀ᵐ θ ∂uniformDirection, ∃ p, segmentPath z ℓ H Y F θ = x :: p ∧
      (∀ v ∈ x :: p, v ∈ S) ∧ (x :: p).getLast (List.cons_ne_nil x p) ∉ B)
    (hb : ∀ a ∈ S, a ∉ A → Bornology.IsBounded (H a))
    (hpos : ∀ a ∈ S, a ∉ A → 0 < infDist z (H a)) :
    ∃ y ∈ A, (∃ w, w ∉ A ∧ m y w ≠ 0) ∧
      (∀ v ∈ A, greenFn m (B : Set ℤ) y x ≤ greenFn m (B : Set ℤ) v x) ∧
      greenKernel m (B : Set ℤ) y x ≤
        ∑ a ∈ S with a ∉ A, (mdeg m a : ℝ) * (diam (H a) / infDist z (H a)) ^ 2 := by
  have hR' : ∀ a b, m a b ≠ 0 → m b a ≠ 0 := fun a b h => by rwa [hsymm b a]
  have hθ := segmentPathFlow_antisymm (z := z) (ρ := ℓ) (H := H) (Y := Y) (F := F)
  have hθc : ∀ a b, m a b = 0 → segmentPathFlow z ℓ H Y F a b = 0 := fun a b h0 =>
    segmentPathFlow_eq_zero_of_not_rel_ae hR' hchain (not_not.2 h0)
  obtain ⟨y, hyA, hyout, hymin, hyle⟩ := exists_mem_innerBoundary_greenKernel_le_restrictedEnergy
    hlf hcons hsymm hBS hAB hS hx hθ hθc (sum_segmentPathFlow_eq_ite_of_path_ae hHc hpath)
  refine ⟨y, hyA, hyout, hymin, hyle.trans (restrictedFlowEnergy_le_of_edgeBound hlf hsymm hθ hθc
    (d := fun a => diam (H a) / infDist z (H a)) fun a ha haA b _ => ?_)⟩
  exact abs_segmentPathFlow_le_diam_div_infDist_ae hHc hnd
    (fun θ a h => mem_segmentDirections_of_mem_segmentPath hF h) (hb a ha haA) (hpos a ha haA) b

end MatedCRT
