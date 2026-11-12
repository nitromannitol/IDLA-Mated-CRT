import MatedCRT.FirstPass.Derived.GreenFlowEnergy
import LatticeProb.Network.SegmentPathPoissonBound
import LatticeProb.Analysis.FatInballFlowEnergy

/-!
# The killed Green function bounded by random segment paths through fat cells

This is the effective resistance upper bound of [BG20, lem-eff-res-upper] in the form used for
the crude Green function bound [BG20, lem-eff-res-diag]. Let the vertices `a ∈ S` of the
multigraph with edge multiplicity `m` carry cells `H a ⊆ ℂ` that are pairwise disjoint up to
null sets, of diameter in `[r, M]`, contained in `closedBall u R`, and fat: each contains a ball
of radius `κ · diam (H a)`. For a direction `θ`, let the path `segmentPath u ρ H Y F θ` run
through the cells met by the segment from `u` in direction `θ`.

If every such path is self-avoiding, uses only edges of `m`, starts at the pole `x ∈ A`, stays in
`S` and ends outside `A`, then its expected crossing flow is a unit flow from `x` out of `A`
(`LatticeProb.sum_segmentPathFlow_eq_ite_of_path`) whose energy is at most
`Δ ((log₂ (M/r) + 1) · 16/κ² + 8 log (R/r)/κ²)` when every degree is at most `Δ`
(`LatticeProb.sum_sum_sq_div_segmentPathFlow_le`). The Thomson bound for the killed Green
function (`greenFn_le_mdeg_mul_flowEnergy`) then gives, for every `a`,

  `G_A(a, x) ≤ deg(x) · ½ · Δ · ((log₂ (M/r) + 1) · 16/κ² + 8 log (R/r)/κ²)`.

The existence of the paths is a hypothesis of the lemma (the topological input of
[BG20, lem-eff-res-upper], step 1).

`greenFn_le_of_segmentPaths_of_inballs` is the same bound when the cells are only assumed to have
pairwise disjoint inballs `ball (c a) (κ · diam (H a))` (`LatticeProb.sum_sum_sq_div_le_of_fatInballs`):
the space-filling curve is parametrized by LQG area, which is singular to Lebesgue measure, so
almost-disjointness of the cells for Lebesgue measure is not available, while disjointness of open
sets inside distinct cells is.
-/

namespace MatedCRT

open Finset Function Metric MeasureTheory LatticeProb

variable {m : ℤ → ℤ → ℕ}

/-- The sum of the edge multiplicities at `a` over any finite set is at most the degree of `a`. -/
theorem sum_le_mdeg (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (S : Finset ℤ) (a : ℤ) :
    ∑ b ∈ S, m a b ≤ mdeg m a := by
  rw [mdeg, finsum_eq_sum_of_support_subset (s := S ∪ (hlf a).toFinset) _ fun b hb => by
    simp only [Function.mem_support] at hb
    simp [hb]]
  exact Finset.sum_le_sum_of_subset Finset.subset_union_left

/-- **Crude bound for the killed Green function by random segment paths through fat cells.**
If in every direction the path through the cells met by the segment from `u` is self-avoiding,
uses only edges of the multigraph, starts at the pole `x ∈ A`, stays in `S` and ends outside `A`,
and the cells of `S` are fat (inradius `κ · diam`), of diameter in `[r, M]`, inside
`closedBall u R`, with degrees at most `Δ`, then every entry `G_A(a, x)` is at most
`deg(x) · ½ · Δ · ((log₂ (M/r) + 1) · 16/κ² + 8 log (R/r)/κ²)`. -/
theorem greenFn_le_of_segmentPaths (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hsymm : ∀ a b, m a b = m b a)
    {A S Y : Finset ℤ} (hAS : A ⊆ S) (hS : ∀ a ∈ A, ∀ b, m a b ≠ 0 → b ∈ S) {x : ℤ}
    (hx : x ∈ A) {H : ℤ → Set ℂ} {c : ℤ → ℂ} {u : ℂ} {ρ κ r M R Δ : ℝ} (hκ : 0 < κ)
    (hr : 0 < r) (hrM : r ≤ M) (hrR : r ≤ R) (hΔ : 0 ≤ Δ)
    (hd : (S : Set ℤ).Pairwise (AEDisjoint volume on H))
    (hHc : ∀ y ∈ Y, IsClosed (H y))
    (hHm : ∀ a ∈ S, MeasurableSet (H a)) (hb : ∀ a ∈ S, Bornology.IsBounded (H a))
    (hball : ∀ a ∈ S, ball (c a) (κ * diam (H a)) ⊆ H a)
    (hlo : ∀ a ∈ S, r ≤ diam (H a)) (hhi : ∀ a ∈ S, diam (H a) ≤ M)
    (hsub : ∀ a ∈ S, H a ⊆ closedBall u R)
    (hdeg : ∀ a ∈ S, (mdeg m a : ℝ) ≤ Δ)
    {F : Finset ℤ → List ℤ} (hF : ∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T)
    (hnd : ∀ θ, (segmentPath u ρ H Y F θ).Nodup)
    (hchain : ∀ θ, (segmentPath u ρ H Y F θ).IsChain fun a b => m a b ≠ 0)
    (hpath : ∀ θ, ∃ p, segmentPath u ρ H Y F θ = x :: p ∧ (∀ v ∈ x :: p, v ∈ S) ∧
      (x :: p).getLast (List.cons_ne_nil x p) ∉ A) (a : ℤ) :
    greenFn m (A : Set ℤ) a x ≤ (mdeg m x : ℝ) * ((1 / 2) * (Δ *
      ((Real.logb 2 (M / r) + 1) * (16 / κ ^ 2) + 8 * Real.log (R / r) / κ ^ 2))) := by
  have hchain' : ∀ θ, (segmentPath u ρ H Y F θ).IsChain fun a b => (m a b : ℝ) ≠ 0 :=
    fun θ => (hchain θ).imp fun ⦃_ _⦄ h => by exact_mod_cast h
  have hR' : ∀ a b : ℤ, (m a b : ℝ) ≠ 0 → (m b a : ℝ) ≠ 0 := fun a b h => by
    rwa [hsymm b a]
  refine (greenFn_le_mdeg_mul_flowEnergy hlf hcons hsymm hAS hS hx
    (θ := segmentPathFlow u ρ H Y F) (fun a b => segmentPathFlow_antisymm a b)
    (fun a b h0 => segmentPathFlow_eq_zero_of_not_rel hR' hchain' (by simp [h0]))
    (sum_segmentPathFlow_eq_ite_of_path hHc hpath) a).trans ?_
  have hE := sum_sum_sq_div_segmentPathFlow_le (c := c) (w := fun a b => (m a b : ℝ))
    hκ hr hrM hrR hΔ hd hHc hHm hb hball hlo hhi hsub
    (fun a b => show (m a b : ℝ) = m b a by rw [hsymm a b]) (fun _ _ => Nat.cast_nonneg _)
    (fun a b h => by
      have h' : m a b ≠ 0 := by simpa using h
      simpa using Nat.one_le_iff_ne_zero.2 h')
    (fun a ha => show ∑ b ∈ S, (m a b : ℝ) ≤ Δ by
      rw [← Nat.cast_sum]
      exact (Nat.cast_le.2 (sum_le_mdeg hlf S a)).trans (hdeg a ha))
    hF hnd hchain'
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (by norm_num))
    (Nat.cast_nonneg _)

/-- **Crude bound for the killed Green function by random segment paths, disjoint inballs.**
The bound of `greenFn_le_of_segmentPaths` with the almost-disjointness and measurability of the
cells replaced by pairwise disjointness of the inballs `ball (c a) (κ · diam (H a))`. -/
theorem greenFn_le_of_segmentPaths_of_inballs (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hsymm : ∀ a b, m a b = m b a)
    {A S Y : Finset ℤ} (hAS : A ⊆ S) (hS : ∀ a ∈ A, ∀ b, m a b ≠ 0 → b ∈ S) {x : ℤ}
    (hx : x ∈ A) {H : ℤ → Set ℂ} {c : ℤ → ℂ} {u : ℂ} {ρ κ r M R Δ : ℝ} (hκ : 0 < κ)
    (hr : 0 < r) (hrM : r ≤ M) (hrR : r ≤ R) (hΔ : 0 ≤ Δ)
    (hdisj : (S : Set ℤ).PairwiseDisjoint fun a => ball (c a) (κ * diam (H a)))
    (hHc : ∀ y ∈ Y, IsClosed (H y)) (hb : ∀ a ∈ S, Bornology.IsBounded (H a))
    (hball : ∀ a ∈ S, ball (c a) (κ * diam (H a)) ⊆ H a)
    (hlo : ∀ a ∈ S, r ≤ diam (H a)) (hhi : ∀ a ∈ S, diam (H a) ≤ M)
    (hsub : ∀ a ∈ S, H a ⊆ closedBall u R)
    (hdeg : ∀ a ∈ S, (mdeg m a : ℝ) ≤ Δ)
    {F : Finset ℤ → List ℤ} (hF : ∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T)
    (hnd : ∀ θ, (segmentPath u ρ H Y F θ).Nodup)
    (hchain : ∀ θ, (segmentPath u ρ H Y F θ).IsChain fun a b => m a b ≠ 0)
    (hpath : ∀ θ, ∃ p, segmentPath u ρ H Y F θ = x :: p ∧ (∀ v ∈ x :: p, v ∈ S) ∧
      (x :: p).getLast (List.cons_ne_nil x p) ∉ A) (a : ℤ) :
    greenFn m (A : Set ℤ) a x ≤ (mdeg m x : ℝ) * ((1 / 2) * (Δ *
      ((Real.logb 2 (M / r) + 1) * (16 / κ ^ 2) + 8 * Real.log (R / r) / κ ^ 2))) := by
  have hchain' : ∀ θ, (segmentPath u ρ H Y F θ).IsChain fun a b => (m a b : ℝ) ≠ 0 :=
    fun θ => (hchain θ).imp fun ⦃_ _⦄ h => by exact_mod_cast h
  have hR' : ∀ a b : ℤ, (m a b : ℝ) ≠ 0 → (m b a : ℝ) ≠ 0 := fun a b h => by
    rwa [hsymm b a]
  refine (greenFn_le_mdeg_mul_flowEnergy hlf hcons hsymm hAS hS hx
    (θ := segmentPathFlow u ρ H Y F) (fun a b => segmentPathFlow_antisymm a b)
    (fun a b h0 => segmentPathFlow_eq_zero_of_not_rel hR' hchain' (by simp [h0]))
    (sum_segmentPathFlow_eq_ite_of_path hHc hpath) a).trans ?_
  have hE := sum_sum_sq_div_le_of_fatInballs (θ := segmentPathFlow u ρ H Y F)
    (w := fun a b => (m a b : ℝ)) hκ hr hrM hrR hΔ hdisj hb hball hlo hhi hsub
    (fun _ _ => Nat.cast_nonneg _)
    (fun a b h => by
      have h' : m a b ≠ 0 := fun h0 =>
        h (segmentPathFlow_eq_zero_of_not_rel hR' hchain' (by simp [h0]))
      simpa using Nat.one_le_iff_ne_zero.2 h')
    (fun a ha => show ∑ b ∈ S, (m a b : ℝ) ≤ Δ by
      rw [← Nat.cast_sum]
      exact (Nat.cast_le.2 (sum_le_mdeg hlf S a)).trans (hdeg a ha))
    (fun a _ b _ => abs_segmentPathFlow_le_one hHc hnd a b)
    (fun a ha hfar b _ => abs_segmentPathFlow_le_diam_div_infDist hHc hnd
      (fun θ a h => mem_segmentDirections_of_mem_segmentPath hF h) (hb a ha)
      (diam_nonneg.trans_lt hfar) b)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (by norm_num))
    (Nat.cast_nonneg _)

end MatedCRT
