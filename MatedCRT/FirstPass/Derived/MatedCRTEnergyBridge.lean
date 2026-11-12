import MatedCRT.FirstPass.Derived.MatedCRTGraphBridge

/-!
# The Dirichlet energy of the mated-CRT multigraph as an ordered-pair sum

Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* (arXiv:1807.07511), Definition 1.1,
defines the Dirichlet energy of `f` on the subgraph induced by `S` as a sum over its edges,
`∑_{e} (f(src e) - f(tgt e))²`, parallel edges counted with multiplicity. In Leonardo Bonanno's
development (adapted in Lattice-Probability) this is `MatedCRTHarmonic.GMS3.energy G S f` for the
locally finite multigraph `G = MatedCRTHarmonic.MatedCRT.graph ε ω h`.

The Green function estimates of this formalization (Berestycki–Gwynne, arXiv:2003.10320, (4.15) and
(4.16)) use the ordered-pair form `(1/2) ∑_{a, b ∈ S} m(a, b) (f(a) - f(b))²` with the edge
multiplicity `m = bmEdgeCount ε L R` of Definition 1.1. This file identifies the two:

* `gms3Energy_graph_eq`: for `ε ≥ 0` and a finite vertex set `S`,
  `GMS3.energy (graph ε ω h) S f = (1/2) ∑_{a ∈ S} ∑_{b ∈ S} bmEdgeCount ε L R a b (f a - f b)²`
  for the boundary-length pair `(L, R)` of `ω`.

The proof splits every edge into its two darts (`GMS3.sum_edgesIn_darts`), groups the darts leaving
`a` by their target, and counts them with `card_filter_outDarts_graph`.

* `sum_sum_mul_sq_sub_le_of_eqOn`: if `h` has no increment across the pairs `(a, b)` with
  `m(a, b) ≠ 0` that are not both in `T`, and `h = g` on `T`, then the ordered-pair energy of `h`
  over `S` is at most that of `g` over any finite `U` containing `S ∩ T`. With `T = V^ε(D)` this
  bounds the energy of the test function built from the discrete harmonic extension `g` on an
  annulus `D` by the energy of `g` on the subgraph `𝒢^ε(D)`.
-/

open Finset

namespace MatedCRT

open MatedCRTHarmonic MatedCRTHarmonic.LFMultigraph MatedCRTHarmonic.Harmonic

section Graph

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2}
  (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)

/-- **Dirichlet energy of the mated-CRT multigraph as an ordered-pair sum.** For `ε ≥ 0` and a
finite set `S` of vertices, the energy of `f` on the subgraph induced by `S`
(Gwynne–Miller–Sheffield Definition 1.1, a sum over edges with both ends in `S`) equals
`(1/2) ∑_{a ∈ S} ∑_{b ∈ S} m(a, b) (f(a) - f(b))²` for the edge multiplicity
`m = bmEdgeCount ε L R` of the boundary-length pair `(L, R)` of `ω`. -/
theorem gms3Energy_graph_eq (hε : 0 ≤ ε) (S : Finset ℤ) (f : ℤ → ℝ) :
    GMS3.energy (MatedCRTHarmonic.MatedCRT.graph ε ω h) S f =
      (1 / 2) * ∑ a ∈ S, ∑ b ∈ S,
        (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) a b : ℝ) * (f a - f b) ^ 2 := by
  set G := MatedCRTHarmonic.MatedCRT.graph ε ω h with hG
  set F : G.Dart → ℝ := fun d => (1 / 2) * (f (G.dsrc d) - f (G.dtgt d)) ^ 2 with hF
  have h1 : GMS3.energy G S f = ∑ e ∈ GMS3.edgesIn G S, (F (e, false) + F (e, true)) := by
    unfold GMS3.energy
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hF, dsrc_false, dsrc_true, dtgt_false, dtgt_true]
    ring
  rw [h1, GMS3.sum_edgesIn_darts G S F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (t := S) (g := G.dtgt)
    (by intro d hd; simp only [Finset.mem_filter] at hd; exact hd.2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.sum_congr rfl (g := fun _ => (1 / 2) * (f a - f b) ^ 2) (fun d hd => by
      simp only [Finset.mem_filter] at hd
      simp only [hF, (mem_outDarts G).mp hd.1.1, hd.2]), Finset.sum_const, nsmul_eq_mul,
    ← card_filter_outDarts_graph h hε a b]
  have key : ∀ A B : Finset G.Dart, A = B →
      (A.card : ℝ) * ((1 / 2) * (f a - f b) ^ 2) = (1 / 2) * ((B.card : ℝ) * (f a - f b) ^ 2) := by
    rintro A B rfl
    ring
  apply key
  ext d
  simp only [Finset.mem_filter]
  exact ⟨fun hd => ⟨hd.1.1, hd.2⟩, fun hd => ⟨⟨hd.1, hd.2 ▸ hb⟩, hd.2⟩⟩

end Graph

/-- **Energy of a function with no increment off `T`.** Let `h` have no increment across the pairs
`(a, b)` with `m(a, b) ≠ 0` that are not both in `T`, and let `h = g` on `T`. Then for finite `S` and
`U` with `S ∩ T ⊆ U`, the ordered-pair energy `∑_{a, b ∈ S} m(a, b) (h(a) - h(b))²` is at most
`∑_{a, b ∈ U} m(a, b) (g(a) - g(b))²`. -/
theorem sum_sum_mul_sq_sub_le_of_eqOn {α : Type*} {m : α → α → ℕ} {T : Set α} {S U : Finset α}
    {h g : α → ℝ} (hT : ∀ a b, m a b ≠ 0 → ¬ (a ∈ T ∧ b ∈ T) → h a = h b)
    (hhg : ∀ a ∈ T, h a = g a) (hSU : ∀ a ∈ S, a ∈ T → a ∈ U) :
    ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (h a - h b) ^ 2 ≤
      ∑ a ∈ U, ∑ b ∈ U, (m a b : ℝ) * (g a - g b) ^ 2 := by
  classical
  have hzero : ∀ a b, ¬ (a ∈ T ∧ b ∈ T) → (m a b : ℝ) * (h a - h b) ^ 2 = 0 := by
    intro a b hab
    by_cases hm : m a b = 0
    · simp [hm]
    · simp [hT a b hm hab]
  have hsub : S.filter (· ∈ T) ⊆ U := fun a ha => by
    rw [Finset.mem_filter] at ha
    exact hSU a ha.1 ha.2
  calc ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (h a - h b) ^ 2
      = ∑ a ∈ S.filter (· ∈ T), ∑ b ∈ S.filter (· ∈ T), (m a b : ℝ) * (g a - g b) ^ 2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_filter]
        split_ifs with ha
        · refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs with hb
          · rw [hhg a ha, hhg b hb]
          · exact hzero a b fun h' => hb h'.2
        · exact Finset.sum_eq_zero fun b _ => hzero a b fun h' => ha h'.1
    _ ≤ ∑ a ∈ S.filter (· ∈ T), ∑ b ∈ U, (m a b : ℝ) * (g a - g b) ^ 2 :=
        Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => by positivity
    _ ≤ ∑ a ∈ U, ∑ b ∈ U, (m a b : ℝ) * (g a - g b) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun a _ _ =>
          Finset.sum_nonneg fun b _ => by positivity

end MatedCRT
