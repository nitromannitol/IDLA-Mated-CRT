import MatedCRT.FirstPass.Derived.MatedCRTEnergyBridge
import LatticeProb.Analysis.AnnulusHarmonicExtensionTest

/-!
# Energy of the annulus test function built from a discrete harmonic extension

Let `D = B_r(c) \ B̄_s(c)` with `0 < s < r`, let `g` be the discrete harmonic extension
(Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps*, arXiv:1807.07511, (1.6)) on `D`
of boundary data equal to `1` on `∂B_s(c)` and `0` on `∂B_r(c)`, and let
`φ = annulusTestFunction H c s r g` be the test function on the condenser `(V(B̄_s(c)), V(B_r(c)))`
that equals `g` on `V(D)`, `1` on the other vertices whose cells meet `B̄_s(c)` and `0` elsewhere.
When adjacent vertices have intersecting cells, `φ` has no increment across an edge that is not
inside `V(D)`, so its Dirichlet energy is at most the Dirichlet energy of `g` on the subgraph
`𝒢(D)` induced by `V(D)`. This is the comparison used in the proof of Berestycki–Gwynne
(arXiv:2003.10320), Lemma 4.3, to bound the effective conductance of an annulus by the energy of the
harmonic extension, which Gwynne–Miller–Sheffield Theorem 3.2 controls.

* `sum_sum_mul_sq_sub_annulusTestFunction_le`: the comparison for the ordered-pair energy
  `∑_{a, b} m(a, b) (φ(a) - φ(b))²` of an arbitrary edge multiplicity `m` whose positive entries join
  intersecting cells.
* `gms3Energy_annulusTestFunction_le`: the same comparison for the Dirichlet energy
  `GMS3.energy` of the mated-CRT multigraph (Gwynne–Miller–Sheffield, Definition 1.1).
-/

open Metric Set Finset

namespace MatedCRT

open MatedCRTHarmonic LatticeProb

/-- **Energy of the annulus test function, ordered-pair form.** Let the positive entries of the edge
multiplicity `m` join vertices with intersecting cells, let the cells be preconnected, and let `g`
be the discrete harmonic extension on `D = B_r(c) \ B̄_s(c)` of boundary data `f` equal to `1` on
`∂B_s(c)` and `0` on `∂B_r(c)`, no cell meeting both circles. Then for finite vertex sets `S` and
`U` with `S ∩ V(D) ⊆ U`, the ordered-pair energy of `annulusTestFunction H c s r g` over `S` is at
most that of `g` over `U`. -/
theorem sum_sum_mul_sq_sub_annulusTestFunction_le {V E : Type*} (G : LFMultigraph V E)
    {m : V → V → ℕ} {H : V → Set ℂ} {c : ℂ} {s r : ℝ} {f : ℂ → ℝ} {g : V → ℝ}
    (hadj : ∀ a b, m a b ≠ 0 → (H a ∩ H b).Nonempty)
    (hH : ∀ x, IsPreconnected (H x)) (hs : 0 < s) (hsr : s < r)
    (hf1 : ∀ z ∈ sphere c s, f z = 1) (hf0 : ∀ z ∈ sphere c r, f z = 0)
    (hsep : ∀ x, (H x ∩ sphere c s).Nonempty → ¬(H x ∩ sphere c r).Nonempty)
    (hg : G.IsHarmonicExtension H (ball c r \ closedBall c s) f g) {S U : Finset V}
    (hSU : ∀ a ∈ S, a ∈ verticesMeeting H (ball c r \ closedBall c s) → a ∈ U) :
    ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) *
        (annulusTestFunction H c s r g a - annulusTestFunction H c s r g b) ^ 2 ≤
      ∑ a ∈ U, ∑ b ∈ U, (m a b : ℝ) * (g a - g b) ^ 2 := by
  obtain ⟨-, -, hD, hpair⟩ := annulusTestFunction_spec G hH hs hsr hf1 hf0 hsep hg
  refine sum_sum_mul_sq_sub_le_of_eqOn
    (T := verticesMeeting H (ball c r \ closedBall c s)) (fun a b hm hab => ?_) hD hSU
  exact hpair a b (hadj a b hm) (not_and_or.1 hab)

/-- **Energy of the annulus test function on the mated-CRT multigraph.** For `ε ≥ 0`, if adjacent
vertices of the mated-CRT multigraph `𝒢^ε` have intersecting cells `H`, the cells are preconnected,
and `g` is the discrete harmonic extension on `D = B_r(c) \ B̄_s(c)` of boundary data equal to `1` on
`∂B_s(c)` and `0` on `∂B_r(c)` (no cell meeting both circles), then the Dirichlet energy of
`annulusTestFunction H c s r g` on the subgraph induced by `S` is at most the Dirichlet energy of
`g` on the subgraph induced by any finite `U ⊇ S ∩ V(D)`. -/
theorem gms3Energy_annulusTestFunction_le {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hω : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω) (hε : 0 ≤ ε)
    {H : ℤ → Set ℂ} {c : ℂ} {s r : ℝ} {f : ℂ → ℝ} {g : ℤ → ℝ}
    (hadj : ∀ a b : ℤ, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) a b ≠ 0 →
      (H a ∩ H b).Nonempty)
    (hH : ∀ x, IsPreconnected (H x)) (hs : 0 < s) (hsr : s < r)
    (hf1 : ∀ z ∈ sphere c s, f z = 1) (hf0 : ∀ z ∈ sphere c r, f z = 0)
    (hsep : ∀ x, (H x ∩ sphere c s).Nonempty → ¬(H x ∩ sphere c r).Nonempty)
    (hg : (MatedCRTHarmonic.MatedCRT.graph ε ω hω).IsHarmonicExtension H
      (ball c r \ closedBall c s) f g) {S U : Finset ℤ}
    (hSU : ∀ a ∈ S, a ∈ verticesMeeting H (ball c r \ closedBall c s) → a ∈ U) :
    GMS3.energy (MatedCRTHarmonic.MatedCRT.graph ε ω hω) S (annulusTestFunction H c s r g) ≤
      GMS3.energy (MatedCRTHarmonic.MatedCRT.graph ε ω hω) U g := by
  rw [gms3Energy_graph_eq hω hε, gms3Energy_graph_eq hω hε]
  exact mul_le_mul_of_nonneg_left
    (sum_sum_mul_sq_sub_annulusTestFunction_le _ hadj hH hs hsr hf1 hf0 hsep hg hSU)
    (by norm_num)

end MatedCRT
