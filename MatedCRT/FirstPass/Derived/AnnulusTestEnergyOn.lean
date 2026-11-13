import MatedCRT.FirstPass.Derived.AnnulusTestEnergy
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.EnergyOn

/-!
# The annulus test function has finite-sum energy at most the energy of the harmonic extension

Berestycki–Gwynne (2020), proof of Lemma 4.3, the step from (4.7) to (4.15). Let `g` be the discrete harmonic
extension on `D = B_r(c) \ B̄_s(c)` of boundary data equal to `1` on `∂B_s(c)` and `0` on `∂B_r(c)`, for the
mated-CRT multigraph `𝒢^ε`, with preconnected cells, adjacent vertices having intersecting cells, and no cell meeting
both circles. Then the test function `annulusTestFunction H c s r g` (equal to `1` on `V(B̄_s(c))` and `0` off
`V(B_r(c))`) has, on every finite vertex set `T`, ordered-pair energy
`(1/2) ∑_{k, l ∈ T} m(k, l) (h k - h l)²` at most the edge energy `Energy(g; 𝒢^ε(V(D)))` of Gwynne–Miller–Sheffield
(2019), Definition 1.1, which is the quantity bounded in (4.7).
-/

set_option autoImplicit false

open Metric Set
open scoped ENNReal

namespace MatedCRT

open MatedCRTHarmonic LatticeProb

/-- **The edge energy is monotone in the vertex set.** `Energy(g; G(S)) ≤ Energy(g; G(S'))` for `S ⊆ S'`: the edges
with both ends in `S` are among those with both ends in `S'`. -/
theorem lfMultigraph_energyOn_mono {V E : Type*} (G : LFMultigraph V E) {S S' : Set V} (hSS' : S ⊆ S')
    (g : V → ℝ) : G.energyOn S g ≤ G.energyOn S' g :=
  ENNReal.tsum_mono_subtype (fun e : E => ENNReal.ofReal ((g (G.src e) - g (G.tgt e)) ^ 2))
    (s := {e | G.src e ∈ S ∧ G.tgt e ∈ S}) (t := {e | G.src e ∈ S' ∧ G.tgt e ∈ S'})
    fun _ he => ⟨hSS' he.1, hSS' he.2⟩

/-- **The edge energy on a finite vertex set is the finite edge sum** `GMS3.energy`: `Energy(g; G(S))` of
Gwynne–Miller–Sheffield (2019), Definition 1.1, for finite `S`. -/
theorem lfMultigraph_energyOn_coe_finset {V E : Type*} (G : LFMultigraph V E) (S : Finset V) (g : V → ℝ) :
    G.energyOn (S : Set V) g = ENNReal.ofReal (GMS3.energy G S g) := by
  classical
  have hset : {e : E | G.src e ∈ (S : Set V) ∧ G.tgt e ∈ (S : Set V)} =
      ((GMS3.edgesIn G S : Finset E) : Set E) := by
    ext e
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, GMS3.mem_edgesIn]
  have h1 : G.energyOn (S : Set V) g =
      ∑' e : ({e : E | G.src e ∈ (S : Set V) ∧ G.tgt e ∈ (S : Set V)} : Set E),
        ENNReal.ofReal ((g (G.src e.1) - g (G.tgt e.1)) ^ 2) := rfl
  rw [h1, hset, Finset.tsum_subtype' (GMS3.edgesIn G S)
    (fun e => ENNReal.ofReal ((g (G.src e) - g (G.tgt e)) ^ 2)), GMS3.energy,
    ENNReal.ofReal_sum_of_nonneg (fun e _ => sq_nonneg _)]

/-- **Finite-sum energy of the annulus test function** (Berestycki–Gwynne (2020), proof of Lemma 4.3). For
`ε ≥ 0`, if adjacent vertices of the mated-CRT multigraph `𝒢^ε` have intersecting cells `H`, the cells are
preconnected, no cell meets both circles, and `g` is the discrete harmonic extension on `D = B_r(c) \ B̄_s(c)` of
boundary data equal to `1` on `∂B_s(c)` and `0` on `∂B_r(c)`, then for every finite vertex set `T` the ordered-pair
energy `(1/2) ∑_{k, l ∈ T} m(k, l) (h k - h l)²` of `h = annulusTestFunction H c s r g` is at most
`Energy(g; 𝒢^ε(V(D)))`. -/
theorem ofReal_sum_annulusTestFunction_le_energyOn {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hω : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω) (hε : 0 ≤ ε)
    {H : ℤ → Set ℂ} {c : ℂ} {s r : ℝ} {f : ℂ → ℝ} {g : ℤ → ℝ}
    (hadj : ∀ a b : ℤ, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) a b ≠ 0 →
      (H a ∩ H b).Nonempty)
    (hH : ∀ x, IsPreconnected (H x)) (hs : 0 < s) (hsr : s < r)
    (hf1 : ∀ z ∈ sphere c s, f z = 1) (hf0 : ∀ z ∈ sphere c r, f z = 0)
    (hsep : ∀ x, (H x ∩ sphere c s).Nonempty → ¬(H x ∩ sphere c r).Nonempty)
    (hg : (MatedCRTHarmonic.MatedCRT.graph ε ω hω).IsHarmonicExtension H
      (ball c r \ closedBall c s) f g) (T : Finset ℤ) :
    ENNReal.ofReal ((1 / 2) * ∑ k ∈ T, ∑ l ∈ T,
        (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k l : ℝ) *
          (annulusTestFunction H c s r g k - annulusTestFunction H c s r g l) ^ 2) ≤
      (MatedCRTHarmonic.MatedCRT.graph ε ω hω).energyOn
        (verticesMeeting H (ball c r \ closedBall c s)) g := by
  classical
  set U : Finset ℤ := T.filter (· ∈ verticesMeeting H (ball c r \ closedBall c s)) with hU
  have h1 := gms3Energy_annulusTestFunction_le hω hε hadj hH hs hsr hf1 hf0 hsep hg (S := T) (U := U)
    fun a ha hD => Finset.mem_filter.2 ⟨ha, hD⟩
  rw [← gms3Energy_graph_eq hω hε]
  calc ENNReal.ofReal (GMS3.energy (MatedCRTHarmonic.MatedCRT.graph ε ω hω) T
          (annulusTestFunction H c s r g))
      ≤ ENNReal.ofReal (GMS3.energy (MatedCRTHarmonic.MatedCRT.graph ε ω hω) U g) :=
        ENNReal.ofReal_le_ofReal h1
    _ = (MatedCRTHarmonic.MatedCRT.graph ε ω hω).energyOn (U : Set ℤ) g :=
        (lfMultigraph_energyOn_coe_finset _ U g).symm
    _ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω hω).energyOn
          (verticesMeeting H (ball c r \ closedBall c s)) g :=
        lfMultigraph_energyOn_mono _ (fun a ha => (Finset.mem_filter.1 ha).2) g

end MatedCRT
