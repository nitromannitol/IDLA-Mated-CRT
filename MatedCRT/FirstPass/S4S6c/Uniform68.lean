import MatedCRT.FirstPass.S4S6c.TraceBand68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S4S6c.GreenTest68
import MatedCRT.FirstPass.S4S6c.Uniform68Selector
import MatedCRT.Defs.Map
import MatedCRT.Defs.RandomWalk

/-!
# Lemma 6.8 for one configuration (q2, task fp-S4S6c-envscaling-6-7-6-8, file `Uniform68.lean`)

Per-configuration form of `UniformConstantOrderLowerBoundStmt` (`FirstPass/S6d.lean:90`): for a fixed
embedding `η`, a fixed edge multiplicity `m` and fixed `r, ρ, s, d, g, N` the bound
`ENNReal.ofReal (1/2) ≤ srwLaw m a {walk exits the thickened set at a vertex outside S' ∪ Θ}`
is `TraceBand68.trace_band` with the cell cover `H v := cell ε η v`, the filled set
`F := fillCells ε η Θ` and the vertex points `P v := vertexPoint ε η v`.

The cell-level inputs of `trace_band` are discharged here from the cell lemmas of `TraceInputs68`
(continuity of `η` gives boundedness and preconnectedness of the cells; `vertexPoint` lies in its cell).
The remaining inputs are the probabilistic and cell-size inputs of LEMMA68 (hypotheses here, see the report).

Terminology: harmonic-measure and Green-function language of Armitage-Gardiner; the walk is the simple
random walk on the mated-CRT map (Duplantier-Sheffield, Berestycki-Powell, Gwynne-Miller annulus iteration).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace MatedCRT
namespace Uniform68

/-- For an open set `U` the closed-cell vertex set `V(U) = meetVerts` equals the open-cell set `cellVertices`:
closure `cell v` meets the open set `U` exactly when `cell v` does. -/
theorem meetVerts_eq_cellVertices {ε : ℝ} {η : ℝ → ℂ} {U : Set ℂ} (hU : IsOpen U) :
    FrontierSeparation.meetVerts (cell ε η) U = cellVertices ε η U := by
  ext v
  simp only [FrontierSeparation.meetVerts, cellVertices, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hzc, hzU⟩
    obtain ⟨w, hwU, hwC⟩ := mem_closure_iff.1 hzc U hU hzU
    exact ⟨w, hwC, hwU⟩
  · rintro ⟨z, hzC, hzU⟩
    exact ⟨z, subset_closure hzC, hzU⟩

/-- **Per-configuration lower bound (LEMMA68 Lemma 6.8, uniform form, one configuration).** `trace_band`
specialized to the cells `cell ε η`, the filled set `fillCells ε η Θ` and the vertex points `vertexPoint ε η`. -/
theorem config_exit_lower_bound
    {ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {Θ S' : Set ℤ} {a : ℤ} {r ρ s d g s₀ : ℝ} {N : ℕ}
    {ctr : ℤ → ℂ} {rad : ℤ → ℝ}
    (hε : 0 < ε) (hη : Continuous η)
    (hadj : ∀ u v, m u v ≠ 0 → (cell ε η u ∩ cell ε η v).Nonempty)
    (hr : 0 < r) (hd : d < r / 2) (hdiamA : Metric.diam (cell ε η a) ≤ d)
    (ha : a ∈ vClosure m Θ)
    (hexit : ∀ᵐ x ∂srwLaw m a, vExitTime (cellVertices ε η (Metric.thickening r (fillCells ε η Θ))) x ≠ ⊤)
    (hs₀ : 0 < s₀) (hball : ball (0 : ℂ) s₀ ⊆ fillCells ε η Θ)
    (hcl : closure (fillCells ε η Θ) ⊆ ball (0 : ℂ) (ρ / 2))
    (hctr : ∀ v, dist (ctr v) (vertexPoint ε η v) ≤ g)
    (hsm0 : ∀ v, (cell ε η v ∩ ball (0 : ℂ) ρ).Nonempty → ∀ u ∈ closure (cell ε η v),
      ∀ u' ∈ closure (cell ε η v), dist u u' ≤ d)
    (hsmC : ∀ y v, (closure (cell ε η v) ∩ closedBall (ctr y) (2 * rad y)).Nonempty →
      ∀ x ∈ closure (cell ε η v), ∀ y' ∈ closure (cell ε η v), dist x y' ≤ d)
    (hρ : ∀ y, d < rad y / 4) (hgeo : ∀ y, 4 * rad y / 3 + d + rad y / 4 + d < 2 * rad y)
    (hlt : ∀ y, g + d < 4 * rad y / 3)
    (hrad0 : ∀ v ∈ BandInduction68.band (vertexPoint ε η) (fillCells ε η Θ) r d, 0 ≤ rad v)
    (hrad : ∀ v ∈ BandInduction68.band (vertexPoint ε η) (fillCells ε η Θ) r d, rad v ≤ s)
    (hd0 : 0 ≤ d) (hg : 0 ≤ g) (hs : 0 < s) (hsr : s ≤ r / 1000) (hdr : d ≤ r / 1000)
    (hgd : g + d < s) (hrρ : r ≤ ρ / 100) (hNs : (N : ℝ) * s ≤ r / 100)
    {q0 ζ : ℝ} (hq0 : 0 < q0) (hq0' : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (hr1 : r ≤ 1)
    (hrA : r ≤ (q0 / 200 * ζ ^ 2 / (16 * Real.log 2)) ^ (2 / ζ))
    (hN : r ^ (-ζ) / 200 ≤ N)
    (Good : Set (ℕ → ℤ))
    (hGood : ∀ b ∈ FrontierSeparation.frontierVerts (cell ε η) (Metric.thickening (r / 2) (fillCells ε η Θ)),
      srwLaw m b Goodᶜ = 0)
    (hGoodPath : ∀ x ∈ Good, |Metric.infDist (vertexPoint ε η (x 0)) (fillCells ε η Θ) - r / 2| ≤ d ∧
      (∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) ∧
      ∀ i : ℕ, dist (vertexPoint ε η (x i)) (vertexPoint ε η (x 0)) ≤ 3 * r / 100 →
        vExitTime (innerVertices (cell ε η) (ball (ctr (x i)) (2 * rad (x i))))
          (WalkPotential.pathShift i x) ≠ ⊤)
    (hfinBS : ∀ y ∈ HcPrinted68.bandSet (cell ε η) ctr rad,
      ∀ᵐ x ∂srwLaw m y, vExitTime (innerVertices (cell ε η) (ball (ctr y) (4 * rad y / 3))) x ≠ ⊤)
    (hloc : ∀ y ∈ HcPrinted68.bandSet (cell ε η) ctr rad,
      ∀ b ∈ {b : ℤ | (closure (cell ε η b) ∩ Metric.sphere (ctr y) (4 * rad y / 3)).Nonempty},
      srwLaw m b (TestBound68.stayIn (fun b => innerVertices (cell ε η) (ball (vertexPoint ε η b) (rad y / 4)))
        (S' \ Θ) b) ≤ ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2))
    (τ : ℕ → (ℕ → ℤ) → ℕ∞) (S : ℕ → Set (ℕ → ℤ))
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ (M : ℕ) (x : ℕ → ℤ) (i : ℕ), τ M x = (i : ℕ∞) →
      τ (M + 1) x = (i : ℕ∞) + vExitTime (TraceBand68.testWt (cell ε η) (vertexPoint ε η) ctr rad
        (fillCells ε η Θ) r d (x i)) (WalkPotential.pathShift i x))
    (hτtop : ∀ M x, τ M x = ⊤ → τ (M + 1) x = ⊤)
    (hS0 : S 0 = univ)
    (hSsucc : ∀ M, S (M + 1) = S M ∩ {x | ∃ k : ℕ, τ M x = k ∧
      WalkPotential.pathShift k x ∈ SuccessiveExitStop.stayInRegionOf
        (TraceBand68.testWt (cell ε η) (vertexPoint ε η) ctr rad (fillCells ε η Θ) r d)
        (TraceBand68.testAof (cell ε η) (vertexPoint ε η) ctr rad (fillCells ε η Θ) r d (S' \ Θ)) (x k)}) :
    ENNReal.ofReal (1 / 2) ≤ srwLaw m a
      {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime (cellVertices ε η (Metric.thickening r (fillCells ε η Θ))) x ∧
        x n ∈ cellVertices ε η (Metric.thickening r (fillCells ε η Θ)) \ (S' ∪ Θ)} := by
  have hexit' : ∀ᵐ x ∂srwLaw m a, vExitTime (FrontierSeparation.meetVerts (cell ε η)
      (Metric.thickening r (fillCells ε η Θ))) x ≠ ⊤ := by
    rw [meetVerts_eq_cellVertices Metric.isOpen_thickening]
    exact hexit
  have hbdd : ∀ v, Bornology.IsBounded (cell ε η v) := fun v => TraceInputs68.cell_isBounded hη v
  have hconn : ∀ v, IsPreconnected (cell ε η v) := fun v => TraceInputs68.cell_isPreconnected hη v
  have hne : ∀ v, (cell ε η v).Nonempty := fun v => TraceInputs68.cell_nonempty hε η v
  have hadj' : ∀ u v, m u v ≠ 0 → (closure (cell ε η u) ∩ closure (cell ε η v)).Nonempty := by
    intro u v huv
    obtain ⟨z, hz⟩ := hadj u v huv
    exact ⟨z, subset_closure hz.1, subset_closure hz.2⟩
  have hF : ∀ k ∈ Θ, cell ε η k ⊆ fillCells ε η Θ :=
    fun k hk => subset_biUnion_of_mem (u := cell ε η) hk
  have hFne : (fillCells ε η Θ).Nonempty := ⟨0, hball (mem_ball_self hs₀)⟩
  have hFball : fillCells ε η Θ ⊆ ball (0 : ℂ) (ρ / 2) := fun z hz => hcl (subset_closure hz)
  have hPmem : ∀ v, vertexPoint ε η v ∈ cell ε η v := fun v => GreenTest68.vertexPoint_mem_cell hε v
  exact TraceBand68.trace_band (H := cell ε η) (m := m) (F := fillCells ε η Θ) (Θ := Θ) (S' := S') (a := a)
    (r := r) (ρ := ρ) (s := s) (d := d) (g := g) (N := N) (P := vertexPoint ε η) (ctr := ctr) (rad := rad)
    (q0 := q0) (ζ := ζ) hr hd (fun v => hbdd v) hdiamA (fun v => hconn v) (fun v => hne v) hadj' hF ha hexit'
    hFne hFball hPmem hctr hsm0 hsmC hρ hgeo hlt hrad0 hrad hd0 hg hs hsr hdr hgd hrρ hNs hq0 hq0' hζ hζ' hr1 hrA hN
    Good hGood hGoodPath hfinBS hloc τ S hτ0 hτsucc hτtop hS0 hSsucc

end Uniform68
end MatedCRT

#print axioms MatedCRT.Uniform68.config_exit_lower_bound
