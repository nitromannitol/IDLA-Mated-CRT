import MatedCRT.FirstPass.S4S6c.Uniform68
import MatedCRT.FirstPass.S4S6c.GoodEvent68
import MatedCRT.FirstPass.S4S6c.ExitAe68
import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.FirstPass.S4S6c.FrontierStart68
import MatedCRT.FirstPass.S4S6c.Tau68
import MatedCRT.FirstPass.S4S6c.GreenTest68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S4S6c.CellBoundary

/-!
# Walk-level inputs of `Uniform68.config_exit_lower_bound` discharged (q2, task fp-S4S6c-envscaling-6-7-6-8, file `Uniform68Walk.lean`)

`config_exit_lower_bound_walk` is the per-configuration Lemma 6.8 with the walk-level hypotheses of the configuration
proved from existing lemmas:

* `hexit` (a.s. finite exit from the thickened filled set): `ExitAe68.ae_exit_ne_top_of_bounded` (properness of `η`,
  local finiteness and consecutive adjacency of `m` as inputs), with `Uniform68.meetVerts_eq_cellVertices`;
* `hW`, `hfinBS` (finite inner windows): `ExitNull68.exit_null_of_finite`, finiteness of `innerVertices` of a bounded set;
* `hGood`, `hGoodPath` (the good event of LEMMA68 C1-C2): `GoodEvent68.ae_good` with the frontier start distance
  `FrontierStart68.start_dist_of_frontier`;
* `τ`, `S`: `Tau68.tauSeq` and `Tau68.staySeq` (their recursions are the definitions).

Remaining environment inputs: `Tendsto η (cocompact ℝ) (cocompact ℂ)` (a.s. from `IsValid.ae_tendsto_cocompact`), local
finiteness `IsLocallyFiniteMult m` and `m k (k+1) ≠ 0`, and the local test `hloc` (`Uniform68Events.hloc_point` gives it per
start vertex from the event inputs).

Terminology: Markov property of the walk at fixed times (Norris), good event (Berestycki-Gwynne killing on leaving V(D)),
inner vertices `I(D)` (LEMMA68 notation), Green function and exit times (Armitage-Gardiner).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace MatedCRT
namespace Uniform68Walk

/-- Finiteness of the inner window `I(D) = innerVertices (cell ε η) D` of a bounded set `D` under properness of `η`. -/
theorem innerVertices_finite {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {D : Set ℂ} (hD : Bornology.IsBounded D) : (innerVertices (cell ε η) D).Finite :=
  (TraceInputs68.cellVertices_finite_of_tendsto hε hp hD).subset fun _ hv => hv.1

/-- The good event of LEMMA68 C1-C2 for the filled set `F`, centre data `ctr, rad` and scales `r, d`: the start lies at
distance `r/2 ± d` from `F`, the steps are stays or edges, and every window exit along the path is finite. -/
def walkGood (ε : ℝ) (η : ℝ → ℂ) (m : ℤ → ℤ → ℕ) (ctr : ℤ → ℂ) (rad : ℤ → ℝ) (F : Set ℂ) (r d : ℝ) :
    Set (ℕ → ℤ) :=
  {x | |infDist (vertexPoint ε η (x 0)) F - r / 2| ≤ d ∧
    (∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) ∧
    ∀ i : ℕ, vExitTime (innerVertices (cell ε η) (ball (ctr (x i)) (2 * rad (x i)))) (WalkPotential.pathShift i x) ≠ ⊤}

/-- **Lemma 6.8 for one configuration, walk-level inputs discharged** (`Uniform68.config_exit_lower_bound` without
`hexit`, `hGood`, `hGoodPath`, `hfinBS` and the τ/S sequences). -/
theorem config_exit_lower_bound_walk
    {ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {Θ S' : Set ℤ} {a : ℤ} {r ρ s d g s₀ : ℝ} {N : ℕ}
    {ctr : ℤ → ℂ} {rad : ℤ → ℝ}
    (hε : 0 < ε) (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ u v, m u v ≠ 0 → (cell ε η u ∩ cell ε η v).Nonempty)
    (hr : 0 < r) (hd : d < r / 2) (hdiamA : Metric.diam (cell ε η a) ≤ d)
    (ha : a ∈ vClosure m Θ)
    (hs₀ : 0 < s₀) (hball : ball (0 : ℂ) s₀ ⊆ fillCells ε η Θ)
    (hcl : closure (fillCells ε η Θ) ⊆ ball (0 : ℂ) (ρ / 2))
    (hctr : ∀ v, dist (ctr v) (vertexPoint ε η v) ≤ g)
    (hsm0 : ∀ v, (cell ε η v ∩ ball (0 : ℂ) ρ).Nonempty → ∀ u ∈ closure (cell ε η v), ∀ u' ∈ closure (cell ε η v), dist u u' ≤ d)
    (hρ : ∀ y, d < rad y / 4) (hgeo : ∀ y, 4 * rad y / 3 + d + rad y / 4 + d < 2 * rad y)
    (hlt : ∀ y, g + d < 4 * rad y / 3)
    (hrad0 : ∀ v ∈ BandInduction68.band (vertexPoint ε η) (fillCells ε η Θ) r d, 0 ≤ rad v)
    (hrad : ∀ v ∈ BandInduction68.band (vertexPoint ε η) (fillCells ε η Θ) r d, rad v ≤ s)
    (hd0 : 0 ≤ d) (hg : 0 ≤ g) (hs : 0 < s) (hsr : s ≤ r / 1000) (hdr : d ≤ r / 1000)
    (hgd : g + d < s) (hrρ : r ≤ ρ / 100) (hNs : (N : ℝ) * s ≤ r / 100)
    {q0 ζ : ℝ} (hq0 : 0 < q0) (hq0' : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (hr1 : r ≤ 1)
    (hrA : r ≤ (q0 / 200 * ζ ^ 2 / (16 * Real.log 2)) ^ (2 / ζ))
    (hN : r ^ (-ζ) / 200 ≤ N)
    (hloc : ∀ y ∈ HcPrinted68.bandSet (cell ε η) ctr rad,
      ∀ b ∈ {b : ℤ | (closure (cell ε η b) ∩ Metric.sphere (ctr y) (4 * rad y / 3)).Nonempty},
      srwLaw m b (TestBound68.stayIn (fun b => innerVertices (cell ε η) (ball (vertexPoint ε η b) (rad y / 4)))
        (S' \ Θ) b) ≤ ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2)) :
    ENNReal.ofReal (1 / 2) ≤ srwLaw m a
      {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime (cellVertices ε η (Metric.thickening r (fillCells ε η Θ))) x ∧
        x n ∈ cellVertices ε η (Metric.thickening r (fillCells ε η Θ)) \ (S' ∪ Θ)} := by
  have hFball : fillCells ε η Θ ⊆ ball (0 : ℂ) (ρ / 2) := fun z hz => hcl (subset_closure hz)
  have hFne : (fillCells ε η Θ).Nonempty := ⟨0, hball (mem_ball_self hs₀)⟩
  have hPmem : ∀ v, vertexPoint ε η v ∈ cell ε η v := fun v => GreenTest68.vertexPoint_mem_cell hε v
  -- finiteness of the windows and the exit-null property of every window
  have hW : ∀ y : ℤ, srwLaw m y {x | vExitTime (innerVertices (cell ε η) (ball (ctr y) (2 * rad y))) x = ⊤} = 0 :=
    fun y => ExitNull68.exit_null_of_finite hlf hcons
      (innerVertices_finite hε hp Metric.isBounded_ball) y
  -- the walk-level good event
  have hGood : ∀ b ∈ FrontierSeparation.frontierVerts (cell ε η) (Metric.thickening (r / 2) (fillCells ε η Θ)),
      srwLaw m b (walkGood ε η m ctr rad (fillCells ε η Θ) r d)ᶜ = 0 := by
    intro b hb
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [GoodEvent68.ae_good m (fun y => innerVertices (cell ε η) (ball (ctr y) (2 * rad y))) b hW]
      with x hx hxG
    apply hxG
    obtain ⟨h0, hl, hf⟩ := hx
    simp only [walkGood, Set.mem_ofPred_eq]
    refine ⟨?_, hl, hf⟩
    rw [h0]
    exact FrontierStart68.start_dist_of_frontier hr hrρ hFne hFball hPmem hsm0 hb
  have hGoodPath : ∀ x ∈ walkGood ε η m ctr rad (fillCells ε η Θ) r d,
      |Metric.infDist (vertexPoint ε η (x 0)) (fillCells ε η Θ) - r / 2| ≤ d ∧
      (∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) ∧
      ∀ i : ℕ, dist (vertexPoint ε η (x i)) (vertexPoint ε η (x 0)) ≤ 3 * r / 100 →
        vExitTime (innerVertices (cell ε η) (ball (ctr (x i)) (2 * rad (x i)))) (WalkPotential.pathShift i x) ≠ ⊤ := by
    intro x hx
    simp only [walkGood, Set.mem_ofPred_eq] at hx
    exact ⟨hx.1, hx.2.1, fun i _ => hx.2.2 i⟩
  have hfinBS : ∀ y ∈ HcPrinted68.bandSet (cell ε η) ctr rad,
      ∀ᵐ x ∂srwLaw m y, vExitTime (innerVertices (cell ε η) (ball (ctr y) (4 * rad y / 3))) x ≠ ⊤ := by
    intro y _
    exact (measure_eq_zero_iff_ae_notMem.1
      (ExitNull68.exit_null_of_finite hlf hcons (innerVertices_finite hε hp Metric.isBounded_ball) y)).mono
      fun x hx => hx
  -- the a.s. finite exit from the thickened filled set
  have hbd : Bornology.IsBounded (Metric.thickening r (fillCells ε η Θ)) := by
    refine (Metric.isBounded_ball (x := (0 : ℂ)) (r := ρ / 2 + r)).subset ?_
    intro z hz
    obtain ⟨w, hw, hzw⟩ := Metric.mem_thickening_iff.1 hz
    have hw' : w ∈ ball (0 : ℂ) (ρ / 2) := hFball hw
    rw [Metric.mem_ball] at hw' ⊢
    linarith [dist_triangle z w 0]
  have hexit : ∀ᵐ x ∂srwLaw m a, vExitTime (cellVertices ε η (Metric.thickening r (fillCells ε η Θ))) x ≠ ⊤ := by
    have h := ExitAe68.ae_exit_ne_top_of_bounded hε hη hp hlf hcons hbd a
    rw [Uniform68.meetVerts_eq_cellVertices Metric.isOpen_thickening] at h
    exact h
  -- the concrete tests and stay sets
  have hτ0 : ∀ x, Tau68.tauSeq (fun v => TraceBand68.testWt (cell ε η) (vertexPoint ε η) ctr rad
      (fillCells ε η Θ) r d v) 0 x = 0 := fun x => Tau68.tauSeq_zero _ x
  exact Uniform68.config_exit_lower_bound hε hη hadj hr hd hdiamA ha hexit hs₀ hball hcl hctr hsm0 hρ hgeo hlt
    hrad0 hrad hd0 hg hs hsr hdr hgd hrρ hNs hq0 hq0' hζ hζ' hr1 hrA hN
    (walkGood ε η m ctr rad (fillCells ε η Θ) r d) hGood hGoodPath hfinBS hloc
    (Tau68.tauSeq (fun v => TraceBand68.testWt (cell ε η) (vertexPoint ε η) ctr rad (fillCells ε η Θ) r d v))
    (Tau68.staySeq (fun v => TraceBand68.testWt (cell ε η) (vertexPoint ε η) ctr rad (fillCells ε η Θ) r d v)
      (fun v => TraceBand68.testAof (cell ε η) (vertexPoint ε η) ctr rad (fillCells ε η Θ) r d (S' \ Θ) v))
    hτ0
    (fun M x i h => Tau68.tauSeq_succ_of_eq h)
    (fun M x h => Tau68.tauSeq_succ_of_top h)
    (Tau68.staySeq_zero _ _)
    (fun M => Tau68.staySeq_succ _ _ M)

end Uniform68Walk
end MatedCRT

#print axioms MatedCRT.Uniform68Walk.config_exit_lower_bound_walk
