import MatedCRT.FirstPass.Derived.SrwRingPieces
import MatedCRT.FirstPass.Derived.SrwRingSeparation
import MatedCRT.FirstPass.Derived.SrwGraphAdjBridge
import MatedCRT.FirstPass.Derived.SrwWalkLawBridge
import MatedCRT.FirstPass.Derived.SrwAnnulusExit
import LatticeProb.LQG.TemplateWalkCover
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces

/-!
# Assembly of the per-pair ring estimate for the simple random walk on the mated-CRT map

Berestycki–Gwynne (2020), Lemma 3.10 in the per-pair form (3.21), as a quenched statement on one environment.  Fix grid
data: a centre `z'`, radii `a < b`, a point `w`, a radius `r`, and a barrier `I` of vertices.  On the environment
suppose

* from every vertex whose cell meets `∂B_c(z')`, `c ∈ {a, b}`, the edge-end walk follows a polar template itinerary
  (Gwynne–Miller–Sheffield (2019), Proposition 3.6) with probability at least `p₀`;
* from every vertex whose cell meets `B_r(w)` the edge-end walk satisfies the event of Lemma 3.11, display (3.35),
  with probability at least `p₁`.

Then from every vertex whose cell lies in the open annulus `a < ‖· - z'‖ < b`, simple random walk on the edge count
separates a vertex `y` with `w ∈ cell y` from `I` through the trace before the first visit to `I`, with probability at
least `p₀ p₁`.  The proof is the two-restart lower bound at the first circle and at `B_r(w)`
(`srwLaw_twoRestart_lower`), the bridge from edge-end walk bounds to the walk on vertices
(`walkLaw_vertexPath_preimage_le_srwLaw`), and the separation by two spheres (`srwLaw_graphSeparates_lower`).
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov MatedCRTHarmonic.CellFamily
open MatedCRTHarmonic.GMSMain.T15A

/-- **A polar template itinerary reaches the ball and stays off the barrier.** A walk whose cells follow the polar
template of radius `c` around `z'` has a cell inside `B_{c/6}(w)` when `|‖w - z'‖ - c| ≤ c/50`; if `c / 6 ≤ r`, it
hits the vertices meeting `B_r(w)` at a finite time and meets no vertex of `I` up to then, when the cells of `I` are
disjoint from the annulus `A_{4c/5, 6c/5}(z')`. -/
theorem hsub_of_polarTemplateItinerary {E' : Type*} {G : LFMultigraph ℤ E'} {o : ℤ} (H : CellularEmbedding G o)
    {z' w : ℂ} {c r : ℝ} (hc : 0 < c) (hcr : c / 6 ≤ r) (hw : |‖w - z'‖ - c| ≤ c / 50) {I : Set ℤ}
    (hI : ∀ k ∈ I, Disjoint (H.cell k) (annulus z' (4 * c / 5) (6 * c / 5))) {ζ : ℕ → ℤ}
    (hζ : PolarTemplateItinerary H z' c ζ) :
    vHitTime (verticesMeeting H.cell (ball w r)) ζ ≠ ⊤ ∧
      ∀ i : ℕ, (i : ℕ∞) ≤ vHitTime (verticesMeeting H.cell (ball w r)) ζ → ζ i ∉ I := by
  obtain ⟨n, ϑ, α, β, hW, hann, -⟩ := hζ
  obtain ⟨j, hjn, hj⟩ := LatticeProb.LQG.exists_cell_subset_ball_of_isTemplateWalk hW hc hw
  have hjB : ζ j ∈ verticesMeeting H.cell (ball w r) := by
    obtain ⟨p, hp⟩ := (H.isConnected_cell (ζ j)).nonempty
    exact ⟨p, hp, Metric.ball_subset_ball hcr (hj hp)⟩
  have hle := TraceFrom68.vHitTime_le_of_mem hjB
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top j) hle, fun i hi hiI => ?_⟩
  have hij : i ≤ j := by exact_mod_cast hi.trans hle
  obtain ⟨p, hp⟩ := (H.isConnected_cell (ζ i)).nonempty
  exact (Set.disjoint_left.1 (hI _ hiI)) hp (hann i (hij.trans hjn) hp)

section Assembly

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
include h

/-- **The per-pair ring estimate on one environment** (see the module documentation). -/
theorem srwLaw_ringPair_lower (hε : 0 ≤ ε) {o : ℤ}
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω h) o)
    (hlf : IsLocallyFiniteMult (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
    (hcons : ∀ k : ℤ, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k (k + 1) ≠ 0)
    {z' w : ℂ} {a b r : ℝ} (ha0 : 0 < a) (hb0 : 0 < b) (hr : 0 ≤ r) (har : a / 6 ≤ r) (hbr : b / 6 ≤ r)
    (hwa : |‖w - z'‖ - a| ≤ a / 50) (hwb : |‖w - z'‖ - b| ≤ b / 50)
    (hF : (LatticeProb.LQG.annulusCells H.cell z' a b).Finite) {I : Set ℤ}
    (hIcirc : ∀ k ∈ I, (∀ q ∈ H.cell k, dist q z' < a) ∨ (∀ q ∈ H.cell k, b < dist q z'))
    (hIann : ∀ c, (c = a ∨ c = b) → ∀ k ∈ I, Disjoint (H.cell k) (annulus z' (4 * c / 5) (6 * c / 5)))
    (hIfar : ∀ k ∈ I, ∃ q ∈ H.cell k, 2 * r ≤ dist q w) {p₀ p₁ : ℝ≥0∞}
    (hItin : ∀ c, (c = a ∨ c = b) → ∀ y ∈ verticesMeeting H.cell (sphere z' c),
      p₀ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
        {ξ | PolarTemplateItinerary H z' c ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)})
    (h311 : ∀ y ∈ verticesMeeting H.cell (ball w r),
      p₁ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
        {ξ | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω h) H.cell w r
          ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)})
    {x : ℤ} (hx : x ∈ LatticeProb.LQG.annulusCells H.cell z' a b) {y : ℤ} (hy : w ∈ H.cell y) :
    p₀ * p₁ ≤ srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x
      {ξ | GraphSeparates (srwGraph (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
        (traceBefore (id : ℤ → ℤ) I ξ) {y} I} := by
  have hadj := graph_adj_eq_srwGraph h hε
  have hJ : ∀ k, IsPreconnected (H.cell k) := fun k => (H.isConnected_cell k).isPreconnected
  have hne : ∀ k, (H.cell k).Nonempty := fun k => (H.isConnected_cell k).nonempty
  have hmeet : ∀ j k, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) j k ≠ 0 →
      (H.cell j ∩ H.cell k).Nonempty := by
    intro j k hjk
    have hne' : j ≠ k := by
      rintro rfl
      exact hjk (by simp [bmEdgeCount])
    exact H.inter_of_adj j k (by rw [hadj]; exact ⟨hne', Or.inl hjk⟩)
  have hE : MeasurableSet {X : ℕ → ℤ | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω h) H.cell w r X} :=
    measurableSet_lemma311Event_paths _ _ _ _
  have h0 : ∀ y ∈ {k : ℤ | ∃ q ∈ H.cell k, dist q z' = a ∨ dist q z' = b},
      p₀ ≤ srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) y
        {ζ | PolarTemplateItinerary H z' a ζ ∨ PolarTemplateItinerary H z' b ζ} := by
    rintro y' ⟨q, hq, hd | hd⟩
    · exact (hItin a (Or.inl rfl) y' ⟨q, hq, hd⟩).trans
        ((walkLaw_vertexPath_preimage_le_srwLaw h hε y' {ζ | PolarTemplateItinerary H z' a ζ}).trans
          (measure_mono fun ζ hζ => Or.inl hζ))
    · exact (hItin b (Or.inr rfl) y' ⟨q, hq, hd⟩).trans
        ((walkLaw_vertexPath_preimage_le_srwLaw h hε y' {ζ | PolarTemplateItinerary H z' b ζ}).trans
          (measure_mono fun ζ hζ => Or.inr hζ))
  have hsub : ∀ ζ ∈ {ζ : ℕ → ℤ | PolarTemplateItinerary H z' a ζ ∨ PolarTemplateItinerary H z' b ζ},
      vHitTime (verticesMeeting H.cell (ball w r)) ζ ≠ ⊤ ∧
        ∀ i : ℕ, (i : ℕ∞) ≤ vHitTime (verticesMeeting H.cell (ball w r)) ζ → ζ i ∉ I := by
    rintro ζ (hζ | hζ)
    · exact hsub_of_polarTemplateItinerary H ha0 har hwa (hIann a (Or.inl rfl)) hζ
    · exact hsub_of_polarTemplateItinerary H hb0 hbr hwb (hIann b (Or.inr rfl)) hζ
  have h1 : ∀ y ∈ verticesMeeting H.cell (ball w r),
      p₁ ≤ srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) y
        {X : ℕ → ℤ | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω h) H.cell w r X} :=
    fun y' hy' => (h311 y' hy').trans
      (walkLaw_vertexPath_preimage_le_srwLaw h hε y'
        {X : ℕ → ℤ | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω h) H.cell w r X})
  have hpre := ae_srwLaw_hitCircle_before hlf hcons hJ hne hmeet hF hx hIcirc
  have h2 := srwLaw_twoRestart_lower (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x
    {k : ℤ | ∃ q ∈ H.cell k, dist q z' = a ∨ dist q z' = b} (verticesMeeting H.cell (ball w r)) I hE h0 hsub h1 hpre
  have hEq : {X : ℕ → ℤ | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω h) H.cell w r X} =
      {X | sepBeforeHit (srwGraph (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
        (verticesMeeting H.cell (sphere w (r / 2))) (verticesMeeting H.cell (sphere w (2 * r))) X} := by
    ext X
    simp only [Set.mem_ofPred_eq]
    rw [← hadj]
    exact Iff.rfl
  rw [hEq] at h2
  exact srwLaw_graphSeparates_lower hJ hne hmeet hr
    (S := verticesMeeting H.cell (sphere w (r / 2))) (T := verticesMeeting H.cell (sphere w (2 * r)))
    (B := verticesMeeting H.cell (ball w r)) (I₀ := {k : ℤ | ∃ q ∈ H.cell k, dist q z' = a ∨ dist q z' = b})
    (fun k q hq hd => ⟨q, hq, hd⟩) (fun k q hq hd => ⟨q, hq, hd⟩)
    (fun k hk => by
      obtain ⟨q, hq, hqb⟩ := hk
      exact ⟨q, hq, by linarith [mem_ball.1 hqb]⟩)
    ⟨w, hy, by rw [dist_self]; linarith⟩ hIfar h2

end Assembly

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.hsub_of_polarTemplateItinerary
#print axioms MatedCRT.srwLaw_ringPair_lower
