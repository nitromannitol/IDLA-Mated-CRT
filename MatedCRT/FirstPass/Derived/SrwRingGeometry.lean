import LatticeProb.LQG.ChainAnnulusCrossing
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Annulus

/-!
# Geometry of the barrier in the per-pair ring estimate

Deterministic facts about a cellular embedding that the per-pair ring estimate of Berestycki–Gwynne (2020), Lemma 3.10
(display (3.21)), needs for its barrier `I = P ∪ O`: the finitely many vertices whose cells lie in a bounded open
annulus, and the position of the barrier cells relative to the template annuli `A_{4c/5, 6c/5}(z')` around the grid
circles `c ∈ {a, b}`.  Here `P` is a set of cells inside the ball `B_{a/4}(z')` (the pole of the Green function) and `O`
the set of vertices having a cell point outside the ball `B_T(z')`, where cells meeting `B_{6b/5}(z')` have diameter at
most `δ` and `6b/5 + δ ≤ T`.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open MatedCRTHarmonic

/-- **Finiteness of the cells inside an annulus.** In a cellular embedding (compact, connected, locally finite
cells), only finitely many cells lie in a bounded open annulus. -/
theorem finite_annulusCells {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)
    (z : ℂ) (a b : ℝ) : (LatticeProb.LQG.annulusCells H.cell z a b).Finite := by
  refine (H.locallyFinite_cell.finite_nonempty_inter_compact (isCompact_closedBall z b)).subset ?_
  intro k hk
  obtain ⟨x, hx⟩ := (H.isConnected_cell k).nonempty
  exact ⟨x, hx, mem_closedBall.2 (hk x hx).2.le⟩

/-- A connected set that misses the shell `{r ≤ dist · z < R}` and has a point at distance at least `R` from `z` lies
entirely at distance at least `R` from `z`. -/
theorem forall_le_dist_of_isPreconnected {C : Set ℂ} (hC : IsPreconnected C) {z : ℂ} {r R : ℝ}
    (hrR : r < R) (hd : Disjoint C (annulus z r R)) {p : ℂ} (hp : p ∈ C) (hpR : R ≤ dist p z) :
    ∀ x ∈ C, R ≤ dist x z := by
  have hD : IsPreconnected ((fun x => dist x z) '' C) :=
    hC.image _ (continuous_id.dist continuous_const).continuousOn
  intro x hx
  by_contra hcon
  have hlt : dist x z < R := not_le.1 hcon
  by_cases hxr : r ≤ dist x z
  · exact Set.disjoint_left.1 hd hx ⟨mem_ball.2 hlt, fun h => absurd (mem_ball.1 h) (not_lt.2 hxr)⟩
  · have hm : r ∈ (fun x => dist x z) '' C :=
      hD.Icc_subset ⟨x, hx, rfl⟩ ⟨p, hp, rfl⟩ ⟨(not_le.1 hxr).le, hrR.le.trans hpR⟩
    obtain ⟨u, hu, hur⟩ := hm
    have hur' : dist u z = r := hur
    exact Set.disjoint_left.1 hd hu ⟨mem_ball.2 (by linarith), fun h => absurd (mem_ball.1 h) (by linarith)⟩

/-- **Barrier geometry for the per-pair ring estimate.** Let `a ≤ b` be radii, `w` a point with `2r + a/4 ≤ ‖w - z'‖`
and `2r + ‖w - z'‖ ≤ T`.  If the cells of `P` lie in the closed ball of radius `a/4` about `z'`, every cell of `O` has
a point farther than `T ≥ 6b/5 + δ` from `z'`, and every cell meeting `B_{6b/5}(z')` has diameter at most `δ`, then
the cells of `P ∪ O` lie inside `B_a(z')` or outside `B̄_b(z')`, miss the annuli `A_{4c/5,6c/5}(z')` for `c ∈ {a, b}`,
and each has a point at distance at least `2r` from `w`. -/
theorem ringPair_barrier_geometry {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)
    {z' w : ℂ} {a b r δ T : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 ≤ δ)
    (hdiam : ∀ k, (H.cell k ∩ ball z' (6 * b / 5)).Nonempty → ∀ x ∈ H.cell k, ∀ x' ∈ H.cell k, dist x x' ≤ δ)
    {P O : Set V} (hP : ∀ k ∈ P, ∀ q ∈ H.cell k, dist q z' ≤ a / 4)
    (hO : ∀ k ∈ O, ∃ q ∈ H.cell k, T < dist q z') (hT : 6 * b / 5 + δ ≤ T)
    (hTw : 2 * r + ‖w - z'‖ ≤ T) (hPw : 2 * r + a / 4 ≤ ‖w - z'‖) :
    (∀ k ∈ P ∪ O, (∀ q ∈ H.cell k, dist q z' < a) ∨ (∀ q ∈ H.cell k, b < dist q z')) ∧
    (∀ c, (c = a ∨ c = b) → ∀ k ∈ P ∪ O, Disjoint (H.cell k) (annulus z' (4 * c / 5) (6 * c / 5))) ∧
    (∀ k ∈ P ∪ O, ∃ q ∈ H.cell k, 2 * r ≤ dist q w) := by
  have hb : 0 < b := ha.trans_le hab
  have hann : ∀ c, (c = a ∨ c = b) → ∀ k ∈ P ∪ O,
      Disjoint (H.cell k) (annulus z' (4 * c / 5) (6 * c / 5)) := by
    intro c hc k hk
    have hac : a ≤ c := by rcases hc with rfl | rfl <;> linarith
    have hcb : c ≤ b := by rcases hc with rfl | rfl <;> linarith
    rw [Set.disjoint_left]
    intro q hq hqa
    obtain ⟨hq1, hq2⟩ := hqa
    have hq1' : dist q z' < 6 * c / 5 := mem_ball.1 hq1
    have hq2' : 4 * c / 5 ≤ dist q z' := not_lt.1 fun h => hq2 (mem_ball.2 h)
    rcases hk with hk | hk
    · have := hP k hk q hq
      linarith
    · obtain ⟨q0, hq0, hq0T⟩ := hO k hk
      have hd : dist q0 q ≤ δ :=
        hdiam k ⟨q, hq, mem_ball.2 (by linarith)⟩ q0 hq0 q hq
      have := dist_triangle q0 q z'
      linarith
  refine ⟨?_, hann, ?_⟩
  · intro k hk
    rcases hk with hk | hk
    · exact Or.inl fun q hq => lt_of_le_of_lt (hP k hk q hq) (by linarith)
    · obtain ⟨q0, hq0, hq0T⟩ := hO k hk
      refine Or.inr fun q hq => ?_
      have := forall_le_dist_of_isPreconnected (H.isConnected_cell k).isPreconnected
        (by linarith : 4 * b / 5 < 6 * b / 5) (hann b (Or.inr rfl) k (Or.inr hk)) hq0 (by linarith) q hq
      linarith
  · intro k hk
    rcases hk with hk | hk
    · obtain ⟨q0, hq0⟩ := (H.isConnected_cell k).nonempty
      refine ⟨q0, hq0, ?_⟩
      have h1 := hP k hk q0 hq0
      have h2 := dist_triangle w q0 z'
      rw [dist_comm w q0] at h2
      have h3 : dist w z' = ‖w - z'‖ := dist_eq_norm w z'
      linarith
    · obtain ⟨q0, hq0, hq0T⟩ := hO k hk
      refine ⟨q0, hq0, ?_⟩
      have h2 := dist_triangle q0 w z'
      have h3 : dist w z' = ‖w - z'‖ := dist_eq_norm w z'
      linarith

end MatedCRT

#print axioms MatedCRT.finite_annulusCells
#print axioms MatedCRT.forall_le_dist_of_isPreconnected
#print axioms MatedCRT.ringPair_barrier_geometry
