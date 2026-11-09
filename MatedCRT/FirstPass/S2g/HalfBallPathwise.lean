import Mathlib
import MatedCRT.FirstPass.S2g.ClosureRadius

/-!
# Pathwise canonical half-ball witness (fp-S2g, q1)

Reduction of the witness `Λ t = regularizedCluster μ (3/4) 0 t` of `ConeCanonicalHalfBallStep` (CHATGPT-q1-open-steps.md
H8) to pathwise inputs. Free from the definitions: the regularized cluster is open, lies in `B_{3/4}` (interior of a
closure inside the closed disc, `open_subset_ball_of_subset_closedBall`), and contains the pole `0` once the raw cluster
is open (`cluster` contains its pole by its first clause `x = z`). The remaining inputs are the monotonicity (HB Lemma 3.3),
the continuity of the closure radius (H5), the small-time nonemptiness (H4), the boundedness of the stopping set (H4, from
Lemma 3.4 and Proposition 5.3), the openness of the raw cluster, and the family property (H6-H7) at the canonical time.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls

/-- The raw cluster `Λ_{B_{3/4};0}(t)` lies in `B_{3/4}`, so the regularized cluster does too. -/
theorem regularizedCluster_subset_ball_three_quarters (μ : Measure ℂ) (t : ℝ) :
    regularizedCluster μ (3 / 4) 0 t ⊆ ball 0 (3 / 4) := by
  have hc : cluster μ (3 / 4) 0 t ⊆ ball 0 (3 / 4) := fun x hx => by
    unfold cluster at hx
    exact hx.1
  have hcl : closure (cluster μ (3 / 4) 0 t) ⊆ closedBall 0 (3 / 4) :=
    closure_minimal (hc.trans ball_subset_closedBall) isClosed_closedBall
  unfold regularizedCluster
  exact open_subset_ball_of_subset_closedBall isOpen_interior (interior_subset.trans hcl)

/-- The regularized cluster is open (an interior). -/
theorem isOpen_regularizedCluster (μ : Measure ℂ) (t : ℝ) : IsOpen (regularizedCluster μ (3 / 4) 0 t) :=
  isOpen_interior

/-- The pole `0` lies in the regularized cluster once the raw cluster is open. -/
theorem zero_mem_regularizedCluster_of_open {μ : Measure ℂ} {t : ℝ} (hopen : IsOpen (cluster μ (3 / 4) 0 t)) :
    (0 : ℂ) ∈ regularizedCluster μ (3 / 4) 0 t := by
  have h0 : (0 : ℂ) ∈ cluster μ (3 / 4) 0 t := by
    unfold cluster
    exact ⟨mem_ball_self (by norm_num), Or.inl rfl⟩
  unfold regularizedCluster
  exact interior_maximal subset_closure hopen h0

/-- **Pathwise canonical half-ball witness** (CHATGPT-q1-open-steps.md H4, H5, H8). For a measure `μ` on `ℂ`, if the raw
clusters `Λ_{B_{3/4};0}(t)` are open for `t > 0`, the regularized clusters are monotone and have continuous closure radius
on `(0, ∞)`, some regularized cluster at a positive time is inside `B_{1/2}`, the stopping set is bounded above, and the
family `t ↦ regularizedCluster μ (3/4) 0 t` has the harmonic-ball properties on `(0, T)` with `T` the canonical time, then
`T` is positive, the family has the properties, and it is stopped at `∂B_{1/2}` at `T`. -/
theorem canonical_witness_of_pathwise {μ : Measure ℂ}
    (hcopen : ∀ t, 0 < t → IsOpen (cluster μ (3 / 4) 0 t))
    (hmono : MonotoneOn (fun t => regularizedCluster μ (3 / 4) 0 t) (Ioi 0))
    (hcont : ∃ U : ℝ, sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball 0 (1 / 2)} < U ∧
      ContinuousOn (fun t => closureRadius (regularizedCluster μ (3 / 4) 0 t)) (Ioo 0 U))
    (hne : ∃ s : ℝ, 0 < s ∧ regularizedCluster μ (3 / 4) 0 s ⊆ ball 0 (1 / 2))
    (hbdd : BddAbove {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball 0 (1 / 2)})
    (hfam : IsConeHarmonicBallFamilyOn μ (regularizedCluster μ (3 / 4) 0)
      (sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball 0 (1 / 2)})) :
    0 < sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball 0 (1 / 2)} ∧
      IsConeHarmonicBallFamilyOn μ (regularizedCluster μ (3 / 4) 0)
        (sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball 0 (1 / 2)}) ∧
      IsStoppedAtHalfBall (regularizedCluster μ (3 / 4) 0)
        (sSup {t : ℝ | 0 < t ∧ regularizedCluster μ (3 / 4) 0 t ⊆ ball 0 (1 / 2)}) := by
  obtain ⟨hst, hpos⟩ := stopped_halfBall_of_closureRadius
    (L := fun t => regularizedCluster μ (3 / 4) 0 t)
    (fun t => isOpen_regularizedCluster μ t) (fun t => regularizedCluster_subset_ball_three_quarters μ t)
    hmono hcont (fun t ht => zero_mem_regularizedCluster_of_open (hcopen t ht)) hne hbdd
  exact ⟨hpos, hfam, hst⟩

end MatedCRT
