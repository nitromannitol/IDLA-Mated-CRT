import MatedCRT.FirstPass.S2g.GoodSet
import MatedCRT.FirstPass.S2h.CertRel
import MatedCRT.FirstPass.S2h.CertSets

/-!
# Charged balls of a certificate: the punctured contact set

The charged-ball predicate `certD` of `CertRel.lean` is the generic predicate of
`CertSets.lean` for the raw positivity `0 < certRaw t w` at the data points `z j`, which lie in the punctured disc
`B_{3/4} \ {0}` and are dense there. The contact set is `certCluster (3/4) t w` (GoodSet.lean) minus the pole.
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls

open Classical in
/-- The extension of a candidate on `B̄_{3/4}` by `0` to `ℂ`; only its values on `B̄_{3/4}` enter the certificate. -/
noncomputable def extW (w : DiscW) : ℂ → ℝ := fun x => if h : x ∈ closedBall (0 : ℂ) (3 / 4) then w ⟨x, h⟩ else 0

theorem extW_apply (w : DiscW) (y : closedBall (0 : ℂ) (3 / 4)) : extW w (y : ℂ) = w y := by
  simp [extW]

theorem extW_continuousOn (w : DiscW) : ContinuousOn (extW w) (closedBall (0 : ℂ) (3 / 4)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hr : (closedBall (0 : ℂ) (3 / 4)).domRestrict (extW w) = fun y => w y := by
    funext y
    exact extW_apply w y
  rw [hr]
  exact w.continuous

/-- On the punctured disc, the contact set of `w` (the cluster minus the pole) is the set where the raw field
`w + t G_{B_{3/4}}(0,·)` is positive. -/
theorem mem_punct_cluster_iff (t : ℝ) (w : DiscW) (y : closedBall (0 : ℂ) (3 / 4))
    (hy : (y : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0}) :
    (y : ℂ) ∈ certCluster (3 / 4) t (extW w) \ {0} ↔ 0 < certRaw t w y := by
  have hne : (y : ℂ) ≠ 0 := hy.2
  have hball : (y : ℂ) ∈ ball (0 : ℂ) (3 / 4) := hy.1
  have hext : extW w (y : ℂ) = w y := extW_apply w y
  have hmem : (y : ℂ) ∈ certCluster (3 / 4) t (extW w) ↔
      -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 (y : ℂ) < w y := by
    unfold certCluster
    rw [mem_ofPred_eq, hext]
    exact ⟨fun h => h.2.resolve_left hne, fun h => ⟨hball, Or.inr h⟩⟩
  rw [mem_sdiff, hmem]
  unfold certRaw
  constructor
  · rintro ⟨h1, _⟩
    linarith
  · intro h
    exact ⟨by linarith, fun h0 => hne (mem_singleton_iff.1 h0)⟩

/-- The punctured contact set is open (GoodSet.lean `isOpen_certCluster`, minus the pole). -/
theorem isOpen_punct_cluster (hpole : FrozenGreenDiscPole) {t : ℝ} (ht : 0 < t) (w : DiscW) :
    IsOpen (certCluster (3 / 4) t (extW w) \ {0}) :=
  (isOpen_certCluster hpole (by norm_num) ht (extW_continuousOn w)).sdiff isClosed_singleton

/-- **Dense data in the punctured disc.** There are data points `z j` of `B̄_{3/4}`, lying in the punctured
open disc, such that every open set meeting the punctured disc contains some `z j`. -/
theorem exists_punct_dense_data :
    ∃ z : ℕ → closedBall (0 : ℂ) (3 / 4), (∀ j, (z j : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0}) ∧
      ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O := by
  have hX : Nonempty ↥(ball (0 : ℂ) (3 / 4) \ {0}) :=
    ⟨⟨(1 / 2 : ℂ), by norm_num [mem_ball, mem_sdiff]⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ↥(ball (0 : ℂ) (3 / 4) \ {0})
  refine ⟨fun j => ⟨(u j : ℂ), ball_subset_closedBall (u j).2.1⟩, fun j => (u j).2, ?_⟩
  intro O hO hne
  obtain ⟨x, hxO, hxp⟩ := hne
  have hO' : IsOpen (Subtype.val ⁻¹' O : Set ↥(ball (0 : ℂ) (3 / 4) \ {0})) :=
    hO.preimage continuous_subtype_val
  obtain ⟨j, hj⟩ := hu.exists_mem_open hO' ⟨⟨x, hxp⟩, hxO⟩
  exact ⟨j, hj⟩

/-- **Charged balls of a certificate.** For dense data `z` in the punctured disc, the
predicate `certD z U t w i` (every basis ball `V` with closure in `U i` has a data point of positive raw field) holds iff
the basis ball `U i` lies in the closure of the punctured contact set. -/
theorem certD_iff_subset_closure_cluster (hpole : FrozenGreenDiscPole) {t : ℝ} (ht : 0 < t)
    {U : ℕ → Set ℂ} (hopen : ∀ V, IsOpen (U V)) (hne : ∀ V, (U V).Nonempty)
    (hreg : ∀ O : Set ℂ, IsOpen O → ∀ x ∈ O, ∃ V, x ∈ U V ∧ closure (U V) ⊆ O)
    {z : ℕ → closedBall (0 : ℂ) (3 / 4)} (hz : ∀ j, (z j : ℂ) ∈ ball (0 : ℂ) (3 / 4) \ {0})
    (hzd : ∀ O : Set ℂ, IsOpen O → (O ∩ (ball (0 : ℂ) (3 / 4) \ {0})).Nonempty → ∃ j, (z j : ℂ) ∈ O)
    (w : DiscW) (i : ℕ) :
    certD z U t w i ↔ U i ⊆ closure (certCluster (3 / 4) t (extW w) \ {0}) := by
  have hCsub : certCluster (3 / 4) t (extW w) \ {0} ⊆ ball (0 : ℂ) (3 / 4) \ {0} :=
    fun x hx => ⟨hx.1.1, hx.2⟩
  have hCo := isOpen_punct_cluster hpole ht w
  unfold certD
  refine charged_iff_subset_closure hopen hne hreg (C := certCluster (3 / 4) t (extW w) \ {0})
    (z := fun j => (z j : ℂ)) (R := fun j => 0 < certRaw t w (z j)) ?_ ?_ i
  · intro j hj
    exact (mem_punct_cluster_iff t w (z j) (hz j)).2 hj
  · rintro O hO ⟨x, hxO, hxC⟩
    obtain ⟨j, hj⟩ := hzd (O ∩ (certCluster (3 / 4) t (extW w) \ {0})) (hO.inter hCo)
      ⟨x, ⟨hxO, hxC⟩, hCsub hxC⟩
    exact ⟨j, hj.1, (mem_punct_cluster_iff t w (z j) (hz j)).1 hj.2⟩

end MatedCRT
