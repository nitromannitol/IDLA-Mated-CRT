import MatedCRT.FirstPass.Frozen.S2g
import HarmonicBalls.FirstPass.Phase2.CampbellCountedForms
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-!
# Initial compact confinement of the whole-plane clusters

The input `FrozenHBInitialConfinement` (`MatedCRT/FirstPass/Frozen/S2g.lean`) of the IDLA paper is a corollary of
results of Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity*, arXiv:2208.11795v3: Proposition 5.2
(the closed clusters `closure Λ^0_t` of the unit disk shrink to the pole as `t ↓ 0`), Lemma 3.3 (monotonicity of the
clusters in `t`) and Lemma 3.5 (compatibility of the clusters of nested disks), at `α₀ = γ < Q`.

The argument is the one recorded in the docstring of the input: the closed clusters `closure Λ_{B_1;0}(t)`, `t > 0`,
are compact (they lie in the closed unit disk) and directed downwards by Lemma 3.3, and their intersection is `{0}`
by Proposition 5.2; by compactness one of them lies in `B_{1/2}`. Lemma 3.5 then identifies the cluster of `B_{3/4}`
at that time with the cluster of `B_1`, so the regularized cluster `int (closure Λ_{B_{3/4};0}(s))` lies in `B_{1/2}`.

* `exists_closure_cluster_subset_ball_half`: the compactness step, deterministic.
* `frozenHBInitialConfinement_of_sec5`: the input from Proposition 5.2 and Lemmas 3.3, 3.5.
* `frozenHBInitialConfinement_of_ballMassBounds`: the input from the Ding-Gwynne ball-mass bounds (through the
  proved form of Proposition 5.2) and the volume growth condition at all scales (through the proved Lemmas 3.3, 3.5).
-/

open MeasureTheory Filter Topology Set Metric HarmonicBalls

namespace MatedCRT.FirstPass.Derived

/-- Compactness step. For a measure `μ` on `ℂ` whose unit-disk clusters with pole `0` increase in `t` and whose
closed clusters shrink to the pole (`⋂_{t > 0} closure Λ_{B_1;0}(t) = {0}`), some closed cluster at a positive time
lies in `B_{1/2}`. -/
theorem exists_closure_cluster_subset_ball_half {μ : Measure ℂ}
    (hmono : ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ t₂ → cluster μ 1 0 t₁ ⊆ cluster μ 1 0 t₂)
    (hint : ⋂ t ∈ Ioi (0 : ℝ), closure (cluster μ 1 0 t) = {0}) :
    ∃ s : ℝ, 0 < s ∧ closure (cluster μ 1 0 s) ⊆ ball (0 : ℂ) (1 / 2) := by
  let V : Ioi (0 : ℝ) → Set ℂ := fun t => closure (cluster μ 1 0 t)
  have hdir : Directed (· ⊇ ·) V := by
    intro a b
    have hab : (0 : ℝ) < min (a : ℝ) b := lt_min (mem_Ioi.1 a.2) (mem_Ioi.1 b.2)
    refine ⟨⟨min (a : ℝ) b, mem_Ioi.2 hab⟩, ?_, ?_⟩
    · exact closure_mono (hmono _ _ hab (min_le_left _ _))
    · exact closure_mono (hmono _ _ hab (min_le_right _ _))
  have hcpt : ∀ t, IsCompact (V t) := fun t =>
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => ball_subset_closedBall (show x ∈ ball (0 : ℂ) 1 from hx.1))
        isClosed_closedBall)
  have hiInter : (⋂ t, V t) = {0} := by
    rw [← hint]
    ext x
    simp only [V, mem_iInter, Subtype.forall, mem_Ioi]
  have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, mem_Ioi.2 one_pos⟩⟩
  have hU : ball (0 : ℂ) (1 / 2) ∈ 𝓝ˢ (⋂ t, V t) := by
    rw [hiInter, isOpen_ball.mem_nhdsSet, singleton_subset_iff]
    exact mem_ball_self (by norm_num)
  obtain ⟨t, ht⟩ := exists_subset_nhds_of_isCompact hdir hcpt hU
  exact ⟨t, mem_Ioi.1 t.2, ht⟩

/-- `FrozenHBInitialConfinement` from Proposition 5.2 (`ClusterContinuityStmt`) and Lemmas 3.3
(`ClusterMonotoneStmt`) and 3.5 (`ClusterCompatibilityStmt`) of the harmonic-balls paper, applied at `α₀ = γ`
(`γ < Q` for `0 < γ < 2`), at the pole `0`, with `R = 1`, `s₁ = 3/4`, `s₂ = 1`. -/
theorem frozenHBInitialConfinement_of_sec5
    (h52 : ClusterContinuityStmt.{0}) (h33 : ClusterMonotoneStmt.{0})
    (h35 : ClusterCompatibilityStmt.{0}) : FrozenHBInitialConfinement := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ _ hGFF hμ
  have hQ : γ < lqgQ γ := by
    unfold lqgQ
    have h : γ / 2 < 2 / γ := by
      rw [div_lt_div_iff₀ (by norm_num) hγ0]
      nlinarith
    linarith
  have e52 := h52 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hGFF hμ
  have e33 := h33 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hGFF hμ
  have e35 := h35 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hGFF hμ 1 one_pos
  filter_upwards [e52, e33, e35] with ω h52ω h33ω h35ω
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 2) := mem_ball_self (by norm_num)
  obtain ⟨s, hs, hsub⟩ := exists_closure_cluster_subset_ball_half
    (fun t₁ t₂ ht₁ ht₁₂ => h33ω t₁ t₂ 1 ht₁ ht₁₂ one_pos 0 (mem_ball_self one_pos))
    (h52ω 0 h0).1
  refine ⟨s, hs, ?_⟩
  have hsub34 : closure (cluster (μ ω) 1 0 s) ⊆ ball (0 : ℂ) (3 / 4) :=
    hsub.trans (ball_subset_ball (by norm_num))
  have heq : cluster (μ ω) (3 / 4) 0 s = cluster (μ ω) 1 0 s :=
    h35ω s hs (3 / 4) (by norm_num) 0 (mem_ball_self (by norm_num)) 1 ⟨by norm_num, le_rfl⟩ hsub34
      (3 / 4) ⟨le_rfl, by norm_num⟩
  unfold regularizedCluster
  rw [heq]
  exact interior_subset.trans hsub

/-- `FrozenHBInitialConfinement` from the Ding-Gwynne ball-mass bounds on `Type` (`hDG`, through the counted form
of Proposition 5.2 with the marked Campbell identity supplied) and the volume growth condition at all scales
(`hI2`, through the proved Lemmas 3.3 and 3.5). -/
theorem frozenHBInitialConfinement_of_ballMassBounds
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0}) : FrozenHBInitialConfinement :=
  frozenHBInitialConfinement_of_sec5 (HarmonicBalls.Closure.closure_5_2_derivedInputsCampbell hDG)
    (clusterMonotone_proved hI2) (clusterCompatibility_proved hI2)

end MatedCRT.FirstPass.Derived
