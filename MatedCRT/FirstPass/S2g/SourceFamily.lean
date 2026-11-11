import HarmonicBalls.Draft.Section3
import HarmonicBalls.Draft.Section5

/-! # Source pathwise inputs through the Harmonic Balls family

For a whole-plane source `μ`, let `Λ` be a family of Theorem 5.5 (`IsRegularizedClusterFamily`) and let
`A_t = regularizedCluster μ (3/4) 0 t`. The identifications `Λ_t = A_t` used for the pathwise inputs are proved from
Draft statements only: the clause `Λ_t = regularizedCluster μ r 0 t` of `IsRegularizedClusterFamily`
(Theorem 5.5, HB Draft Section5), cluster compatibility (Lemma 3.5, `ClusterCompatibilityStmt`, HB Draft Section3) and
boundary-nullness at radius `1` (Proposition 5.3, `ClusterBoundaryMeasureZeroStmt`, HB Draft Section5).
Terminology: Armitage-Gardiner (regularized clusters), Armstrong-Kuusi-Mourrat (harmonic balls), Duplantier-Sheffield (LQG). -/

open MeasureTheory Set Filter Topology Metric HarmonicBalls

namespace MatedCRT

/-- Compatibility of the raw clusters at one ambient radius `R` (HB Lemma 3.5, `ClusterCompatibilityStmt`, fixed `R`). -/
def ClusterCompatibleAt (μ : Measure ℂ) (R : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, s₁ ≤ R → ∀ z ∈ ball (0 : ℂ) s₁, ∀ s₂ ∈ Set.Icc s₁ R,
    closure (cluster μ s₂ z t) ⊆ ball 0 s₁ → ∀ s ∈ Set.Icc s₁ R, cluster μ s z t = cluster μ s₂ z t

/-- Global-to-local identification: a family member inside `B_{9/16}` is the regularized cluster at radius `3/4`
(the clause of `IsRegularizedClusterFamily` with `s = 5/8 ≤ r = 3/4`). -/
theorem eq_regularizedCluster_of_subset_ball {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → closure (Λ t) ⊆ ball (0 : ℂ) s →
      ∀ r : ℝ, s ≤ r → Λ t = regularizedCluster μ r 0 t)
    {t : ℝ} (ht : 0 < t) (hsub : Λ t ⊆ ball (0 : ℂ) (9 / 16)) :
    Λ t = regularizedCluster μ (3 / 4) 0 t := by
  have hcl : closure (Λ t) ⊆ ball (0 : ℂ) (5 / 8) :=
    (closure_minimal (hsub.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball (by norm_num))
  exact hfam t ht (5 / 8) (by norm_num) hcl (3 / 4) (by norm_num)

/-- Local-to-global identification: if the closure of the radius-`3/4` raw cluster lies in `B_{s₁}` with `0 < s₁ ≤ 3/4`, then
`Λ_t` is the regularized cluster at radius `3/4`. Proof: a natural radius `N` containing the bounded `Λ_t` in its interior
(clause of `IsRegularizedClusterFamily` at `r = N`), and Lemma 3.5 at `R = N` with `s₂ = 3/4` giving `cluster N = cluster 3/4`. -/
theorem eq_regularizedCluster_of_closure_ball {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → closure (Λ t) ⊆ ball (0 : ℂ) s →
      ∀ r : ℝ, s ≤ r → Λ t = regularizedCluster μ r 0 t)
    (hbdd : ∀ t : ℝ, 0 < t → Bornology.IsBounded (Λ t))
    (hcomp : ∀ N : ℕ, 0 < N → ClusterCompatibleAt μ (N : ℝ))
    {t s₁ : ℝ} (ht : 0 < t) (hs₁ : 0 < s₁) (hs₁' : s₁ ≤ 3 / 4)
    (hcl : closure (cluster μ (3 / 4) 0 t) ⊆ ball (0 : ℂ) s₁) :
    Λ t = regularizedCluster μ (3 / 4) 0 t := by
  obtain ⟨M, hM⟩ := (hbdd t ht).subset_closedBall (0 : ℂ)
  obtain ⟨N, hN⟩ := exists_nat_gt (max M 1)
  have hMN : M < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have h1N : (1 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hN0 : 0 < N := by exact_mod_cast (show (0 : ℝ) < (N : ℝ) by linarith)
  have hcl' : closure (Λ t) ⊆ ball (0 : ℂ) (N : ℝ) :=
    (closure_minimal hM Metric.isClosed_closedBall).trans (Metric.closedBall_subset_ball hMN)
  have hΛN : Λ t = regularizedCluster μ (N : ℝ) 0 t :=
    hfam t ht (N : ℝ) (by linarith) hcl' (N : ℝ) le_rfl
  have hc := hcomp N hN0 t ht s₁ (by linarith) (0 : ℂ) (Metric.mem_ball_self hs₁) (3 / 4)
    ⟨hs₁', by linarith⟩ hcl (N : ℝ) ⟨by linarith, le_rfl⟩
  rw [hΛN]
  unfold regularizedCluster
  rw [hc]

/-- Boundary-nullness at radius `3/4` from radius `1`: Lemma 3.5 with `R = 1` gives `cluster 1 = cluster 3/4` when the
radius-`3/4` closure lies in `B_{s₁}`, and Proposition 5.3 (`ClusterBoundaryMeasureZeroStmt`, radius `1`) applies. -/
theorem frontier_null_of_radius_one {μ : Measure ℂ} {t s₁ : ℝ} (ht : 0 < t) (hs₁ : 0 < s₁) (hs₁' : s₁ ≤ 3 / 4)
    (hcomp1 : ClusterCompatibleAt μ 1)
    (hb1 : closure (cluster μ 1 0 t) ⊆ ball (0 : ℂ) 1 → μ (frontier (cluster μ 1 0 t)) = 0)
    (hcl : closure (cluster μ (3 / 4) 0 t) ⊆ ball (0 : ℂ) s₁) :
    μ (frontier (cluster μ (3 / 4) 0 t)) = 0 := by
  have hc := hcomp1 t ht s₁ (by linarith) (0 : ℂ) (Metric.mem_ball_self hs₁) (3 / 4)
    ⟨hs₁', by norm_num⟩ hcl 1 ⟨by linarith, le_rfl⟩
  rw [hc] at hb1
  exact hb1 (hcl.trans (Metric.ball_subset_ball (by linarith)))

/-- Closure of the raw radius-`3/4` cluster inside the closed half-ball, when the regularized cluster lies in `B_{1/2}`:
the raw cluster is open, so `Λ ⊆ int (closure Λ)` and `closure Λ = closure (int (closure Λ))`. -/
theorem closure_cluster_subset_closedBall_half {μ : Measure ℂ} {t : ℝ}
    (hopen : IsOpen (cluster μ (3 / 4) 0 t))
    (hsub : regularizedCluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) (1 / 2)) :
    closure (cluster μ (3 / 4) 0 t) ⊆ closedBall (0 : ℂ) (1 / 2) := by
  have h1 : closure (cluster μ (3 / 4) 0 t) ⊆ closure (regularizedCluster μ (3 / 4) 0 t) :=
    closure_mono (interior_maximal subset_closure hopen)
  have h2 : closure (regularizedCluster μ (3 / 4) 0 t) ⊆ closedBall (0 : ℂ) (1 / 2) := by
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    exact closure_mono hsub
  exact h1.trans h2

/-- Almost surely, the compatibility of the raw clusters at every natural ambient radius `N > 0` (HB Lemma 3.5,
`ClusterCompatibilityStmt`; countably many `R`, so `ae_all_iff`). -/
theorem ae_clusterCompatibleAt_of_draft {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hQ : γ < lqgQ γ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hW : IsWholePlaneGFF P hC hcirc) (hL : IsLQGMeasureOfField P γ γ hcirc μ)
    (hCompat : ClusterCompatibilityStmt.{0}) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, 0 < N → ClusterCompatibleAt (μ ω) (N : ℝ) := by
  refine ae_all_iff.2 fun N => ?_
  by_cases hN : 0 < N
  · filter_upwards [hCompat γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hW hL (N : ℝ) (by exact_mod_cast hN)] with ω hω
    exact fun _ => hω
  · exact ae_of_all _ fun ω h => absurd h hN

end MatedCRT
