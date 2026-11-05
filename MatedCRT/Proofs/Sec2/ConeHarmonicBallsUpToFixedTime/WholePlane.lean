import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import HarmonicBalls.Draft.Section1
import HarmonicBalls.Draft.Section3
import HarmonicBalls.Draft.Section5

/-!
# Lemma 2.4 for `h^ℂ - γ log |·|` from HB22

`wholePlaneHalfBallFamilyStep_of_hb`: for the whole-plane GFF `h^ℂ` and the LQG measure `μ` of `h^ℂ - γ log |·|`,
a.s. there is a family of Lemma 2.4 for `μ` (`WholePlaneHalfBallFamilyStep`). This is the input of the proof of
Lemma 2.4 (lines 540-545) before the transfer to the quantum cone. It uses only the HB22 Draft statements (cited
results of Bou-Rabee-Gwynne, arXiv:2208.11795):
* Theorem 1.1 (`ExistenceUniquenessHarmonicBallsStmt`): the family `{Λ_t}_{t > 0}` of harmonic balls centred at `0`;
* Theorem 5.5 (`ExistenceHarmonicBallsStmt`) and Proposition 5.6 (`UniquenessHarmonicBallsStmt`): `Λ_t` is the
  regularized cluster `int(cl Λ_{B_ρ}(t))` once `Λ_t ⋐ B_s`, `s ≤ ρ`;
* Lemma 3.1 (`LeastSupersolutionMemStmt`), Lemma 3.2 (`ClusterOpenLaplacianStmt`), Lemma 3.4
  (`ClusterConservationOfMassStmt`): continuity, Laplacian and boundary values of the least supersolution `w̄^{B_ρ}_t`;
* Lemma 3.5 (`ClusterCompatibilityStmt`) and Proposition 5.3 (`ClusterBoundaryMeasureZeroStmt`): `μ(∂Λ_{B_ρ}(t)) = 0`
  for the clusters inside `B_{3/4}`, so that the Laplacian of Lemma 3.2 is `μ|_{Λ_t}` (condition (c) of Theorem 2.3);
* Proposition 5.2 (`ClusterContinuityStmt`), Lemma 3.3 (`ClusterMonotoneStmt`) and Lemma 5.8
  (`ClusterStrongCompatibilityStmt`): `Λ_t ⊆ B_{1/2}` for small `t > 0` (so `T > 0`).
The family is stopped at `∂B_{1/2}` by `hasConeHarmonicBallsUpToHalfBall_of_conditions`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT

/-- `γ < Q = 2/γ + γ/2` for `γ ∈ (0, 2)`: the field `h^ℂ - γ log |·|` is in the range `α₀ < Q` of HB22. -/
theorem gamma_lt_lqgQ_of_lt_two {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : γ < lqgQ γ := by
  have hid : lqgQ γ - γ = ((2 - γ) * (2 + γ)) / (2 * γ) := by
    unfold lqgQ
    field_simp
    ring
  have h2 : 0 < 2 - γ := by linarith
  have hpos : 0 < lqgQ γ - γ := by
    rw [hid]
    positivity
  linarith

/-- The cluster `Λ_{U;z}(t)` of the disk `U = B_r` is the cluster `Λ_{B_r;z}(t)`. -/
theorem clusterOn_ball_eq_cluster (μ : Measure ℂ) {r : ℝ} (hr : 0 < r) (z : ℂ) (t : ℝ) :
    clusterOn μ (ball 0 r) z t = cluster μ r z t := by
  have hS : supersolutionsOn μ (ball 0 r) z t = supersolutions μ r z t := by
    simp only [supersolutionsOn, supersolutions, closure_ball (0 : ℂ) hr.ne']
  have hL : leastSupersolutionOn μ (ball 0 r) z t = leastSupersolution μ r z t := by
    funext x
    simp only [leastSupersolutionOn, leastSupersolution, hS]
  simp only [clusterOn, cluster, hL]

/-- Compactness: if `t ↦ K_t` (`t > 0`) is a nondecreasing family of compact sets and `⋂_{t > 0} K_t` lies in an open
set `U`, then `K_t ⊆ U` for some `t > 0`. -/
theorem exists_pos_subset_of_iInter_subset {K : ℝ → Set ℂ} (hmono : ∀ s t : ℝ, 0 < s → s ≤ t → K s ⊆ K t)
    (hcpt : ∀ t : ℝ, 0 < t → IsCompact (K t)) (hcl : ∀ t : ℝ, 0 < t → IsClosed (K t)) {U : Set ℂ}
    (hU : IsOpen U) (hint : ⋂ t ∈ Ioi (0 : ℝ), K t ⊆ U) : ∃ t : ℝ, 0 < t ∧ K t ⊆ U := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hanti : Antitone fun n : ℕ => K (1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact hmono _ _ (hpos n) (by gcongr)
  have hsubU : ⋂ n : ℕ, K (1 / ((n : ℝ) + 1)) ⊆ U := by
    intro x hx
    apply hint
    simp only [mem_iInter] at hx ⊢
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < t from ht)
    exact hmono _ _ (hpos n) hn.le (hx n)
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' hanti.directed_ge (fun n => hcpt _ (hpos n))
    (fun n => hcl _ (hpos n)) (hU.mem_nhdsSet.2 hsubU)
  exact ⟨_, hpos n, hn⟩

/-- **Lemma 2.4 for `h^ℂ - γ log |·|`** from HB22 (Theorems 1.1, 5.5, Propositions 5.2, 5.3, 5.6, Lemmas 3.1-3.5,
5.8): a.s. the family of harmonic balls of Theorem 1.1 centred at `0`, stopped when it reaches `∂B_{1/2}`, is a family
of Lemma 2.4 for the LQG measure of `h^ℂ - γ log |·|`. -/
theorem wholePlaneHalfBallFamilyStep_of_hb (h11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (h55 : ExistenceHarmonicBallsStmt.{0}) (h56 : UniquenessHarmonicBallsStmt.{0})
    (h31 : LeastSupersolutionMemStmt.{0}) (h32 : ClusterOpenLaplacianStmt.{0}) (h33 : ClusterMonotoneStmt.{0})
    (h34 : ClusterConservationOfMassStmt.{0}) (h35 : ClusterCompatibilityStmt.{0})
    (h52 : ClusterContinuityStmt.{0}) (h53 : ClusterBoundaryMeasureZeroStmt.{0})
    (h58 : ClusterStrongCompatibilityStmt.{0}) : WholePlaneHalfBallFamilyStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ _ hgff hlqg
  have hQ : γ < lqgQ γ := gamma_lt_lqgQ_of_lt_two hγ0 hγ2
  -- the family of Theorem 5.5, chosen for every sample and every centre
  let Λhat : Ω → ℂ → ℝ → Set ℂ := fun ω z =>
    Classical.epsilon fun Λ : ℝ → Set ℂ => IsRegularizedClusterFamily (μ ω) Λ z
  have hΛhat : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z := by
    filter_upwards [h55 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hgff hlqg] with ω hω z
    exact Classical.epsilon_spec (hω z)
  have h35' : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ, 0 < t → ∀ s₁ ≤ (n : ℝ) + 1, ∀ z ∈ ball (0 : ℂ) s₁,
      ∀ s₂ ∈ Icc s₁ ((n : ℝ) + 1), closure (cluster (μ ω) s₂ z t) ⊆ ball 0 s₁ →
      ∀ s ∈ Icc s₁ ((n : ℝ) + 1), cluster (μ ω) s z t = cluster (μ ω) s₂ z t :=
    ae_all_iff.2 fun n => h35 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hgff hlqg _ (by positivity)
  filter_upwards [h11 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hgff hlqg,
    h56 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hgff hlqg Λhat hΛhat, hΛhat,
    h31 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hgff hlqg, h32 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hgff hlqg,
    h33 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hgff hlqg, h34 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hgff hlqg, h35',
    h52 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hgff hlqg, h53 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hgff hlqg,
    h58 γ γ hγ0 hγ2 hQ Ω P hC hcirc μ hgff hlqg Λhat hΛhat (ball 0 1) isOpen_ball isBounded_ball, hlqg]
    with ω h11ω h56ω hΛω h31ω h32ω h33ω h34ω h35ω h52ω h53ω h58ω hlim
  have := hlim.isLocallyFiniteMeasure
  obtain ⟨Λ, hΛ, -⟩ := h11ω 0
  have heq : EqOn Λ (Λhat ω 0) (Ioi 0) := h56ω 0 Λ hΛ
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  -- `Λ_t` is the regularized cluster of every larger disk once it is compactly contained in a disk (Theorem 5.5)
  have hreg : ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → closure (Λ t) ⊆ ball 0 s → ∀ r : ℝ, s ≤ r →
      Λ t = interior (closure (cluster (μ ω) r 0 t)) := by
    intro t ht s hs hcl r hr
    rw [heq ht] at hcl ⊢
    exact (hΛω 0).2.2 t ht s hs hcl r hr
  -- small times (Proposition 5.2, Lemma 3.3, Lemma 5.8)
  have hsmall : ∃ t : ℝ, 0 < t ∧ Λ t ⊆ ball 0 (1 / 2) := by
    have hcb : ∀ t : ℝ, closure (cluster (μ ω) 1 0 t) ⊆ closedBall 0 1 :=
      fun t => closure_minimal (fun x hx => ball_subset_closedBall hx.1) isClosed_closedBall
    have hint : ⋂ t ∈ Ioi (0 : ℝ), closure (cluster (μ ω) 1 0 t) ⊆ ball (0 : ℂ) (1 / 4) := by
      rw [(h52ω 0 (mem_ball_self (by norm_num))).1]
      exact singleton_subset_iff.2 (mem_ball_self (by norm_num))
    obtain ⟨t, ht, hsub⟩ := exists_pos_subset_of_iInter_subset (K := fun t => closure (cluster (μ ω) 1 0 t))
      (fun s t hs hst => closure_mono (h33ω s t 1 hs hst one_pos 0 h0))
      (fun t _ => (isCompact_closedBall 0 1).of_isClosed_subset isClosed_closure (hcb t))
      (fun t _ => isClosed_closure) isOpen_ball hint
    have hsub' : closure (cluster (μ ω) 1 0 t) ⊆ ball 0 (1 / 2) := hsub.trans (ball_subset_ball (by norm_num))
    have hc := h58ω t ht 0 h0 (Or.inr (by
      rw [clusterOn_ball_eq_cluster _ one_pos]
      exact hsub'.trans (ball_subset_ball (by norm_num))))
    rw [clusterOn_ball_eq_cluster _ one_pos] at hc
    refine ⟨t, ht, ?_⟩
    rw [heq ht]
    refine subset_closure.trans ?_
    rw [hc]
    exact hsub'
  refine hasConeHarmonicBallsUpToHalfBall_of_conditions (fun t ht => (hΛ.1 t ht).1) hΛ.2 ?_
    measure_ball_lt_top.ne hsmall
  intro t r ht hhalf hr hsub ρ hρ
  have hρ0 : 0 < ρ := hr.trans hρ
  have h0ρ : (0 : ℂ) ∈ ball (0 : ℂ) ρ := mem_ball_self hρ0
  have hclr : closure (Λ t) ⊆ closedBall 0 r :=
    closure_minimal (hsub.trans ball_subset_closedBall) isClosed_closedBall
  have hclh : closure (Λ t) ⊆ closedBall 0 (1 / 2) :=
    closure_minimal (hhalf.trans ball_subset_closedBall) isClosed_closedBall
  have hΛC : Λ t = interior (closure (cluster (μ ω) ρ 0 t)) :=
    hreg t ht ((r + ρ) / 2) (by positivity) (hclr.trans (closedBall_subset_ball (by linarith))) ρ (by linarith)
  obtain ⟨hCopen, -, ν, -, -, hνle, hlap, -⟩ := h32ω t ρ ht hρ0 0 h0ρ
  set C := cluster (μ ω) ρ 0 t with hCdef
  have hCsub : C ⊆ Λ t := by
    rw [hΛC]
    exact interior_maximal subset_closure hCopen
  have hsubC : Λ t ⊆ closure C := by
    rw [hΛC]
    exact interior_subset
  have hclC : closure C ⊆ ball 0 (min ρ (3 / 4)) := by
    intro x hx
    have hx' := closure_mono hCsub hx
    have h1 := mem_closedBall_zero_iff.1 (hclr hx')
    have h2 := mem_closedBall_zero_iff.1 (hclh hx')
    exact mem_ball_zero_iff.2 (lt_min (by linarith) (by linarith))
  -- the cluster of `B_ρ` is the cluster of `B_1` (Lemma 3.5)
  obtain ⟨n, hn⟩ := exists_nat_ge (max ρ 1)
  have hρn : ρ ≤ (n : ℝ) + 1 := by linarith [le_max_left ρ 1]
  have h1n : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [le_max_right ρ 1]
  have hs₁ : min ρ (3 / 4) ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hC1 : cluster (μ ω) 1 0 t = C :=
    h35ω n t ht (min ρ (3 / 4)) (hs₁.trans h1n) 0 (mem_ball_self (lt_min hρ0 (by norm_num))) ρ
      ⟨min_le_left _ _, hρn⟩ hclC 1 ⟨hs₁, h1n⟩
  -- `μ(∂Λ_{B_ρ}(t)) = 0` (Proposition 5.3)
  have hfront : μ ω (frontier C) = 0 := by
    have hcl1 : closure (cluster (μ ω) 1 0 t) ⊆ ball 0 1 := by
      rw [hC1]
      exact hclC.trans (ball_subset_ball hs₁)
    have := h53ω 0 h0 t ht hcl1
    rwa [hC1] at this
  have hsd : Λ t \ C ⊆ frontier C := fun x hx =>
    show x ∈ closure C \ interior C from ⟨hsubC hx.1, fun h => hx.2 (interior_subset h)⟩
  have hdiff : μ ω (Λ t \ C) = 0 := measure_mono_null hsd hfront
  have hrestr : (μ ω).restrict C = (μ ω).restrict (Λ t) := by
    have h0' : μ ω (C \ Λ t) = 0 :=
      measure_mono_null (fun x hx => (hx.2 (hCsub hx.1)).elim) measure_empty
    have hae : C =ᵐ[μ ω] Λ t := ae_eq_set.2 ⟨h0', hdiff⟩
    exact Measure.restrict_congr_set hae
  have hνfront : ν.restrict (frontier C) = 0 := by
    have hfb : frontier C ⊆ ball 0 ρ :=
      frontier_subset_closure.trans (hclC.trans (ball_subset_ball (min_le_left _ _)))
    have h1 := Measure.le_iff'.1 hνle (frontier C)
    rw [Measure.restrict_apply' measurableSet_ball, Measure.restrict_apply' measurableSet_ball,
      inter_eq_left.2 hfb, hfront] at h1
    rw [Measure.restrict_eq_zero]
    exact nonpos_iff_eq_zero.1 h1
  rw [hνfront, add_zero, hrestr] at hlap
  refine ⟨hΛC, (h31ω t ρ ht hρ0 0 h0ρ).2.1, hlap, fun x hx => ?_⟩
  have hx' : x ∉ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff, not_lt]
    exact (mem_sphere_zero_iff_norm.1 hx).ge
  have hG : greenFunction (ball 0 ρ) 0 x = 0 := by
    simp [greenFunction, hx']
  have hod := (h34ω ρ t hρ0 ht 0 h0ρ).2.1 x hx
  simpa only [odometer, hG, mul_zero, add_zero] using hod

end MatedCRT
