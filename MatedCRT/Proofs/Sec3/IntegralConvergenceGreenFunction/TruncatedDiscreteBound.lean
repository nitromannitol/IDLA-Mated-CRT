import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.Truncation

/-!
# Lemma 3.4: pathwise bound for the truncated discrete occupation

For two test functions `F`, `G` that are `δ`-close on the ball `B = ball z r`, the discrete truncated occupations
`truncatedDiscreteOccupation S B y F N ε ω` and `… G N ε ω` (the walk killed on leaving the interior cells
`V^ε(B) \ V^ε(∂B)`) differ by at most `(mε)⁻¹ N δ`. This is the discrete half of the finite-net argument for the
environment-dependent fixed-time step.

The geometric input: an interior vertex has its marked point in the ball, because its cell is the image of an
interval under the continuous curve `η`, hence connected; it meets the ball and does not meet the boundary, so it
lies in the ball.

Terminology: vertices `V^ε(D)`, cells `H^ε_a` (Armstrong–Kuusi–Mourrat, Section 1 of the paper), killed walk.
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- An interior vertex (its cell meets `B` and does not meet the boundary `∂B`) has its marked point in the open
ball `B`, when the curve `η` is continuous. -/
theorem vertexPoint_mem_ball_of_interior {ε : ℝ} {η : ℝ → ℂ} {z : ℂ} {r : ℝ} (hε : 0 < ε)
    (hη : Continuous η) {k : ℤ} (hk : k ∈ interiorCellVertices ε η (ball z r)) :
    vertexPoint ε η k ∈ ball z r := by
  obtain ⟨hD, hF⟩ := hk
  obtain ⟨p, hpc, hpB⟩ := hD
  have hcon : IsPreconnected (cell ε η k) := isPreconnected_Icc.image η hη.continuousOn
  have hF' : ¬ (cell ε η k ∩ frontier (ball z r)).Nonempty := hF
  have hsub : cell ε η k ⊆ ball z r := by
    refine hcon.subset_left_of_subset_union isOpen_ball (isOpen_compl_iff.2 isClosed_closure)
      (Set.disjoint_left.2 fun q hqB hqC => hqC (subset_closure hqB)) ?_ ⟨p, hpc, hpB⟩
    intro q hq
    by_cases hqB : q ∈ ball z r
    · exact Or.inl hqB
    · by_cases hqC : q ∈ closure (ball z r)
      · exfalso
        apply hF'
        refine ⟨q, hq, ?_⟩
        rw [frontier, isOpen_ball.interior_eq]
        exact ⟨hqC, hqB⟩
      · exact Or.inr hqC
  have hpt : vertexPoint ε η k ∈ cell ε η k := by
    refine ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_refl _⟩, rfl⟩
  exact hsub hpt

/-- The walk has not left `A` by time `n` iff `x j ∈ A` for all `j ≤ n`. -/
theorem natLt_vExitTime_iff_forall_le (A : Set ℤ) (x : ℕ → ℤ) (n : ℕ) :
    (n : ℕ∞) < vExitTime A x ↔ ∀ j ≤ n, x j ∈ A := by
  classical
  unfold vExitTime
  split_ifs with h
  · constructor
    · intro hlt j hj
      have hnm : n < Nat.find h := ENat.natCast_lt_natCast.1 hlt
      have hjm : j < Nat.find h := lt_of_le_of_lt hj hnm
      by_contra hjA
      exact Nat.find_min h hjm hjA
    · intro hA
      have hnot : ¬ (Nat.find h ≤ n) := fun hle => (Nat.find_spec h) (hA _ hle)
      exact ENat.natCast_lt_natCast.2 (not_le.1 hnot)
  · simp only [not_exists, not_not] at h
    simp only [ENat.natCast_lt_top, true_iff]
    exact fun j _ => h j

/-- The event that the walk stays in `A` up to time `n` is measurable in the path variable. -/
theorem measurableSet_natLt_vExitTime (A : Set ℤ) (n : ℕ) :
    MeasurableSet {x : ℕ → ℤ | (n : ℕ∞) < vExitTime A x} := by
  have hset : {x : ℕ → ℤ | (n : ℕ∞) < vExitTime A x}
      = ⋂ j ∈ Finset.range (n + 1), (fun x : ℕ → ℤ => x j) ⁻¹' A := by
    ext x
    simp only [Set.mem_ofPred_eq, natLt_vExitTime_iff_forall_le, Set.mem_iInter, Finset.mem_range,
      Set.mem_preimage]
    constructor
    · intro h j hj
      exact h j (Nat.lt_succ_iff.1 hj)
    · intro h j hj
      exact h j (Nat.lt_succ_of_le hj)
  rw [hset]
  exact Finset.measurableSet_biInter _ fun j _ => (measurable_pi_apply j) (MeasurableSet.of_discrete)

/-- **Pathwise bound for the discrete truncated occupation.** If `F` and `G` are `δ`-close on the ball `B`, and
both are bounded there by `M`, then the discrete truncated occupations differ by at most `(mε)⁻¹ · N · δ`. -/
theorem truncatedDiscreteOccupation_sub_le {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (y z : ℂ)
    {r : ℝ} (F G : Ω → ℂ → ℝ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) (hm : 0 < S.mε ε) (ω : Ω)
    (hη : Continuous (S.η ω)) {M : ℝ} (hM0 : 0 ≤ M) (hFM : ∀ q ∈ ball z r, |F ω q| ≤ M)
    (hGM : ∀ q ∈ ball z r, |G ω q| ≤ M) {δ : ℝ} (hδ : 0 ≤ δ) (hFG : ∀ q ∈ ball z r, |F ω q - G ω q| ≤ δ) :
    |truncatedDiscreteOccupation S (ball z r) y F N ε ω - truncatedDiscreteOccupation S (ball z r) y G N ε ω|
      ≤ (S.mε ε)⁻¹ * (N * δ) := by
  unfold truncatedDiscreteOccupation
  set A := interiorCellVertices ε (S.η ω) (ball z r) with hA
  set μ := srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) with hμ
  set hF : (ℕ → ℤ) → ℝ := fun x => ∑ n ∈ Finset.range N,
    if (n : ℕ∞) < vExitTime A x then F ω (vertexPoint ε (S.η ω) (x n)) else 0 with hFdef
  set hG : (ℕ → ℤ) → ℝ := fun x => ∑ n ∈ Finset.range N,
    if (n : ℕ∞) < vExitTime A x then G ω (vertexPoint ε (S.η ω) (x n)) else 0 with hGdef
  -- a summand is controlled by the bound on the ball, since interior vertices lie in the ball
  have hterm : ∀ (H : ℂ → ℝ) (c : ℝ), 0 ≤ c → (∀ q ∈ ball z r, |H q| ≤ c) → ∀ (x : ℕ → ℤ) (n : ℕ),
      |if (n : ℕ∞) < vExitTime A x then H (vertexPoint ε (S.η ω) (x n)) else 0| ≤ c := by
    intro H c hc0 hc x n
    split_ifs with hn
    · have hxn : x n ∈ A := (natLt_vExitTime_iff_forall_le A x n).1 hn n le_rfl
      exact hc _ (vertexPoint_mem_ball_of_interior hε hη hxn)
    · rw [abs_zero]
      exact hc0
  have hbF : ∀ x, |hF x| ≤ N * M := by
    intro x
    simp only [hFdef]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun n _ => hterm (F ω) M hM0 hFM x n).trans ?_)
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hbG : ∀ x, |hG x| ≤ N * M := by
    intro x
    simp only [hGdef]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun n _ => hterm (G ω) M hM0 hGM x n).trans ?_)
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hdiff : ∀ (x : ℕ → ℤ) (n : ℕ),
      |(if (n : ℕ∞) < vExitTime A x then F ω (vertexPoint ε (S.η ω) (x n)) else 0)
        - (if (n : ℕ∞) < vExitTime A x then G ω (vertexPoint ε (S.η ω) (x n)) else 0)| ≤ δ := by
    intro x n
    split_ifs with hn
    · have hxn : x n ∈ A := (natLt_vExitTime_iff_forall_le A x n).1 hn n le_rfl
      exact hFG _ (vertexPoint_mem_ball_of_interior hε hη hxn)
    · simp only [sub_self, abs_zero]
      exact hδ
  have hpt : ∀ x, |hF x - hG x| ≤ N * δ := by
    intro x
    simp only [hFdef, hGdef]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun n _ => hdiff x n).trans ?_)
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hFv : Measurable fun k : ℤ => F ω (vertexPoint ε (S.η ω) k) := measurable_of_countable _
  have hGv : Measurable fun k : ℤ => G ω (vertexPoint ε (S.η ω) k) := measurable_of_countable _
  have hmF : Measurable hF := by
    simp only [hFdef]
    exact Finset.measurable_sum _ fun n _ =>
      Measurable.ite (measurableSet_natLt_vExitTime A n) (hFv.comp (measurable_pi_apply n)) measurable_const
  have hmG : Measurable hG := by
    simp only [hGdef]
    exact Finset.measurable_sum _ fun n _ =>
      Measurable.ite (measurableSet_natLt_vExitTime A n) (hGv.comp (measurable_pi_apply n)) measurable_const
  have hintF : Integrable hF μ :=
    Integrable.mono' (integrable_const (N * M)) hmF.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hbF x)
  have hintG : Integrable hG μ :=
    Integrable.mono' (integrable_const (N * M)) hmG.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hbG x)
  have hint : |∫ x, hF x ∂μ - ∫ x, hG x ∂μ| ≤ N * δ := by
    rw [← integral_sub hintF hintG]
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => hF x - hG x) (C := N * δ)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hpt x)
    rw [Real.norm_eq_abs] at h
    simpa using h
  rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hm)]
  exact mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hm.le)
