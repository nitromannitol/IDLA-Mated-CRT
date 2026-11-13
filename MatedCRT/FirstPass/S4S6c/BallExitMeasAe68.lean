import MatedCRT.FirstPass.S4S6c.BallExitMeas68

/-!
# Finite-domain exit moments under almost-sure exit bounds

`hmom_pair_ae` is `FiniteExitMomentHoneMain68.hmom_pair_of_finiteDomain` at one index `k`, with the pointwise
bounds `hTdom` (exit domination) and `hRbd` (radius bound) replaced by their almost-sure form under `srwLaw m a`
on the whole walk space. The proof is the same; the bounds enter only through `filter_upwards`
(`ae_center_mem_ae`, the a.s. form of `ae_center_mem`), because `integrable_postTime_pow` needs the domination
almost surely on all walks with `T k w < ⊤`. A bound restricted to `prefixSet` would not give that integrability.
-/

namespace MatedCRT
namespace BallExitMeasAe68

open MeasureTheory Set Filter FiniteExitMomentHone68 FiniteExitMomentHoneMain68
open Lemma68WalkBridge Lemma68Window Function
open scoped ENNReal

/-- The a.s. form of `FiniteExitMomentHoneMain68.ae_center_mem`: the exit domination holds almost surely. -/
lemma ae_center_mem_ae {m : ℤ → ℤ → ℕ} {D : Set ℤ} (a : ℤ) {τ : (ℕ → ℤ) → ℕ∞}
    (hτ : ∀ᵐ w ∂srwLaw m a, τ w < ⊤ → τ w ≤ vExitTime D w) :
    ∀ᵐ w ∂srwLaw m a, τ w < ⊤ → w (τ w).toNat ∈ D ∪ vBoundary m D ∪ {a} := by
  filter_upwards [srwLaw_ae_start m a, MatedCRT.FirstPass36.H2.ae_step_adjacent m a, hτ] with w hw0 hadj hτw hT
  have ht : ((τ w).toNat : ℕ∞) = τ w := ENat.natCast_toNat hT.ne
  rcases Nat.eq_zero_or_pos (τ w).toNat with h0 | hpos
  · rw [h0]
    exact Set.mem_union_right _ (Set.mem_singleton_iff.2 hw0)
  · rcases lt_or_eq_of_le (hτw hT) with hlt | heq
    · rw [← ht] at hlt
      exact Set.mem_union_left _ (Set.mem_union_left _ (natCast_lt_vExitTime_iff.1 hlt _ le_rfl))
    · have hspec : vExitTime D w = ((τ w).toNat : ℕ∞) := by
        rw [ht]
        exact heq.symm
      obtain ⟨hout, hin⟩ := (MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec D w _).1 hspec
      obtain ⟨j, hj⟩ : ∃ j, (τ w).toNat = j + 1 := ⟨(τ w).toNat - 1, by omega⟩
      rw [hj] at hout hin ⊢
      rcases hadj j with h | h
      · exact absurd (by rw [h]; exact hin j (Nat.lt_succ_self j)) hout
      · have hB : w (j + 1) ∈ vBoundary m D := by
          simp only [vBoundary, mem_ofPred_eq]
          exact ⟨hout, w j, hin j (Nat.lt_succ_self j), h⟩
        exact Set.mem_union_left _ (Set.mem_union_right _ hB)


set_option linter.unusedVariables false in
/-- **Finite-domain exit moments under almost-sure bounds (one index `k`).** Same conclusion as
`FiniteExitMomentHoneMain68.hmom_pair_of_finiteDomain`; the bounds `hTdom`, `hRbd` hold almost surely under
`srwLaw m a` (on all walks with `T k w < ⊤`). -/
theorem hmom_pair_ae {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hp : Filter.Tendsto η (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (hε : 0 < ε) (a : ℤ)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (k : ℕ)
    (hTdom : ∃ D : Set ℤ, D.Finite ∧ ∀ᵐ w ∂srwLaw m a, T k w < ⊤ → T k w ≤ vExitTime D w)
    (hRbd : ∃ s : ℝ, ∀ᵐ w ∂srwLaw m a, T k w < ⊤ → R k w ≤ s) :
    Integrable ({w : ℕ → ℤ | T k w < ⊤}.indicator (fun w =>
        ((ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ)))
      (srwLaw m a) ∧
    Integrable ({w : ℕ → ℤ | T k w < ⊤}.indicator (fun w =>
        ((ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2))
      (srwLaw m a) := by
  have hmeasBall : Measurable fun w : ℕ → ℤ =>
      ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) :=
    BallExitMeas68.measurable_ballExitSigma_walkParam ε η hη hε (hT k) (hR k)
  obtain ⟨D, hD, hTD⟩ := hTdom
  obtain ⟨s, hs⟩ := hRbd
  have hBfin : (vBoundary m D).Finite := (hD.biUnion fun b _ => hlf b).subset fun c hc => by
    obtain ⟨_, b, hb, hbc⟩ := hc
    exact Set.mem_biUnion hb hbc
  have hVfin : (D ∪ vBoundary m D ∪ {a}).Finite := (hD.union hBfin).union (Set.finite_singleton a)
  set G : Set ℤ := ⋃ v ∈ D ∪ vBoundary m D ∪ {a},
    cellVertices ε η (Metric.ball (vertexPoint ε η v) (s / 4)) with hGdef
  have hGfin : G.Finite := hVfin.biUnion fun v _ => MatedCRT.S5c.cellVertices_ball_finite hη hp hε _ _
  have hcont : ∀ᵐ w ∂srwLaw m a, T k w < ⊤ →
      interiorCellVertices ε η (Metric.ball (vertexPoint ε η (w (T k w).toNat)) (R k w / 4)) ⊆ G := by
    filter_upwards [ae_center_mem_ae (m := m) a hTD, hs] with w hw hsw hT'
    intro y hy
    have hc := hw hT'
    have hmono : ∀ z, z ∈ cellVertices ε η (Metric.ball (vertexPoint ε η (w (T k w).toNat)) (R k w / 4)) →
        z ∈ cellVertices ε η (Metric.ball (vertexPoint ε η (w (T k w).toNat)) (s / 4)) := by
      intro z hz
      exact hz.mono (Set.inter_subset_inter_right _
        (Metric.ball_subset_ball (by linarith [hsw hT'])))
    exact Set.mem_biUnion hc (hmono y hy.1)
  obtain ⟨Nf, hfun⟩ : ∃ Nf : (ℕ → ℤ) → ℕ,
      Nf = fun w => ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) :=
    ⟨_, rfl⟩
  have hZ : ∀ᵐ w ∂srwLaw m a, T k w < ⊤ →
      ((Nf w : ℕ) : ℕ∞) ≤ vExitTime G (postTimePath (fun n w => w n) (T k) w) := by
    filter_upwards [hcont] with w hw hT'
    rw [hfun]
    exact (ENat.natCast_toNat_le_self _).trans (vExitTime_mono_set (hw hT') _)
  have hZm : Measurable fun w : ℕ → ℤ => (((Nf w : ℕ) : ℕ∞)).toNat := by
    simp only [ENat.toNat_natCast, hfun]
    exact hmeasBall
  obtain ⟨N, hN⟩ := FiniteExitMoment68.exists_nat_bound_expectedExitTime hlf hcons hGfin
  obtain ⟨L, hL0, hL⟩ := FiniteExitMoment68.exists_block_le_half hN
  have hTw := isWalkRandomTime_of_isStoppingTime (hT k)
  have h2 := integrable_postTime_pow (Z := fun w : ℕ → ℤ => ((Nf w : ℕ) : ℕ∞)) hTw hL0 hL hZm hZ 2
    (by norm_num) (FiniteExitMoment68.tsum_block_sq_ne_top L)
  have hfin1 : ∑' j : ℕ, (((j + 1) * L : ℕ) : ℝ≥0∞) ^ 1 * (1 / 2 : ℝ≥0∞) ^ j ≠ ⊤ :=
    ne_top_of_le_ne_top (FiniteExitMoment68.tsum_block_sq_ne_top L)
      (ENNReal.tsum_le_tsum fun j => mul_le_mul_of_nonneg_right
        (by
          rw [pow_one, pow_two]
          exact le_mul_of_one_le_right (by exact zero_le)
            (Nat.one_le_cast.2 (Nat.mul_pos (Nat.succ_pos j) hL0)))
        (by exact zero_le))
  have h1 := integrable_postTime_pow (Z := fun w : ℕ → ℤ => ((Nf w : ℕ) : ℕ∞)) hTw hL0 hL hZm hZ 1
    (by norm_num) hfin1
  simp only [ENat.toNat_natCast, hfun, pow_one] at h1
  simp only [ENat.toNat_natCast, hfun] at h2
  exact ⟨h1, h2⟩


set_option linter.unusedVariables false in
/-- **Finite-domain exit moments under a finite stopped-range localization (one index `k`; item 4).**
Same conclusion as `hmom_pair_ae`, with the finite stopped range `hstopFin` in place of the exit domination `hTdom`: the
stopped vertex `w (T k w).toNat` lies a.s. in a finite set `F`. Only `hRbd` (the a.s. radius bound) is used besides
`hstopFin`.
The cells of the test balls are finite on `F` (`MatedCRT.S5c.cellVertices_ball_finite`), so `G` is finite. -/
theorem hmom_pair_stopFin_ae {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hp : Filter.Tendsto η (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (hε : 0 < ε) (a : ℤ)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (k : ℕ)
    (hstopFin : ∃ F : Set ℤ, F.Finite ∧ ∀ᵐ w ∂srwLaw m a, T k w < ⊤ → w (T k w).toNat ∈ F)
    (hRbd : ∃ s : ℝ, ∀ᵐ w ∂srwLaw m a, T k w < ⊤ → R k w ≤ s) :
    Integrable ({w : ℕ → ℤ | T k w < ⊤}.indicator (fun w =>
        ((ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ)))
      (srwLaw m a) ∧
    Integrable ({w : ℕ → ℤ | T k w < ⊤}.indicator (fun w =>
        ((ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2))
      (srwLaw m a) := by
  have hmeasBall : Measurable fun w : ℕ → ℤ =>
      ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) :=
    BallExitMeas68.measurable_ballExitSigma_walkParam ε η hη hε (hT k) (hR k)
  obtain ⟨F, hF, hstop⟩ := hstopFin
  obtain ⟨s, hs⟩ := hRbd
  set G : Set ℤ := ⋃ v ∈ F,
    cellVertices ε η (Metric.ball (vertexPoint ε η v) (s / 4)) with hGdef
  have hGfin : G.Finite := hF.biUnion fun v _ => MatedCRT.S5c.cellVertices_ball_finite hη hp hε _ _
  have hcont : ∀ᵐ w ∂srwLaw m a, T k w < ⊤ →
      interiorCellVertices ε η (Metric.ball (vertexPoint ε η (w (T k w).toNat)) (R k w / 4)) ⊆ G := by
    filter_upwards [hstop, hs] with w hw hsw hT'
    intro y hy
    have hc := hw hT'
    have hmono : ∀ z, z ∈ cellVertices ε η (Metric.ball (vertexPoint ε η (w (T k w).toNat)) (R k w / 4)) →
        z ∈ cellVertices ε η (Metric.ball (vertexPoint ε η (w (T k w).toNat)) (s / 4)) := by
      intro z hz
      exact hz.mono (Set.inter_subset_inter_right _
        (Metric.ball_subset_ball (by linarith [hsw hT'])))
    exact Set.mem_biUnion hc (hmono y hy.1)
  obtain ⟨Nf, hfun⟩ : ∃ Nf : (ℕ → ℤ) → ℕ,
      Nf = fun w => ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) :=
    ⟨_, rfl⟩
  have hZ : ∀ᵐ w ∂srwLaw m a, T k w < ⊤ →
      ((Nf w : ℕ) : ℕ∞) ≤ vExitTime G (postTimePath (fun n w => w n) (T k) w) := by
    filter_upwards [hcont] with w hw hT'
    rw [hfun]
    exact (ENat.natCast_toNat_le_self _).trans (vExitTime_mono_set (hw hT') _)
  have hZm : Measurable fun w : ℕ → ℤ => (((Nf w : ℕ) : ℕ∞)).toNat := by
    simp only [ENat.toNat_natCast, hfun]
    exact hmeasBall
  obtain ⟨N, hN⟩ := FiniteExitMoment68.exists_nat_bound_expectedExitTime hlf hcons hGfin
  obtain ⟨L, hL0, hL⟩ := FiniteExitMoment68.exists_block_le_half hN
  have hTw := isWalkRandomTime_of_isStoppingTime (hT k)
  have h2 := integrable_postTime_pow (Z := fun w : ℕ → ℤ => ((Nf w : ℕ) : ℕ∞)) hTw hL0 hL hZm hZ 2
    (by norm_num) (FiniteExitMoment68.tsum_block_sq_ne_top L)
  have hfin1 : ∑' j : ℕ, (((j + 1) * L : ℕ) : ℝ≥0∞) ^ 1 * (1 / 2 : ℝ≥0∞) ^ j ≠ ⊤ :=
    ne_top_of_le_ne_top (FiniteExitMoment68.tsum_block_sq_ne_top L)
      (ENNReal.tsum_le_tsum fun j => mul_le_mul_of_nonneg_right
        (by
          rw [pow_one, pow_two]
          exact le_mul_of_one_le_right (by exact zero_le)
            (Nat.one_le_cast.2 (Nat.mul_pos (Nat.succ_pos j) hL0)))
        (by exact zero_le))
  have h1 := integrable_postTime_pow (Z := fun w : ℕ → ℤ => ((Nf w : ℕ) : ℕ∞)) hTw hL0 hL hZm hZ 1
    (by norm_num) hfin1
  simp only [ENat.toNat_natCast, hfun, pow_one] at h1
  simp only [ENat.toNat_natCast, hfun] at h2
  exact ⟨h1, h2⟩


end BallExitMeasAe68
end MatedCRT

#print axioms MatedCRT.BallExitMeasAe68.ae_center_mem_ae
#print axioms MatedCRT.BallExitMeasAe68.hmom_pair_ae
#print axioms MatedCRT.BallExitMeasAe68.hmom_pair_stopFin_ae
