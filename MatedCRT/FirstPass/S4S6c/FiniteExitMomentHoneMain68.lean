import MatedCRT.FirstPass.S4S6c.FiniteExitMomentHone68
import MatedCRT.FirstPass.S4S6c.HoneWalk
import MatedCRT.FirstPass.S6r.OneTest.Concrete
import MatedCRT.FirstPass.S3i.StrongMarkov
import MatedCRT.FirstPass.S5c.GreenUpper

/-!
# Hone binders on finite test domains

Serves Lemma 6.8 (`lemma:constant-order-lower-bound-div`) through its replacement proof [C26] (`eq:c26-first-moment`,
`eq:c26-second-moment`): the binders `hmom1`, `hmom2` of the walk-centred exit estimates are discharged on finite test
domains. Main declarations: `hmom_pair_of_finiteDomain` (finite first and second moments of the test counts
`1_{T_k<∞} ballExitSigma` under `srwLaw m a`, when each `T_k` is dominated by the exit time of a finite vertex set) and
`ae_center_mem` (the centre vertex of a dominated random time lies almost surely in `D ∪ ∂D ∪ {a}`).
-/

namespace MatedCRT
namespace FiniteExitMomentHoneMain68

open MeasureTheory Set Filter FiniteExitMomentHone68
open Lemma68WalkBridge Lemma68Window Function
open scoped ENNReal

/-- The centre vertex `w_{T}` of a random time dominated by the exit time of `D` lies almost surely in
`D ∪ ∂D ∪ {a}` (`∂D = vBoundary m D`): before the exit it is in `D`; at the exit it is adjacent to `D`. -/
lemma ae_center_mem {m : ℤ → ℤ → ℕ} {D : Set ℤ} (a : ℤ) {τ : (ℕ → ℤ) → ℕ∞}
    (hτ : ∀ w, τ w < ⊤ → τ w ≤ vExitTime D w) :
    ∀ᵐ w ∂srwLaw m a, τ w < ⊤ → w (τ w).toNat ∈ D ∪ vBoundary m D ∪ {a} := by
  filter_upwards [srwLaw_ae_start m a, MatedCRT.FirstPass36.H2.ae_step_adjacent m a] with w hw0 hadj hT
  have ht : ((τ w).toNat : ℕ∞) = τ w := ENat.natCast_toNat hT.ne
  rcases Nat.eq_zero_or_pos (τ w).toNat with h0 | hpos
  · rw [h0]
    exact Set.mem_union_right _ (Set.mem_singleton_iff.2 hw0)
  · rcases lt_or_eq_of_le (hτ w hT) with hlt | heq
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

-- `hR` is part of the hone interface; it is needed for the measurability of the test count, which is
-- currently the named hypothesis `hmeasBall`, so the binder is kept unused here.
set_option linter.unusedVariables false in
/-- **Hone binders `hmom1`, `hmom2` on finite test domains.** If each `T k`
is dominated by the exit time of a finite vertex set `D_k` (`T k ≤ τ_{D_k}` on `{T k < ⊤}`) and the radii
`R k` are bounded on `{T k < ⊤}`, then the test counts `1_{T_k<∞} ballExitSigma` have finite first and second
moments under `srwLaw m a`. The test balls live in the finite vertex set of the cells meeting the balls of
radius `s/4` around the finitely many candidate centres (properness of `η`). -/
theorem hmom_pair_of_finiteDomain {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hp : Filter.Tendsto η (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (hε : 0 < ε) (a : ℤ)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hTdom : ∀ k, ∃ D : Set ℤ, D.Finite ∧ ∀ w, T k w < ⊤ → T k w ≤ vExitTime D w)
    (hRbd : ∀ k, ∃ s : ℝ, ∀ w, T k w < ⊤ → R k w ≤ s)
    (hmeasBall : ∀ k, Measurable fun w : ℕ → ℤ =>
      ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w))
    (k : ℕ) :
    Integrable ({w : ℕ → ℤ | T k w < ⊤}.indicator (fun w =>
        ((ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ)))
      (srwLaw m a) ∧
    Integrable ({w : ℕ → ℤ | T k w < ⊤}.indicator (fun w =>
        ((ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2))
      (srwLaw m a) := by
  obtain ⟨D, hD, hTD⟩ := hTdom k
  obtain ⟨s, hs⟩ := hRbd k
  have hBfin : (vBoundary m D).Finite := (hD.biUnion fun b _ => hlf b).subset fun c hc => by
    obtain ⟨_, b, hb, hbc⟩ := hc
    exact Set.mem_biUnion hb hbc
  have hVfin : (D ∪ vBoundary m D ∪ {a}).Finite := (hD.union hBfin).union (Set.finite_singleton a)
  set G : Set ℤ := ⋃ v ∈ D ∪ vBoundary m D ∪ {a},
    cellVertices ε η (Metric.ball (vertexPoint ε η v) (s / 4)) with hGdef
  have hGfin : G.Finite := hVfin.biUnion fun v _ => MatedCRT.S5c.cellVertices_ball_finite hη hp hε _ _
  have hcont : ∀ᵐ w ∂srwLaw m a, T k w < ⊤ →
      interiorCellVertices ε η (Metric.ball (vertexPoint ε η (w (T k w).toNat)) (R k w / 4)) ⊆ G := by
    filter_upwards [ae_center_mem (m := m) a (fun w hw => hTD w hw)] with w hw hT'
    intro y hy
    have hc := hw hT'
    have hmono : ∀ z, z ∈ cellVertices ε η (Metric.ball (vertexPoint ε η (w (T k w).toNat)) (R k w / 4)) →
        z ∈ cellVertices ε η (Metric.ball (vertexPoint ε η (w (T k w).toNat)) (s / 4)) := by
      intro z hz
      exact hz.mono (Set.inter_subset_inter_right _
        (Metric.ball_subset_ball (by linarith [hs w hT'])))
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
    exact hmeasBall k
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

end FiniteExitMomentHoneMain68
end MatedCRT
