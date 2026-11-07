import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedBoundaryEvent

/-! Common-event boundary estimate for the prepared compactness lemma. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric Tightness

/-- The corrected discrete Hölder estimate yields the prepared boundary
modulus simultaneously for every admissible family. -/
theorem preparedBoundaryVertexModuliStep_of_holder {𝒮 : SpaceFillingSLEModel}
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) : PreparedBoundaryVertexModuliStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS e he
  obtain ⟨ξ, A, β, hξ, _, hA, hβ, _, hHχ⟩ := hH γ hγ hγ2 ρ hρ hρ1
  have hχi : ∀ i : ℕ, (0 : ℝ) < 1 / ((i : ℝ) + 1) := fun i => by positivity
  have hχi1 : ∀ i : ℕ, 1 / ((i : ℝ) + 1) ≤ 1 := fun i =>
    (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
  have hNpos : ∀ N : ℕ, (0 : ℝ) < (N : ℝ) + 1 := fun N => by positivity
  choose ξ' Cc hξ'0 hξ'1 hCc hHij using fun i N : ℕ =>
    hHχ (1 / ((i : ℝ) + 1)) ((N : ℝ) + 1) (hχi i) (hχi1 i) (hNpos N)
  filter_upwards [ae_all_iff.2 fun i : ℕ => ae_all_iff.2 fun N : ℕ =>
      ae_eventually_mem_of_polyHighProb (hHij i N Ω S hS) he,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS,
    hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hHijω hadjω hηω hpω
  intro D hD E u C hEr hE0 hb j hhol
  have hEpos : ∀ n, 0 < E ω n := fun n => by
    obtain ⟨k, hk⟩ := hEr n
    rw [← hk]
    exact he.1 k
  have hlfn : ∀ n, IsLocallyFiniteMult (S.mult (E ω n) ω) := fun n =>
    isLocallyFiniteMult_of_cells hηω.1 hpω (hEpos n) (hadjω _ (hEpos n))
  have hDo := (hD j).2.1
  have hDc := (hD j).2.2
  have hDρ := (hD j).1
  have hDb : Bornology.IsBounded (D j) := isBounded_ball.subset hDρ
  obtain ⟨hsc, hharm, χ, C', hχ, hχ1, hC', hdat⟩ := hhol
  obtain ⟨i, hi⟩ := exists_nat_one_div_lt hχ
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * C')
  have hρ1' : 0 < 1 - ρ := by linarith
  obtain ⟨ε₀, hε₀, hcell⟩ := exists_cell_near_vertexPoint hηω.1 hpω hDb.closure (s := 1 - ρ) hρ1'
  have hclρ : closure (D j) ⊆ closedBall (0 : ℂ) ρ := (closure_mono hDρ).trans closure_ball_subset_closedBall
  have hgood : ∀ᶠ n in atTop, ∀ (D' : Set ℂ) (f : ℤ → ℝ),
      D' ⊆ ball 0 ρ → IsOpen D' → IsConnected D' →
      (∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D', matedLaplacian (S.mult (E ω n) ω) f a = 0) →
      (SimplyConnectedSpace D' ∧ ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D'),
        ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D'),
          |f a - f b| ≤ ((N : ℝ) + 1) * max (E ω n)
            ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ (1 / ((i : ℝ) + 1))) →
      ∀ a ∈ cellVertices (E ω n) (S.η ω) D', ∀ b ∈ cellVertices (E ω n) (S.η ω) D',
        |f a - f b| ≤ max (Cc i N) (A * ⨆ a' : cellVertices (E ω n) (S.η ω) D', |f a'|) *
          max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ' i N := by
    apply eventually_of_range (Q := fun r => ∀ (D' : Set ℂ) (f : ℤ → ℝ),
      D' ⊆ ball 0 ρ → IsOpen D' → IsConnected D' →
      (∀ a ∈ interiorCellVertices r (S.η ω) D', matedLaplacian (S.mult r ω) f a = 0) →
      (SimplyConnectedSpace D' ∧ ∀ a ∈ cellVertices r (S.η ω) (frontier D'),
        ∀ b ∈ cellVertices r (S.η ω) (frontier D'),
          |f a - f b| ≤ ((N : ℝ) + 1) * max r
            ‖vertexPoint r (S.η ω) a - vertexPoint r (S.η ω) b‖ ^ (1 / ((i : ℝ) + 1))) →
      ∀ a ∈ cellVertices r (S.η ω) D', ∀ b ∈ cellVertices r (S.η ω) D',
        |f a - f b| ≤ max (Cc i N) (A * ⨆ a' : cellVertices r (S.η ω) D', |f a'|) *
          max r ‖vertexPoint r (S.η ω) a - vertexPoint r (S.η ω) b‖ ^ ξ' i N) he.1 hEr hE0
    filter_upwards [hHijω i N] with n hn D' f hsub hopen hconn hh
    exact (hn D' f hsub hopen hconn hh).2
  have hHm : ∀ᶠ n in atTop, ∀ a ∈ cellVertices (E ω n) (S.η ω) (D j), ∀ b ∈ cellVertices (E ω n) (S.η ω) (D j),
      E ω n * |u j ω n a - u j ω n b| ≤ max (Cc i N) (A * C j ω) *
        max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ' i N := by
    filter_upwards [hgood, hE0.eventually (gt_mem_nhds (lt_min hε₀ one_pos))] with n hn hεn a ha b hb'
    have hE := hEpos n
    have hεε₀ : E ω n < ε₀ := hεn.trans_le (min_le_left _ _)
    have hε1 : E ω n < 1 := hεn.trans_le (min_le_right _ _)
    have hfharm : ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) (D j),
        matedLaplacian (S.mult (E ω n) ω) (fun b => E ω n * u j ω n b) a = 0 := by
      intro a ha
      show mLaplacian _ (fun b => E ω n * u j ω n b) a = 0
      rw [Tightness.mLaplacian_const_mul (hlfn n), show mLaplacian (S.mult (E ω n) ω) (u j ω n) a = 0 from hharm n a ha, mul_zero]
    have hnear : ∀ c ∈ cellVertices (E ω n) (S.η ω) (frontier (D j)), ‖vertexPoint (E ω n) (S.η ω) c‖ < 1 := by
      intro c hc
      obtain ⟨z, hzc, hzf⟩ := hc
      have hzcl : z ∈ closure (D j) := frontier_subset_closure hzf
      have h1 := hcell (E ω n) hE hεε₀ c ⟨z, hzc, hzcl⟩ z hzc
      have h2 : ‖z‖ ≤ ρ := by simpa using hclρ hzcl
      calc ‖vertexPoint (E ω n) (S.η ω) c‖ = ‖z - (z - vertexPoint (E ω n) (S.η ω) c)‖ := by congr 1; ring
        _ ≤ ‖z‖ + ‖z - vertexPoint (E ω n) (S.η ω) c‖ := norm_sub_le _ _
        _ < 1 := by linarith
    have hfdata : ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier (D j)), ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier (D j)),
        |E ω n * u j ω n a - E ω n * u j ω n b| ≤ ((N : ℝ) + 1) *
          max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ (1 / ((i : ℝ) + 1)) := by
      intro a ha b hb'
      set X := max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ with hX
      have hX0 : 0 < X := lt_max_of_lt_left hE
      have hX2 : X ≤ 2 := by
        refine max_le (by linarith) ?_
        have := norm_sub_le (vertexPoint (E ω n) (S.η ω) a) (vertexPoint (E ω n) (S.η ω) b)
        linarith [hnear a ha, hnear b hb']
      have hd := hdat n a ha b hb'
      have hpow := rpow_le_two_mul_rpow hX0 hX2 (hχi i).le hi.le hχ1
      have hXi : 0 ≤ X ^ (1 / ((i : ℝ) + 1)) := Real.rpow_nonneg hX0.le _
      rw [← mul_sub, abs_mul, abs_of_pos hE]
      calc E ω n * |u j ω n a - u j ω n b| ≤ E ω n * (C' / E ω n * X ^ χ) := mul_le_mul_of_nonneg_left hd hE.le
        _ = C' * X ^ χ * (E ω n * (E ω n)⁻¹) := by rw [div_eq_mul_inv]; ring
        _ = C' * X ^ χ := by rw [mul_inv_cancel₀ hE.ne', mul_one]
        _ ≤ C' * (2 * X ^ (1 / ((i : ℝ) + 1))) := mul_le_mul_of_nonneg_left hpow hC'.le
        _ = (2 * C') * X ^ (1 / ((i : ℝ) + 1)) := by ring
        _ ≤ ((N : ℝ) + 1) * X ^ (1 / ((i : ℝ) + 1)) := mul_le_mul_of_nonneg_right (by linarith) hXi
    have hne : Nonempty (cellVertices (E ω n) (S.η ω) (D j)) := ⟨⟨a, ha⟩⟩
    have hsup : (⨆ a' : cellVertices (E ω n) (S.η ω) (D j), |E ω n * u j ω n a'|) ≤ C j ω := by
      refine ciSup_le fun c => ?_
      rw [abs_mul, abs_of_pos hE]
      calc E ω n * |u j ω n c| ≤ E ω n * (C j ω / E ω n) := mul_le_mul_of_nonneg_left ((hb j).2.2 n c c.2) hE.le
        _ = C j ω * (E ω n * (E ω n)⁻¹) := by rw [div_eq_mul_inv]; ring
        _ = C j ω := by rw [mul_inv_cancel₀ hE.ne', mul_one]
    have hmain := hn (D j) (fun b => E ω n * u j ω n b) hDρ hDo hDc hfharm ⟨hsc, hfdata⟩ a ha b hb'
    have hmaxpow : 0 ≤ max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ' i N :=
      Real.rpow_nonneg (le_max_of_le_left hE.le) _
    have hle : max (Cc i N) (A * ⨆ a' : cellVertices (E ω n) (S.η ω) (D j), |E ω n * u j ω n a'|) ≤
        max (Cc i N) (A * C j ω) := max_le_max le_rfl (mul_le_mul_of_nonneg_left hsup hA.le)
    calc E ω n * |u j ω n a - u j ω n b| = |E ω n * u j ω n a - E ω n * u j ω n b| := by
          rw [← mul_sub, abs_mul, abs_of_pos hE]
      _ ≤ _ := hmain
      _ ≤ max (Cc i N) (A * C j ω) *
          max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ' i N :=
        mul_le_mul_of_nonneg_right hle hmaxpow
  have hdata' : ∀ᶠ n in atTop, ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier (D j)),
      ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier (D j)), |u j ω n a - u j ω n b| ≤
        C' / E ω n * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ χ :=
    Filter.Eventually.of_forall hdat
  exact closure_vertexEquicontinuous hEpos hE0 hηω.1 hpω hηω.2.2.1 hDo hDb hχ hC'.le
    (le_max_of_le_left (hCc i N).le) (hξ'0 i N) hdata' hHm

/-- Corrected Lemma 3.1 follows from the random-walk normalization, the exit
estimates, and the corrected discrete Hölder estimate. -/
theorem discretePotentialTightnessPrepared_of_inputs {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮) :
    DiscretePotentialTightnessPreparedStmt 𝒮 :=
  discretePotentialTightnessPrepared_of_vertexModuli hm
    (preparedTightnessVertexModuliStep_of_boundary h217 h218 hH
      (preparedBoundaryVertexModuliStep_of_holder hH))

end MatedCRT

#print axioms MatedCRT.discretePotentialTightnessPrepared_of_inputs
