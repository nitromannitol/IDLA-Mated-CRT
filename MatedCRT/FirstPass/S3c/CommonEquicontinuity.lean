import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Final

/-!
# Lemma 3.1 (corrected, [C11]): one almost-sure event for the equicontinuity step

`tightness_equicontinuity_common` is `tightnessEquicontinuityStep_of_steps`
(MatedCRT/Proofs/Sec3/DiscretePotentialTightness/Equicontinuity.lean) with the almost-sure event moved in front of the
domain and of the data. The events that proof intersects are `∀ᵐ ω, ∀ᶠ j, ω ∈ G (e j)` (Borel-Cantelli along the
polynomially summable scales `e`, `ae_eventually_mem_of_polyHighProb`), `AdjacentCellsMeetAeStep` and the environment
events `isAreaParametrized`, `ae_tendsto_cocompact`. None of them mentions `D`, `E`, `u` or `C`. The random scales
`E ω n ∈ range e` with `E ω n → 0` transfer the Borel-Cantelli event to `E` pointwise (`Tightness.eventually_mem_of_range`).
So one event `Ω₀` serves every admissible domain and data, as [C11] requires: "one almost-sure event, inherited by all
measurable random subsequences and countable families".
-/

open MatedCRT.Tightness
open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.S3c

/-- The witness set of an almost-sure predicate: a single event `Ω₀` with `∀ᵐ ω, ω ∈ Ω₀` on which `Q` holds. -/
theorem exists_common_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Q : Ω → Prop}
    (h : ∀ᵐ ω ∂P, Q ω) :
    ∃ Ω₀ : Set Ω, (∀ᵐ ω ∂P, ω ∈ Ω₀) ∧ ∀ ω ∈ Ω₀, Q ω :=
  ⟨{ω | Q ω}, h, fun _ hω => hω⟩

/-- Borel-Cantelli along the deterministic scales `e`, for every random sequence with values in `range e` tending to
zero: one almost-sure event on which every such `E` eventually lies in `G`. The set `G` is abstract here, so no
higher-order unification against a `setOf` is needed when the lemma is applied. -/
theorem ae_forall_eventually_mem_range {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : ℝ → Set Ω}
    (hG : PolyHighProb P G) {e : ℕ → ℝ} (he : IsPolySummableScales e) :
    ∀ᵐ ω ∂P, ∀ E : ℕ → ℝ, (∀ n, E n ∈ range e) → Tendsto E atTop (𝓝 0) → ∀ᶠ n in atTop, ω ∈ G (E n) := by
  filter_upwards [ae_eventually_mem_of_polyHighProb hG he] with ω hω
  intro E hEe hEt
  exact eventually_of_range (Q := fun r => ω ∈ G r) he.1 hEe hEt hω

/-- **Lemma 3.1, equicontinuity with a common event** (C11). For a deterministic polynomially summable scale sequence
`e` there is one probability-one event `Ω₀`, chosen before the domain and the data, such that for every connected open
domain `D ⊆ B_ρ`, every `σ(h,η)`-measurable `E` with values in `range e` tending to zero and every `u`, `C` satisfying the
hypotheses of Lemma 3.1, the asymptotic vertex equicontinuity of `u^ε` holds at every `ω ∈ Ω₀`: on compacts of `D`, and
on `cl(D)` under the "moreover" hypotheses. -/
theorem tightness_equicontinuity_common {𝒮 : SpaceFillingSLEModel} (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ e : ℕ → ℝ, IsPolySummableScales e → ∃ Ω₀ : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ Ω₀) ∧
    ∀ D : Set ℂ, D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
    ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ), IsTightnessData S D e E u C →
    ∀ ω ∈ Ω₀, (∀ K : Set ℂ, IsCompact K → K ⊆ D → IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u ω) K) ∧
      (HasHolderBoundaryData S D E u ω → IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u ω) (closure D)) := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS e he
  obtain ⟨α, hα, h18α⟩ := h218 γ hγ hγ2
  obtain ⟨C₁, hC₁, h18C⟩ := h18α ρ hρ hρ1
  obtain ⟨q, hq, h17q⟩ := h217 γ hγ hγ2
  have h17 := (h17q ρ hρ hρ1 Ω S.P S.hC S.hcirc S.μ hS.isConeField).2
  obtain ⟨ξ, A, β, hξ, -, hA, hβ, -, hHχ⟩ := hH γ hγ hγ2 ρ hρ hρ1
  obtain ⟨_, _, _, _, _, hH1⟩ := hHχ 1 1 one_pos le_rfl one_pos
  have hχi : ∀ i : ℕ, (0 : ℝ) < 1 / ((i : ℝ) + 1) := fun i => by positivity
  have hχi1 : ∀ i : ℕ, 1 / ((i : ℝ) + 1) ≤ 1 := fun i =>
    (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
  have hNpos : ∀ N : ℕ, (0 : ℝ) < (N : ℝ) + 1 := fun N => by positivity
  choose ξ' Cc hξ'0 hξ'1 hCc hHij using fun i N : ℕ =>
    hHχ (1 / ((i : ℝ) + 1)) ((N : ℝ) + 1) (hχi i) (hχi1 i) (hNpos N)
  -- The common event: every Borel-Cantelli event is a statement about `e` alone, and the environment events are fixed.
  have hEv := (ae_forall_eventually_mem_range (h18C Ω S hS) he).and
    ((ae_eventually_mem_of_polyHighProb h17 he).and
    ((ae_forall_eventually_mem_range (hH1 Ω S hS) he).and
    ((ae_all_iff.2 fun i : ℕ => ae_all_iff.2 fun N : ℕ =>
        ae_forall_eventually_mem_range (hHij i N Ω S hS) he).and
    ((hadj γ hγ hγ2 Ω S hS).and (hS.isAreaParametrized.and hS.ae_tendsto_cocompact)))))
  obtain ⟨Ω₀, hΩ₀, hQ⟩ := exists_common_of_ae hEv
  refine ⟨Ω₀, hΩ₀, fun D hDρ hDo hDc E u C hdata ω hω => ?_⟩
  obtain ⟨-, hEe, hEt, -, -, hCp, hlap, hbd⟩ := hdata
  obtain ⟨h18ω₀, h17ω, hHω₀, hHijω₀, hadjω, hηω, hpω⟩ := hQ ω hω
  have h18ω := h18ω₀ (E ω) (hEe ω) (hEt ω)
  have hHω := hHω₀ (E ω) (hEe ω) (hEt ω)
  have hHijω := fun i N : ℕ => hHijω₀ i N (E ω) (hEe ω) (hEt ω)
  have hEpos : ∀ ω n, 0 < E ω n := fun ω n => by
    obtain ⟨j, hj⟩ := hEe ω n
    rw [← hj]
    exact he.1 j
  have hlfn : ∀ n, IsLocallyFiniteMult (S.mult (E ω n) ω) := fun n =>
    isLocallyFiniteMult_of_cells hηω.1 hpω (hEpos ω n) (hadjω _ (hEpos ω n))
  have hDb : Bornology.IsBounded D := isBounded_ball.subset hDρ
  refine ⟨fun K hK hKD => ?_, fun hhol => ?_⟩
  · -- the interior part
    have hM : ∀ R₀ : ℝ, 0 < R₀ → ∃ R : ℝ, 0 < R ∧ R < R₀ ∧
        ∀ y ∈ ball (0 : ℂ) ρ, largestExitTimeRV (S.μ ω) (ball y R) ≤ ENNReal.ofReal (R ^ q) := by
      intro R₀ hR₀
      obtain ⟨j, hj1, hj2⟩ := (h17ω.and (he.tendsto_zero.eventually (gt_mem_nhds hR₀))).exists
      exact ⟨e j, he.1 j, hj2, hj1⟩
    have hHball : ∀ᶠ n in atTop, ∀ (x : ℂ) (r : ℝ), 0 < r → ball x r ⊆ ball 0 ρ → ∀ f : ℤ → ℝ,
        (∀ a ∈ interiorCellVertices (E ω n) (S.η ω) (ball x r), matedLaplacian (S.mult (E ω n) ω) f a = 0) →
        ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) (ball x r), ∀ b ∈ cellVertices (E ω n) (S.η ω) (ball x r),
          |f a - f b| * infDist (vertexPoint (E ω n) (S.η ω) a) (frontier (ball x r)) ^ ξ ≤
            A * (⨆ a' : cellVertices (E ω n) (S.η ω) (ball x r), |f a'|) *
              max (E ω n ^ β) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ := by
      filter_upwards [hHω] with n hn x r hr hxr f hf
      exact (hn (ball x r) f hxr isOpen_ball ((convex_ball x r).isConnected (nonempty_ball.2 hr)) hf).1
    have hQ' : ∀ᶠ n in atTop, ∀ D' : Set ℂ, D' ⊆ ball 0 ρ → ∀ a ∈ cellVertices (E ω n) (S.η ω) D',
        expectedExitTime (S.mult (E ω n) ω) (interiorCellVertices (E ω n) (S.η ω) D') a ≤
          ENNReal.ofReal (C₁ * (E ω n)⁻¹) * largestExitTimeRV (S.μ ω) (thickening (E ω n ^ α) D') := by
      filter_upwards [h18ω] with n hn D' hD' a ha
      exact (hn.2 D' hD' a ha).2
    exact interior_vertexEquicontinuous (m := fun n => S.mult (E ω n) ω) (hEpos ω) (hEt ω) hηω.1 hpω
      (fun n => hadjω _ (hEpos ω n)) (fun n k => S.mult_succ_ne_zero (hEpos ω n).le ω k) hDo hDρ hK hKD
      (hCp ω).le (hlap ω) (hbd ω) hξ hA.le hβ hα hC₁.le hq hHball hQ' hM
  · -- the "moreover" part
    obtain ⟨hsc, hharm, χ, C', hχ, hχ1, hC', hdat⟩ := hhol
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hχ
    obtain ⟨N, hN⟩ := exists_nat_ge (2 * C')
    have hρ1' : 0 < 1 - ρ := by linarith
    obtain ⟨ε₀, hε₀, hcell⟩ := exists_cell_near_vertexPoint hηω.1 hpω hDb.closure (s := 1 - ρ) hρ1'
    have hclρ : closure D ⊆ closedBall (0 : ℂ) ρ := (closure_mono hDρ).trans closure_ball_subset_closedBall
    have hHm : ∀ᶠ n in atTop, ∀ a ∈ cellVertices (E ω n) (S.η ω) D, ∀ b ∈ cellVertices (E ω n) (S.η ω) D,
        E ω n * |u ω n a - u ω n b| ≤ max (Cc i N) (A * C ω) *
          max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ' i N := by
      filter_upwards [hHijω i N, (hEt ω).eventually (gt_mem_nhds (lt_min hε₀ one_pos))] with n hn hεn a ha b hb
      have hE := hEpos ω n
      have hεε₀ : E ω n < ε₀ := hεn.trans_le (min_le_left _ _)
      have hε1 : E ω n < 1 := hεn.trans_le (min_le_right _ _)
      have hfharm : ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
          matedLaplacian (S.mult (E ω n) ω) (fun b => E ω n * u ω n b) a = 0 := by
        intro a ha
        show mLaplacian _ (fun b => E ω n * u ω n b) a = 0
        rw [mLaplacian_const_mul (hlfn n), show mLaplacian (S.mult (E ω n) ω) (u ω n) a = 0 from hharm n a ha,
          mul_zero]
      have hnear : ∀ c ∈ cellVertices (E ω n) (S.η ω) (frontier D), ‖vertexPoint (E ω n) (S.η ω) c‖ < 1 := by
        intro c hc
        obtain ⟨z, hzc, hzf⟩ := hc
        have hzcl : z ∈ closure D := frontier_subset_closure hzf
        have h1 := hcell (E ω n) hE hεε₀ c ⟨z, hzc, hzcl⟩ z hzc
        have h2 : ‖z‖ ≤ ρ := by simpa using hclρ hzcl
        calc ‖vertexPoint (E ω n) (S.η ω) c‖ = ‖z - (z - vertexPoint (E ω n) (S.η ω) c)‖ := by congr 1; ring
          _ ≤ ‖z‖ + ‖z - vertexPoint (E ω n) (S.η ω) c‖ := norm_sub_le _ _
          _ < 1 := by linarith
      have hfdata : ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D), ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D),
          |E ω n * u ω n a - E ω n * u ω n b| ≤ ((N : ℝ) + 1) *
            max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ (1 / ((i : ℝ) + 1)) := by
        intro a ha b hb
        set X := max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ with hX
        have hX0 : 0 < X := lt_max_of_lt_left hE
        have hX2 : X ≤ 2 := by
          refine max_le (by linarith) ?_
          have := norm_sub_le (vertexPoint (E ω n) (S.η ω) a) (vertexPoint (E ω n) (S.η ω) b)
          linarith [hnear a ha, hnear b hb]
        have hd := hdat n hε1 a ha b hb
        have hpow := rpow_le_two_mul_rpow hX0 hX2 (hχi i).le hi.le hχ1
        have hXi : 0 ≤ X ^ (1 / ((i : ℝ) + 1)) := Real.rpow_nonneg hX0.le _
        rw [← mul_sub, abs_mul, abs_of_pos hE]
        calc E ω n * |u ω n a - u ω n b| ≤ E ω n * (C' / E ω n * X ^ χ) := mul_le_mul_of_nonneg_left hd hE.le
          _ = C' * X ^ χ * (E ω n * (E ω n)⁻¹) := by rw [div_eq_mul_inv]; ring
          _ = C' * X ^ χ := by rw [mul_inv_cancel₀ hE.ne', mul_one]
          _ ≤ C' * (2 * X ^ (1 / ((i : ℝ) + 1))) := mul_le_mul_of_nonneg_left hpow hC'.le
          _ = (2 * C') * X ^ (1 / ((i : ℝ) + 1)) := by ring
          _ ≤ ((N : ℝ) + 1) * X ^ (1 / ((i : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) hXi
      have hne : Nonempty (cellVertices (E ω n) (S.η ω) D) := ⟨⟨a, ha⟩⟩
      have hsup : (⨆ a' : cellVertices (E ω n) (S.η ω) D, |E ω n * u ω n a'|) ≤ C ω := by
        refine ciSup_le fun c => ?_
        rw [abs_mul, abs_of_pos hE]
        calc E ω n * |u ω n c| ≤ E ω n * (C ω / E ω n) := mul_le_mul_of_nonneg_left (hbd ω n c c.2) hE.le
          _ = C ω * (E ω n * (E ω n)⁻¹) := by rw [div_eq_mul_inv]; ring
          _ = C ω := by rw [mul_inv_cancel₀ hE.ne', mul_one]
      have hmain := (hn D (fun b => E ω n * u ω n b) hDρ hDo hDc hfharm).2 ⟨hsc, hfdata⟩ a ha b hb
      have hmaxpow : 0 ≤ max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ' i N :=
        Real.rpow_nonneg (le_max_of_le_left hE.le) _
      have hle : max (Cc i N) (A * ⨆ a' : cellVertices (E ω n) (S.η ω) D, |E ω n * u ω n a'|) ≤
          max (Cc i N) (A * C ω) := max_le_max le_rfl (mul_le_mul_of_nonneg_left hsup hA.le)
      calc E ω n * |u ω n a - u ω n b| = |E ω n * u ω n a - E ω n * u ω n b| := by
            rw [← mul_sub, abs_mul, abs_of_pos hE]
        _ ≤ _ := hmain
        _ ≤ max (Cc i N) (A * C ω) *
            max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ ξ' i N :=
          mul_le_mul_of_nonneg_right hle hmaxpow
    have hdata' : ∀ᶠ n in atTop, ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D),
        ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D), |u ω n a - u ω n b| ≤
          C' / E ω n * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ χ := by
      filter_upwards [(hEt ω).eventually (gt_mem_nhds one_pos)] with n hn
      exact hdat n hn
    exact closure_vertexEquicontinuous (hEpos ω) (hEt ω) hηω.1 hpω hηω.2.2.1 hDo hDb hχ hC'.le
      (le_max_of_le_left (hCc i N).le) (hξ'0 i N) hdata' hHm
