import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.OfSteps
import MatedCRT.Draft.Section2

/-!
# Lemma 6.7: the model steps

* `walkExitsStep`: `WalkExitsStep` from Lemma 2.7 (volume growth: `μ_h(B_δ(0)) ≥ δ^{β⁻}`, so `μ_h(B_{s₀}) ≥ ε^α` with
  probability tending to `1`) and Lemma 2.19 (`Q^ε_D < ∞` for Borel `D ⊆ B_ρ` with `μ_h(D) ≥ ε^α`).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

theorem ProbTendsToOne.mono_ev {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (h : ProbTendsToOne P E) (hEF : ∀ᶠ ε in 𝓝[>] (0 : ℝ), E ε ⊆ F ε) : ProbTendsToOne P F :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h (Eventually.of_forall fun _ => zero_le)
    (hEF.mono fun _ hε => measure_mono (compl_subset_compl.2 hε))

/-- `ε^b → 0` as `ε → 0⁺`, for `b > 0`. -/
theorem tendsto_rpow_nhdsGT_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ => ε ^ b) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun ε : ℝ => ε ^ b) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ b)) :=
    ((Real.continuousAt_rpow_const 0 b (Or.inr hb.le)).tendsto).mono_left nhdsWithin_le_nhds
  rwa [Real.zero_rpow hb.ne'] at h

/-- An event of polynomially high probability as `δ → 0`, evaluated at `δ = ε^b` (`b > 0`), holds with probability
tending to `1` as `ε → 0`. -/
theorem HarmonicBalls.PolyHighProb.probTendsToOne_rpow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (h : HarmonicBalls.PolyHighProb P E) {b : ℝ} (hb : 0 < b) :
    ProbTendsToOne P fun ε => E (ε ^ b) := by
  obtain ⟨p, hp, C, r₀, hr₀, hbound⟩ := h
  have hg := tendsto_rpow_nhdsGT_zero hb
  have hup : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * (ε ^ b) ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have h3 := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto).comp hg
    rw [Real.zero_rpow hp.ne'] at h3
    have h4 := (h3.const_mul C)
    rw [mul_zero] at h4
    have h5 := ENNReal.tendsto_ofReal h4
    rwa [ENNReal.ofReal_zero] at h5
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin, hg.eventually (Iio_mem_nhds hr₀)] with ε hε hεr
  exact hbound _ (Real.rpow_pos_of_pos hε b) hεr

theorem HarmonicBalls.PolyHighProb.probTendsToOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (h : HarmonicBalls.PolyHighProb P E) : ProbTendsToOne P E := by
  have := HarmonicBalls.PolyHighProb.probTendsToOne_rpow h one_pos
  simpa only [Real.rpow_one] using this

namespace ConstantOrder

open Classical in
theorem vExitTime_eq_top_iff {W : Set ℤ} {y : ℕ → ℤ} : vExitTime W y = ⊤ ↔ ∀ n, y n ∈ W := by
  unfold vExitTime
  split_ifs with h
  · refine ⟨fun e => absurd e (ENat.natCast_ne_top _), fun hall => ?_⟩
    obtain ⟨n, hn⟩ := h
    exact absurd (hall n) hn
  · exact ⟨fun _ n => not_not.1 fun hn => h ⟨n, hn⟩, fun _ => rfl⟩

/-- A finite expected exit time forces the walk to exit almost surely. -/
theorem srwLaw_vExitTime_eq_top_eq_zero {m : ℤ → ℤ → ℕ} {W : Set ℤ} {a : ℤ}
    (h : expectedExitTime m W a < ⊤) : srwLaw m a {x | vExitTime W x = ⊤} = 0 := by
  have hN : {x : ℕ → ℤ | vExitTime W x = ⊤} = ⋂ n, (fun x : ℕ → ℤ => x n) ⁻¹' W := by
    ext x; simp [vExitTime_eq_top_iff]
  have hNm : MeasurableSet {x : ℕ → ℤ | vExitTime W x = ⊤} := by
    rw [hN]
    exact MeasurableSet.iInter fun n => (Set.to_countable W).measurableSet.preimage (measurable_pi_apply n)
  by_contra hpos
  have hle : ∫⁻ x, {x : ℕ → ℤ | vExitTime W x = ⊤}.indicator (fun _ => (⊤ : ℝ≥0∞)) x ∂srwLaw m a ≤
      expectedExitTime m W a := by
    unfold expectedExitTime
    refine lintegral_mono fun x => ?_
    by_cases hx : vExitTime W x = ⊤
    · rw [Set.indicator_of_mem (show x ∈ {x : ℕ → ℤ | vExitTime W x = ⊤} from hx), hx]
      simp
    · rw [Set.indicator_of_notMem (show x ∉ {x : ℕ → ℤ | vExitTime W x = ⊤} from hx)]
      exact zero_le
  rw [lintegral_indicator_const hNm, ENNReal.top_mul hpos] at hle
  exact absurd (lt_of_le_of_lt hle h) (lt_irrefl _)

/-- Distinct cells of an area-parametrized curve overlap in a null set: `μ(η([a,b]) ∩ η([b,d])) = 0` since
`μ(η([a,d])) = d - a = μ(η([a,b])) + μ(η([b,d]))`. -/
theorem cell_inter_null {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    {j k : ℤ} (hjk : j < k) : μ (cell ε η j ∩ cell ε η k) = 0 := by
  have hjk' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
  have hab : ε * ((j : ℝ) - 1) < ε * j := by nlinarith
  have hbd : ε * (j : ℝ) < ε * k := by nlinarith
  have hU : η '' Icc (ε * ((j : ℝ) - 1)) (ε * k) =
      η '' Icc (ε * ((j : ℝ) - 1)) (ε * j) ∪ η '' Icc (ε * (j : ℝ)) (ε * k) := by
    rw [← image_union, Icc_union_Icc_eq_Icc hab.le hbd.le]
  have hmeas : MeasurableSet (η '' Icc (ε * (j : ℝ)) (ε * k)) :=
    (isCompact_Icc.image h.1).isClosed.measurableSet
  have key := measure_union_add_inter (μ := μ) (η '' Icc (ε * ((j : ℝ) - 1)) (ε * j)) hmeas
  rw [← hU, h.2.2.2 _ _ (hab.trans hbd), h.2.2.2 _ _ hab, h.2.2.2 _ _ hbd,
    ← ENNReal.ofReal_add (by linarith) (by linarith),
    show ε * (j : ℝ) - ε * ((j : ℝ) - 1) + (ε * k - ε * j) = ε * k - ε * ((j : ℝ) - 1) by ring] at key
  have h0 : μ (η '' Icc (ε * ((j : ℝ) - 1)) (ε * j) ∩ η '' Icc (ε * (j : ℝ)) (ε * k)) = 0 :=
    (ENNReal.add_right_inj ENNReal.ofReal_ne_top).1 (key.trans (add_zero _).symm)
  refine measure_mono_null (inter_subset_inter (fun y hy => hy) ?_) h0
  exact image_mono (Icc_subset_Icc (by nlinarith) le_rfl)

end ConstantOrder

open ConstantOrder in
/-- **`CellVerticesBallFiniteStep`** from Lemma 2.7 (volume growth: `μ_h(B_R) < ∞` by a finite cover with small
balls), Lemma 2.8 (the cells meeting `B_ρ` are small, hence lie in `B_R`, `R = (1 + ρ)/2`) and the area
parametrization (each cell has mass `ε`, distinct cells overlap in null sets): `#F ε ≤ μ_h(B_R)` for every finite
`F ⊆ V^ε(B_ρ)`. -/
theorem cellVerticesBallFiniteStep (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) : CellVerticesBallFiniteStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  set e : ℝ := 1 / (2 + γ) ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he, div_lt_one (by positivity)]
    nlinarith
  have hA := HarmonicBalls.PolyHighProb.probTendsToOne (h28 γ hγ hγ2 e ρ he0 he1 hρ hρ1 Ω S hS)
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ := by
    unfold IsConeField
    exact ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have hB := HarmonicBalls.PolyHighProb.probTendsToOne
    (h27 γ hγ hγ2 ((2 - γ) ^ 2 / 4) ((2 + γ) ^ 2 / 2 + 1) (by nlinarith) (by nlinarith) (by linarith)
      Ω S.P S.hC S.hcirc S.μ hcone)
  have hC := probTendsToOne_of_ae (G := {ω | IsAreaParametrized (S.μ ω) (S.η ω)}) hS.isAreaParametrized
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  refine ((hA.inter hB).inter hC).mono_ev ?_
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_rpow_nhdsGT_zero he0).eventually (Iio_mem_nhds (show (0 : ℝ) < (1 - ρ) / 2 by linarith)),
    hid.eventually (Iio_mem_nhds (show (0 : ℝ) < (1 - ρ) / 2 by linarith))] with ε hε hεe hε2 ω hω
  obtain ⟨⟨hωA, hωB⟩, hωC⟩ := hω
  simp only [mem_ofPred_eq] at hωA hωB hωC hε2 ⊢
  have hε0 : 0 < ε := hε
  have hcellR : ∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ), cell ε (S.η ω) k ⊆ ball 0 ((1 + ρ) / 2) := by
    intro k hk y hy
    obtain ⟨p, hp, hpρ⟩ := hk
    have hdiam := (hωA k ⟨p, hp, hpρ⟩).2
    rw [show 2 / (2 + γ) ^ 2 - e = e by rw [he]; ring] at hdiam
    have hbdd : Bornology.IsBounded (cell ε (S.η ω) k) := (isCompact_Icc.image hωC.1).isBounded
    have hyp := dist_le_diam_of_mem hbdd hy hp
    rw [mem_ball, dist_zero_right] at hpρ ⊢
    rw [dist_eq_norm] at hyp
    have := norm_sub_norm_le y p
    linarith
  have hfin_each : ∀ z ∈ closedBall (0 : ℂ) ((1 + ρ) / 2), S.μ ω (ball z ε) ≠ ⊤ := by
    intro z hz
    have hz' : z ∈ ball (0 : ℂ) (1 - ε) := by
      rw [mem_closedBall, dist_zero_right] at hz
      rw [mem_ball, dist_zero_right]
      linarith
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hωB z hz').2
  have hμR : S.μ ω (ball 0 ((1 + ρ) / 2)) < ⊤ := by
    obtain ⟨t, htR, htfin, hcover⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : ℂ) ((1 + ρ) / 2)) hε0
    exact lt_of_le_of_lt (measure_mono (ball_subset_closedBall.trans hcover))
      (measure_biUnion_lt_top htfin fun z hz => (hfin_each z (htR hz)).lt_top)
  have hcellμ : ∀ k : ℤ, S.μ ω (cell ε (S.η ω) k) = ENNReal.ofReal ε := fun k => by
    unfold cell
    rw [hωC.2.2.2 _ _ (by nlinarith)]
    congr 1
    ring
  by_contra hinf
  obtain ⟨n, hn⟩ := exists_nat_gt ((S.μ ω (ball 0 ((1 + ρ) / 2))).toReal / ε)
  obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
  have hsum : S.μ ω (⋃ k ∈ F, cell ε (S.η ω) k) = ∑ k ∈ F, S.μ ω (cell ε (S.η ω) k) := by
    refine measure_biUnion_finset₀ ?_ fun k _ =>
      (isCompact_Icc.image hωC.1).isClosed.measurableSet.nullMeasurableSet
    intro j _ k _ hjk
    show S.μ ω (cell ε (S.η ω) j ∩ cell ε (S.η ω) k) = 0
    rcases lt_or_gt_of_ne hjk with h | h
    · exact cell_inter_null hωC hε0 h
    · rw [inter_comm]
      exact cell_inter_null hωC hε0 h
  have hle : (n : ℝ≥0∞) * ENNReal.ofReal ε ≤ S.μ ω (ball 0 ((1 + ρ) / 2)) := by
    calc (n : ℝ≥0∞) * ENNReal.ofReal ε = ∑ k ∈ F, S.μ ω (cell ε (S.η ω) k) := by
          rw [Finset.sum_congr rfl fun k _ => hcellμ k, Finset.sum_const, hFcard, nsmul_eq_mul]
      _ = S.μ ω (⋃ k ∈ F, cell ε (S.η ω) k) := hsum.symm
      _ ≤ S.μ ω (ball 0 ((1 + ρ) / 2)) := measure_mono (iUnion₂_subset fun k hk => hcellR k (hFsub hk))
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
    ENNReal.ofReal_le_iff_le_toReal hμR.ne] at hle
  rw [div_lt_iff₀ hε0] at hn
  linarith

open ConstantOrder in
/-- **`WalkExitsStep`** from Lemma 2.7 (volume growth) and Lemma 2.19 (finite expected exit times). -/
theorem walkExitsStep (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) : WalkExitsStep 𝒮 := by
  intro γ hγ hγ2 ρ s₀ hρ hρ1 hs₀ Ω _ S hS
  obtain ⟨α, q, hα, -, h⟩ := h219 γ hγ hγ2
  have hE1 := HarmonicBalls.PolyHighProb.probTendsToOne (h ρ hρ hρ1 Ω S hS).1
  set βm : ℝ := (2 + γ) ^ 2 / 2 + 1 with hβm
  have hβm0 : 0 < βm := by positivity
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ := by
    unfold IsConeField
    exact ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have hE2 := HarmonicBalls.PolyHighProb.probTendsToOne_rpow
    (h27 γ hγ hγ2 ((2 - γ) ^ 2 / 4) βm (by nlinarith) (by nlinarith) (by linarith)
      Ω S.P S.hC S.hcirc S.μ hcone) (div_pos hα hβm0)
  refine (hE1.inter hE2).mono_ev ?_
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_rpow_nhdsGT_zero (div_pos hα hβm0)).eventually (Iio_mem_nhds (lt_min hs₀ one_pos))]
    with ε hε hsmall ω hω
  obtain ⟨hω1, hω2⟩ := hω
  simp only [mem_ofPred_eq] at hω1 hω2 ⊢
  have hε0 : 0 < ε := hε
  have hδ0 : 0 < ε ^ (α / βm) := Real.rpow_pos_of_pos hε0 _
  have hδs : ε ^ (α / βm) < s₀ := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hδ1 : ε ^ (α / βm) < 1 := lt_of_lt_of_le hsmall (min_le_right _ _)
  intro O hO hsO hOρ a
  have hμ : ENNReal.ofReal (ε ^ α) ≤ S.μ ω O := by
    have h0 := (hω2 0 (mem_ball_self (by linarith))).1
    rw [← Real.rpow_mul hε0.le, div_mul_cancel₀ α hβm0.ne'] at h0
    exact h0.trans (measure_mono ((ball_subset_ball hδs.le).trans hsO))
  exact srwLaw_vExitTime_eq_top_eq_zero (hω1 O hO.measurableSet hOρ hμ a).2

end MatedCRT
