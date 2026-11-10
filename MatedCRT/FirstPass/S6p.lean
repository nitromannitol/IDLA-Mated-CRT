import MatedCRT.FirstPass.S5S6S7
import MatedCRT.Steps.Sec6.AnnulusHit
import MatedCRT.Steps.Sec6.GoodAnnulusPrevalence

/-!
# Lemma 6.4 with a constant depending only on `γ` and `c₀` (correction [C18])

The printed Lemma 6.4 (`lemma:good-prevalance`, corrected tex line 2664) says "a constant `C` depending only on `γ`".
The correction [C18] (author-approved 2026-11-09) replaces it by "depending only on `γ` and `c₀`": the proof gives
`C(γ, c₀)` and `c₀ = c₀(ρ, γ)` is fixed once `ρ` is. The Draft statement `GoodAnnulusPrevalenceStmt`
(Draft/Section6.lean:56) quantifies `∀ ρ` before `∃ C`, which does not record this. This file gives:

* `GoodAnnulusPrevalenceUniformStmt`: the body of `GoodAnnulusPrevalenceStmt` with `∀ ρ` moved after `∃ C`, and
  `GoodAnnulusPrevalenceUniformStmt.toStmt`, the sanity check that it implies the Draft statement;
* `AnnulusHitUniformStmt`: Lemma 6.5 (`lemma:annulus-hit`, `C = C(p)`) with the same move;
* `annulusHit_uniform`, `goodAnnulusPrevalence_uniform_of_steps`: the existing proofs
  (`annulusHit_of_steps`, Steps/Sec6/AnnulusHit.lean:102; `goodAnnulusPrevalence_of_steps`,
  Steps/Sec6/GoodAnnulusPrevalence.lean:94) with the quantifiers swapped, nothing else changed. The swap is valid because
  the constant `C = 601^{2γ²} C₁` of Lemma 6.5 uses only `C₁` from `WholePlaneGoodAnnulusTightnessStep`, which has no `ρ`,
  and the constant `C` of Lemma 6.4 is taken from Lemma 6.5 with the same `C` for every `ρ`.
  `AnnulusHitUniformStmt` is this file's uniform form of Lemma 6.5 (not a new claim of the paper).
-/

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT

namespace FirstPass64

/-- **Lemma 6.5 with the constant before `ρ`** (lemma:annulus-hit, `C = C(p)`, corrected tex line 2682): the statement
`AnnulusHitStmt` (Draft/Section6.lean:72) with `∀ ρ` moved after `∃ C`. -/
def AnnulusHitUniformStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ c₀ : ℝ, 0 < c₀ → c₀ < 1 / 5 →
  ∀ p : ℝ, 0 < p → p < 1 → ∃ C : ℝ, 0 < C ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → annulus z (r / 3) (3 * r) ⊆ ball 0 ρ →
    r / 100 ≤ infDist 0 (annulus z (r / 3) (3 * r)) →
    P {ω | ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z} ≤ ENNReal.ofReal (1 - p)

/-- **Lemma 6.5, uniform form.** The proof of `annulusHit_of_steps` with `ρ` introduced after the constant. -/
theorem annulusHit_uniform (h0 : WholePlaneLQGExistenceStep)
    (h1 : ConeWholePlaneWeylComparisonStep) (h2a : WholePlaneLQGCoordinateChangeStep)
    (h2b : WholePlaneGoodAnnulusTightnessStep) : AnnulusHitUniformStmt := by
  intro γ hγ hγ2 c₀ hc₀ hc₀' p hp hp1
  obtain ⟨C₁, hC₁, htight⟩ := h2b γ hγ hγ2 c₀ hc₀ hc₀' p hp hp1
  have hA : (0 : ℝ) < ((601 : ℝ) ^ (γ ^ 2)) ^ 2 * C₁ := by positivity
  refine ⟨((601 : ℝ) ^ (γ ^ 2)) ^ 2 * C₁, hA, ?_⟩
  intro ρ hρ hρ1 Ω _ P hC hcirc μ hcone r z hr hsub hdist
  obtain ⟨Ω', mΩ', P', hC', hcirc', μ', hP', hwp, hlqg⟩ := h0 γ hγ hγ2
  obtain ⟨hC'', hcirc'', μ'', c, hwp'', hlqg'', hc⟩ :=
    h2a γ hγ hγ2 Ω' P' hC' hcirc' μ' hP' hwp hlqg r hr z
  calc P {ω | ¬ IsGoodAnnulusEvent (μ ω) c₀ (((601 : ℝ) ^ (γ ^ 2)) ^ 2 * C₁) r z}
      ≤ P' {ω | ¬ IsGoodAnnulusEvent ((μ' ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-γ ^ 2))) c₀
          (((601 : ℝ) ^ (γ ^ 2)) ^ 2 * C₁) r z} :=
        h1 γ hγ hγ2 ρ hρ hρ1 c₀ hc₀ hc₀' _ hA Ω P hC hcirc μ hcone Ω' P' hC' hcirc' μ' hP' hwp hlqg r z
          hr hsub hdist
    _ ≤ P' {ω | ¬ IsGoodAnnulusEvent (μ' ω) c₀ C₁ r z} := by
        refine measure_mono fun ω hω hE => hω ?_
        exact isGoodAnnulusEvent_withDensity_norm_rpow hr hc₀' hC₁.le (sq_nonneg γ) hdist hE
    _ = P' {ω | ¬ IsGoodAnnulusEvent (μ'' ω) c₀ C₁ 1 0} := by
        refine measure_congr ?_
        filter_upwards [hc] with ω hω
        refine propext (not_congr ?_)
        rw [isGoodAnnulusEvent_map_iff hr, hω.2.2]
        exact isGoodAnnulusEvent_smul_iff hω.1 hω.2.1
    _ ≤ ENNReal.ofReal (1 - p) := htight Ω' P' hC'' hcirc'' μ'' hP' hwp'' hlqg''

/-- **Lemma 6.4 with a constant depending only on `γ` and `c₀`** (lemma:good-prevalance; correction [C18]): the body of
`GoodAnnulusPrevalenceStmt` (Draft/Section6.lean:56) with `∀ ρ` moved after `∃ C`. Nothing else changes. -/
def GoodAnnulusPrevalenceUniformStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ c₀ : ℝ, 0 < c₀ → c₀ < 1 / 5 → ∃ C : ℝ, 0 < C ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  PolyHighProb P fun δ => {ω | ∀ z : ℂ, z ∈ ball 0 (ρ - 3 * Real.sqrt δ) \ ball 0 (10 * Real.sqrt δ) →
    (∃ m n : ℤ, z = ((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)) →
    ∃ r : ℝ, δ ≤ r ∧ r ≤ Real.sqrt δ ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulusEvent (μ ω) c₀ C r z}

/-- The uniform statement implies the Draft statement `GoodAnnulusPrevalenceStmt` (for each `ρ`, the same `C`). -/
theorem GoodAnnulusPrevalenceUniformStmt.toStmt (H : GoodAnnulusPrevalenceUniformStmt) :
    GoodAnnulusPrevalenceStmt := by
  intro γ hγ hγ2 ρ hρ hρ1 c₀ hc₀ hc₀'
  obtain ⟨C, hC, h⟩ := H γ hγ hγ2 c₀ hc₀ hc₀'
  exact ⟨C, hC, h ρ hρ hρ1⟩

/-- **Lemma 6.4, uniform form.** The proof of `goodAnnulusPrevalence_of_steps` with `C` chosen before `ρ`. -/
theorem goodAnnulusPrevalence_uniform_of_steps (h66 : AnnulusIterateStmt) (h65 : AnnulusHitUniformStmt)
    (hT : AnnulusIterateConeTransferStep) (hL : GoodAnnulusEventLocalityStep) :
    GoodAnnulusPrevalenceUniformStmt := by
  intro γ hγ hγ2 c₀ hc₀ hc₀'
  obtain ⟨p, C₆, hp, hp1, hC₆, hiter⟩ :=
    hT h66 (1 / 12) (3 / 4) (by norm_num) (by norm_num) (by norm_num) (20 * Real.log 7) (by positivity)
  obtain ⟨C, hCpos, hhitU⟩ := h65 γ hγ hγ2 c₀ hc₀ hc₀' p hp hp1
  refine ⟨C, hCpos, ?_⟩
  intro ρ hρ hρ1
  have hhit := hhitU ρ hρ hρ1
  intro Ω _ P hC hcirc μ hcone
  have : IsProbabilityMeasure P := hcone.1
  -- the bound at one grid point, from Lemmas 6.5 and 6.6
  have hpoint : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ z ∈ ball (0 : ℂ) (ρ - 3 * Real.sqrt δ) \ ball 0 (10 * Real.sqrt δ),
      P {ω | ∀ k ∈ Finset.Icc 1 (prevalenceCount δ),
          ω ∉ {ω | IsGoodAnnulusEvent (μ ω) c₀ C (prevalenceRadius δ k) z}} ≤
        ENNReal.ofReal (C₆ * Real.exp (-(20 * Real.log 7) * prevalenceCount δ)) := by
    intro δ hδ hδ1 z hz
    have hadm : ∀ k, annulus z (prevalenceRadius δ k / 3) (3 * prevalenceRadius δ k) ⊆ ball 0 ρ ∧
        prevalenceRadius δ k / 100 ≤
          infDist 0 (annulus z (prevalenceRadius δ k / 3) (3 * prevalenceRadius δ k)) := fun k =>
      annulus_region_admissible (prevalenceRadius_pos δ k) (prevalenceRadius_le_sqrt hδ k) hz
    have hann : ∀ k, annulus z (1 / 12 * (4 * prevalenceRadius δ k)) (3 / 4 * (4 * prevalenceRadius δ k)) =
        annulus z (prevalenceRadius δ k / 3) (3 * prevalenceRadius δ k) := by
      intro k
      congr 1 <;> ring
    refine hiter γ hγ hγ2 Ω P hC hcirc μ hcone z (fun k => 4 * prevalenceRadius δ k)
      (fun k => {ω | IsGoodAnnulusEvent (μ ω) c₀ C (prevalenceRadius δ k) z}) ?_ ?_ ?_ ?_ ?_ ?_
      (prevalenceCount δ)
    · refine antitone_nat_of_succ_le fun k => ?_
      show 4 * prevalenceRadius δ (k + 1) ≤ 4 * prevalenceRadius δ k
      rw [prevalenceRadius_succ]
      have := prevalenceRadius_pos δ k
      linarith
    · intro k
      show 0 < 4 * prevalenceRadius δ k
      have := prevalenceRadius_pos δ k
      linarith
    · intro k
      show 4 * prevalenceRadius δ (k + 1) / (4 * prevalenceRadius δ k) ≤ 1 / 12
      have := prevalenceRadius_pos δ k
      rw [prevalenceRadius_succ, div_le_iff₀ (by linarith)]
      linarith
    · intro k
      show annulus z (1 / 12 * (4 * prevalenceRadius δ k)) (3 / 4 * (4 * prevalenceRadius δ k)) ⊆ ball 0 1
      rw [hann k]
      exact (hadm k).1.trans (ball_subset_ball hρ1.le)
    · intro k
      show ∃ E' : Set Ω, MeasurableSet[modConstSigma hC
          (annulus z (1 / 12 * (4 * prevalenceRadius δ k)) (3 / 4 * (4 * prevalenceRadius δ k)))] E' ∧
        {ω | IsGoodAnnulusEvent (μ ω) c₀ C (prevalenceRadius δ k) z} =ᵐ[P] E'
      rw [hann k]
      exact hL γ hγ hγ2 c₀ hc₀ hc₀' C hCpos Ω P hC hcirc μ hcone (prevalenceRadius δ k) z
        (prevalenceRadius_pos δ k) ((hadm k).1.trans (ball_subset_ball hρ1.le))
    · intro k
      exact ofReal_le_measure_of_compl_le hp.le hp1.le
        (hhit Ω P hC hcirc μ hcone (prevalenceRadius δ k) z (prevalenceRadius_pos δ k) (hadm k).1 (hadm k).2)
  -- union bound over the grid
  refine ⟨3, by norm_num, 201 ^ 2 * C₆ * 7 ^ 25, 1, by norm_num, fun δ hδ hδ1 => ?_⟩
  have hδ1' : δ ≤ 1 := hδ1.le
  set M : ℕ := ⌊100 / δ⌋₊
  set S : Finset (ℤ × ℤ) := (Finset.Icc (-(M : ℤ)) M) ×ˢ (Finset.Icc (-(M : ℤ)) M) with hS
  set K : ℕ := prevalenceCount δ
  set reg : Set ℂ := ball (0 : ℂ) (ρ - 3 * Real.sqrt δ) \ ball 0 (10 * Real.sqrt δ)
  set B : ℤ × ℤ → Set Ω := fun x => {ω | ((δ / 100 : ℝ) : ℂ) * (x.1 + x.2 * Complex.I) ∈ reg ∧
    ∀ k ∈ Finset.Icc 1 K, ¬ IsGoodAnnulusEvent (μ ω) c₀ C (prevalenceRadius δ k)
      (((δ / 100 : ℝ) : ℂ) * (x.1 + x.2 * Complex.I))}
  have hsub : {ω | ∀ z : ℂ, z ∈ reg → (∃ m n : ℤ, z = ((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)) →
      ∃ r : ℝ, δ ≤ r ∧ r ≤ Real.sqrt δ ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        IsGoodAnnulusEvent (μ ω) c₀ C r z}ᶜ ⊆ ⋃ x ∈ S, B x := by
    intro ω hω
    rw [mem_compl_iff, mem_ofPred_eq] at hω
    push Not at hω
    obtain ⟨z, hz, ⟨m, n, rfl⟩, hno⟩ := hω
    have hz1 : ‖((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)‖ < 1 := by
      have h := hz.1
      rw [mem_ball, dist_zero_right] at h
      have := Real.sqrt_nonneg δ
      linarith
    refine mem_iUnion₂.2 ⟨(m, n), Finset.mem_product.2 (grid_mem_Icc hδ hz1), hz, fun k hk hE => ?_⟩
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.1 hk
    exact hno _ (le_prevalenceRadius hδ hδ1' hk1 hkK) (prevalenceRadius_le_sqrt hδ k) ⟨_, rfl⟩ hE
  have hBle : ∀ x ∈ S, P (B x) ≤ ENNReal.ofReal (C₆ * Real.exp (-(20 * Real.log 7) * K)) := by
    intro x _
    by_cases hx : ((δ / 100 : ℝ) : ℂ) * (x.1 + x.2 * Complex.I) ∈ reg
    · exact (measure_mono fun ω hω => hω.2).trans (hpoint δ hδ hδ1' _ hx)
    · calc P (B x) ≤ P ∅ := measure_mono fun ω hω => (hx hω.1).elim
        _ = 0 := measure_empty
        _ ≤ _ := zero_le
  have hcard : (S.card : ℝ) = (2 * (M : ℝ) + 1) ^ 2 := by
    rw [hS, card_grid]
    push_cast
    ring
  have hMle : (M : ℝ) ≤ 100 / δ := Nat.floor_le (by positivity)
  have h1δ : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have h2M : 2 * (M : ℝ) + 1 ≤ 201 / δ := by
    have e : (201 : ℝ) / δ = 2 * (100 / δ) + 1 / δ := by ring
    rw [e]
    linarith
  have hsq : (2 * (M : ℝ) + 1) ^ 2 ≤ (201 / δ) ^ 2 := pow_le_pow_left₀ (by positivity) h2M 2
  have hexp := exp_prevalenceCount_le hδ
  have hexp0 : 0 ≤ Real.exp (-(20 * Real.log 7) * K) := (Real.exp_pos _).le
  have hreal : (S.card : ℝ) * (C₆ * Real.exp (-(20 * Real.log 7) * K)) ≤
      201 ^ 2 * C₆ * 7 ^ 25 * δ ^ (3 : ℝ) := by
    rw [hcard, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (2 * (M : ℝ) + 1) ^ 2 * (C₆ * Real.exp (-(20 * Real.log 7) * K))
        ≤ (201 / δ) ^ 2 * (C₆ * (7 ^ 25 * δ ^ 5)) :=
          mul_le_mul hsq (mul_le_mul_of_nonneg_left hexp hC₆.le) (mul_nonneg hC₆.le hexp0) (by positivity)
      _ = 201 ^ 2 * C₆ * 7 ^ 25 * δ ^ 3 := by
          field_simp
  calc P {ω | ∀ z : ℂ, z ∈ reg → (∃ m n : ℤ, z = ((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)) →
        ∃ r : ℝ, δ ≤ r ∧ r ≤ Real.sqrt δ ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulusEvent (μ ω) c₀ C r z}ᶜ
      ≤ P (⋃ x ∈ S, B x) := measure_mono hsub
    _ ≤ ∑ x ∈ S, P (B x) := measure_biUnion_finset_le S B
    _ ≤ ∑ x ∈ S, ENNReal.ofReal (C₆ * Real.exp (-(20 * Real.log 7) * K)) := Finset.sum_le_sum hBle
    _ = ENNReal.ofReal ((S.card : ℝ) * (C₆ * Real.exp (-(20 * Real.log 7) * K))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (201 ^ 2 * C₆ * 7 ^ 25 * δ ^ (3 : ℝ)) := ENNReal.ofReal_le_ofReal hreal

/-- **Lemma 6.4 with `C = C(γ, c₀)`** (lemma:good-prevalance; correction [C18]), from the FIRST-PASS inputs of
`firstPass_6_4` (MatedCRT/FirstPass/S5S6S7.lean:57), which are the inputs of Lemma 6.5. -/
theorem firstPass_6_4_uniform (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) :
    GoodAnnulusPrevalenceUniformStmt :=
  goodAnnulusPrevalence_uniform_of_steps annulusIterate
    (annulusHit_uniform h0 AnnulusHitField.coneWholePlaneWeylComparison h2
      (wholePlaneGoodAnnulusTightness_of_volumeTail h0 hV))
    (annulusIterateConeTransfer hR)
    (goodAnnulusEventLocality Field.ConeCircle.circleAverageModConstStep)

end FirstPass64

end MatedCRT
