import MatedCRT.Draft.Section6
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Counting

/-!
# Lemma 6.4 (lemma:good-prevalance, line 2318): steps of the printed proof (lines 2387-2400)

The proof combines Lemma 6.5 (`AnnulusHitStmt`, the event has probability at least `p` for a suitable `C`) with
Lemma 6.6 (`AnnulusIterateStmt`, near-independence across concentric annuli), then takes a union bound over the
grid. Two facts about the fields are step Props (INPUT-REQUESTS IR-c4-5 and IR-c4-6):

* `GoodAnnulusEventLocalityStep` (lines 2388-2390). `E_r(z)` depends only on `μ_h|_{𝔸_{r/3,3r}(z)}`, and is
  unchanged when this measure is multiplied by a constant. Hence, by locality and Weyl scaling (Fact 2.2), it is
  a.s. determined by `h|_{𝔸_{r/3,3r}(z)}` viewed modulo additive constant.
* `AnnulusIterateConeTransferStep`. Lemma 6.6 is stated for the whole-plane GFF and for annuli centred at `0`. The
  proof applies it to the cone field `h` and to annuli centred at `z`. The transfer uses eq:gff (line 444,
  `h|_{B_1} =d (h^ℂ - γ log |·|)|_{B_1}`; IR-A1 `ConeRestrictionInput`) and the translation invariance of `h^ℂ`
  modulo additive constant (eq:gff-scaling). Adding the deterministic function `-γ log |·|` maps events determined
  modulo constants on an annulus to events of the same kind.

The rest is deterministic and proved here, with `MatedCRT/Proofs/Sec6/GoodAnnulusPrevalence/Counting.lean`:

* Lemma 6.6 is applied with `s₁ = 1/12`, `s₂ = 3/4` and `α = 20 log 7`. The radii `R_k = 4 r_k` give
  `𝔸_{s₁ R_k, s₂ R_k}(z) = 𝔸_{r_k/3, 3 r_k}(z)` and ratio `1/49`, where `r_k = 7^{-(n₀ + 2k)} ∈ [δ, δ^{1/2}]`.
* With `K ≍ log₄₉ δ^{-1/2}` radii, `C e^{-αK} ≤ C 7^{25} δ^5`.
* The union bound runs over at most `(201/δ)²` grid points. The constant of the polynomially high probability is
  `201² C 7^{25}` and the exponent is `3`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

/-- **Lemma 6.6 for the cone field, on annuli centred at any `z` inside `B_1`.** Same constants `p, C` as Lemma 6.6.
Events determined modulo constants by the cone field on `𝔸_{s₁ r_k, s₂ r_k}(z) ⊆ B_1` satisfy the conclusion of
Lemma 6.6. -/
def ConeAnnulusIterateProp : Prop :=
  ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → ∀ α : ℝ, 0 < α → ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 < C ∧
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ (z : ℂ) (r : ℕ → ℝ) (E : ℕ → Set Ω), Antitone r → (∀ k, 0 < r k) → (∀ k, r (k + 1) / r k ≤ s₁) →
    (∀ k, annulus z (s₁ * r k) (s₂ * r k) ⊆ ball 0 1) →
    (∀ k, ∃ E' : Set Ω, MeasurableSet[modConstSigma hC (annulus z (s₁ * r k) (s₂ * r k))] E' ∧ E k =ᵐ[P] E') →
    (∀ k, ENNReal.ofReal p ≤ P (E k)) →
    ∀ K : ℕ, P {ω | ∀ k ∈ Finset.Icc 1 K, ω ∉ E k} ≤ ENNReal.ofReal (C * Real.exp (-α * K))

/-- **Transfer of Lemma 6.6 to the cone field** (INPUT-REQUESTS IR-c4-5). It uses eq:gff (line 444;
`ConeRestrictionInput`, IR-A1) and the translation invariance modulo additive constant of the whole-plane GFF
(eq:gff-scaling). -/
def AnnulusIterateConeTransferStep : Prop := AnnulusIterateStmt → ConeAnnulusIterateProp

/-- **`E_r(z)` is a.s. determined by `h|_{𝔸_{r/3,3r}(z)}` modulo additive constant** (lines 2388-2390;
INPUT-REQUESTS IR-c4-6). Locality and Weyl scaling of `μ_h` (Fact 2.2) with `isGoodAnnulusEvent_smul_iff`. -/
def GoodAnnulusEventLocalityStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ c₀ : ℝ, 0 < c₀ → c₀ < 1 / 5 → ∀ C : ℝ, 0 < C →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → annulus z (r / 3) (3 * r) ⊆ ball 0 1 →
    ∃ E' : Set Ω, MeasurableSet[modConstSigma hC (annulus z (r / 3) (3 * r))] E' ∧
      {ω | IsGoodAnnulusEvent (μ ω) c₀ C r z} =ᵐ[P] E'

/-- **Lemma 6.4 from Lemmas 6.5, 6.6 and its steps** (proof lines 2387-2400). -/
theorem goodAnnulusPrevalence_of_steps (h66 : AnnulusIterateStmt) (h65 : AnnulusHitStmt)
    (hT : AnnulusIterateConeTransferStep) (hL : GoodAnnulusEventLocalityStep) :
    GoodAnnulusPrevalenceStmt := by
  intro γ hγ hγ2 ρ hρ hρ1 c₀ hc₀ hc₀'
  obtain ⟨p, C₆, hp, hp1, hC₆, hiter⟩ :=
    hT h66 (1 / 12) (3 / 4) (by norm_num) (by norm_num) (by norm_num) (20 * Real.log 7) (by positivity)
  obtain ⟨C, hCpos, hhit⟩ := h65 γ hγ hγ2 ρ hρ hρ1 c₀ hc₀ hc₀' p hp hp1
  refine ⟨C, hCpos, ?_⟩
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

end MatedCRT
