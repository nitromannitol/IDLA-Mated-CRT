import MatedCRT.FirstPass.S2g.Canonical

/-! # Scale gluing for the global family: two scale-independent pieces of Lemma 2.6

For the all-time family of Lemma 2.6 (`ConeScaleInvarianceStmt`), the global family of a cone measure is glued from the
canonical families at the scales `b_k = k + 1`. This file proves the two pieces that do not
depend on any measurability of the gluing:

* `eqOn_of_isConeHarmonicBallFamily`: a global cone family agrees with any cone family on `(0, T)` on that interval
  (fixed-time uniqueness, `IsConeHarmonicBallFamilyOn.eqOn`);
* `ae_forall_exists_scale_gt`: almost surely, for every `M`, some scale `(k+1) T_k` exceeds `M`, when the scaled canonical
  times `T_k` have the law of the canonical time `X`, which is almost surely positive. This is `sup_k L_k = ∞` in
  (`P[L_n ≤ M] → 0`). -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

/-- A global cone family agrees with any cone family on `(0, T)` (deterministic). -/
theorem eqOn_of_isConeHarmonicBallFamily {μ : Measure ℂ} {Λ Λ' : ℝ → Set ℂ} {T : ℝ}
    (hΛ : IsConeHarmonicBallFamily μ Λ) (hΛ' : IsConeHarmonicBallFamilyOn μ Λ' T) :
    EqOn Λ' Λ (Ioo 0 T) := by
  rcases le_or_gt T 0 with hT | hT
  · intro t ht
    exact absurd (lt_of_lt_of_le ht.2 hT) (not_lt.2 ht.1.le)
  · have h := (hΛ.isConeHarmonicBallFamilyOn hT).eqOn hΛ'
    rwa [min_self] at h

/-- **Sup of the scaled canonical times is infinite, almost surely.** Let `X` be a.s. positive and a.e.
measurable, and let `T k` (scale `k + 1`) have the law of `X`. Then almost surely, for every `M`, there is `k` with
`M < (k + 1) * T k`. Proof: `P[∀ k, (k+1) T_k ≤ M] ≤ P[X ≤ 1/(j+1)]` for every `j`, and `P[X ≤ 1/(j+1)] → P[X ≤ 0] = 0`
by continuity from above. -/
theorem ae_forall_exists_scale_gt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {T : ℕ → Ω → ℝ}
    (hT : ∀ k, AEMeasurable (T k) P) (hlaw : ∀ k, P.map (T k) = P.map X) :
    ∀ᵐ ω ∂P, ∀ M : ℕ, ∃ k : ℕ, (M : ℝ) < ((k : ℝ) + 1) * T k ω := by
  -- the decreasing sets `A j = {X ≤ 1/(j+1)}`, with intersection `{X ≤ 0}`
  let A : ℕ → Set Ω := fun j => X ⁻¹' Iic (1 / ((j : ℝ) + 1))
  have hAm : ∀ j, NullMeasurableSet (A j) P := fun j => hX.nullMeasurableSet_preimage measurableSet_Iic
  have hAnti : Antitone A := by
    intro i j hij ω hω
    simp only [A, mem_preimage, mem_Iic] at hω ⊢
    refine le_trans hω (one_div_le_one_div_of_le ?_ ?_)
    · positivity
    · exact_mod_cast Nat.add_le_add_right hij 1
  have hInter : (⋂ j, A j) = X ⁻¹' Iic 0 := by
    ext ω
    simp only [A, mem_iInter, mem_preimage, mem_Iic]
    constructor
    · intro h
      by_contra hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (not_le.1 hc)
      exact absurd (h n) (not_le.2 hn)
    · intro h j
      exact le_trans h (by positivity)
  have hP0 : P (X ⁻¹' Iic 0) = 0 := by
    have h := ae_iff.1 hpos
    have hset : {ω | ¬ 0 < X ω} = X ⁻¹' Iic 0 := by
      ext ω
      simp [not_lt]
    rwa [hset] at h
  have hTend : Tendsto (fun j => P (A j)) atTop (𝓝 (P (⋂ j, A j))) :=
    tendsto_measure_iInter_atTop hAm hAnti ⟨0, measure_ne_top P _⟩
  rw [hInter, hP0] at hTend
  -- for each `M`, the event that all scaled times are at most `M` is null
  have hnull : ∀ M : ℕ, P {ω | ∀ k : ℕ, ((k : ℝ) + 1) * T k ω ≤ (M : ℝ)} = 0 := by
    intro M
    have key : ∀ j : ℕ, P {ω | ∀ k : ℕ, ((k : ℝ) + 1) * T k ω ≤ (M : ℝ)} ≤ P (A j) := by
      intro j
      set K : ℕ := M * (j + 1) with hKdef
      have hK : (M : ℝ) / ((K : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity), hKdef]
        push_cast
        linarith
      have hlawr : P {ω | T K ω ≤ (M : ℝ) / ((K : ℝ) + 1)} = P {ω | X ω ≤ (M : ℝ) / ((K : ℝ) + 1)} := by
        have h1 : (P.map (T K)) (Iic ((M : ℝ) / ((K : ℝ) + 1))) = (P.map X) (Iic ((M : ℝ) / ((K : ℝ) + 1))) := by
          rw [hlaw K]
        rwa [Measure.map_apply_of_aemeasurable (hT K) measurableSet_Iic,
          Measure.map_apply_of_aemeasurable hX measurableSet_Iic] at h1
      calc P {ω | ∀ k : ℕ, ((k : ℝ) + 1) * T k ω ≤ (M : ℝ)}
          ≤ P {ω | ((K : ℝ) + 1) * T K ω ≤ (M : ℝ)} :=
            measure_mono fun ω hω => hω K
        _ = P {ω | T K ω ≤ (M : ℝ) / ((K : ℝ) + 1)} := by
            congr 1
            ext ω
            have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
            simp only [mem_ofPred_eq]
            rw [le_div_iff₀ hKpos]
            exact ⟨fun h => by linarith, fun h => by linarith⟩
        _ = P {ω | X ω ≤ (M : ℝ) / ((K : ℝ) + 1)} := hlawr
        _ ≤ P (A j) := measure_mono fun ω hω => by
            simp only [A, mem_preimage, mem_Iic] at hω ⊢
            exact le_trans hω hK
    have hle : P {ω | ∀ k : ℕ, ((k : ℝ) + 1) * T k ω ≤ (M : ℝ)} ≤ 0 := ge_of_tendsto' hTend key
    exact nonpos_iff_eq_zero.1 hle
  rw [ae_all_iff]
  intro M
  rw [ae_iff]
  convert hnull M using 2
  ext ω
  simp only [mem_ofPred_eq, not_exists, not_lt]

/-- **Scale gluing of a global cone family (deterministic).** Let `Λ` be a global cone family for
`μ` and let `Λs n` be cone families for `μ` on `(0, L n)`, where the scales cover every natural number
(`∀ M, ∃ n, M < L n`). Then the global family process of `Λ` is the glued process
`(t, x) ↦ 0 < t ∧ ∃ n, t < L n ∧ x ∈ Λs n t`. Fixed-time uniqueness (`eqOn_of_isConeHarmonicBallFamily`) identifies `Λ_t`
with `Λs n t` at every `t < L n`, and the covering of scales gives a scale `L n > t` for every positive time `t`. -/
theorem globalFamilyProcess_eq_of_scales {μ : Measure ℂ} {Λ : ℝ → Set ℂ} (hΛ : IsConeHarmonicBallFamily μ Λ)
    {L : ℕ → ℝ} {Λs : ℕ → ℝ → Set ℂ} (hfam : ∀ n, IsConeHarmonicBallFamilyOn μ (Λs n) (L n))
    (hcov : ∀ M : ℕ, ∃ n, (M : ℝ) < L n) :
    globalFamilyProcess Λ = fun p => 0 < p.1 ∧ ∃ n, p.1 < L n ∧ p.2 ∈ Λs n p.1 := by
  have heq := fun n => eqOn_of_isConeHarmonicBallFamily hΛ (hfam n)
  have key : ∀ p : ℝ × ℂ, 0 < p.1 → (p.2 ∈ Λ p.1 ↔ ∃ n, p.1 < L n ∧ p.2 ∈ Λs n p.1) := by
    intro p hp
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := hcov ⌈p.1⌉₊
      have ht : p.1 < L n := lt_of_le_of_lt (Nat.le_ceil p.1) hn
      have hmem : p.1 ∈ Ioo 0 (L n) := ⟨hp, ht⟩
      refine ⟨n, ht, ?_⟩
      rw [heq n hmem]
      exact hx
    · rintro ⟨n, ht, hx⟩
      have hmem : p.1 ∈ Ioo 0 (L n) := ⟨hp, ht⟩
      rw [← heq n hmem]
      exact hx
  funext p
  show globalFamilyProcess Λ p = (0 < p.1 ∧ ∃ n, p.1 < L n ∧ p.2 ∈ Λs n p.1)
  apply propext
  constructor
  · intro h
    have h' : 0 < p.1 ∧ p.2 ∈ Λ p.1 := h
    exact ⟨h'.1, (key p h'.1).1 h'.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (key p h1).2 h2⟩

end MatedCRT
