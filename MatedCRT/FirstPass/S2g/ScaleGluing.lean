import MatedCRT.FirstPass.S2g.Canonical

/-! # Scale gluing for the global family (q1, fp-S2g): two scale-independent pieces of Lemma 2.6

For the all-time family of Lemma 2.6 (`ConeScaleInvarianceStmt`), the global family of a cone measure is glued from the
canonical families at the scales `b_k = k + 1` (G-S2-2-5-2-6 Section 2). This file proves the two pieces that do not
depend on any measurability of the gluing:

* `eqOn_of_isConeHarmonicBallFamily`: a global cone family agrees with any cone family on `(0, T)` on that interval
  (fixed-time uniqueness, `IsConeHarmonicBallFamilyOn.eqOn`);
* `ae_forall_exists_scale_gt`: almost surely, for every `M`, some scale `(k+1) T_k` exceeds `M`, when the scaled canonical
  times `T_k` have the law of the canonical time `X`, which is almost surely positive. This is `sup_k L_k = ∞` in
  G-S2-2-5-2-6 Section 2 (`P[L_n ≤ M] → 0`). -/

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

/-- **Sup of the scaled canonical times is infinite, almost surely (q1, fp-S2g).** Let `X` be a.s. positive and a.e.
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

end MatedCRT
