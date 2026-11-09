import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section4
import MatedCRT.FirstPass.S5c.BadEvents
import MatedCRT.FirstPass.S5c.SubseqBorelCantelli

/-!
# FIRST PASS, Lemma 5.3 and E-c1-5: B2 almost-sure errors and cells along a deterministic subsequence

CHATGPT-5-1-B2-Ec15.md §1 (referee CORRECT; operator 21:50 and 22:25 UTC): choose a deterministic `ε_k → 0` with summable
failure bounds, then Borel-Cantelli. Here the failure events are: at each level `s_i = t 2^{-i}`, `i ≤ k`, the uniform error
`sup_{B_ρ} |w̄^ε_{s_i} - (c₀/6) w_{s_i}|` exceeds `2^{-k}` on `{s_i < T}` (Theorem 4.1, `ConvergenceDivisibleStmt`, Section4.lean:39),
and the cells meeting `B_ρ` have diameter above `ε^{β}`, `β = 1/(2+γ)^2`, with polynomially high probability
(`CellSizeEstimateStmt`, Section2.lean:131, with `ζ = 1/(2+γ)^2`). Conclusion: a.s., for all large `k`, on `{t < T}`, every
level `s_i`, `i ≤ k`, has error at most `2^{-k}` and every cell meeting `B_ρ` has diameter at most `2^{-k}`.
No measurable threshold is selected.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology HarmonicBalls
open scoped ENNReal

/-- **B2 almost-sure errors and cells** (CHATGPT-5-1-B2-Ec15.md §1): see the module docstring. -/
theorem exists_subseq_errors_cells_eventually {𝒮 : SpaceFillingSLEModel}
    (hConv : ConvergenceDivisibleStmt 𝒮) (hCell : CellSizeEstimateStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    {t : ℝ} (ht : 0 < t) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → ∀ᶠ k in atTop,
        (∀ i ≤ k, ∀ x ∈ ball (0 : ℂ) ρ,
          |rescaledMatedLeastSupersolution S ρ (t * (1 / 2) ^ i) (ε k) ω x -
            S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 (t * (1 / 2) ^ i) x| ≤ (2⁻¹ : ℝ) ^ k) ∧
        (∀ z : ℤ, (cell (ε k) (S.η ω) z ∩ ball (0 : ℂ) ρ).Nonempty →
          diam (cell (ε k) (S.η ω) z) ≤ (2⁻¹ : ℝ) ^ k) := by
  have hβ : (0 : ℝ) < 1 / (2 + γ) ^ 2 := div_pos one_pos (pow_pos (by linarith) 2)
  have hβ1 : 1 / (2 + γ) ^ 2 < 1 :=
    (div_lt_one (pow_pos (by linarith : (0 : ℝ) < 2 + γ) 2)).2 (by nlinarith)
  have hexp : 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 := by ring
  -- the good-cell event with the exponent `β = 1/(2+γ)^2`
  let E : ℝ → Set Ω := fun ε => {ω | ∀ z : ℤ, (cell ε (S.η ω) z ∩ ball (0 : ℂ) ρ).Nonempty →
    diam (cell ε (S.η ω) z) ≤ ε ^ (1 / (2 + γ) ^ 2)}
  have hpoly := hCell γ hγ0 hγ2 (1 / (2 + γ) ^ 2) ρ hβ hβ1 hρ0 hρ1 Ω S hS
  have hcellC : Tendsto (fun ε => S.P (E ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_compl_of_polyHighProb hpoly) (Eventually.of_forall fun _ => zero_le) ?_
    refine Eventually.of_forall fun ε => measure_mono fun ω hω hD => hω fun z hz => ?_
    have h2 := (hD z hz).2
    rw [hexp] at h2
    exact h2
  have hβlim : Tendsto (fun ε : ℝ => ε ^ (1 / (2 + γ) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : ContinuousAt (fun ε : ℝ => ε ^ (1 / (2 + γ) ^ 2)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr hβ.le)
    have h1 : Tendsto (fun ε : ℝ => ε ^ (1 / (2 + γ) ^ 2)) (𝓝[>] 0)
        (𝓝 ((0 : ℝ) ^ (1 / (2 + γ) ^ 2))) :=
      h0.tendsto.mono_left nhdsWithin_le_nhds
    rwa [Real.zero_rpow hβ.ne'] at h1
  -- cell bad events: the complement of the good cell event, plus the (eventually empty) size event
  let cellBad : ℕ → ℝ → Set Ω := fun k ε =>
    (E ε)ᶜ ∪ {ω | (2⁻¹ : ℝ) ^ k < ε ^ (1 / (2 + γ) ^ 2)}
  have hcellBad : ∀ k : ℕ, Tendsto (fun ε => S.P (cellBad k ε)) (𝓝[>] 0) (𝓝 0) := by
    intro k
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (1 / (2 + γ) ^ 2) < (2⁻¹ : ℝ) ^ k :=
      hβlim.eventually (gt_mem_nhds (pow_pos (by norm_num) k))
    have hcongr : ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P (E ε)ᶜ = S.P (cellBad k ε) := by
      filter_upwards [hev] with ε hε
      have hempty : {ω : Ω | (2⁻¹ : ℝ) ^ k < ε ^ (1 / (2 + γ) ^ 2)} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun ω hω => (not_lt.2 hε.le) hω
      simp only [cellBad, hempty, union_empty]
    exact Tendsto.congr' hcongr hcellC
  -- error bad events at level `t 2^{-i}` with threshold `2^{-k}`
  let errSet : ℕ → ℕ → ℝ → Set Ω := fun i k ε =>
    {ω | t * (1 / 2) ^ i < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
      (2⁻¹ : ℝ) ^ k < |rescaledMatedLeastSupersolution S ρ (t * (1 / 2) ^ i) ε ω x -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 (t * (1 / 2) ^ i) x|}
  have hlevel : ∀ i : ℕ, 0 < t * (1 / 2 : ℝ) ^ i := fun i => mul_pos ht (pow_pos (by norm_num) i)
  have herr : ∀ k : ℕ, ∀ i ≤ k, Tendsto (fun ε => S.P (errSet i k ε)) (𝓝[>] 0) (𝓝 0) :=
    fun k i _ => hConv γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS Λ hΛ (t * (1 / 2) ^ i) (hlevel i)
      ((2⁻¹ : ℝ) ^ k) (pow_pos (by norm_num) k)
  -- the bad event at index `k` and the Borel-Cantelli subsequence
  let Bad : ℝ → ℕ → Set Ω := fun ε k => (⋃ i ∈ Finset.range (k + 1), errSet i k ε) ∪ cellBad k ε
  have hbad : ∀ k : ℕ, Tendsto (fun ε => S.P (Bad ε k)) (𝓝[>] 0) (𝓝 0) := by
    intro k
    have h1 := (tendsto_measure_biUnion_range_zero (fun i ε => errSet i k ε) k
      (fun i hi => herr k i hi)).add (hcellBad k)
    rw [add_zero] at h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun ε => ?_)
    exact measure_union_le _ _
  obtain ⟨ε, hpos, hlim, hae⟩ := exists_subseq_ae_eventually_good Bad hbad
  refine ⟨ε, hpos, hlim, ?_⟩
  filter_upwards [hae] with ω hω hT
  filter_upwards [hω] with k hk
  have hnotErr : ω ∉ ⋃ i ∈ Finset.range (k + 1), errSet i k (ε k) := fun h => hk (mem_union_left _ h)
  have hnotCell : ω ∉ cellBad k (ε k) := fun h => hk (mem_union_right _ h)
  have hE : ω ∈ E (ε k) := by
    by_contra hnot
    exact hnotCell (mem_union_left _ hnot)
  have hE' : ∀ z : ℤ, (cell (ε k) (S.η ω) z ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (cell (ε k) (S.η ω) z) ≤ (ε k) ^ (1 / (2 + γ) ^ 2) := hE
  refine ⟨fun i hi x hx => ?_, fun z hz => ?_⟩
  · by_contra hlt
    have hlt' : (2⁻¹ : ℝ) ^ k < |rescaledMatedLeastSupersolution S ρ (t * (1 / 2) ^ i) (ε k) ω x -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 (t * (1 / 2) ^ i) x| := not_le.1 hlt
    have htime : t * (1 / 2) ^ i < clusterExitTime (Λ ω) ρ :=
      lt_of_le_of_lt (mul_le_of_le_one_right ht.le (pow_le_one₀ (by norm_num) (by norm_num))) hT
    exact hnotErr (mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le hi), htime, x, hx, hlt'⟩)
  · have hsmall : ¬ ((2⁻¹ : ℝ) ^ k < (ε k) ^ (1 / (2 + γ) ^ 2)) := fun h => hnotCell (mem_union_right _ h)
    exact (hE' z hz).trans (not_lt.1 hsmall)

end MatedCRT.S5c
