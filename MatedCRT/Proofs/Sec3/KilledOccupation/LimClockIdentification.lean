import MatedCRT.LPStaging.Prob.CauchyInProbabilitySubseq

/-!
# Identification of the limit clock: Borel-Cantelli transfer from a product measure

Let `P` be a measure on `Ω`, `Q` a measure on `Z`, and `ψ : Ω → Y` measurable. The image `M` of `P ⊗ Q` under
`(ω, b) ↦ (ψ ω, b)` is the joint law of the field and the path. If the events `{ofReal ((1/2)^k) < D k}` have `M`-mass at
most `ofReal ((1/2)^k)`, the first Borel-Cantelli lemma (`LatticeProb.ae_eventually_le_of_prob_le`) gives `M`-almost
every point eventually below the level, and Fubini for the product measure (`Measure.ae_ae_of_ae_prod`) gives the
statement for `P`-almost every `ω` and `Q`-almost every `b`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- Borel-Cantelli transfer from the image `((P ⊗ Q).map fun p ↦ (ψ p.1, p.2))` of a product measure: if the
`k`-th events have mass at most `(1/2)^k`, then for `P`-almost every `ω` and `Q`-almost every `b`, `D k (ψ ω, b)`
is eventually at most `(1/2)^k`. -/
theorem ae_ae_eventually_le_of_map_prob_le {Ω Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [MeasurableSpace Z] (P : Measure Ω) (Q : Measure Z) [SFinite Q] (ψ : Ω → Y) (hψ : Measurable ψ)
    (D : ℕ → Y × Z → ℝ≥0∞)
    (hD : ∀ k, ((P.prod Q).map fun p : Ω × Z => (ψ p.1, p.2)) {x | ENNReal.ofReal ((1 / 2) ^ k) < D k x}
        ≤ ENNReal.ofReal ((1 / 2) ^ k)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, ∀ᶠ k in atTop, D k (ψ ω, b) ≤ ENNReal.ofReal ((1 / 2) ^ k) := by
  have hf : Measurable fun p : Ω × Z => (ψ p.1, p.2) :=
    (hψ.comp measurable_fst).prodMk measurable_snd
  have h1 : ∀ᵐ x ∂((P.prod Q).map fun p : Ω × Z => (ψ p.1, p.2)),
      ∀ᶠ k in atTop, D k x ≤ ENNReal.ofReal ((1 / 2) ^ k) :=
    LatticeProb.ae_eventually_le_of_prob_le _ D hD
  have h2 : ∀ᵐ p ∂(P.prod Q), ∀ᶠ k in atTop, D k (ψ p.1, p.2) ≤ ENNReal.ofReal ((1 / 2) ^ k) :=
    ae_of_ae_map hf.aemeasurable h1
  exact Measure.ae_ae_of_ae_prod h2

/-- Choice of a strictly increasing subsequence `k` along which, for `μ`-almost every `x`, eventually in `j` the point
`x` avoids the `j`-th event `E (k j) j`: the event `E (k j) j` is chosen with mass at most `(1/2)^j`, and the first
Borel-Cantelli lemma (`MeasureTheory.ae_eventually_notMem`) gives the conclusion. -/
theorem exists_strictMono_ae_eventually_notMem {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (E : ℕ → ℕ → Set X) (h : ∀ j : ℕ, Tendsto (fun k => μ (E k j)) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ x ∂μ, ∀ᶠ j in atTop, x ∉ E (k j) j := by
  have hN : ∀ j : ℕ, ∃ N : ℕ, ∀ m ≥ N, μ (E m j) < ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
    intro j
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
      rw [ENNReal.ofReal_pos]; positivity
    exact eventually_atTop.1 ((h j).eventually (gt_mem_nhds hpos))
  choose N hN using hN
  have hstrict : StrictMono fun j : ℕ => j + ∑ i ∈ Finset.range (j + 1), N i := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    have h1 := Finset.sum_range_succ N (j + 1)
    show j + ∑ i ∈ Finset.range (j + 1), N i < j + 1 + ∑ i ∈ Finset.range (j + 1 + 1), N i
    omega
  have hge : ∀ j : ℕ, N j ≤ j + ∑ i ∈ Finset.range (j + 1), N i := fun j => by
    have : N j ≤ ∑ i ∈ Finset.range (j + 1), N i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.self_mem_range_succ j)
    omega
  have hbd : ∀ j : ℕ, μ (E (j + ∑ i ∈ Finset.range (j + 1), N i) j) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) :=
    fun j => (hN j _ (hge j)).le
  have hgeom : ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ≠ ∞ := by
    have hr : ENNReal.ofReal (1 / 2) < 1 := by
      rw [ENNReal.ofReal_lt_one]; norm_num
    simp_rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'
  refine ⟨fun j => j + ∑ i ∈ Finset.range (j + 1), N i, hstrict, ?_⟩
  have hsum : ∑' j : ℕ, μ (E (j + ∑ i ∈ Finset.range (j + 1), N i) j) ≠ ∞ :=
    ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum hbd)
  exact ae_eventually_notMem hsum

/-- A real sequence whose consecutive gaps are eventually at most `(1/2)^m` and which converges along a subsequence
converges: the shifted sequence is Cauchy (geometric gaps), so it converges to the limit of the subsequence. -/
theorem tendsto_of_subseq_of_gap_le_geometric_two {x : ℕ → ℝ} {L : ℝ} {k : ℕ → ℕ} (hk : StrictMono k)
    (hgap : ∀ᶠ m in atTop, |x m - x (m + 1)| ≤ (1 / 2 : ℝ) ^ m)
    (hsub : Tendsto (fun j => x (k j)) atTop (𝓝 L)) : Tendsto x atTop (𝓝 L) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hgap
  have hcauchy : CauchySeq fun m => x (m + N) := by
    refine cauchySeq_of_le_geometric_two (C := 2) fun m => ?_
    show dist (x (m + N)) (x (m + 1 + N)) ≤ 2 / 2 / 2 ^ m
    rw [Real.dist_eq, show m + 1 + N = m + N + 1 by omega]
    have h1 := hN (m + N) (by omega)
    have h2 : (1 / 2 : ℝ) ^ (m + N) ≤ (1 / 2 : ℝ) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h3 : (2 : ℝ) / 2 / 2 ^ m = (1 / 2 : ℝ) ^ m := by
      rw [div_pow, one_pow]; ring
    rw [h3]
    exact h1.trans h2
  have hlim : Tendsto (fun m => x (m + N)) atTop (𝓝 L) := by
    have hf : Tendsto (fun j => k j - N) atTop atTop :=
      tendsto_atTop_mono (fun j => by show j - N ≤ k j - N; have h : j ≤ k j := hk.id_le j; omega) (tendsto_sub_atTop_nat N)
    have ha : Tendsto ((fun m => x (m + N)) ∘ fun j => k j - N) atTop (𝓝 L) := by
      refine hsub.congr' ?_
      filter_upwards [hk.tendsto_atTop.eventually_ge_atTop N] with j hj
      simp only [Function.comp]
      rw [Nat.sub_add_cancel hj]
    exact tendsto_nhds_of_cauchySeq_of_subseq hcauchy hf ha
  exact (tendsto_add_atTop_iff_nat N).1 hlim

end MatedCRT.KilledOccupation

#print axioms MatedCRT.KilledOccupation.ae_ae_eventually_le_of_map_prob_le
#print axioms MatedCRT.KilledOccupation.exists_strictMono_ae_eventually_notMem
#print axioms MatedCRT.KilledOccupation.tendsto_of_subseq_of_gap_le_geometric_two
