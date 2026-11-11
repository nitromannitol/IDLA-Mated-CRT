import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxClockSubsequence

/-!
# Lemma 3.4: a joint Borel–Cantelli subsequence of approximate clocks

`exists_strictMono_joint_cauchy` extracts a strictly increasing subsequence `φ` that is **independent of the point**
of the measure space: for `μ`-almost every point `p` the approximations `G (φ j) p` converge at every rational time.
The hypothesis is the joint convergence in measure of the family `G k` on the events
`{∃ q ∈ ℚ≥0 ∩ [0, T], η ≤ |G k p q - G l p q|}` as `(k, l) → ∞` in `ℕ × ℕ`.

This is the device that gives a jointly measurable limit of the approximate Liouville clocks in the environment and
the Brownian path (the measurability of the truncated occupations, `LBMTruncatedOccupationMeasurableStep`). The
subsequence is chosen once for the product measure, so its limit is a measurable function of `(ω, b)`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

/-- **Joint Cauchy subsequence.** If the events `{∃ q ∈ ℚ≥0 ∩ [0, T], η ≤ |G k p q - G l p q|}` have measure tending to
zero as `(k, l) → ∞` in `ℕ × ℕ` for every `T ∈ ℕ` and `η > 0`, then there is a strictly increasing `φ : ℕ → ℕ` such
that, for `μ`-almost every `p`, the sequence `j ↦ G (φ j) p q` is Cauchy for every rational time `q ≥ 0`.
Proof: choose thresholds `N j` with `μ (A j k l) < 2⁻¹ ^ j` for `k, l ≥ N j`; take `φ j ≥ N j` strictly increasing, so
that the consecutive events `D j = A j (φ j) (φ (j+1))` have summable measures; Borel–Cantelli gives that a.e. point
lies in only finitely many `D j`, and this yields eventually small consecutive differences at each rational time. -/
theorem exists_strictMono_joint_cauchy {β : Type*} [MeasurableSpace β] (μ : Measure β)
    (G : ℕ → β → ℝ≥0 → ℝ)
    (hconv : ∀ (T : ℕ) (η : ℝ), 0 < η →
      Tendsto (fun kl : ℕ × ℕ => μ {p | ∃ q : ℚ≥0, (q : ℝ) ≤ T ∧
        η ≤ |G kl.1 p (q : ℝ≥0) - G kl.2 p (q : ℝ≥0)|}) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ p ∂μ, ∀ q : ℚ≥0, CauchySeq (fun j => G (φ j) p (q : ℝ≥0)) := by
  have hεpos : ∀ j : ℕ, (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ j := fun j =>
    ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) j
  have hAε : ∀ j : ℕ, ∀ᶠ kl : ℕ × ℕ in atTop,
      μ {p | ∃ q : ℚ≥0, (q : ℝ) ≤ j ∧ (1 / 2 : ℝ) ^ j ≤ |G kl.1 p (q : ℝ≥0) - G kl.2 p (q : ℝ≥0)|}
        < (2⁻¹ : ℝ≥0∞) ^ j := fun j =>
    (hconv j ((1 / 2 : ℝ) ^ j) (by positivity)).eventually (gt_mem_nhds (hεpos j))
  have hN : ∀ j : ℕ, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N,
      μ {p | ∃ q : ℚ≥0, (q : ℝ) ≤ j ∧ (1 / 2 : ℝ) ^ j ≤ |G k p (q : ℝ≥0) - G l p (q : ℝ≥0)|}
        < (2⁻¹ : ℝ≥0∞) ^ j := by
    intro j
    obtain ⟨⟨a, b⟩, h⟩ := Filter.eventually_atTop.1 (hAε j)
    exact ⟨max a b, fun k hk l hl => h (k, l)
      (Prod.mk_le_mk.2 ⟨(le_max_left a b).trans hk, (le_max_right a b).trans hl⟩)⟩
  choose N hN using hN
  -- the subsequence `M j ≥ N j`, strictly increasing
  let M : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup N + j
  have hMlt : ∀ j, M j < M (j + 1) := by
    intro j
    have hsup : (Finset.range (j + 1)).sup N ≤ (Finset.range (j + 1 + 1)).sup N :=
      Finset.sup_mono (Finset.range_mono (Nat.le_succ (j + 1)))
    simp only [M]
    omega
  have hMN : ∀ j, N j ≤ M j := by
    intro j
    have hle : N j ≤ (Finset.range (j + 1)).sup N :=
      Finset.le_sup (f := N) (Finset.mem_range.2 (Nat.lt_succ_self j))
    simp only [M]
    omega
  -- the consecutive bad events along the subsequence
  let D : ℕ → Set β := fun j => {p | ∃ q : ℚ≥0, (q : ℝ) ≤ j ∧
      (1 / 2 : ℝ) ^ j ≤ |G (M j) p (q : ℝ≥0) - G (M (j + 1)) p (q : ℝ≥0)|}
  have hDμ : ∀ j, μ (D j) ≤ (2⁻¹ : ℝ≥0∞) ^ j := fun j =>
    (hN j (M j) (hMN j) (M (j + 1)) ((hMN j).trans (hMlt j).le)).le
  have hsum : ∑' j, μ (D j) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hDμ)
    simp [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
  refine ⟨M, strictMono_nat_of_lt_succ hMlt, ?_⟩
  filter_upwards [ae_eventually_notMem hsum] with p hp
  intro q
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hp
  obtain ⟨J', hJ'⟩ : ∃ J' : ℕ, J' = max J ⌈(q : ℝ)⌉₊ := ⟨_, rfl⟩
  have hJJ : J ≤ J' := by rw [hJ']; exact le_max_left _ _
  have hJc : ⌈(q : ℝ)⌉₊ ≤ J' := by rw [hJ']; exact le_max_right _ _
  -- eventually the consecutive differences at the rational time `q` are below `(1/2)^j`
  have hdiff : ∀ j, J' ≤ j →
      dist (G (M j) p (q : ℝ≥0)) (G (M (j + 1)) p (q : ℝ≥0)) < (1 / 2 : ℝ) ^ j := by
    intro j hj
    have hqj : (q : ℝ) ≤ j := by
      have h1 : (q : ℝ) ≤ ⌈(q : ℝ)⌉₊ := Nat.le_ceil _
      have h2 : ⌈(q : ℝ)⌉₊ ≤ j := le_trans hJc hj
      exact h1.trans (by exact_mod_cast h2)
    have hnot := hJ j (le_trans hJJ hj)
    simp only [D, Set.mem_ofPred_eq, not_exists, not_and, not_le] at hnot
    rw [Real.dist_eq]
    exact hnot q hqj
  have hcauchy : CauchySeq (fun n => G (M (n + J')) p (q : ℝ≥0)) := by
    refine cauchySeq_of_le_geometric (C := (1 / 2 : ℝ) ^ J') (r := 1 / 2) (by norm_num) ?_
    intro n
    have h := hdiff (n + J') (by omega)
    have e : n + 1 + J' = n + J' + 1 := by omega
    simp only [e]
    calc dist (G (M (n + J')) p (q : ℝ≥0)) (G (M (n + J' + 1)) p (q : ℝ≥0))
        ≤ (1 / 2 : ℝ) ^ (n + J') := h.le
      _ = (1 / 2 : ℝ) ^ J' * (1 / 2 : ℝ) ^ n := by ring
  exact (cauchySeq_shift (u := fun j => G (M j) p (q : ℝ≥0)) J').1 hcauchy

/-- **Identification of an almost sure limit with an in-measure limit.** Let `a j` be measurable and converge
almost everywhere to a measurable `L`, and let `F` be an arbitrary function (not assumed measurable) such that
`a j` converges to `F` in outer measure: `Q {b | η ≤ |a j b - F b|} → 0` for every `η > 0`. Then `L = F` almost
everywhere. This identifies the limit of the approximate clocks with the clock itself, the clock being only
characterised by convergence in probability (`IsLQGClock`). -/
theorem ae_eq_of_ae_tendsto_of_outer {β : Type*} [MeasurableSpace β] (Q : Measure β) [IsFiniteMeasure Q]
    (a : ℕ → β → ℝ) (L F : β → ℝ) (ha : ∀ j, Measurable (a j)) (hL : Measurable L)
    (hlim : ∀ᵐ b ∂Q, Tendsto (fun j => a j b) atTop (𝓝 (L b)))
    (hF : ∀ η : ℝ, 0 < η → Tendsto (fun j => Q {b | η ≤ |a j b - F b|}) atTop (𝓝 0)) :
    ∀ᵐ b ∂Q, L b = F b := by
  have hnull : ∀ η : ℝ, 0 < η → Q {b | η ≤ |L b - F b|} = 0 := by
    intro η hη
    -- `E J`: the points where some `a j`, `j ≥ J`, is at distance at least `η/2` from `L`
    let E : ℕ → Set β := fun J => ⋃ j : ℕ, ⋃ (_ : J ≤ j), {b | η / 2 ≤ |a j b - L b|}
    have hEmeas : ∀ J, MeasurableSet (E J) := fun J =>
      MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
        measurableSet_le measurable_const (((ha j).sub hL).abs)
    have hEanti : Antitone E := by
      intro J J' hJJ' b hb
      simp only [E, Set.mem_iUnion, exists_prop, Set.mem_ofPred_eq] at hb ⊢
      obtain ⟨j, hj, hbj⟩ := hb
      exact ⟨j, le_trans hJJ' hj, hbj⟩
    have hEnull : Q (⋂ J, E J) = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hlim)
      intro b hb hT
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hT (η / 2) (half_pos hη)
      have hbN := Set.mem_iInter.1 hb N
      simp only [E, Set.mem_iUnion, exists_prop, Set.mem_ofPred_eq] at hbN
      obtain ⟨j, hj, hbj⟩ := hbN
      have hdist := hN j hj
      rw [Real.dist_eq] at hdist
      linarith
    have hEtend : Tendsto (fun J => Q (E J)) atTop (𝓝 0) := by
      have h := tendsto_measure_iInter_atTop (μ := Q) (fun J => (hEmeas J).nullMeasurableSet) hEanti
        ⟨0, measure_ne_top Q _⟩
      rw [hEnull] at h
      exact h
    have hbound : ∀ j : ℕ, Q {b | η ≤ |L b - F b|} ≤ Q {b | η / 2 ≤ |a j b - F b|} + Q (E j) := by
      intro j
      have hsub : {b | η ≤ |L b - F b|} ⊆ {b | η / 2 ≤ |a j b - F b|} ∪ E j := by
        intro b hb
        by_cases hbE : b ∈ E j
        · exact Or.inr hbE
        · left
          have h1 : |a j b - L b| < η / 2 := by
            by_contra hcon
            replace hcon := not_lt.1 hcon
            exact hbE (by simp only [E, Set.mem_iUnion, exists_prop, Set.mem_ofPred_eq]
                          exact ⟨j, le_rfl, hcon⟩)
          have htri := abs_sub_le (L b) (a j b) (F b)
          rw [abs_sub_comm (L b) (a j b)] at htri
          simp only [Set.mem_ofPred_eq] at hb ⊢
          linarith
      exact (measure_mono hsub).trans (measure_union_le _ _)
    have hsum0 : Tendsto (fun j => Q {b | η / 2 ≤ |a j b - F b|} + Q (E j)) atTop (𝓝 0) := by
      simpa using (hF (η / 2) (half_pos hη)).add hEtend
    exact le_antisymm (ge_of_tendsto hsum0 (Eventually.of_forall fun j => hbound j)) zero_le
  have key : ∀ n : ℕ, Q {b | 1 / ((n : ℝ) + 1) ≤ |L b - F b|} = 0 := fun n =>
    hnull _ (by positivity)
  refine ae_iff.2 (measure_mono_null ?_ (measure_iUnion_null fun n => key n))
  intro b hb
  simp only [Set.mem_ofPred_eq] at hb
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 hb))
  exact Set.mem_iUnion.2 ⟨n, le_of_lt hn⟩

end MatedCRT
