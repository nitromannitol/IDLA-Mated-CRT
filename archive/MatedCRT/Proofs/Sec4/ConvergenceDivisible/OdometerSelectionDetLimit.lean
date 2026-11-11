import MatedCRT.Proofs.Sec4.ConvergenceDivisible.OdometerSelectionHolder

/-! # Limits of the selected subsequence in a Hölder class

From a uniform Cauchy bound `2 (1/2)^k` on `K` (indices at least `k+1`) and centres `c k` in a Hölder class with
`|u_{k+1} - c_k| ≤ (1/2)^k` on `K`, the sequence `u` converges uniformly on `K` to a limit `g`, the centres
converge to `g`, and `g` lies in the same Hölder class (`HolderClassOn`), hence is Hölder continuous. -/

namespace MatedCRT

open Set Metric Filter Topology

lemma holderExp_le_one (j : ℕ) : holderExp j ≤ 1 := by
  unfold holderExp
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

/-- A Hölder class function on `K` is `IsHolderContinuousOn` with the class exponent. -/
lemma isHolderContinuousOn_of_holderClassOn {K : Set ℂ} {g : ℂ → ℝ} {m j : ℕ}
    (hg : HolderClassOn K (m : ℝ) (holderExp j) g) : IsHolderContinuousOn g K := by
  obtain ⟨_, hH⟩ := hg
  have hα := holderExp_pos j
  refine ⟨((m : ℝ)).toNNReal, ⟨holderExp j, hα.le⟩, ?_, ?_, ?_⟩
  · show (0 : ℝ) < holderExp j
    exact hα
  · show holderExp j ≤ 1
    exact holderExp_le_one j
  · intro x hx y hy
    have h1 := hH x hx y hy
    have hr : ENNReal.ofReal ((m : ℝ) * dist x y ^ holderExp j) =
        (((m : ℝ)).toNNReal : ENNReal) * edist x y ^ holderExp j := by
      rw [ENNReal.ofReal_mul (by positivity), edist_dist,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le]
      rfl
    show edist (g x) (g y) ≤ (((m : ℝ)).toNNReal : ENNReal) * edist x y ^ holderExp j
    calc edist (g x) (g y) = ENNReal.ofReal |g x - g y| := by rw [edist_dist, Real.dist_eq]
      _ ≤ ENNReal.ofReal ((m : ℝ) * dist x y ^ holderExp j) := ENNReal.ofReal_le_ofReal h1
      _ = _ := hr

lemma pow_half_eventually_small {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, 2 * (1 / 2 : ℝ) ^ k < ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨k, by linarith⟩

/-- A uniformly Cauchy-on-`K` sequence with dyadic bounds has a uniform limit `g` on `K`, with the same
dyadic bounds against `g`. -/
lemma exists_limit_of_cauchy {K : Set ℂ} (u : ℕ → ℂ → ℝ)
    (hcau : ∀ k ℓ ℓ', k + 1 ≤ ℓ → k + 1 ≤ ℓ' → ∀ x ∈ K, |u ℓ x - u ℓ' x| ≤ 2 * (1 / 2 : ℝ) ^ k) :
    ∃ g : ℂ → ℝ, (∀ k ℓ, k + 1 ≤ ℓ → ∀ x ∈ K, |u ℓ x - g x| ≤ 2 * (1 / 2 : ℝ) ^ k) ∧
      TendstoUniformlyOn u g atTop K := by
  have hlim : ∀ x : ℂ, ∃ L : ℝ, x ∈ K → Tendsto (fun ℓ => u ℓ x) atTop (𝓝 L) := by
    intro x
    by_cases hx : x ∈ K
    · have hcs : CauchySeq (fun ℓ => u ℓ x) := by
        rw [Metric.cauchySeq_iff']
        intro ε hε
        obtain ⟨k, hk⟩ := pow_half_eventually_small hε
        refine ⟨k + 1, fun ℓ hℓ => ?_⟩
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (hcau k ℓ (k + 1) hℓ le_rfl x hx) hk
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
      exact ⟨L, fun _ => hL⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose g hg using hlim
  have hbound : ∀ k ℓ, k + 1 ≤ ℓ → ∀ x ∈ K, |u ℓ x - g x| ≤ 2 * (1 / 2 : ℝ) ^ k := by
    intro k ℓ hℓ x hx
    have ht : Tendsto (fun ℓ' => |u ℓ x - u ℓ' x|) atTop (𝓝 |u ℓ x - g x|) :=
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => u ℓ x) atTop (𝓝 (u ℓ x))).sub
        (hg x hx)).abs
    refine le_of_tendsto ht ?_
    exact Filter.eventually_atTop.2 ⟨k + 1, fun ℓ' hℓ' => hcau k ℓ ℓ' hℓ hℓ' x hx⟩
  refine ⟨g, hbound, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := pow_half_eventually_small hε
  refine Filter.eventually_atTop.2 ⟨k + 1, fun ℓ hℓ x hx => ?_⟩
  have h := hbound k ℓ hℓ x hx
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-- The centres converge to the limit at the dyadic rate. -/
lemma tendsto_centers {K : Set ℂ} {u : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {c : ℕ → ℂ → ℝ}
    (hb : ∀ k ℓ, k + 1 ≤ ℓ → ∀ x ∈ K, |u ℓ x - g x| ≤ 2 * (1 / 2 : ℝ) ^ k)
    (hc : ∀ k, ∀ x ∈ K, |u (k + 1) x - c k x| ≤ (1 / 2 : ℝ) ^ k) :
    ∀ x ∈ K, Tendsto (fun k => c k x) atTop (𝓝 (g x)) := by
  intro x hx
  have hlim : Tendsto (fun k : ℕ => 3 * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 3
    simpa using h
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hlim
  rw [Real.dist_eq]
  have h1 := hc k x hx
  have h1' : |c k x - u (k + 1) x| ≤ (1 / 2 : ℝ) ^ k := by
    rw [abs_sub_comm]
    exact h1
  have h2 := hb k (k + 1) le_rfl x hx
  have htri := abs_sub_le (c k x) (u (k + 1) x) (g x)
  linarith

/-- The uniform limit of the selected subsequence lies in the Hölder class of the centres. -/
lemma holder_limit_of_centers {K : Set ℂ} {u : ℕ → ℂ → ℝ} {c : ℕ → ℂ → ℝ} {m j : ℕ}
    (hcau : ∀ k ℓ ℓ', k + 1 ≤ ℓ → k + 1 ≤ ℓ' → ∀ x ∈ K, |u ℓ x - u ℓ' x| ≤ 2 * (1 / 2 : ℝ) ^ k)
    (hc : ∀ k, ∀ x ∈ K, |u (k + 1) x - c k x| ≤ (1 / 2 : ℝ) ^ k)
    (hcls : ∀ k, HolderClassOn K (m : ℝ) (holderExp j) (c k)) :
    ∃ g : ℂ → ℝ, ContinuousOn g K ∧ IsHolderContinuousOn g K ∧ TendstoUniformlyOn u g atTop K := by
  obtain ⟨g, hb, hu⟩ := exists_limit_of_cauchy u hcau
  have hconv := tendsto_centers hb hc
  have hG : HolderClassOn K (m : ℝ) (holderExp j) g := holderClassOn_of_tendsto hcls hconv
  exact ⟨g, holderClassOn_continuousOn (holderExp_pos j) hG,
    isHolderContinuousOn_of_holderClassOn hG, hu⟩

end MatedCRT
