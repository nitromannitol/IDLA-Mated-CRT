import Mathlib

/-!
# An adapted version of a limit in probability, valid for every starting point

Let `P z` be a family of laws on a path space with a filtration `ℱ t`, let `A n t` be `ℱ t`-measurable
processes with continuous paths, and let `F` be a *raw* process (no measurability whatever) which is the
limit in `P z`-probability, uniformly on every compact time interval, of `A n`, for every start `z`.
Then there is an adapted process `G`, defined without reference to `z`, with `G t = F · t` for all `t`
`P z`-almost surely, for every `z`.

The construction is the diagonal subsequence of Borel–Cantelli type: for each `j` the index `n_j(z)` is
the least admissible threshold of the (Borel in `z`) quantities `P z {sup_{t ≤ j} |A n - A m| > 2^{-j}}`,
and `G t b = lim_j A_{n_j(b 0)} b t`; since `b 0` is `ℱ 0`-measurable, `G t` is `ℱ t`-measurable, and
under `P z`, `b 0 = z` almost surely, so `G` is the almost sure limit of a fixed subsequence.

The statement is stated for outer measures (no measurability of `F` is used).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT.AdaptedVersion

section Aux

variable {Ω' : Type*}

theorem measurable_limUnder_nat {m : MeasurableSpace Ω'} {f : ℕ → Ω' → ℝ}
    (hf : ∀ j, Measurable (f j)) :
    Measurable (fun b => limUnder atTop (fun j => f j b)) :=
  (StronglyMeasurable.limUnder (l := atTop) (f := f) (fun j => (hf j).stronglyMeasurable)).measurable

theorem measurable_apply_index {m : MeasurableSpace Ω'} {g : Ω' → ℕ} (hg : Measurable g)
    {f : ℕ → Ω' → ℝ} (hf : ∀ k, Measurable (f k)) : Measurable (fun b => f (g b) b) := by
  have h : Measurable (fun p : Ω' × ℕ => f p.2 p.1) :=
    measurable_from_prod_countable_left (fun k => hf k)
  exact h.comp (measurable_id.prodMk hg)

/-- The nonnegative real number attached to a rational. -/
noncomputable def ratTime (q : ℚ) : ℝ≥0 := Real.toNNReal (q : ℝ)

theorem denseRange_ratTime : DenseRange ratTime :=
  ((Function.Surjective.denseRange (fun x : ℝ≥0 => ⟨(x : ℝ), Real.toNNReal_coe⟩ :
      Function.Surjective Real.toNNReal)).comp Rat.denseRange_cast continuous_real_toNNReal :)

/-- A continuous function bounded by `c` in absolute value at the rational times `≤ j` is bounded by `c` at
all times `≤ j`. -/
theorem abs_le_of_forall_rat {f : ℝ≥0 → ℝ} (hf : Continuous f) {c : ℝ} (j : ℕ)
    (h : ∀ q : ℚ, ratTime q ≤ j → |f (ratTime q)| ≤ c) : ∀ t : ℝ≥0, t ≤ j → |f t| ≤ c := by
  have hcl : IsClosed {t : ℝ≥0 | |f t| ≤ c} := isClosed_le (continuous_abs.comp hf) continuous_const
  have hsub : Iio (j : ℝ≥0) ⊆ closure (Iio (j : ℝ≥0) ∩ range ratTime) :=
    (denseRange_ratTime).open_subset_closure_inter isOpen_Iio
  have hcl2 : closure (Iio (j : ℝ≥0) ∩ range ratTime) ⊆ {t : ℝ≥0 | |f t| ≤ c} := by
    refine closure_minimal ?_ hcl
    rintro _ ⟨hlt, q, rfl⟩
    exact h q (le_of_lt hlt)
  intro t ht
  rcases ht.lt_or_eq with hlt | rfl
  · exact hcl2 (hsub hlt)
  · have := h (j : ℚ) (by simp [ratTime])
    simpa [ratTime] using this

end Aux

section Main

variable {X Ω : Type*} [MeasurableSpace X] [mΩ : MeasurableSpace Ω]

/-- The event that two processes differ by more than `2^{-j}` at a rational time `≤ j`. -/
def ratEvent (A : ℕ → ℝ≥0 → Ω → ℝ) (n m j : ℕ) : Set Ω :=
  ⋃ q : ℚ, {b | ratTime q ≤ j ∧ ((2 : ℝ)⁻¹) ^ j < |A n (ratTime q) b - A m (ratTime q) b|}

theorem measurableSet_ratEvent {A : ℕ → ℝ≥0 → Ω → ℝ} (hA : ∀ n t, Measurable (A n t)) (n m j : ℕ) :
    MeasurableSet (ratEvent A n m j) := by
  refine MeasurableSet.iUnion fun q => ?_
  by_cases hq : ratTime q ≤ j
  · have : {b | ratTime q ≤ j ∧ ((2 : ℝ)⁻¹) ^ j < |A n (ratTime q) b - A m (ratTime q) b|} =
        {b | ((2 : ℝ)⁻¹) ^ j < |A n (ratTime q) b - A m (ratTime q) b|} := by
      ext b; simp [hq]
    rw [this]
    exact measurableSet_lt measurable_const
      (continuous_abs.measurable.comp ((hA n (ratTime q)).sub (hA m (ratTime q))))
  · have : {b | ratTime q ≤ j ∧ ((2 : ℝ)⁻¹) ^ j < |A n (ratTime q) b - A m (ratTime q) b|} = ∅ := by
      ext b; simp [hq]
    rw [this]
    exact MeasurableSet.empty

omit mΩ in
theorem ratEvent_subset {A : ℕ → ℝ≥0 → Ω → ℝ} (F : Ω → ℝ≥0 → ℝ) (n m j : ℕ) :
    ratEvent A n m j ⊆
      {b | ∃ t ≤ (j : ℝ≥0), ((2 : ℝ)⁻¹) ^ j / 2 ≤ |A n t b - F b t|} ∪
      {b | ∃ t ≤ (j : ℝ≥0), ((2 : ℝ)⁻¹) ^ j / 2 ≤ |A m t b - F b t|} := by
  intro b hb
  obtain ⟨q, hq, hlt⟩ := mem_iUnion.1 hb
  have h3 := abs_sub_le (A n (ratTime q) b) (F b (ratTime q)) (A m (ratTime q) b)
  have h4 := abs_sub_comm (F b (ratTime q)) (A m (ratTime q) b)
  by_cases h1 : ((2 : ℝ)⁻¹) ^ j / 2 ≤ |A n (ratTime q) b - F b (ratTime q)|
  · exact Or.inl ⟨ratTime q, hq, h1⟩
  · refine Or.inr ⟨ratTime q, hq, ?_⟩
    push Not at h1
    have hlt' : ((2 : ℝ)⁻¹) ^ j < |A n (ratTime q) b - A m (ratTime q) b| := hlt
    linarith

/-- **An adapted version valid for every start.**  See the module docstring. -/
theorem exists_adapted_version
    (P : Kernel X Ω) (ℱ : ℝ≥0 → MeasurableSpace Ω) (hℱ : ∀ t, ℱ t ≤ mΩ) (hmono : Monotone ℱ)
    (ξ : Ω → X) (hξ : Measurable[ℱ 0] ξ) (hξP : ∀ z, ∀ᵐ b ∂P z, ξ b = z)
    (A : ℕ → ℝ≥0 → Ω → ℝ) (hA : ∀ n t, Measurable[ℱ t] (A n t))
    (hAc : ∀ n b, Continuous fun t => A n t b) (F : Ω → ℝ≥0 → ℝ)
    (hF : ∀ z (T : ℝ≥0) (η : ℝ), 0 < η →
      Tendsto (fun n => P z {b | ∃ t ≤ T, η ≤ |A n t b - F b t|}) atTop (𝓝 0)) :
    ∃ G : ℝ≥0 → Ω → ℝ, (∀ t, Measurable[ℱ t] (G t)) ∧
      ∀ z, ∀ᵐ b ∂P z, ∀ t, G t b = F b t := by
  classical
  have hAm : ∀ n t, Measurable (A n t) := fun n t => (hA n t).mono (hℱ t) le_rfl
  -- thresholds at which the diagonal events are small
  have hev : ∀ z (i : ℕ), ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      P z (ratEvent A n m i) ≤ (2⁻¹ : ℝ≥0∞) ^ i := by
    intro z i
    have hη : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ i / 2 := by positivity
    have ht := ENNReal.tendsto_nhds_zero.1 (hF z i _ hη)
    have hε : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ (i + 1) := ENNReal.pow_pos (by simp) _
    obtain ⟨N, hN⟩ := eventually_atTop.1 (ht _ hε)
    refine ⟨N, fun n hn m hm => ?_⟩
    calc P z (ratEvent A n m i)
        ≤ P z ({b | ∃ t ≤ (i : ℝ≥0), ((2 : ℝ)⁻¹) ^ i / 2 ≤ |A n t b - F b t|} ∪
            {b | ∃ t ≤ (i : ℝ≥0), ((2 : ℝ)⁻¹) ^ i / 2 ≤ |A m t b - F b t|}) :=
          measure_mono (ratEvent_subset F n m i)
      _ ≤ P z {b | ∃ t ≤ (i : ℝ≥0), ((2 : ℝ)⁻¹) ^ i / 2 ≤ |A n t b - F b t|} +
          P z {b | ∃ t ≤ (i : ℝ≥0), ((2 : ℝ)⁻¹) ^ i / 2 ≤ |A m t b - F b t|} := measure_union_le _ _
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ (i + 1) + (2⁻¹ : ℝ≥0∞) ^ (i + 1) := add_le_add (hN n hn) (hN m hm)
      _ = (2⁻¹ : ℝ≥0∞) ^ i := by
          rw [pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
  obtain ⟨Pr, hPr⟩ : ∃ Pr : ℕ → ℕ → X → Prop, ∀ j N z, Pr j N z ↔
      ∀ i ≤ j, ∀ n ≥ N, ∀ m ≥ N, P z (ratEvent A n m i) ≤ (2⁻¹ : ℝ≥0∞) ^ i :=
    ⟨_, fun _ _ _ => Iff.rfl⟩
  have hex : ∀ z j, ∃ N, Pr j N z := by
    intro z j
    choose Nf hNf using hev z
    refine ⟨(Finset.range (j + 1)).sup Nf, (hPr _ _ _).2 fun i hi n hn m hm => hNf i n ?_ m ?_⟩
    · exact le_trans (Finset.le_sup (f := Nf) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) hn
    · exact le_trans (Finset.le_sup (f := Nf) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) hm
  let N₀ : ℕ → X → ℕ := fun j z => Nat.find (hex z j)
  have hN₀spec : ∀ j z, Pr j (N₀ j z) z := fun j z => Nat.find_spec (hex z j)
  have hPr_mono : ∀ j N N' z, N ≤ N' → Pr j N z → Pr j N' z := by
    intro j N N' z h hp
    rw [hPr] at hp ⊢
    intro i hi n hn m hm
    exact hp i hi n (h.trans hn) m (h.trans hm)
  have hN₀le : ∀ j N z, N₀ j z ≤ N ↔ Pr j N z := fun j N z =>
    ⟨fun h => hPr_mono j _ _ z h (hN₀spec j z), fun h => Nat.find_min' (hex z j) h⟩
  have hN₀step : ∀ j z, N₀ j z ≤ N₀ (j + 1) z := by
    intro j z
    refine (hN₀le j _ z).2 ((hPr _ _ _).2 fun i hi => ?_)
    exact ((hPr _ _ _).1 (hN₀spec (j + 1) z)) i (hi.trans (Nat.le_succ j))
  have hN₀meas : ∀ j, Measurable (N₀ j) := by
    intro j
    refine measurable_of_Iic fun N => ?_
    have h1 : N₀ j ⁻¹' Iic N = {z | Pr j N z} := by
      ext z; exact hN₀le j N z
    have h2 : {z | Pr j N z} = ⋂ i : ℕ, ⋂ (_ : i ≤ j), ⋂ n : ℕ, ⋂ (_ : n ≥ N), ⋂ m : ℕ, ⋂ (_ : m ≥ N),
        {z | P z (ratEvent A n m i) ≤ (2⁻¹ : ℝ≥0∞) ^ i} := by
      ext z; simp only [hPr, mem_iInter]; rfl
    rw [h1, h2]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun n =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le (Kernel.measurable_coe P (measurableSet_ratEvent hAm n m i))
      measurable_const
  let n : ℕ → X → ℕ := fun j z => N₀ j z + j
  have hnmeas : ∀ j, Measurable (n j) := fun j => (hN₀meas j).add_const j
  have hn_ge : ∀ j z, j ≤ n j z := fun j z => Nat.le_add_left _ _
  -- Borel–Cantelli
  have hBC : ∀ z, ∀ᵐ b ∂P z, ∀ᶠ j in atTop, b ∉ ratEvent A (n j z) (n (j + 1) z) j := by
    intro z
    have hbound : ∀ j, P z (ratEvent A (n j z) (n (j + 1) z) j) ≤ (2⁻¹ : ℝ≥0∞) ^ j := by
      intro j
      exact ((hPr _ _ _).1 (hN₀spec j z)) j le_rfl _ (Nat.le_add_right _ _) _
        ((hN₀step j z).trans (Nat.le_add_right _ _))
    have hsum : ∑' j, P z (ratEvent A (n j z) (n (j + 1) z) j) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
      rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.ofNat_ne_top
    have h0 := measure_limsup_atTop_eq_zero hsum
    have h1 : ∀ᵐ b ∂P z, b ∉ limsup (fun j => ratEvent A (n j z) (n (j + 1) z) j) atTop := by
      rw [ae_iff]; simpa using h0
    filter_upwards [h1] with b hb
    rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently] at hb
    exact hb
  have hcauchy : ∀ z b, (∀ᶠ j in atTop, b ∉ ratEvent A (n j z) (n (j + 1) z) j) → ∀ t : ℝ≥0,
      ∃ l, Tendsto (fun j => A (n j z) t b) atTop (𝓝 l) := by
    intro z b hb t
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hb
    set J' := max J ⌈(t : ℝ)⌉₊ with hJ'
    have hstep : ∀ k, |A (n (k + J') z) t b - A (n (k + J' + 1) z) t b| ≤ (2 : ℝ)⁻¹ ^ (k + J') := by
      intro k
      have hk : J ≤ k + J' := le_trans (le_max_left _ _) (Nat.le_add_left _ _)
      have hnot := hJ (k + J') hk
      have htle : t ≤ ((k + J' : ℕ) : ℝ≥0) := by
        have h1 : (t : ℝ) ≤ (⌈(t : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈(t : ℝ)⌉₊ : ℝ) ≤ ((k + J' : ℕ) : ℝ) := by
          exact_mod_cast le_trans (le_max_right _ _) (Nat.le_add_left _ _)
        rw [← NNReal.coe_le_coe]
        simpa using h1.trans h2
      have hq : ∀ q : ℚ, ratTime q ≤ ((k + J' : ℕ) : ℝ≥0) →
          |(fun s => A (n (k + J') z) s b - A (n (k + J' + 1) z) s b) (ratTime q)| ≤
            (2 : ℝ)⁻¹ ^ (k + J') := by
        intro q hq
        by_contra hlt
        push Not at hlt
        exact hnot (mem_iUnion.2 ⟨q, hq, hlt⟩)
      exact abs_le_of_forall_rat (f := fun s => A (n (k + J') z) s b - A (n (k + J' + 1) z) s b)
        ((hAc _ b).sub (hAc _ b)) (k + J') hq t htle
    have hcs : CauchySeq (fun k => A (n (k + J') z) t b) := by
      refine cauchySeq_of_le_geometric_two (C := 2) fun k => ?_
      rw [Real.dist_eq]
      have e : k + 1 + J' = k + J' + 1 := by omega
      have h1 := hstep k
      have h2 : (2 : ℝ)⁻¹ ^ (k + J') ≤ 2 / 2 / 2 ^ k := by
        rw [pow_add, inv_pow, inv_pow]
        have h3 : ((2 : ℝ) ^ J')⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
        calc ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ J')⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = 2 / 2 / 2 ^ k := by field_simp
      rw [e]
      exact h1.trans h2
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete ((cauchySeq_shift (u := fun j => A (n j z) t b) J').1 hcs)
    exact ⟨l, hl⟩
  refine ⟨fun t b => limUnder atTop (fun j => A (n j (ξ b)) t b), ?_, ?_⟩
  · intro t
    have hmeasj : ∀ j, Measurable[ℱ t] (fun b => A (n j (ξ b)) t b) := by
      intro j
      have h1 : Measurable[ℱ t] (n j ∘ ξ) :=
        (hnmeas j).comp (hξ.mono (hmono (show (0 : ℝ≥0) ≤ t from zero_le)) le_rfl)
      exact @measurable_apply_index Ω (ℱ t) (n j ∘ ξ) h1 (fun k b => A k t b) (fun k => hA k t)
    exact @measurable_limUnder_nat Ω (ℱ t) (fun j b => A (n j (ξ b)) t b) hmeasj
  · intro z
    have hlim : ∀ᵐ b ∂P z, ∀ t, Tendsto (fun j => A (n j z) t b) atTop
        (𝓝 (limUnder atTop (fun j => A (n j (ξ b)) t b))) := by
      filter_upwards [hBC z, hξP z] with b hb hξb t
      rw [hξb]
      obtain ⟨l, hl⟩ := hcauchy z b hb t
      rw [hl.limUnder_eq]
      exact hl
    have hnull : ∀ (T : ℝ≥0) (η : ℝ), 0 < η → ∀ᵐ b ∂P z, ∀ t ≤ T,
        |limUnder atTop (fun j => A (n j (ξ b)) t b) - F b t| < η := by
      intro T η hη
      set H : ℕ → Set Ω := fun j => {b | ∃ t ≤ T, η / 2 ≤ |A (n j z) t b - F b t|} with hH
      have hHt : Tendsto (fun j => P z (H j)) atTop (𝓝 0) :=
        (hF z T (η / 2) (by positivity)).comp
          (tendsto_atTop_mono (fun j => hn_ge j z) tendsto_id)
      have hnullH : P z (⋃ J, ⋂ j ≥ J, H j) = 0 := by
        refine measure_iUnion_null fun J => ?_
        refine le_antisymm ?_ zero_le
        exact ge_of_tendsto hHt (eventually_atTop.2 ⟨J, fun j hj =>
          measure_mono (iInter₂_subset j hj)⟩)
      have hN : ∀ᵐ b ∂P z, b ∉ ⋃ J, ⋂ j ≥ J, H j := by
        have hset : {b | ¬ b ∉ ⋃ J, ⋂ j ≥ J, H j} = ⋃ J, ⋂ j ≥ J, H j := Set.ext fun b => not_not
        rw [ae_iff, hset]; exact hnullH
      filter_upwards [hN, hlim] with b hb hlb t ht
      by_contra hge
      push Not at hge
      apply hb
      obtain ⟨J, hJ⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 (hlb t)) (η / 2) (by positivity))
      refine mem_iUnion.2 ⟨J, mem_iInter₂.2 fun j hj => ⟨t, ht, ?_⟩⟩
      have h1 := hJ j hj
      rw [Real.dist_eq] at h1
      have h2 := abs_sub_le (limUnder atTop (fun j => A (n j (ξ b)) t b)) (A (n j z) t b) (F b t)
      have h3 := abs_sub_comm (A (n j z) t b) (limUnder atTop (fun j => A (n j (ξ b)) t b))
      linarith
    have hall : ∀ᵐ b ∂P z, ∀ k : ℕ, ∀ t ≤ (k : ℝ≥0),
        |limUnder atTop (fun j => A (n j (ξ b)) t b) - F b t| < 1 / ((k : ℝ) + 1) := by
      rw [ae_all_iff]
      intro k
      exact hnull k _ (by positivity)
    filter_upwards [hall] with b hb t
    by_contra hne
    have hpos : 0 < |limUnder atTop (fun j => A (n j (ξ b)) t b) - F b t| :=
      abs_pos.2 (sub_ne_zero.2 hne)
    obtain ⟨k, hk⟩ := exists_nat_gt (max (t : ℝ)
      (1 / |limUnder atTop (fun j => A (n j (ξ b)) t b) - F b t|))
    have htk : t ≤ (k : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]
      simpa using ((le_max_left _ _).trans hk.le)
    have h1 := hb k t htk
    have h2 : 1 / |limUnder atTop (fun j => A (n j (ξ b)) t b) - F b t| < k :=
      (le_max_right _ _).trans_lt hk
    have h3 : 1 / ((k : ℝ) + 1) < |limUnder atTop (fun j => A (n j (ξ b)) t b) - F b t| := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at h2
      nlinarith
    linarith

end Main

end MatedCRT.AdaptedVersion
