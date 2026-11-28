import LatticeProb.Prob.CorrelatedBMWindowIndependence
import LatticeProb.Prob.CorrelatedBMIncrementGaussian
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.PathProperties

/-!
# The coordinates of a correlated Brownian pair are monotone on no interval

Let `μ` be the law of a two-sided correlated Brownian pair.  Fix a coordinate `X`, real numbers
`a < b` and `n ≥ 1`, and cut `[a, b]` into `n` intervals of equal length.  The increments of `X`
over these intervals are independent centred Gaussian variables of positive variance (the
coordinate process is Gaussian and increments over intervals with disjoint interiors are
uncorrelated), so each is nonnegative with probability `1 / 2`, and all `n` are nonnegative with
probability `2⁻ⁿ`.  If `X` is monotone on `[a, b]` then all `n` increments are nonnegative; letting
`n → ∞` gives probability zero, and the same holds for antitone `X`.  A union over rational
endpoints shows that almost surely neither coordinate is monotone or antitone on any interval of
positive length.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MatedCRT.PeanosphereTriplePoints

open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2 lrCoord)
open LatticeProb.CorrelatedBM (coneIncr measurable_coneIncr map_coneIncr_eq_gaussianReal
  iIndepFun_increment_windows)

private lemma gaussianReal_Ici_zero {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v (Ici 0) = 2⁻¹ ∧ gaussianReal 0 v (Iic 0) = 2⁻¹ := by
  have hneg : (gaussianReal 0 v).map (fun x => -x) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  have h2 : gaussianReal 0 v (Iic 0) = gaussianReal 0 v (Ici 0) := by
    conv_lhs => rw [← hneg]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext x
    simp
  have h0 : gaussianReal 0 v {0} = 0 :=
    gaussianReal_absolutelyContinuous 0 hv (Real.volume_singleton)
  have h3 := measure_union_add_inter (μ := gaussianReal 0 v) (Ici (0 : ℝ))
    (measurableSet_Iic (a := (0 : ℝ)))
  have hu : (Ici (0 : ℝ)) ∪ Iic 0 = univ := by
    ext x
    simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
    exact le_total 0 x
  have hi : (Ici (0 : ℝ)) ∩ Iic 0 = {0} := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Iic, mem_singleton_iff]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  rw [hu, hi, h0, measure_univ, add_zero, h2, ← two_mul] at h3
  have h4 : gaussianReal 0 v (Ici 0) = 2⁻¹ := by
    refine ENNReal.eq_inv_of_mul_eq_one_left ?_
    rw [mul_comm]
    exact h3.symm
  exact ⟨h4, h2.trans h4⟩

/-- Left endpoint of the `k`-th of `n` equal pieces of `[a, b]`. -/
private noncomputable def winL (a b : ℝ) (n : ℕ) (k : Fin n) : ℝ :=
  a + (b - a) * ((k : ℕ) : ℝ) / n

/-- Right endpoint of the `k`-th of `n` equal pieces of `[a, b]`. -/
private noncomputable def winR (a b : ℝ) (n : ℕ) (k : Fin n) : ℝ :=
  a + (b - a) * (((k : ℕ) : ℝ) + 1) / n

private lemma winR_sub_winL (a b : ℝ) (n : ℕ) (k : Fin n) :
    winR a b n k - winL a b n k = (b - a) / n := by
  unfold winR winL
  ring

private lemma winL_le_winR {a b : ℝ} (hab : a ≤ b) {n : ℕ} (k : Fin n) :
    winL a b n k ≤ winR a b n k := by
  have h := winR_sub_winL a b n k
  have h0 : 0 ≤ (b - a) / n := div_nonneg (sub_nonneg.2 hab) (Nat.cast_nonneg _)
  linarith

private lemma le_winL {a b : ℝ} (hab : a ≤ b) {n : ℕ} (k : Fin n) : a ≤ winL a b n k := by
  unfold winL
  have : 0 ≤ (b - a) * ((k : ℕ) : ℝ) / n :=
    div_nonneg (mul_nonneg (sub_nonneg.2 hab) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  linarith

private lemma winR_le {a b : ℝ} (hab : a ≤ b) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    winR a b n k ≤ b := by
  unfold winR
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt k.2
  have : (b - a) * (((k : ℕ) : ℝ) + 1) / n ≤ b - a := by
    rw [div_le_iff₀ hn']
    exact mul_le_mul_of_nonneg_left hk (sub_nonneg.2 hab)
  linarith

private lemma winR_le_winL {a b : ℝ} (hab : a ≤ b) {n : ℕ} (hn : 0 < n) {j k : Fin n}
    (hjk : j < k) : winR a b n j ≤ winL a b n k := by
  unfold winR winL
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (j : ℕ) + 1 ≤ (k : ℕ) := hjk
  have hjk' : ((j : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast h1
  have : (b - a) * (((j : ℕ) : ℝ) + 1) / n ≤ (b - a) * ((k : ℕ) : ℝ) / n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hjk' (sub_nonneg.2 hab)) hn'.le
  linarith

private lemma measure_forall_incr_mem {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n) {S : Set ℝ}
    (hS : MeasurableSet S) (hhalf : ∀ v : ℝ≥0, v ≠ 0 → gaussianReal 0 v S = 2⁻¹) :
    μ {ω | ∀ k : Fin n, coneIncr i (winR a b n k) (winL a b n k) ω ∈ S} = (2⁻¹) ^ n := by
  have := hμ.isProbabilityMeasure
  have hsep : ∀ j k : Fin n, j ≠ k →
      winR a b n j ≤ winL a b n k ∨ winR a b n k ≤ winL a b n j := fun j k hjk =>
    (lt_or_gt_of_ne hjk).imp (winR_le_winL hab.le hn) (winR_le_winL hab.le hn)
  have hind := iIndepFun_increment_windows hμ (winL a b n) (winR a b n) hsep
  have hmem : ∀ k : Fin n, winR a b n k ∈ Icc (winL a b n k) (winR a b n k) := fun k =>
    ⟨winL_le_winR hab.le k, le_rfl⟩
  have hind' : iIndepFun (fun (k : Fin n) ω => coneIncr i (winR a b n k) (winL a b n k) ω) μ :=
    hind.comp (fun k f => f (i, ⟨winR a b n k, hmem k⟩)) fun k => measurable_pi_apply _
  have hprod := hind'.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun _ => S) (fun _ _ => hS)
  have hset : {ω | ∀ k : Fin n, coneIncr i (winR a b n k) (winL a b n k) ω ∈ S} =
      ⋂ k ∈ (Finset.univ : Finset (Fin n)),
        (fun ω => coneIncr i (winR a b n k) (winL a b n k) ω) ⁻¹' S := by
    ext ω
    simp
  have hk : ∀ k : Fin n, μ ((fun ω => coneIncr i (winR a b n k) (winL a b n k) ω) ⁻¹' S) =
      2⁻¹ := by
    intro k
    rw [← Measure.map_apply (measurable_coneIncr i _ _) hS,
      map_coneIncr_eq_gaussianReal hμ i]
    apply hhalf
    have hpos : 0 < |winR a b n k - winL a b n k| := by
      rw [winR_sub_winL]
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact abs_pos.2 (div_pos (sub_pos.2 hab) this).ne'
    exact (Real.toNNReal_pos.2 hpos).ne'
  rw [hset, hprod]
  simp [hk]

private lemma measure_eq_zero_of_le_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : Set Ω} (h : ∀ n : ℕ, 0 < n → μ s ≤ (2⁻¹) ^ n) : μ s = 0 := by
  have ht : Tendsto (fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.one_half_lt_one
  exact le_antisymm (ge_of_tendsto ht (eventually_atTop.2 ⟨1, fun n hn => h n hn⟩)) bot_le

private lemma measure_monotoneOn_eq_zero {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) {a b : ℝ} (hab : a < b) :
    μ {ω | MonotoneOn (fun t => lrCoord i t ω) (Icc a b)} = 0 := by
  refine measure_eq_zero_of_le_pow fun n hn => ?_
  rw [← measure_forall_incr_mem hμ i hab hn (S := Ici 0) measurableSet_Ici
    fun v hv => (gaussianReal_Ici_zero hv).1]
  refine measure_mono fun ω hω k => ?_
  have hω' : MonotoneOn (fun t => lrCoord i t ω) (Icc a b) := hω
  have hL : winL a b n k ∈ Icc a b :=
    ⟨le_winL hab.le k, (winL_le_winR hab.le k).trans (winR_le hab.le hn k)⟩
  have hR : winR a b n k ∈ Icc a b :=
    ⟨(le_winL hab.le k).trans (winL_le_winR hab.le k), winR_le hab.le hn k⟩
  have h := hω' hL hR (winL_le_winR hab.le k)
  rw [mem_Ici]
  exact sub_nonneg.2 h

private lemma measure_antitoneOn_eq_zero {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) {a b : ℝ} (hab : a < b) :
    μ {ω | AntitoneOn (fun t => lrCoord i t ω) (Icc a b)} = 0 := by
  refine measure_eq_zero_of_le_pow fun n hn => ?_
  rw [← measure_forall_incr_mem hμ i hab hn (S := Iic 0) measurableSet_Iic
    fun v hv => (gaussianReal_Ici_zero hv).2]
  refine measure_mono fun ω hω k => ?_
  have hω' : AntitoneOn (fun t => lrCoord i t ω) (Icc a b) := hω
  have hL : winL a b n k ∈ Icc a b :=
    ⟨le_winL hab.le k, (winL_le_winR hab.le k).trans (winR_le hab.le hn k)⟩
  have hR : winR a b n k ∈ Icc a b :=
    ⟨(le_winL hab.le k).trans (winL_le_winR hab.le k), winR_le hab.le hn k⟩
  have h := hω' hL hR (winL_le_winR hab.le k)
  rw [mem_Iic]
  exact sub_nonpos.2 h

private lemma ae_nowhereMonotone_coord {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) :
    ∀ᵐ p ∂μ, NowhereMonotone (fun t => lrCoord i t p) := by
  have hq : ∀ᵐ p ∂μ, ∀ q₁ q₂ : ℚ, (q₁ : ℝ) < q₂ →
      ¬ MonotoneOn (fun t => lrCoord i t p) (Icc (q₁ : ℝ) q₂) ∧
        ¬ AntitoneOn (fun t => lrCoord i t p) (Icc (q₁ : ℝ) q₂) := by
    rw [ae_all_iff]
    intro q₁
    rw [ae_all_iff]
    intro q₂
    by_cases h : (q₁ : ℝ) < q₂
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_monotoneOn_eq_zero hμ i h),
        measure_eq_zero_iff_ae_notMem.1 (measure_antitoneOn_eq_zero hμ i h)] with p hp1 hp2 _
      exact ⟨hp1, hp2⟩
    · exact Eventually.of_forall fun p hlt => absurd hlt h
  filter_upwards [hq] with p hp
  unfold NowhereMonotone
  intro a b hab
  obtain ⟨q₁, ha₁, hb₁⟩ := exists_rat_btwn hab
  obtain ⟨q₂, ha₂, hb₂⟩ := exists_rat_btwn hb₁
  have hsub : Icc (q₁ : ℝ) q₂ ⊆ Icc a b := Icc_subset_Icc ha₁.le hb₂.le
  have := hp q₁ q₂ ha₂
  exact ⟨fun hm => this.1 (hm.mono hsub), fun hm => this.2 (hm.mono hsub)⟩

/-- Almost surely neither coordinate of a correlated Brownian pair is monotone or antitone on any
interval of positive length. -/
theorem ae_nowhereMonotone_of_isCorrelatedBM2 {γ : ℝ} {μ : MeasureTheory.Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ p ∂μ, NowhereMonotone (fun t => (p t).1) ∧ NowhereMonotone (fun t => (p t).2) := by
  filter_upwards [ae_nowhereMonotone_coord hμ 0, ae_nowhereMonotone_coord hμ 1] with p h0 h1
  exact ⟨by simpa [lrCoord] using h0, by simpa [lrCoord] using h1⟩

end MatedCRT.PeanosphereTriplePoints
