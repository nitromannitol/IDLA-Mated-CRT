import MatedCRT.Defs.Notation

/-!
# Dyadic Borel-Cantelli cutoff for polynomially high probability events (q2, task fp-S4S6c-envscaling-6-7-6-8)

Source: LEMMA68.md / CHATGPT-lemma68-open-parts.md, section D2: the random scale `dd(ω)` of the uniform Lemma 6.7/6.8
is a measurable cutoff below which the scale-indexed events hold *simultaneously for every scale* (not one scale at a
time). Mechanism: a family `E δ` of events with `P[(E δ)ᶜ] ≤ C δ^p` (`PolyHighProb`) at dyadic scales `δ = 2^{-j}` is
summable, so by Borel-Cantelli almost surely `ω ∈ E (2^{-j})` for all large `j`; the first such index `K(ω)` gives the
cutoff `dd(ω) = min(r₀/2, 2^{-K(ω)})`. Every scale `δ ≤ dd(ω)` is then witnessed by a dyadic scale `δ' ∈ [δ/2, δ]`
at which `ω ∈ E δ'`.

Terminology: "polynomially high probability" as in the Harmonic-Balls `PolyHighProb`; the cutoff is the random scale of
the good event (Borel-Cantelli over dyadic scales). The sub-σ-algebra `F` is the field σ-algebra (`Measurable[S.fieldSigma]`).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace MatedCRT
namespace DyadicCutoff68

variable {Ω : Type*}

/-- The event at dyadic scale `2^{-j}`: `E (2^{-j})` where the polynomial bound is available (`2^{-j} < r₀`), and
`univ` otherwise (where no bound is claimed). -/
noncomputable def dyadicEvent (E : ℝ → Set Ω) (r₀ : ℝ) (j : ℕ) : Set Ω :=
  if (1 / 2 : ℝ) ^ j < r₀ then E ((1 / 2 : ℝ) ^ j) else univ

/-- The event that the dyadic events hold at every scale `2^{-j}` with `j ≥ k`. -/
def goodFrom (E : ℝ → Set Ω) (r₀ : ℝ) (k : ℕ) : Set Ω :=
  ⋂ j : ℕ, dyadicEvent E r₀ (j + k)

lemma mem_goodFrom {E : ℝ → Set Ω} {r₀ : ℝ} {k : ℕ} {ω : Ω} :
    ω ∈ goodFrom E r₀ k ↔ ∀ j : ℕ, k ≤ j → ω ∈ dyadicEvent E r₀ j := by
  constructor
  · intro h j hj
    have hj' := mem_iInter.1 h (j - k)
    rwa [Nat.sub_add_cancel hj] at hj'
  · intro h
    exact mem_iInter.2 fun j => h _ (Nat.le_add_left k j)

section Measurability

variable {F : MeasurableSpace Ω} {E : ℝ → Set Ω} {r₀ : ℝ}

lemma measurableSet_dyadicEvent (hE : ∀ δ, MeasurableSet[F] (E δ)) (j : ℕ) :
    MeasurableSet[F] (dyadicEvent E r₀ j) := by
  unfold dyadicEvent
  split_ifs
  · exact hE _
  · exact MeasurableSet.univ

lemma measurableSet_goodFrom (hE : ∀ δ, MeasurableSet[F] (E δ)) (k : ℕ) :
    MeasurableSet[F] (goodFrom E r₀ k) :=
  MeasurableSet.iInter fun j => measurableSet_dyadicEvent hE (j + k)

end Measurability

/-- The random scale `dd(ω) = min(r₀/2, 2^{-K(ω)})` with `K(ω)` the first index from which `ω` is good; `r₀/2` off the
good set (a null set, where any positive value is allowed). -/
noncomputable def ddOf (E : ℝ → Set Ω) (r₀ : ℝ) (ω : Ω) : ℝ :=
  open Classical in
  if ω ∈ ⋃ k : ℕ, goodFrom E r₀ k then
    min (r₀ / 2) (⨆ k : ℕ, (goodFrom E r₀ k).indicator (fun _ => (1 / 2 : ℝ) ^ k) ω)
  else r₀ / 2

lemma indicator_dyadic_le_one (E : ℝ → Set Ω) (r₀ : ℝ) (ω : Ω) (k : ℕ) :
    (goodFrom E r₀ k).indicator (fun _ => (1 / 2 : ℝ) ^ k) ω ≤ 1 := by
  unfold Set.indicator
  split_ifs
  · exact pow_le_one₀ (by norm_num) (by norm_num)
  · norm_num

lemma pow_half_rpow (j : ℕ) (p : ℝ) : ((1 / 2 : ℝ) ^ j) ^ p = ((1 / 2 : ℝ) ^ p) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((1 / 2 : ℝ) ^ p) j,
    ← Real.rpow_mul (by norm_num), mul_comm]

/-- **Borel-Cantelli over dyadic scales.** If `P[(E δ)ᶜ] ≤ C δ^p` for small `δ`, then almost surely `ω` is good from
some index on, i.e. `ω ∈ E (2^{-j})` for all large `j`. -/
lemma ae_mem_goodFrom [m : MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → Set Ω) (r₀ C p : ℝ) (_hr₀ : 0 < r₀)
    (hp : 0 < p) (hpoly : ∀ δ : ℝ, 0 < δ → δ < r₀ → P (E δ)ᶜ ≤ ENNReal.ofReal (C * δ ^ p)) :
    ∀ᵐ ω ∂P, ω ∈ ⋃ k : ℕ, goodFrom E r₀ k := by
  set q : ℝ := (1 / 2 : ℝ) ^ p with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hbound : ∀ j : ℕ, P (dyadicEvent E r₀ j)ᶜ ≤ ENNReal.ofReal |C| * ENNReal.ofReal q ^ j := by
    intro j
    unfold dyadicEvent
    split_ifs with h
    · have hδ : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
      calc P (E ((1 / 2 : ℝ) ^ j))ᶜ ≤ ENNReal.ofReal (C * ((1 / 2 : ℝ) ^ j) ^ p) := hpoly _ hδ h
        _ ≤ ENNReal.ofReal (|C| * q ^ j) := by
          apply ENNReal.ofReal_le_ofReal
          rw [pow_half_rpow]
          rw [← hq]
          have hqj : (0 : ℝ) ≤ q ^ j := by positivity
          nlinarith [le_abs_self C, abs_nonneg C]
        _ = ENNReal.ofReal |C| * ENNReal.ofReal q ^ j := by
          rw [ENNReal.ofReal_mul (abs_nonneg C), ENNReal.ofReal_pow hq0.le]
    · simp
  have hsum : ∑' j : ℕ, P (dyadicEvent E r₀ j)ᶜ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (le_trans (ENNReal.tsum_le_tsum hbound) le_rfl)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    refine ENNReal.inv_ne_top.2 ?_
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0.le]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hlim := measure_limsup_atTop_eq_zero hsum
  rw [measure_eq_zero_iff_ae_notMem] at hlim
  filter_upwards [hlim] with ω hω
  have hfreq : ¬ ∃ᶠ j in atTop, ω ∈ (dyadicEvent E r₀ j)ᶜ := fun h =>
    hω (Filter.mem_limsup_iff_frequently_mem.2 h)
  rw [Filter.not_frequently] at hfreq
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hfreq
  refine mem_iUnion.2 ⟨k, mem_goodFrom.2 fun j hj => ?_⟩
  exact not_not.1 (hk j hj)

/-- **Dyadic cutoff** (LEMMA68 D2, the random scale `dd`). For a family of events with polynomially high probability
(`PolyHighProb`), there is a positive `F`-measurable `dd` such that almost surely, every scale `δ ∈ (0, dd ω]` is
witnessed by a dyadic scale `δ' ∈ [δ/2, δ]` at which `ω ∈ E δ'`. -/
theorem exists_dyadic_cutoff {F : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (E : ℝ → Set Ω) (hE : ∀ δ, MeasurableSet[F] (E δ))
    (hpoly : HarmonicBalls.PolyHighProb P E) :
    ∃ dd : Ω → ℝ, Measurable[F] dd ∧ (∀ ω, 0 < dd ω) ∧
      ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → δ ≤ dd ω → ∃ δ' : ℝ, δ / 2 ≤ δ' ∧ δ' ≤ δ ∧ ω ∈ E δ' := by
  obtain ⟨p, hp, C, r₀, hr₀, hpoly⟩ := hpoly
  refine ⟨ddOf E r₀, ?_, ?_, ?_⟩
  · -- measurability of the cutoff in `F`
    unfold ddOf
    have hU : MeasurableSet[F] (⋃ k : ℕ, goodFrom E r₀ k) :=
      MeasurableSet.iUnion fun k => measurableSet_goodFrom hE k
    refine Measurable.ite (p := fun ω => ω ∈ ⋃ k : ℕ, goodFrom E r₀ k) hU ?_ measurable_const
    exact measurable_const.min
      (Measurable.iSup fun k => measurable_const.indicator (measurableSet_goodFrom hE k))
  · intro ω
    unfold ddOf
    split_ifs with h
    · obtain ⟨k, hk⟩ := mem_iUnion.1 h
      have hpos : 0 < (goodFrom E r₀ k).indicator (fun _ => (1 / 2 : ℝ) ^ k) ω := by
        rw [Set.indicator_of_mem hk]
        exact pow_pos (by norm_num) k
      refine lt_min (half_pos hr₀) (lt_of_lt_of_le hpos (le_ciSup (f := fun i => (goodFrom E r₀ i).indicator (fun _ => (1 / 2 : ℝ) ^ i) ω) ?_ k))
      exact ⟨1, by rintro _ ⟨i, rfl⟩; exact indicator_dyadic_le_one E r₀ ω i⟩
    · exact half_pos hr₀
  · classical
    filter_upwards [ae_mem_goodFrom P E r₀ C p hr₀ hp hpoly] with ω hω
    intro δ hδ hδdd
    have hex : ∃ k : ℕ, ω ∈ goodFrom E r₀ k := mem_iUnion.1 hω
    set K0 := Nat.find hex with hK0
    have hspec : ω ∈ goodFrom E r₀ K0 := Nat.find_spec hex
    have hsup : (⨆ k : ℕ, (goodFrom E r₀ k).indicator (fun _ => (1 / 2 : ℝ) ^ k) ω) =
        (1 / 2 : ℝ) ^ K0 := by
      apply le_antisymm
      · apply ciSup_le
        intro k
        unfold Set.indicator
        split_ifs with hk
        · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.find_min' hex hk)
        · positivity
      · refine le_ciSup_of_le ⟨1, ?_⟩ K0 (le_of_eq ?_)
        · rintro _ ⟨i, rfl⟩
          exact indicator_dyadic_le_one E r₀ ω i
        · simp [Set.indicator_of_mem hspec]
    have hdd : ddOf E r₀ ω = min (r₀ / 2) ((1 / 2 : ℝ) ^ K0) := by
      unfold ddOf
      simp only [hω, ↓reduceIte, hsup]
    rw [hdd] at hδdd
    have hδ1 : δ ≤ r₀ / 2 := le_trans hδdd (min_le_left _ _)
    have hδ2 : δ ≤ (1 / 2 : ℝ) ^ K0 := le_trans hδdd (min_le_right _ _)
    have hδ_le_one : δ ≤ 1 := le_trans hδ2 (pow_le_one₀ (by norm_num) (by norm_num))
    have hx1 : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
    have hd1 : (2 : ℝ) ^ n * δ ≤ 1 := (le_div_iff₀ hδ).1 hn1
    have hd2 : 1 < (2 : ℝ) ^ (n + 1) * δ := (div_lt_iff₀ hδ).1 hn2
    have hP : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    have hδ'eq : (1 / 2 : ℝ) ^ (n + 1) * 2 ^ (n + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hδ'pos : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1) := by positivity
    have hup : (1 / 2 : ℝ) ^ (n + 1) ≤ δ := by nlinarith
    have hlow : δ / 2 ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      have h2n : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [h2n] at hδ'eq
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) n]
    have hK : K0 ≤ n + 1 := by
      by_contra hlt
      rw [not_le] at hlt
      have h1 : (1 / 2 : ℝ) ^ K0 < (1 / 2 : ℝ) ^ (n + 1) :=
        pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlt
      linarith
    have hr : (1 / 2 : ℝ) ^ (n + 1) < r₀ := by linarith
    have hmem := (mem_goodFrom.1 hspec) (n + 1) hK
    unfold dyadicEvent at hmem
    simp only [hr, ↓reduceIte] at hmem
    exact ⟨(1 / 2 : ℝ) ^ (n + 1), hlow, hup, hmem⟩

#print axioms MatedCRT.DyadicCutoff68.exists_dyadic_cutoff

end DyadicCutoff68
end MatedCRT
