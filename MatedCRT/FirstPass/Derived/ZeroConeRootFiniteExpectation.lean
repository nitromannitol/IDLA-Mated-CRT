import MatedCRT.Defs.Setting
import LatticeProb.LQG.MatingOfTreesCouplingDegrees
import LatticeProb.LQG.MatingOfTreesCouplingCells
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The finite-expectation hypothesis for the root cell of the shifted zero-cone configuration

Gwynne–Miller–Sheffield (arXiv:1705.11161), Proposition 3.1, verifies the hypotheses of the invariance principle for
random cell configurations (Gwynne–Miller–Sheffield, arXiv:1807.07515, Theorem 1.16; Lattice-Probability
`ReflectedGMS.GMS.theorem1_16`) for the cells `η₀([k - 1 + θ, k + θ])`, `k ∈ ℤ`, of the space-filling curve `η₀`
parametrized by the quantum area of a `0`-quantum cone, shifted by `θ ∈ [0, 1]`. One of these hypotheses, the
finite-expectation condition (1.5) of the invariance principle, asks that `diam(H₀)² / area(H₀)` times the total
conductance `π(H₀)` (and times `π*(H₀) = ∑ 1/c`) of the cell `H₀ = η₀([θ - 1, θ])` containing `0` be integrable.

This file proves it from the cell-moment clause `cellMoments` of the mating-of-trees coupling
(Gwynne–Miller–Sheffield, arXiv:1705.11161, Propositions 4.4 and 4.6), for any conductances bounded by `2` that are
carried by intersecting cells (the boundary-arc conductances of the source are of this kind). The argument:

* every cell `η₀([k - 1 + θ, k + θ])` meeting `H₀` either lies in the ball `B′ = B̄_{4 diam η₀([-1, 1])}(0)` and is
  then counted by the inner degree `degInner η₀`, or contains a crossing from `η₀([-1, 1])` to `∂B′` through the
  interior of `B′`, counted by the outer degree `degOuter η₀` (`card_le_degInner_add_degOuter`);
* hence `π(H₀) ≤ 2 (degInner + degOuter)` and `π*(H₀) ≤ degInner + degOuter`, while
  `diam(H₀)² / area(H₀) ≤ diamAreaSup η₀`;
* Hölder's inequality with an exponent `p ∈ (1, 4/γ²)` for the degrees and the conjugate exponent for
  `diamAreaSup` gives integrability.

## Main results

* `exists_crossing_of_lt`: the crossing interval (deterministic).
* `card_le_degInner_add_degOuter`: the number of cells meeting the root cell (deterministic).
* `tsum_le_two_mul_degInner_add_degOuter`, `tsum_inv_le_degInner_add_degOuter`: the conductance bounds.
* `IsMatingOfTreesCoupling.lintegral_rootRatio_mul_conductance_lt_top`: the finite-expectation bound.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRT.ZeroConeRoot

open MatedCRTHarmonic.MatedCRT (degInner degOuter diamAreaSup degBall)

/-- **A crossing interval.** If `f` is continuous, `f t₀` lies in a closed set `K` of points of norm `< r`, and
`‖f t₁‖ ≥ r` with `t₀ < t₁`, there are `t₀ ≤ a < b ≤ t₁` with `f a ∈ K`, `‖f b‖ = r` and `‖f u‖ < r` for
`a < u < b`. -/
theorem exists_crossing_of_lt {f : ℝ → ℂ} (hf : Continuous f) {K : Set ℂ} (hK : IsClosed K) {r : ℝ}
    (hKr : ∀ z ∈ K, ‖z‖ < r) {t₀ t₁ : ℝ} (ht : t₀ < t₁) (h₀ : f t₀ ∈ K) (h₁ : r ≤ ‖f t₁‖) :
    ∃ a b, t₀ ≤ a ∧ a < b ∧ b ≤ t₁ ∧ f a ∈ K ∧ ‖f b‖ = r ∧ ∀ u ∈ Ioo a b, ‖f u‖ < r := by
  have hnorm : Continuous fun u => ‖f u‖ := continuous_norm.comp hf
  have hSc : IsClosed {u | u ∈ Icc t₀ t₁ ∧ r ≤ ‖f u‖} :=
    isClosed_Icc.inter (isClosed_le continuous_const hnorm)
  have hSne : ({u | u ∈ Icc t₀ t₁ ∧ r ≤ ‖f u‖} : Set ℝ).Nonempty := ⟨t₁, ⟨ht.le, le_rfl⟩, h₁⟩
  have hSbdd : BddBelow {u | u ∈ Icc t₀ t₁ ∧ r ≤ ‖f u‖} := ⟨t₀, fun u hu => hu.1.1⟩
  have hbS := hSc.csInf_mem hSne hSbdd
  have hble : ∀ u ∈ ({u | u ∈ Icc t₀ t₁ ∧ r ≤ ‖f u‖} : Set ℝ), sInf {u | u ∈ Icc t₀ t₁ ∧ r ≤ ‖f u‖} ≤ u :=
    fun u hu => csInf_le hSbdd hu
  generalize sInf {u | u ∈ Icc t₀ t₁ ∧ r ≤ ‖f u‖} = b at hbS hble
  have hlt : ∀ u, t₀ ≤ u → u < b → ‖f u‖ < r := by
    intro u hu hub
    by_contra hcon
    exact absurd (hble u ⟨⟨hu, hub.le.trans hbS.1.2⟩, not_lt.1 hcon⟩) (not_le.2 hub)
  have hb0 : t₀ < b := by
    refine lt_of_le_of_ne hbS.1.1 fun h => ?_
    have h2 := hbS.2
    rw [← h] at h2
    exact absurd h2 (not_le.2 (hKr _ h₀))
  have hbr : ‖f b‖ ≤ r := by
    have hcl : closure (Ico t₀ b) ⊆ {u | ‖f u‖ ≤ r} :=
      (isClosed_le hnorm continuous_const).closure_subset_iff.2 fun u hu => (hlt u hu.1 hu.2).le
    rw [closure_Ico hb0.ne] at hcl
    exact hcl ⟨hb0.le, le_rfl⟩
  have hbeq : ‖f b‖ = r := le_antisymm hbr hbS.2
  have hTc : IsClosed {u | u ∈ Icc t₀ b ∧ f u ∈ K} := isClosed_Icc.inter (hK.preimage hf)
  have hTne : ({u | u ∈ Icc t₀ b ∧ f u ∈ K} : Set ℝ).Nonempty := ⟨t₀, ⟨le_rfl, hb0.le⟩, h₀⟩
  have hTbdd : BddAbove {u | u ∈ Icc t₀ b ∧ f u ∈ K} := ⟨b, fun u hu => hu.1.2⟩
  have haT := hTc.csSup_mem hTne hTbdd
  generalize sSup {u | u ∈ Icc t₀ b ∧ f u ∈ K} = a at haT
  have hab : a < b := by
    refine lt_of_le_of_ne haT.1.2 fun h => ?_
    have h2 := hKr _ haT.2
    rw [h, hbeq] at h2
    exact lt_irrefl r h2
  exact ⟨a, b, haT.1.1, hab, hbS.1.2, haT.2, hbeq, fun u hu => hlt u (haT.1.1.trans hu.1.le) hu.2⟩

/-- **A crossing interval, backwards in time.** The time reversal of `exists_crossing_of_lt`: if `t₁ < t₀`, there
are `t₁ ≤ a < b ≤ t₀` with `‖f a‖ = r`, `f b ∈ K` and `‖f u‖ < r` for `a < u < b`. -/
theorem exists_crossing_of_gt {f : ℝ → ℂ} (hf : Continuous f) {K : Set ℂ} (hK : IsClosed K) {r : ℝ}
    (hKr : ∀ z ∈ K, ‖z‖ < r) {t₀ t₁ : ℝ} (ht : t₁ < t₀) (h₀ : f t₀ ∈ K) (h₁ : r ≤ ‖f t₁‖) :
    ∃ a b, t₁ ≤ a ∧ a < b ∧ b ≤ t₀ ∧ ‖f a‖ = r ∧ f b ∈ K ∧ ∀ u ∈ Ioo a b, ‖f u‖ < r := by
  obtain ⟨a, b, ha, hab, hb, hfa, hfb, hu⟩ := exists_crossing_of_lt (f := fun u => f (-u))
    (hf.comp continuous_neg) hK hKr (neg_lt_neg ht) (by simpa using h₀) (by simpa using h₁)
  refine ⟨-b, -a, by linarith, by linarith, by linarith, hfb, hfa, fun u hu' => ?_⟩
  have := hu (-u) ⟨by linarith [hu'.2], by linarith [hu'.1]⟩
  simpa using this

/-- Unit intervals with distinct integer labels have disjoint interiors. -/
theorem disjoint_Ioo_unit {k k' : ℤ} (h : k ≠ k') (θ : ℝ) :
    Disjoint (Ioo ((k : ℝ) - 1 + θ) ((k : ℝ) - 1 + θ + 1)) (Ioo ((k' : ℝ) - 1 + θ) ((k' : ℝ) - 1 + θ + 1)) := by
  rw [Set.disjoint_left]
  rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
  rcases lt_or_gt_of_ne h with hk | hk
  · have hk' : ((k + 1 : ℤ) : ℝ) ≤ k' := by exact_mod_cast (by omega : k + 1 ≤ k')
    push_cast at hk'
    linarith
  · have hk' : ((k' + 1 : ℤ) : ℝ) ≤ k := by exact_mod_cast (by omega : k' + 1 ≤ k)
    push_cast at hk'
    linarith

/-- **The cells meeting the root cell.** Let `c` be a continuous curve with `c 0 = 0` and
`diam c([-1, 1]) > 0`, and `0 ≤ θ ≤ 1`. The number of labels `k` in a finite set `T` whose cell
`c([k - 1 + θ, k + θ])` meets the root cell `c([θ - 1, θ])` is at most `degInner c + degOuter c`. -/
theorem card_le_degInner_add_degOuter {c : C(ℝ, ℂ)} (hc0 : c 0 = 0) (hD : 0 < diam (c '' Icc (-1) 1))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (T : Finset ℤ)
    (hT : ∀ k ∈ T, (c '' Icc ((k : ℝ) - 1 + θ) ((k : ℝ) - 1 + θ + 1) ∩ c '' Icc (θ - 1) θ).Nonempty) :
    ((T.card : ℕ∞)) ≤ degInner c + degOuter c := by
  classical
  have hKc : IsCompact (c '' Icc (-1) 1) := isCompact_Icc.image c.continuous
  have h0K : (0 : ℂ) ∈ c '' Icc (-1) 1 := ⟨0, ⟨by norm_num, by norm_num⟩, hc0⟩
  have hKD : ∀ z ∈ c '' Icc (-1) 1, ‖z‖ ≤ diam (c '' Icc (-1) 1) := by
    intro z hz
    have := dist_le_diam_of_mem hKc.isBounded hz h0K
    rwa [dist_zero_right] at this
  have hr0 : (4 * diam (c '' Icc (-1) 1)) ≠ 0 := by positivity
  have hKr : ∀ z ∈ c '' Icc (-1) 1, ‖z‖ < 4 * diam (c '' Icc (-1) 1) := fun z hz => by
    linarith [hKD z hz]
  have hball : degBall c = closedBall (0 : ℂ) (4 * diam (c '' Icc (-1) 1)) := rfl
  have hroot : c '' Icc (θ - 1) θ ⊆ c '' Icc (-1) 1 :=
    image_mono (Icc_subset_Icc (by linarith) (by linarith))
  -- the cells inside the ball and the others
  rw [← Finset.card_filter_add_card_filter_not (s := T)
    (fun k : ℤ => c '' Icc ((k : ℝ) - 1 + θ) ((k : ℝ) - 1 + θ + 1) ⊆ degBall c)]
  push_cast
  gcongr
  · -- inner degree
    set Tin := T.filter (fun k : ℤ => c '' Icc ((k : ℝ) - 1 + θ) ((k : ℝ) - 1 + θ + 1) ⊆ degBall c)
    let e := Tin.orderIsoOfFin rfl
    refine le_iSup_of_le Tin.card (le_iSup_of_le (fun i => ((e i : ℤ) : ℝ) - 1 + θ) ?_)
    refine le_iSup_of_le ⟨fun i j hij => disjoint_Ioo_unit (fun h => hij (e.injective (Subtype.ext h))) θ,
      fun i => ⟨(Finset.mem_filter.1 (e i).2).2, ?_⟩⟩ le_rfl
    obtain ⟨z, hz1, hz2⟩ := hT _ (Finset.mem_filter.1 (e i).2).1
    exact ⟨z, hz1, hroot hz2⟩
  · -- outer degree
    set Tout := T.filter (fun k : ℤ => ¬ c '' Icc ((k : ℝ) - 1 + θ) ((k : ℝ) - 1 + θ + 1) ⊆ degBall c)
    have hcross : ∀ k ∈ Tout, ∃ p : ℝ × ℝ, (k : ℝ) - 1 + θ ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ (k : ℝ) - 1 + θ + 1 ∧
        c '' Ioo p.1 p.2 ⊆ interior (degBall c) ∧
        ((c p.1 ∈ frontier (degBall c) ∧ c p.2 ∈ c '' Icc (-1) 1) ∨
          (c p.2 ∈ frontier (degBall c) ∧ c p.1 ∈ c '' Icc (-1) 1)) := by
      intro k hk
      obtain ⟨hkT, hkout⟩ := Finset.mem_filter.1 hk
      obtain ⟨z, ⟨t₀, ht₀, rfl⟩, hz2⟩ := hT k hkT
      obtain ⟨w, ⟨t₁, ht₁, rfl⟩, hw⟩ := not_subset.1 hkout
      rw [hball, mem_closedBall_zero_iff, not_le] at hw
      have hint : interior (degBall c) = ball (0 : ℂ) (4 * diam (c '' Icc (-1) 1)) := by
        rw [hball, interior_closedBall _ hr0]
      have hfr : frontier (degBall c) = sphere (0 : ℂ) (4 * diam (c '' Icc (-1) 1)) := by
        rw [hball, frontier_closedBall _ hr0]
      have hc₀ : c t₀ ∈ c '' Icc (-1) 1 := hroot hz2
      rcases lt_or_gt_of_ne (show t₀ ≠ t₁ from fun h => by
          rw [h] at hc₀; exact absurd (hKr _ hc₀) (not_lt.2 hw.le)) with h01 | h10
      · obtain ⟨a, b, ha, hab, hb, hfa, hfb, hu⟩ := exists_crossing_of_lt c.continuous hKc.isClosed hKr h01
          hc₀ hw.le
        refine ⟨(a, b), ht₀.1.trans ha, hab, hb.trans ht₁.2, ?_, Or.inr ⟨?_, hfa⟩⟩
        · rintro _ ⟨u, hu', rfl⟩
          rw [hint, mem_ball_zero_iff]
          exact hu u hu'
        · rw [hfr, mem_sphere_zero_iff_norm]
          exact hfb
      · obtain ⟨a, b, ha, hab, hb, hfa, hfb, hu⟩ := exists_crossing_of_gt c.continuous hKc.isClosed hKr h10
          hc₀ hw.le
        refine ⟨(a, b), ht₁.1.trans ha, hab, hb.trans ht₀.2, ?_, Or.inl ⟨?_, hfb⟩⟩
        · rintro _ ⟨u, hu', rfl⟩
          rw [hint, mem_ball_zero_iff]
          exact hu u hu'
        · rw [hfr, mem_sphere_zero_iff_norm]
          exact hfa
    choose! P hP using hcross
    let e := Tout.orderIsoOfFin rfl
    refine le_iSup_of_le Tout.card (le_iSup_of_le (fun i => (P (e i)).1)
      (le_iSup_of_le (fun i => (P (e i)).2) ?_))
    refine le_iSup_of_le ⟨fun i => (hP _ (e i).2).2.1, fun i j hij => ?_, fun i => (hP _ (e i).2).2.2.2⟩ le_rfl
    have hne : ((e i : ℤ)) ≠ (e j : ℤ) := fun h => hij (e.injective (Subtype.ext h))
    refine (disjoint_Ioo_unit hne θ).mono ?_ ?_
    · exact Ioo_subset_Ioo (hP _ (e i).2).1 (hP _ (e i).2).2.2.1
    · exact Ioo_subset_Ioo (hP _ (e j).2).1 (hP _ (e j).2).2.2.1

/-- **Total conductance of the root cell.** Under the hypotheses of `card_le_degInner_add_degOuter`, conductances
`m b ≤ 2` from the root cell to the cells `b`, nonzero only for cells meeting the root cell, have total at most
`2 (degInner c + degOuter c)`. -/
theorem tsum_le_two_mul_degInner_add_degOuter {c : C(ℝ, ℂ)} (hc0 : c 0 = 0)
    (hD : 0 < diam (c '' Icc (-1) 1)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (m : ℤ → ℕ) (hm2 : ∀ b, m b ≤ 2)
    (hsupp : ∀ b, m b ≠ 0 →
      (c '' Icc ((b : ℝ) - 1 + θ) ((b : ℝ) - 1 + θ + 1) ∩ c '' Icc (θ - 1) θ).Nonempty) :
    ∑' b, (m b : ℝ≥0∞) ≤ 2 * ((degInner c : ℝ≥0∞) + (degOuter c : ℝ≥0∞)) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [← Finset.sum_filter_ne_zero]
  calc ∑ b ∈ s.filter (fun b => (m b : ℝ≥0∞) ≠ 0), (m b : ℝ≥0∞)
      ≤ ∑ _b ∈ s.filter (fun b => (m b : ℝ≥0∞) ≠ 0), (2 : ℝ≥0∞) :=
        Finset.sum_le_sum fun b _ => by exact_mod_cast hm2 b
    _ = 2 * ((s.filter (fun b => (m b : ℝ≥0∞) ≠ 0)).card : ℝ≥0∞) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ 2 * ((degInner c : ℝ≥0∞) + (degOuter c : ℝ≥0∞)) := by
        gcongr
        rw [← ENat.toENNReal_coe, ← ENat.toENNReal_add, ENat.toENNReal_le]
        refine card_le_degInner_add_degOuter hc0 hD hθ0 hθ1 _ fun k hk => hsupp k ?_
        have := (Finset.mem_filter.1 hk).2
        exact_mod_cast this

/-- **Inverse conductances of the root cell.** Under the hypotheses of `card_le_degInner_add_degOuter`, the sum of
the inverse nonzero conductances from the root cell is at most `degInner c + degOuter c`. -/
theorem tsum_inv_le_degInner_add_degOuter {c : C(ℝ, ℂ)} (hc0 : c 0 = 0)
    (hD : 0 < diam (c '' Icc (-1) 1)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (m : ℤ → ℕ)
    (hsupp : ∀ b, m b ≠ 0 →
      (c '' Icc ((b : ℝ) - 1 + θ) ((b : ℝ) - 1 + θ + 1) ∩ c '' Icc (θ - 1) θ).Nonempty) :
    ∑' b, (if m b = 0 then 0 else ((m b : ℝ≥0∞))⁻¹) ≤ (degInner c : ℝ≥0∞) + (degOuter c : ℝ≥0∞) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ b ∈ s, (if m b = 0 then 0 else ((m b : ℝ≥0∞))⁻¹)
      ≤ ∑ b ∈ s, (if m b = 0 then 0 else (1 : ℝ≥0∞)) := by
        refine Finset.sum_le_sum fun b _ => ?_
        split_ifs with hb
        · exact le_rfl
        · exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb)
    _ = ((s.filter (fun b => m b ≠ 0)).card : ℝ≥0∞) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (degInner c : ℝ≥0∞) + (degOuter c : ℝ≥0∞) := by
        rw [← ENat.toENNReal_coe, ← ENat.toENNReal_add, ENat.toENNReal_le]
        exact card_le_degInner_add_degOuter hc0 hD hθ0 hθ1 _ fun k hk => hsupp k (Finset.mem_filter.1 hk).2

end MatedCRT.ZeroConeRoot
