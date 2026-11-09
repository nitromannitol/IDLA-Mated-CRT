import MatedCRT.Proofs.Sec1.EnvironmentScaling.PostLastZeroShiftedLaw
import MatedCRT.Proposed.DMSRemark44Printed
import MatedCRT.Proofs.Sec1.EnvironmentScaling.RadialLogMajorantProof

/-!
# Measurable post-last-zero functional on path space; law of the path map (DMS Remark 4.4)

Committed here, unconditional:
* `dmsPathMap d`: the drifted post-last-zero path `t ↦ c(ℓ + t)` of DMS Remark 4.4 (pp. 74-75), as a Borel
  map of the continuous path, equal to `dmsDriftedPostLastZeroPath d (· ·)` at every time and every path
  (`exists_measurable_dmsDriftedPostLastZeroPath_wiener`; steps4-final Section 2, lines 429-441). The last zero
  `ℓ = lastZeroR c` is Bonanno's functional (`MatedCRTHarmonic.MatedCRT.lastZeroR`, LatticeProb
  `MatedCRTLastZeroR`). Its Borel measurability is proved from zero sets on compact intervals tested on
  rational points, and the joint measurability uses Mathlib's `measurable_uncurry_of_continuous_of_measurable`.
* `map_pathMap_eq_brownianMotion`: for a Brownian motion `D` (Mathlib `ProbabilityTheory.IsBrownianReal`)
  with everywhere continuous paths, the law of its path map is the Wiener measure `brownianMotion 0`. The proof
  compares finite-dimensional laws (`IsPreBrownianReal.hasLaw`, the projective family) through
  `MeasureTheory.IsProjectiveLimit.unique`, using `brownianMotion_zero_isBrownianReal`.

Not committed here: the arbitrary-space transfer `DMS14Remark44TransferResidual` (steps4-final Section 2,
lines 443-473) and the numbered target from it. The transfer needs a continuous version of an `IsBrownianReal`
process with measurable coordinates, which is `LatticeProb.IsBrownianReal.exists_continuous_indistinguishable`
(LatticeProb/Prob/BrownianPathCoords.lean:28). The lattice-probability modules it imports do not build at the
pinned Mathlib (FiniteMarginal.lean:29 and GaussianLaw.lean:57 fail on `measurable_pi_lambda` arguments), so the
transfer is not closed here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MatedCRT.Sec1

open MatedCRT.Proposed

/-- The drifted real path `u ↦ p(u⁺) + d u` of a continuous path `p` on `ℝ≥0` (DMS Remark 4.4). -/
def dmsDriftedCoord (d : ℝ) (p : MarkovProcess.ContinuousPath ℝ) (u : ℝ) : ℝ :=
  p u.toNNReal + d * u

lemma continuous_dmsDriftedCoord (d : ℝ) (p : MarkovProcess.ContinuousPath ℝ) :
    Continuous (dmsDriftedCoord d p) :=
  (p.continuous.comp continuous_real_toNNReal).add (continuous_const.mul continuous_id)

lemma measurable_dmsDriftedCoord (d u : ℝ) :
    Measurable (fun p : MarkovProcess.ContinuousPath ℝ => dmsDriftedCoord d p u) :=
  (MarkovProcess.ContinuousPath.measurable_coordinateProcess u.toNNReal).add_const (d * u)

/-- For a continuous `f` and `a < b`, `f` has a zero in `[a, b]` iff for every `k` some rational `q ∈ [a, b]`
has `|f q| < 1/(k+1)`: the zero is approached by rational test points (density) and the minimum of `|f|`
on the compact interval is attained. -/
lemma exists_zero_Icc_iff_rat {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    (∃ s ∈ Icc a b, f s = 0) ↔
      ∀ k : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc a b ∧ |f q| < 1 / ((k : ℝ) + 1) := by
  constructor
  · rintro ⟨s, hs, hfs⟩ k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 hf s (1 / ((k : ℝ) + 1)) hε
    have hu : max a (s - δ / 2) < min b (s + δ / 2) :=
      max_lt (lt_min hab (by linarith [hs.1])) (lt_min (by linarith [hs.2]) (by linarith))
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hu
    refine ⟨q, ⟨le_trans (le_max_left _ _) hq1.le, le_trans hq2.le (min_le_left _ _)⟩, ?_⟩
    have h1 : s - δ / 2 < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
    have h2 : (q : ℝ) < s + δ / 2 := lt_of_lt_of_le hq2 (min_le_right _ _)
    have hdist : dist (q : ℝ) s < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
    have hq := hcont _ hdist
    rw [hfs, Real.dist_eq, sub_zero] at hq
    exact hq
  · intro h
    obtain ⟨s, hs, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn
      (Set.nonempty_Icc.2 hab.le) (continuous_abs.comp hf).continuousOn
    refine ⟨s, hs, ?_⟩
    by_contra hne
    have hpos : 0 < |f s| := abs_pos.2 hne
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    obtain ⟨q, hq, hlt⟩ := h k
    have hmin' : |f s| ≤ |f q| := hmin hq
    linarith

/-- The set of continuous paths whose drifted coordinate has a zero in `[a, b]` is Borel. -/
lemma measurableSet_dmsZeroIcc (d a b : ℝ) (hab : a < b) :
    MeasurableSet {p : MarkovProcess.ContinuousPath ℝ | ∃ s ∈ Icc a b, dmsDriftedCoord d p s = 0} := by
  have hset : {p : MarkovProcess.ContinuousPath ℝ | ∃ s ∈ Icc a b, dmsDriftedCoord d p s = 0} =
      ⋂ k : ℕ, ⋃ q : ℚ, {p : MarkovProcess.ContinuousPath ℝ |
        (q : ℝ) ∈ Icc a b ∧ |dmsDriftedCoord d p q| < 1 / ((k : ℝ) + 1)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    exact exists_zero_Icc_iff_rat (continuous_dmsDriftedCoord d p) hab
  rw [hset]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun q => ?_
  rw [Set.ofPred_and]
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  exact measurableSet_lt ((continuous_abs.measurable).comp (measurable_dmsDriftedCoord d q))
    measurable_const

/-- The sets `{p | ∃ s > A, drifted coordinate of p vanishes at s}` are Borel, for every real `A`. -/
lemma measurableSet_dmsZeroAbove (d A : ℝ) :
    MeasurableSet {p : MarkovProcess.ContinuousPath ℝ | ∃ s, A < s ∧ dmsDriftedCoord d p s = 0} := by
  have hset : {p : MarkovProcess.ContinuousPath ℝ | ∃ s, A < s ∧ dmsDriftedCoord d p s = 0} =
      ⋃ n : ℕ, {p : MarkovProcess.ContinuousPath ℝ |
        ∃ s ∈ Icc (A + 1 / ((n : ℝ) + 2)) (A + (n : ℝ) + 2), dmsDriftedCoord d p s = 0} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨s, hAs, hz⟩
      have hδ : 0 < s - A := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / (s - A)) (s - A))
      have hn1 : 1 / (s - A) < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
      have hn2 : s - A < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hle : 1 / ((n : ℝ) + 2) ≤ s - A := (one_div_le hδ hpos).1 (by linarith)
      exact ⟨n, s, ⟨by linarith, by linarith⟩, hz⟩
    · rintro ⟨n, s, ⟨h1, h2⟩, hz⟩
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      exact ⟨s, by linarith, hz⟩
  rw [hset]
  refine MeasurableSet.iUnion fun n => measurableSet_dmsZeroIcc d _ _ ?_
  have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlt1 : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  linarith

/-- The last-zero functional is nonnegative (`sSup ∅ = 0` and the convention `sSup` of an unbounded set is `0`). -/
lemma lastZeroR_nonneg (c : ℝ → ℝ) : 0 ≤ MatedCRTHarmonic.MatedCRT.lastZeroR c := by
  unfold MatedCRTHarmonic.MatedCRT.lastZeroR
  rcases Set.eq_empty_or_nonempty {s : ℝ | 0 ≤ s ∧ c s = 0} with hE | hne
  · simp [hE]
  · by_cases hb : BddAbove {s : ℝ | 0 ≤ s ∧ c s = 0}
    · obtain ⟨s, hs⟩ := hne
      exact le_trans hs.1 (le_csSup hb hs)
    · simp [Real.sSup_of_not_bddAbove hb]

/-- For `0 ≤ x`: `x < lastZeroR c` iff the zero set is bounded above and has a zero beyond `x`. -/
lemma lt_lastZeroR_iff (c : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    x < MatedCRTHarmonic.MatedCRT.lastZeroR c ↔
      BddAbove {s : ℝ | 0 ≤ s ∧ c s = 0} ∧ ∃ s, x < s ∧ c s = 0 := by
  unfold MatedCRTHarmonic.MatedCRT.lastZeroR
  constructor
  · intro h
    have hb : BddAbove {s : ℝ | 0 ≤ s ∧ c s = 0} := by
      by_contra hnb
      rw [Real.sSup_of_not_bddAbove hnb] at h
      exact absurd h (not_lt.2 hx)
    have hne : {s : ℝ | 0 ≤ s ∧ c s = 0}.Nonempty := by
      rcases Set.eq_empty_or_nonempty {s : ℝ | 0 ≤ s ∧ c s = 0} with hE | hne'
      · rw [hE, Real.sSup_empty] at h
        exact absurd h (not_lt.2 hx)
      · exact hne'
    obtain ⟨s, hs, hxs⟩ := exists_lt_of_lt_csSup hne h
    exact ⟨hb, s, hxs, hs.2⟩
  · rintro ⟨hb, s, hxs, hcs⟩
    exact lt_of_lt_of_le hxs (le_csSup hb ⟨by linarith, hcs⟩)

/-- The zero set of a continuous path is bounded above iff it has no zero beyond some natural number. -/
lemma bddAbove_iff_exists_nat (c : ℝ → ℝ) :
    BddAbove {s : ℝ | 0 ≤ s ∧ c s = 0} ↔ ∃ N : ℕ, ¬ ∃ s, (N : ℝ) < s ∧ c s = 0 := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨⌈M⌉₊, ?_⟩
    rintro ⟨s, hs, hcs⟩
    have hmem : s ∈ {s : ℝ | 0 ≤ s ∧ c s = 0} :=
      ⟨le_trans (Nat.cast_nonneg _) hs.le, hcs⟩
    have h1 : s ≤ M := hM hmem
    have h2 : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
    linarith
  · rintro ⟨N, hN⟩
    refine ⟨(N : ℝ), fun s hs => ?_⟩
    by_contra hlt
    have hlt' : (N : ℝ) < s := not_le.1 hlt
    exact hN ⟨s, hlt', hs.2⟩

/-- The last zero of the drifted path is a Borel function of the path. -/
lemma measurable_lastZeroR_dmsDriftedCoord (d : ℝ) :
    Measurable (fun p : MarkovProcess.ContinuousPath ℝ =>
      MatedCRTHarmonic.MatedCRT.lastZeroR (dmsDriftedCoord d p)) := by
  refine measurable_of_Ioi fun x => ?_
  rcases lt_or_ge x 0 with hx | hx
  · have hset : (fun p : MarkovProcess.ContinuousPath ℝ =>
        MatedCRTHarmonic.MatedCRT.lastZeroR (dmsDriftedCoord d p)) ⁻¹' Ioi x = univ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le hx (lastZeroR_nonneg _)
    rw [hset]
    exact MeasurableSet.univ
  · have hset : (fun p : MarkovProcess.ContinuousPath ℝ =>
        MatedCRTHarmonic.MatedCRT.lastZeroR (dmsDriftedCoord d p)) ⁻¹' Ioi x =
        (⋃ N : ℕ, {p : MarkovProcess.ContinuousPath ℝ | ∃ s, (N : ℝ) < s ∧ dmsDriftedCoord d p s = 0}ᶜ) ∩
          {p : MarkovProcess.ContinuousPath ℝ | ∃ s, x < s ∧ dmsDriftedCoord d p s = 0} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_inter_iff, Set.mem_iUnion,
        Set.mem_compl_iff, Set.mem_ofPred_eq]
      rw [lt_lastZeroR_iff (dmsDriftedCoord d p) hx, bddAbove_iff_exists_nat]
    rw [hset]
    exact MeasurableSet.inter (MeasurableSet.iUnion fun N => (measurableSet_dmsZeroAbove d N).compl)
      (measurableSet_dmsZeroAbove d x)

/-- For each fixed time `t`, the drifted post-last-zero coordinate is a Borel function of the path. -/
lemma measurable_dmsDriftedCoord_shift (d : ℝ) (t : ℝ≥0) :
    Measurable (fun p : MarkovProcess.ContinuousPath ℝ =>
      dmsDriftedCoord d p (MatedCRTHarmonic.MatedCRT.lastZeroR (dmsDriftedCoord d p) + (t : ℝ))) := by
  have hu : Measurable (Function.uncurry fun (s : ℝ) (p : MarkovProcess.ContinuousPath ℝ) =>
      dmsDriftedCoord d p s) :=
    measurable_uncurry_of_continuous_of_measurable (fun p => continuous_dmsDriftedCoord d p)
      (fun s => measurable_dmsDriftedCoord d s)
  have hpair : Measurable (fun p : MarkovProcess.ContinuousPath ℝ =>
      (MatedCRTHarmonic.MatedCRT.lastZeroR (dmsDriftedCoord d p) + (t : ℝ), p)) :=
    ((measurable_lastZeroR_dmsDriftedCoord d).add_const (t : ℝ)).prodMk measurable_id
  exact hu.comp hpair

/-- The drifted post-last-zero path is continuous in time, for every continuous path. -/
lemma continuous_dmsDriftedPostLastZeroPath_path (d : ℝ) (p : MarkovProcess.ContinuousPath ℝ) :
    Continuous fun t : ℝ≥0 => dmsDriftedPostLastZeroPath d (fun s => p s) t := by
  have h : (fun t : ℝ≥0 => dmsDriftedPostLastZeroPath d (fun s => p s) t) =
      fun t : ℝ≥0 => dmsDriftedCoord d p
        (MatedCRTHarmonic.MatedCRT.lastZeroR (dmsDriftedCoord d p) + (t : ℝ)) := rfl
  rw [h]
  exact (continuous_dmsDriftedCoord d p).comp (continuous_const.add NNReal.continuous_coe)

/-- The drifted post-last-zero path `t ↦ c(ℓ + t)` (DMS Remark 4.4) as a function of the continuous path. -/
def dmsPathMap (d : ℝ) (p : MarkovProcess.ContinuousPath ℝ) : MarkovProcess.ContinuousPath ℝ :=
  ⟨fun t => dmsDriftedPostLastZeroPath d (fun s => p s) t,
    continuous_dmsDriftedPostLastZeroPath_path d p⟩

/-- The drifted post-last-zero map is Borel on the path space. -/
lemma measurable_dmsPathMap (d : ℝ) : Measurable (dmsPathMap d) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  exact measurable_dmsDriftedCoord_shift d t

/-- **Concrete measurable path-valued version on the Wiener space** (steps4-final Section 2, lines 429-441).
A Borel map `F` of the path with `F ω = dmsDriftedPostLastZeroPath d ω` at every time, for every path. -/
theorem exists_measurable_dmsDriftedPostLastZeroPath_wiener (d : ℝ) :
    ∃ F : MarkovProcess.ContinuousPath ℝ → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      ∀ᵐ ω ∂(MarkovProcess.brownianMotion 0), ∀ t : ℝ≥0,
        F ω t = dmsDriftedPostLastZeroPath d (fun s => ω s) t :=
  ⟨dmsPathMap d, measurable_dmsPathMap d, Filter.Eventually.of_forall fun _ _ => rfl⟩

/-! ### Law of the path map of a continuous Brownian motion -/

/-- The coordinate-evaluation map from continuous paths to all functions `ℝ≥0 → ℝ`. -/
def coordMap (p : MarkovProcess.ContinuousPath ℝ) : ℝ≥0 → ℝ := fun t => p t

lemma measurable_coordMap : Measurable coordMap :=
  measurable_pi_iff.2 fun t => MarkovProcess.ContinuousPath.measurable_coordinateProcess t

/-- A probability law on continuous paths is determined by the law of its coordinate-evaluation map:
the Borel σ-algebra of `C(ℝ≥0, ℝ)` is generated by the evaluations (`ContinuousMap` Borel criterion). -/
lemma eq_of_map_coordMap (μ ν : Measure (MarkovProcess.ContinuousPath ℝ))
    (h : μ.map coordMap = ν.map coordMap) : μ = ν := by
  have hcomap : (inferInstance : MeasurableSpace (MarkovProcess.ContinuousPath ℝ)) =
      MeasurableSpace.comap coordMap MeasurableSpace.pi := by
    refine le_antisymm ?_ measurable_coordMap.comap_le
    show borel (MarkovProcess.ContinuousPath ℝ) ≤ _
    rw [ContinuousMap.borel_eq_iSup_comap_eval]
    refine iSup_le fun a => ?_
    exact ((measurable_pi_apply a).comp (comap_measurable coordMap)).comap_le
  ext A hA
  have hA' : MeasurableSet[MeasurableSpace.comap coordMap MeasurableSpace.pi] A := by
    rw [← hcomap]
    exact hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA'
  calc μ (coordMap ⁻¹' B) = μ.map coordMap B := (Measure.map_apply measurable_coordMap hB).symm
    _ = ν.map coordMap B := by rw [h]
    _ = ν (coordMap ⁻¹' B) := Measure.map_apply measurable_coordMap hB

/-- **Law of the path map of a Brownian motion.** If `D` is a Brownian motion (Mathlib
`ProbabilityTheory.IsBrownianReal`) with measurable coordinates and everywhere continuous paths, the law of
its path map is the Wiener measure `brownianMotion 0`. Both sides have the same finite-dimensional laws
(`IsPreBrownianReal.hasLaw`: the projective family), and `Measure.ext_of_map_restrict_eq`
(lattice-probability, `GaussianLaw.lean`) gives equality of the laws on `ℝ≥0 → ℝ`. -/
lemma map_pathMap_eq_brownianMotion {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : ℝ≥0 → Ω → ℝ} (hD : IsBrownianReal D P)
    (hDm : ∀ t, Measurable (D t)) (hDc : ∀ ω, Continuous fun t => D t ω) :
    P.map (fun ω => (⟨fun t => D t ω, hDc ω⟩ : MarkovProcess.ContinuousPath ℝ)) =
      MarkovProcess.brownianMotion 0 := by
  have hW : IsBrownianReal (fun (t : ℝ≥0) (w : MarkovProcess.ContinuousPath ℝ) => w t)
      (MarkovProcess.brownianMotion 0) := brownianMotion_zero_isBrownianReal
  have hΨm : Measurable (fun ω => (⟨fun t => D t ω, hDc ω⟩ : MarkovProcess.ContinuousPath ℝ)) :=
    ContinuousMap.measurable_iff_eval.2 fun t => hDm t
  -- both coordinate laws on `ℝ≥0 → ℝ` are projective limits of the Wiener family `I ↦ W.map (I.restrict ·)`
  have hDlim : IsProjectiveLimit (P.map (coordMap ∘ fun ω => (⟨fun t => D t ω, hDc ω⟩ :
      MarkovProcess.ContinuousPath ℝ))) (fun I => (MarkovProcess.brownianMotion 0).map
        (fun w => I.restrict (fun t => w t))) := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (measurable_coordMap.comp hΨm)]
    exact (hD.toIsPreBrownianReal.hasLaw I).map_eq.trans (hW.toIsPreBrownianReal.hasLaw I).map_eq.symm
  have hWlim : IsProjectiveLimit ((MarkovProcess.brownianMotion 0).map coordMap)
      (fun I => (MarkovProcess.brownianMotion 0).map (fun w => I.restrict (fun t => w t))) := by
    intro I
    exact Measure.map_map (Finset.measurable_restrict I) measurable_coordMap
  apply eq_of_map_coordMap
  rw [Measure.map_map measurable_coordMap hΨm]
  exact IsProjectiveLimit.unique hDlim hWlim

end MatedCRT.Sec1
