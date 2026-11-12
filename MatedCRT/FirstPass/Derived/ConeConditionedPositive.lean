import MatedCRT.FirstPass.Derived.ConeRadialInvariance

/-!
# Strict positivity of the drifted conditioned limit

If `ν'` is a probability measure on continuous paths whose stopped paths `stopAt (hitFrom c 0 z) z`
have, for Lebesgue-almost every `c > 0`, the law of the first up-crossing piece of the drifted
Brownian motion, then `ν'`-almost surely `0 < z s` for all `s > 0`.

The first up-crossing piece of a path with finite `d₁` is `s ↦ w (min (g + s) d)` for an up-crossing
interval `[g, d]`, which is strictly positive on `(0, ∞)`. The set of strictly positive continuous
paths is not measurable for the product sigma-algebra, but it agrees on continuous paths with the
measurable set `posSet` defined by countably many conditions at rational times.

* `posSet`, `measurableSet_posSet`, `mem_posSet_iff`.
* `ae_forall_pos_of_piece_law`.
-/

namespace MatedCRT.ConeConditionedPositive

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Paths that, for every `n`, are bounded below by some `1/(k+1)` at all rational times in
`[1/(n+1), n+1]`. -/
def posSet : Set (ℝ≥0 → ℝ) :=
  ⋂ n : ℕ, ⋃ k : ℕ, ⋂ q : ℚ, ⋂ (_ : 1 / ((n : ℝ) + 1) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (n : ℝ) + 1),
    {u | 1 / ((k : ℝ) + 1) ≤ u (Real.toNNReal q)}

lemma measurableSet_posSet : MeasurableSet posSet :=
  MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => measurableSet_le measurable_const (measurable_pi_apply _)

/-- On continuous paths, `posSet` is the set of strictly positive paths on `(0, ∞)`. -/
lemma mem_posSet_iff {u : ℝ≥0 → ℝ} (hu : Continuous u) :
    u ∈ posSet ↔ ∀ s : ℝ≥0, 0 < s → 0 < u s := by
  have hf : Continuous fun t : ℝ => u (Real.toNNReal t) := hu.comp continuous_real_toNNReal
  constructor
  · intro h s hs
    obtain ⟨n, hn⟩ := exists_nat_gt (max (s : ℝ) (1 / (s : ℝ)))
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    have hn1 : (s : ℝ) < (n : ℝ) + 1 := by
      have := (le_max_left (s : ℝ) (1 / (s : ℝ))).trans_lt hn
      linarith
    have hn2 : 1 / ((n : ℝ) + 1) < s := by
      have h2 := (le_max_right (s : ℝ) (1 / (s : ℝ))).trans_lt hn
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hs0] at h2
      nlinarith
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (Set.mem_iInter.1 h n)
    have hclosed : IsClosed {t : ℝ | 1 / ((k : ℝ) + 1) ≤ u (Real.toNNReal t)} :=
      isClosed_le continuous_const hf
    have hsub : Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ∩ Set.range ((↑) : ℚ → ℝ) ⊆
        {t : ℝ | 1 / ((k : ℝ) + 1) ≤ u (Real.toNNReal t)} := by
      rintro t ⟨ht, q, rfl⟩
      have := Set.mem_iInter.1 (Set.mem_iInter.1 hk q) ⟨ht.1.le, ht.2.le⟩
      exact this
    have hcl := hclosed.closure_subset_iff.2 hsub
    have hmem := hcl ((Rat.denseRange_cast (𝕜 := ℝ)).open_subset_closure_inter isOpen_Ioo
      (show (s : ℝ) ∈ Set.Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) from ⟨hn2, hn1⟩))
    have : 1 / ((k : ℝ) + 1) ≤ u (Real.toNNReal (s : ℝ)) := hmem
    rw [Real.toNNReal_coe] at this
    exact lt_of_lt_of_le (by positivity) this
  · intro h
    refine Set.mem_iInter.2 fun n => ?_
    have hKc : IsCompact (Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) := isCompact_Icc
    have hne : (Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)).Nonempty :=
      ⟨(n : ℝ) + 1, by
        refine ⟨?_, le_rfl⟩
        rw [div_le_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith⟩
    obtain ⟨x, hxK, hx⟩ := hKc.exists_isMinOn hne hf.continuousOn
    have hxpos : 0 < u (Real.toNNReal x) := by
      refine h _ ?_
      have : (0 : ℝ) < x := lt_of_lt_of_le (by positivity) hxK.1
      exact Real.toNNReal_pos.2 this
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hxpos
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iInter.2 fun q => Set.mem_iInter.2 fun hq => ?_⟩
    exact hk.le.trans (hx hq)

/-- Under the drifted Brownian law, almost surely the first up-crossing piece to a level `c > 0` is
strictly positive on `(0, ∞)`. -/
lemma ae_piece_mem_posSet_driftLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : ProbabilityTheory.IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {μ : ℝ} (hμ : 0 < μ)
    {c : ℝ} (hc : 0 < c) :
    ∀ᵐ w : C(ℝ≥0, ℝ) ∂(LatticeProb.driftLaw P B hcont μ),
      LatticeProb.firstUpcrossPiece c (w : ℝ≥0 → ℝ) ∈ posSet := by
  filter_upwards [LatticeProb.ae_upcrossEnd₁_lt_top_driftLaw hB hm hcont hμ hc] with w hw
  obtain ⟨d, hd, hup, -⟩ := LatticeProb.isUpcross_upcrossStart₁ w.continuous hc hw.ne
  set g := LatticeProb.upcrossStart₁ c (w : ℝ≥0 → ℝ) with hg
  have hpiece : LatticeProb.firstUpcrossPiece c (w : ℝ≥0 → ℝ) = fun s => w (min (g + s) d) := by
    funext s
    simp only [LatticeProb.firstUpcrossPiece, LatticeProb.pieceAt, hd, ENNReal.toNNReal_coe, hg]
  have hcp : Continuous fun s : ℝ≥0 => w (min (g + s) d) :=
    w.continuous.comp ((continuous_const.add continuous_id).min continuous_const)
  rw [hpiece, mem_posSet_iff hcp]
  intro s hs
  rcases lt_or_ge (g + s) d with h | h
  · rw [min_eq_left h.le]
    exact (hup.2.2.2 (g + s) (by simpa using hs) h).1
  · rw [min_eq_right h, hup.2.2.1]
    exact hc

/-- **Strict positivity of the limit.**  If, for Lebesgue-almost every level `c > 0`, the path
`ν'` stopped at its first hit of `c` has the law of the first up-crossing piece of the drifted
Brownian motion, then `ν'`-almost surely `0 < z s` for all `s > 0`. -/
theorem ae_forall_pos_of_piece_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : ProbabilityTheory.IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {μ : ℝ} (hμ : 0 < μ)
    {ν' : Measure C(ℝ≥0, ℝ)}
    (hpiece : ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))),
      (LatticeProb.driftLaw P B hcont μ).map
          (fun w : C(ℝ≥0, ℝ) => LatticeProb.firstUpcrossPiece c (w : ℝ≥0 → ℝ)) =
        ν'.map (fun z : C(ℝ≥0, ℝ) =>
          (LatticeProb.stopAt (LatticeProb.hitFrom c 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ))) :
    ∀ᵐ z : C(ℝ≥0, ℝ) ∂ν', ∀ s : ℝ≥0, 0 < s → 0 < z s := by
  have hex : ∀ n : ℕ, ∃ c : ℝ, c ∈ Ioo (n : ℝ) ((n : ℝ) + 1) ∧
      (LatticeProb.driftLaw P B hcont μ).map
          (fun w : C(ℝ≥0, ℝ) => LatticeProb.firstUpcrossPiece c (w : ℝ≥0 → ℝ)) =
        ν'.map (fun z : C(ℝ≥0, ℝ) =>
          (LatticeProb.stopAt (LatticeProb.hitFrom c 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ)) := by
    intro n
    have h1 := ae_restrict_of_ae_restrict_of_subset (s := Ioo (n : ℝ) ((n : ℝ) + 1))
      (fun c hc => (show (0 : ℝ) < c from lt_of_le_of_lt (Nat.cast_nonneg n) hc.1)) hpiece
    have h2 : ∀ᵐ c ∂(volume.restrict (Ioo (n : ℝ) ((n : ℝ) + 1))), c ∈ Ioo (n : ℝ) ((n : ℝ) + 1) :=
      ae_restrict_mem measurableSet_Ioo
    have hne : (volume.restrict (Ioo (n : ℝ) ((n : ℝ) + 1))) ≠ 0 := by
      intro h0
      rw [Measure.restrict_eq_zero, Real.volume_Ioo] at h0
      simp at h0
    have : (ae (volume.restrict (Ioo (n : ℝ) ((n : ℝ) + 1)))).NeBot := ae_neBot.2 hne
    obtain ⟨c, hc1, hc2⟩ := (h2.and h1).exists
    exact ⟨c, hc1, hc2⟩
  choose c hcmem hceq using hex
  have hae : ∀ᵐ z : C(ℝ≥0, ℝ) ∂ν', ∀ n : ℕ,
      (LatticeProb.stopAt (LatticeProb.hitFrom (c n) 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ) ∈ posSet := by
    rw [ae_all_iff]
    intro n
    have hcpos : 0 < c n := lt_of_le_of_lt (Nat.cast_nonneg n) (hcmem n).1
    have hFm : Measurable fun z : C(ℝ≥0, ℝ) =>
        (LatticeProb.stopAt (LatticeProb.hitFrom (c n) 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ) :=
      measurable_pi_iff.2 fun s => (continuous_eval_const s).measurable.comp
        (LatticeProb.measurable_stopAt_path
          (LatticeProb.measurable_hitFrom (r := fun _ => 0) measurable_const (c n)))
    refine ae_of_ae_map (p := fun u => u ∈ posSet) hFm.aemeasurable ?_
    rw [← hceq n]
    exact (ae_map_iff (LatticeProb.measurable_firstUpcrossPiece (c n)).aemeasurable
      measurableSet_posSet).2 (ae_piece_mem_posSet_driftLaw hB hm hcont hμ hcpos)
  filter_upwards [hae] with z hz s hs
  obtain ⟨K, hK⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := s)).image z.continuous).bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt K
  have hcK : K < c n := hn.trans (hcmem n).1
  have hle : (s : ℝ≥0∞) ≤ LatticeProb.hitFrom (c n) 0 (z : ℝ≥0 → ℝ) := by
    unfold LatticeProb.hitFrom
    refine le_iInf₂ fun t ht => ?_
    by_contra hlt
    rw [not_le] at hlt
    have hts : t < s := by exact_mod_cast hlt
    have h1 : z t ≤ K := hK ⟨t, ⟨(zero_le : (0 : ℝ≥0) ≤ t), hts.le⟩, rfl⟩
    have h2 : z t = c n := ht.2
    linarith
  have hpos := (mem_posSet_iff (LatticeProb.stopAt _ z).continuous).1 (hz n) s hs
  rwa [LatticeProb.stopAt_apply, min_eq_left hle, ENNReal.toNNReal_coe] at hpos

end MatedCRT.ConeConditionedPositive

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped NNReal ENNReal BoundedContinuousFunction

/-- **Strict positivity of the drifted conditioned limit.**  For `ν` the weak limit of Brownian motion
conditioned to stay above the line of slope `-(Q - γ)`, the drifted limit `ν.map (driftMap (Q - γ))`
satisfies `0 < z s` for all `s > 0` almost surely. -/
theorem ae_forall_pos_driftMap_of_isBMConditionedPositive {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {ν : Measure (ContinuousPath ℝ)} (hν : IsBMConditionedPositive (lqgQ γ - γ) ν) :
    ∀ᵐ z : C(ℝ≥0, ℝ) ∂(ν.map (LatticeProb.driftMap (lqgQ γ - γ))),
      ∀ s : ℝ≥0, 0 < s → 0 < z s := by
  have hμ := lqgQ_sub_pos' hγ0 hγ2
  have : IsProbabilityMeasure ν := hν.1
  have hpre : ProbabilityTheory.IsPreBrownianReal (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t)
      (brownianMotion 0) := by
    simpa using MatedCRT.ExitRestart.brownianMotion_isPreBrownianReal 0
  have hB : ProbabilityTheory.IsBrownianReal (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t)
      (brownianMotion 0) := ⟨hpre, Filter.Eventually.of_forall fun ω => ω.continuous⟩
  have hm : ∀ t : ℝ≥0, Measurable fun ω : ContinuousPath ℝ => ω t := fun t =>
    ContinuousPath.measurable_coordinateProcess t
  have hcont : ∀ ω : ContinuousPath ℝ, Continuous fun s : ℝ≥0 => ω s := fun ω => ω.continuous
  have hid : LatticeProb.pathMap (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t) hcont = id :=
    funext fun ω => ContinuousMap.ext fun t => rfl
  have : IsProbabilityMeasure (ν.map (LatticeProb.driftMap (lqgQ γ - γ))) :=
    (Measure.isProbabilityMeasure_map_iff (μ := ν)
      (LatticeProb.measurable_driftMap (lqgQ γ - γ)).aemeasurable).2 inferInstance
  refine MatedCRT.ConeConditionedPositive.ae_forall_pos_of_piece_law hB hm hcont hμ ?_
  refine LatticeProb.ae_map_piece_eq hB hm hcont hμ (ν := ν) fun f => ?_
  have hset : ∀ δ : ℝ, LatticeProb.driftMap (lqgQ γ - γ) ⁻¹' LatticeProb.staySet δ =
      stayAboveEvent (lqgQ γ - γ) δ := by
    intro δ
    ext w
    simp [LatticeProb.staySet, stayAboveEvent]
  simp only [hid, Measure.map_id, hset]
  exact hν.2 f

end MatedCRT.FirstPass.Derived
