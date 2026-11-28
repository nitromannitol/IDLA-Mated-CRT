import LatticeProb.Prob.BrownianLevyReflection
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSteps

/-!
# The reflection barrier for Brownian motion

For a real Brownian motion `B` and `a ≥ 0`, the probability that the path started at `B 0`
reaches the level `-a` before time `T` is at least twice the probability that `B T - B 0 < -a`.
This is the converse of Lévy's inequality, and together with the symmetry of the centred Gaussian
law of `B T - B 0` it yields the survival bound
`P (∀ s ≤ T, -a < B s - B 0) ≤ a √(2 / (π T))`.

The proof works on the dyadic grids `t k = T * min k 2 ^ n / 2 ^ n`.  If the path first passes
below `-a` at the grid point `t k` without overshooting by more than `η`, then the increment from
`t k` to `T` is independent of the passage event and is negative with probability at most
`1 / 2`; the passages with overshoot larger than `η` need an increment over a grid cell exceeding
`η`, and by uniform continuity of the paths this event has probability tending to zero with the
mesh.  A Brownian motion has almost surely continuous paths but is only assumed to have measurable
values up to modification, so the argument is carried out for a measurable modification, which
agrees with `B` at all the countably many grid times almost surely.

## Main results

* `two_mul_measure_lt_le_measure_exists_le`: `2 P (B T - B 0 < -a) ≤ P (∃ s ≤ T, B s - B 0 ≤ -a)`.
* `measure_forall_gt_neg_le`: `P (∀ s ≤ T, -a < B s - B 0) ≤ a √(2 / (π T))`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter MeasurableSpace LatticeProb

open scoped ENNReal NNReal Topology

namespace MatedCRT.PeanosphereTriplePoints

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A centred Gaussian variable is positive with probability at most one half. -/
private theorem two_mul_measure_pos_le_one [IsProbabilityMeasure P] {Z : Ω → ℝ} {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) : 2 * P {ω | 0 < Z ω} ≤ 1 := by
  have h1 : P {ω | 0 < Z ω} = gaussianReal 0 v (Set.Ioi 0) := by
    rw [← hZ.map_eq, Measure.map_apply_of_aemeasurable hZ.aemeasurable measurableSet_Ioi]
    rfl
  have hneg : (gaussianReal 0 v).map (fun x => -x) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  have h2 : gaussianReal 0 v (Set.Iio 0) = gaussianReal 0 v (Set.Ioi 0) := by
    conv_lhs => rw [← hneg]
    rw [Measure.map_apply measurable_neg measurableSet_Iio]
    congr 1
    ext x
    simp
  have hd : Disjoint (Set.Ioi (0 : ℝ)) (Set.Iio 0) :=
    Set.disjoint_left.2 fun x hx hx' => lt_asymm (Set.mem_Ioi.1 hx) (Set.mem_Iio.1 hx')
  have h3 : gaussianReal 0 v (Set.Ioi 0) + gaussianReal 0 v (Set.Iio 0) ≤ 1 := by
    rw [← measure_union hd measurableSet_Iio]
    exact prob_le_one
  rw [h2, ← two_mul] at h3
  rw [h1]
  exact h3

/-- **The reflection inequality on a finite grid with bounded overshoot.**  For a measurable
pre-Brownian motion `X`, a monotone family of times `t 0 ≤ … ≤ t N`, `a ≥ 0` and `η > 0`, twice the
probability that `X (t N) - X (t 0) > a + η` is at most the probability of reaching `a` on the
grid plus twice the probability that some increment of the grid exceeds `η`. -/
private theorem two_mul_measure_gt_le_grid [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ}
    (hX : IsPreBrownianReal X P) (hm : ∀ t, Measurable (X t)) (N : ℕ) (t : ℕ → ℝ≥0)
    (hmono : Monotone t) {a : ℝ} (ha : 0 ≤ a) {η : ℝ} (hη : 0 < η) :
    2 * P {ω | a + η < X (t N) ω - X (t 0) ω} ≤
      P {ω | ∃ k ≤ N, a ≤ X (t k) ω - X (t 0) ω} +
        2 * P {ω | ∃ j < N, η < X (t (j + 1)) ω - X (t j) ω} := by
  classical
  set D : ℕ → Ω → ℝ := fun i ω => X (t (i + 1)) ω - X (t i) ω with hD
  have hDm : ∀ i, Measurable (D i) := fun i => (hm _).sub (hm _)
  have hind : iIndepFun D P := hX.hasIndepIncrements.nat hmono
  set m : ℕ → MeasurableSpace Ω := fun i => MeasurableSpace.comap (D i) inferInstance with hmdef
  have hle : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω) := fun i => (hDm i).comap_le
  have hiIndep : iIndep m P := hind
  have hIndepk : ∀ k : ℕ, Indep (⨆ i ∈ Set.Iio k, m i) (⨆ i ∈ Set.Ici k, m i) P := fun k =>
    indep_iSup_of_disjoint hle hiIndep (Set.Iio_disjoint_Ici le_rfl)
  have hmeas_sum : ∀ (I : Set ℕ) (s : Finset ℕ), (∀ i ∈ s, i ∈ I) →
      Measurable[⨆ i ∈ I, m i] (fun ω => ∑ i ∈ s, D i ω) := by
    intro I s hs
    refine Finset.measurable_sum s (fun i hi => ?_)
    exact Measurable.mono (measurable_iff_comap_le.2 le_rfl) (le_biSup m (hs i hi)) le_rfl
  set S : ℕ → Ω → ℝ := fun j ω => X (t j) ω - X (t 0) ω with hS
  have hSsum : ∀ j, (fun ω => ∑ i ∈ Finset.range j, D i ω) = S j := by
    intro j
    funext ω
    exact Finset.sum_range_sub (fun i => X (t i) ω) j
  have hSmeas : ∀ k j, j ≤ k → Measurable[⨆ i ∈ Set.Iio k, m i] (S j) := by
    intro k j hjk
    rw [← hSsum j]
    exact hmeas_sum _ _ (fun i hi => lt_of_lt_of_le (Finset.mem_range.1 hi) hjk)
  set A : ℕ → Set Ω := fun k =>
    {ω | a ≤ S k ω} ∩ ⋂ j ∈ Finset.range k, {ω | S j ω < a} with hA
  set A' : ℕ → Set Ω := fun k => A k ∩ {ω | S k ω ≤ a + η} with hA'
  set G : ℕ → Set Ω := fun k => {ω | 0 < X (t N) ω - X (t k) ω} with hG
  have hAmeas : ∀ k, MeasurableSet[⨆ i ∈ Set.Iio k, m i] (A k) := by
    intro k
    refine MeasurableSet.inter
      (measurableSet_le measurable_const (hSmeas k k le_rfl)) ?_
    refine MeasurableSet.biInter (Finset.range k).countable_toSet (fun j hj => ?_)
    exact measurableSet_lt
      (hSmeas k j (le_of_lt (Finset.mem_range.1 hj))) measurable_const
  have hA'meas : ∀ k, MeasurableSet[⨆ i ∈ Set.Iio k, m i] (A' k) := fun k =>
    (hAmeas k).inter (measurableSet_le (hSmeas k k le_rfl) measurable_const)
  have hGmeas : ∀ k, k ≤ N → MeasurableSet[⨆ i ∈ Set.Ici k, m i] (G k) := by
    intro k hk
    have heq : (fun ω => ∑ i ∈ Finset.Ico k N, D i ω) = fun ω => X (t N) ω - X (t k) ω := by
      funext ω
      exact sum_Ico_sub_telescope (fun i => X (t i) ω) hk
    have hmeas : Measurable[⨆ i ∈ Set.Ici k, m i] (fun ω => X (t N) ω - X (t k) ω) := by
      rw [← heq]
      exact hmeas_sum _ _ (fun i hi => (Finset.mem_Ico.1 hi).1)
    exact measurableSet_lt measurable_const hmeas
  have hA'm : ∀ k, MeasurableSet (A' k) := fun k =>
    (iSup₂_le fun i (_ : i ∈ Set.Iio k) => hle i) _ (hA'meas k)
  have hGm : ∀ k, MeasurableSet (G k) := fun k =>
    measurableSet_lt measurable_const ((hm _).sub (hm _))
  have hindep : ∀ k, k ≤ N → P (A' k ∩ G k) = P (A' k) * P (G k) := by
    intro k hk
    exact ((hIndepk k).indepSet_of_measurableSet (hA'meas k) (hGmeas k hk)).measure_inter_eq_mul
  have hdisj : ∀ j k : ℕ, j ≠ k → Disjoint (A' j) (A' k) := by
    intro j k hjk
    rw [Set.disjoint_left]
    rintro ω ⟨⟨hωj, hωj'⟩, -⟩ ⟨⟨hωk, hωk'⟩, -⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hωj' hωk' hωj hωk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact absurd hωj (not_le.2 (hωk' j (Finset.mem_range.2 h)))
    · exact absurd hωk (not_le.2 (hωj' k (Finset.mem_range.2 h)))
  have hGhalf : ∀ k, 2 * P (G k) ≤ 1 := fun k =>
    two_mul_measure_pos_le_one (hX.hasLaw_sub (t N) (t k))
  set Bad : Set Ω := {ω | ∃ j < N, η < D j ω} with hBad
  have hcover : {ω | a + η < X (t N) ω - X (t 0) ω} ⊆
      (⋃ k ∈ Finset.range (N + 1), (A' k ∩ G k)) ∪ Bad := by
    intro ω hω
    have hω' : a + η < S N ω := hω
    have hS0 : S 0 ω = 0 := by simp [hS]
    have hex : ∃ j, a ≤ S j ω := ⟨N, by linarith⟩
    obtain ⟨k0, hk0spec, hbefore⟩ : ∃ k0, a ≤ S k0 ω ∧ ∀ j < k0, S j ω < a :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_le.1 (Nat.find_min hex hj)⟩
    have hk0N : k0 ≤ N := by
      by_contra h
      have := hbefore N (not_le.1 h)
      linarith
    by_cases hov : S k0 ω ≤ a + η
    · left
      refine Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hk0N))
        ⟨⟨⟨hk0spec, ?_⟩, hov⟩, ?_⟩
      · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
        exact fun j hj => hbefore j (Finset.mem_range.1 hj)
      · show 0 < X (t N) ω - X (t k0) ω
        have h3 : S N ω - S k0 ω = X (t N) ω - X (t k0) ω := by simp only [hS]; ring
        linarith
    · right
      have hk0pos : k0 ≠ 0 := by
        intro h0
        apply hov
        rw [h0, hS0]
        linarith
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0pos
      have hjN : j < N := by omega
      refine ⟨j, hjN, ?_⟩
      have h1 := hbefore j (by omega)
      have h2 : S k0 ω = S (j + 1) ω := by rw [hj]
      have h3 : D j ω = S (j + 1) ω - S j ω := by simp only [hD, hS]; ring
      rw [h3]
      linarith
  have hP : P {ω | a + η < X (t N) ω - X (t 0) ω} ≤
      ∑ k ∈ Finset.range (N + 1), P (A' k ∩ G k) + P Bad :=
    calc P {ω | a + η < X (t N) ω - X (t 0) ω}
        ≤ P ((⋃ k ∈ Finset.range (N + 1), (A' k ∩ G k)) ∪ Bad) := measure_mono hcover
      _ ≤ P (⋃ k ∈ Finset.range (N + 1), (A' k ∩ G k)) + P Bad := measure_union_le _ _
      _ ≤ _ := by gcongr; exact measure_biUnion_finset_le _ _
  have hsum : 2 * ∑ k ∈ Finset.range (N + 1), P (A' k ∩ G k) ≤
      P {ω | ∃ k ≤ N, a ≤ X (t k) ω - X (t 0) ω} := by
    calc 2 * ∑ k ∈ Finset.range (N + 1), P (A' k ∩ G k)
        = ∑ k ∈ Finset.range (N + 1), 2 * P (A' k ∩ G k) := Finset.mul_sum _ _ _
      _ ≤ ∑ k ∈ Finset.range (N + 1), P (A' k) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkN : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
          rw [hindep k hkN]
          calc 2 * (P (A' k) * P (G k)) = P (A' k) * (2 * P (G k)) := by ring
            _ ≤ P (A' k) * 1 := by gcongr; exact hGhalf k
            _ = P (A' k) := mul_one _
      _ = P (⋃ k ∈ Finset.range (N + 1), A' k) :=
          (measure_biUnion_finset (fun j _ k _ hjk => hdisj j k hjk) (fun k _ => hA'm k)).symm
      _ ≤ _ := by
          refine measure_mono (Set.iUnion₂_subset fun k hk => ?_)
          rintro ω ⟨⟨hωk, -⟩, -⟩
          exact ⟨k, Nat.lt_succ_iff.1 (Finset.mem_range.1 hk), hωk⟩
  calc 2 * P {ω | a + η < X (t N) ω - X (t 0) ω}
      ≤ 2 * (∑ k ∈ Finset.range (N + 1), P (A' k ∩ G k) + P Bad) := by gcongr
    _ = 2 * ∑ k ∈ Finset.range (N + 1), P (A' k ∩ G k) + 2 * P Bad := mul_add _ _ _
    _ ≤ _ := by gcongr

/-- The dyadic grid on `[0, T]` of mesh `T / 2 ^ n`, constant after its last point `T`. -/
private noncomputable def gridTime (T : ℝ≥0) (n k : ℕ) : ℝ≥0 :=
  T * dyadicGrid n (min k (2 ^ n))

private theorem gridTime_mono (T : ℝ≥0) (n : ℕ) : Monotone (gridTime T n) := fun _ _ h =>
  mul_le_mul_of_nonneg_left (dyadicGrid_mono n (min_le_min_right _ h)) (zero_le)

private theorem gridTime_zero (T : ℝ≥0) (n : ℕ) : gridTime T n 0 = 0 := by
  simp [gridTime, dyadicGrid]

private theorem dyadicGrid_two_pow (n : ℕ) : dyadicGrid n (2 ^ n) = 1 := by
  simp only [dyadicGrid, Nat.cast_pow, Nat.cast_ofNat]
  exact div_self (pow_ne_zero _ two_ne_zero)

private theorem gridTime_two_pow (T : ℝ≥0) (n : ℕ) : gridTime T n (2 ^ n) = T := by
  simp [gridTime, dyadicGrid_two_pow]

private theorem gridTime_le (T : ℝ≥0) (n k : ℕ) : gridTime T n k ≤ T := by
  calc gridTime T n k ≤ T * dyadicGrid n (2 ^ n) :=
        mul_le_mul_of_nonneg_left (dyadicGrid_mono n (min_le_right _ _)) (zero_le)
    _ = T := by rw [dyadicGrid_two_pow, mul_one]

private theorem coe_gridTime_succ_sub_le (T : ℝ≥0) (n j : ℕ) :
    (gridTime T n (j + 1) : ℝ) - gridTime T n j ≤ T / 2 ^ n := by
  have h1 : ((min (j + 1) (2 ^ n) : ℕ) : ℝ) ≤ ((min j (2 ^ n) : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : min (j + 1) (2 ^ n) ≤ min j (2 ^ n) + 1)
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  simp only [gridTime, NNReal.coe_mul, coe_dyadicGrid]
  have key : (T : ℝ) * (((min (j + 1) (2 ^ n) : ℕ) : ℝ) / 2 ^ n) -
      (T : ℝ) * (((min j (2 ^ n) : ℕ) : ℝ) / 2 ^ n) =
      (T : ℝ) * (((min (j + 1) (2 ^ n) : ℕ) : ℝ) - ((min j (2 ^ n) : ℕ) : ℝ)) / 2 ^ n := by
    ring
  rw [key]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  calc (T : ℝ) * (((min (j + 1) (2 ^ n) : ℕ) : ℝ) - ((min j (2 ^ n) : ℕ) : ℝ))
      ≤ T * 1 := mul_le_mul_of_nonneg_left (by linarith) T.coe_nonneg
    _ = T := mul_one _

/-- The probability that some increment of the dyadic grids of `-B'` exceeds `η` tends to zero
with the mesh, for a measurable modification `B'` of a Brownian motion `B`. -/
private theorem tendsto_measure_bad_grid [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    {B' : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B' t)) (hag : ∀ t, B t =ᵐ[P] B' t) (T : ℝ≥0)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => P {ω | ∃ j < 2 ^ n,
        η < (-B') (gridTime T n (j + 1)) ω - (-B') (gridTime T n j) ω}) atTop (𝓝 0) := by
  have hmeasSet : ∀ n : ℕ, MeasurableSet {ω | ∃ j < 2 ^ n,
      η < (-B') (gridTime T n (j + 1)) ω - (-B') (gridTime T n j) ω} := by
    intro n
    have hset : {ω | ∃ j < 2 ^ n,
        η < (-B') (gridTime T n (j + 1)) ω - (-B') (gridTime T n j) ω} =
        ⋃ j ∈ Finset.range (2 ^ n),
          {ω | η < (-B') (gridTime T n (j + 1)) ω - (-B') (gridTime T n j) ω} := by
      ext ω
      simp
    rw [hset]
    exact Finset.measurableSet_biUnion _ fun j _ =>
      measurableSet_lt measurable_const (((hm _).neg).sub ((hm _).neg))
  have hgrid : ∀ᵐ ω ∂P, ∀ n k, B (gridTime T n k) ω = B' (gridTime T n k) ω :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hag _
  have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := P)
    (A := (∅ : Set Ω)) atTop MeasurableSet.empty hmeasSet (by
      filter_upwards [hB.cont, hgrid] with ω hcont hω
      have hcon : ContinuousOn (fun t : ℝ≥0 => B t ω) (Set.Icc (0 : ℝ≥0) T) :=
        hcont.continuousOn
      obtain ⟨δ, hδ, huu⟩ := Metric.uniformContinuousOn_iff_le.1
        (isCompact_Icc.uniformContinuousOn_of_continuous hcon) η hη
      have hev : ∀ᶠ n : ℕ in atTop, (T : ℝ) / 2 ^ n ≤ δ := by
        have h := (tendsto_const_nhds (x := (T : ℝ))).div_atTop
          (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ)))
        exact h.eventually (ge_mem_nhds hδ)
      filter_upwards [hev] with n hn
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨j, -, hj⟩
      have hle : gridTime T n j ≤ gridTime T n (j + 1) := gridTime_mono T n (Nat.le_succ j)
      have hd : dist (gridTime T n (j + 1)) (gridTime T n j) ≤ δ := by
        rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hle))]
        exact (coe_gridTime_succ_sub_le T n j).trans hn
      have hu := huu (gridTime T n (j + 1)) ⟨zero_le, gridTime_le T n _⟩ (gridTime T n j)
        ⟨zero_le, gridTime_le T n _⟩ hd
      rw [Real.dist_eq, abs_le] at hu
      simp only [Pi.neg_apply, ← hω] at hj
      linarith [hu.1])
  simpa using hlim

/-- **The reflection inequality along the dyadic grids.**  For a measurable modification `B'` of a
Brownian motion, twice the probability that `B' T - B' 0 < -a` is at most the probability that
`B' - B' 0` reaches `-a` at some dyadic grid point of `[0, T]`. -/
private theorem two_mul_measure_lt_le_measure_iUnion_grid [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {B' : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B' t))
    (hag : ∀ t, B t =ᵐ[P] B' t) (T : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    2 * P {ω | B' T ω - B' 0 ω < -a} ≤
      P (⋃ n : ℕ, {ω | ∃ k ≤ 2 ^ n, B' (gridTime T n k) ω - B' 0 ω ≤ -a}) := by
  have hB' : IsPreBrownianReal B' P := hB.toIsPreBrownianReal.congr hag
  have hX : IsPreBrownianReal (-B') P := hB'.neg
  have hXm : ∀ t, Measurable ((-B') t) := fun t => (hm t).neg
  set M : Set Ω := ⋃ n : ℕ, {ω | ∃ k ≤ 2 ^ n, B' (gridTime T n k) ω - B' 0 ω ≤ -a} with hM
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hη : ∀ η : ℝ, 0 < η → 2 * P {ω | B' T ω - B' 0 ω < -(a + η)} ≤ P M := by
    intro η hη
    have hbad := tendsto_measure_bad_grid hB hm hag T hη
    have hlim := (tendsto_const_nhds (x := P M)).add
      (ENNReal.Tendsto.const_mul hbad (Or.inr h2top))
    rw [mul_zero, add_zero] at hlim
    refine ge_of_tendsto' hlim fun n => ?_
    have hg := two_mul_measure_gt_le_grid hX hXm (2 ^ n) (gridTime T n) (gridTime_mono T n) ha hη
    rw [gridTime_two_pow, gridTime_zero] at hg
    have e1 : {ω | a + η < (-B') T ω - (-B') 0 ω} = {ω | B' T ω - B' 0 ω < -(a + η)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Pi.neg_apply]
      constructor <;> intro h <;> linarith
    have e2 : {ω | ∃ k ≤ 2 ^ n, a ≤ (-B') (gridTime T n k) ω - (-B') 0 ω} ⊆ M := by
      intro ω hω
      obtain ⟨k, hk, h⟩ := hω
      simp only [Pi.neg_apply] at h
      exact Set.mem_iUnion.2 ⟨n, k, hk, by linarith⟩
    rw [e1] at hg
    exact hg.trans (add_le_add_left (measure_mono e2) _)
  have hmono : Monotone (fun m : ℕ =>
      {ω | B' T ω - B' 0 ω < -(a + 1 / ((m : ℝ) + 1))}) := by
    intro i j hij ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    linarith
  have hU : (⋃ m : ℕ, {ω | B' T ω - B' 0 ω < -(a + 1 / ((m : ℝ) + 1))}) =
      {ω | B' T ω - B' 0 ω < -a} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hm⟩
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      linarith
    · intro h
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < -a - (B' T ω - B' 0 ω) by linarith)
      exact ⟨m, by linarith⟩
  have ht := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hU] at ht
  exact le_of_tendsto' (ENNReal.Tendsto.const_mul ht (Or.inr h2top))
    fun m => hη _ (by positivity)

/-- The centred Gaussian law of variance `T` gives mass at most `a √(2 / (π T))` to `[-a, a]`. -/
private theorem gaussianReal_Icc_le {T : ℝ≥0} (hT : T ≠ 0) (a : ℝ) :
    gaussianReal 0 T (Set.Icc (-a) a) ≤ ENNReal.ofReal (a * Real.sqrt (2 / (Real.pi * T))) := by
  have hT' : (0 : ℝ) < T := by positivity
  have hs : 0 < Real.sqrt (2 * Real.pi * T) := Real.sqrt_pos.2 (by positivity)
  rw [gaussianReal_apply 0 hT]
  calc ∫⁻ x in Set.Icc (-a) a, gaussianPDF 0 T x
      ≤ ∫⁻ _ in Set.Icc (-a) a, ENNReal.ofReal (Real.sqrt (2 * Real.pi * T))⁻¹ := by
        refine lintegral_mono fun x => ?_
        simp only [gaussianPDF, gaussianPDFReal_def]
        refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (inv_nonneg.2 hs.le) ?_)
        exact Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.2 (sq_nonneg _)) (by positivity))
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi * T))⁻¹ * volume (Set.Icc (-a) a) :=
        setLIntegral_const _ _
    _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi * T))⁻¹ * (a - -a)) := by
        rw [Real.volume_Icc, ENNReal.ofReal_mul (inv_nonneg.2 hs.le)]
    _ = ENNReal.ofReal (a * Real.sqrt (2 / (Real.pi * T))) := by
        congr 1
        have h2 : Real.sqrt (2 / (Real.pi * T)) = 2 / Real.sqrt (2 * Real.pi * T) := by
          rw [show 2 / (Real.pi * (T : ℝ)) = (2 / Real.sqrt (2 * Real.pi * T)) ^ 2 by
            rw [div_pow, Real.sq_sqrt (by positivity)]
            field_simp]
          exact Real.sqrt_sq (by positivity)
        rw [h2]
        field_simp
        ring

/-- A Brownian motion has a measurable modification: for every `t`, the values at the time `t`
agree almost surely. -/
private theorem exists_measurable_modification [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    ∃ B' : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B' t)) ∧ ∀ t, B t =ᵐ[P] B' t :=
  ⟨fun t => (hB.aemeasurable t).mk (B t), fun t => (hB.aemeasurable t).measurable_mk,
    fun t => (hB.aemeasurable t).ae_eq_mk⟩

/-- **Reflection inequality.**  The probability that a Brownian motion reaches the level `-a`
before time `T` is at least twice the probability that `B T - B 0 < -a`. -/
theorem two_mul_measure_lt_le_measure_exists_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    2 * P {ω | B T ω - B 0 ω < -a} ≤ P {ω | ∃ s ≤ T, B s ω - B 0 ω ≤ -a} := by
  obtain ⟨B', hm, hag⟩ := exists_measurable_modification hB
  have hcore := two_mul_measure_lt_le_measure_iUnion_grid hB hm hag T ha
  have hL : P {ω | B T ω - B 0 ω < -a} = P {ω | B' T ω - B' 0 ω < -a} := by
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hag T, hag 0] with ω h1 h2
    simp only [h1, h2]
  rw [hL]
  refine hcore.trans (measure_mono_ae ?_)
  have hgrid : ∀ᵐ ω ∂P, ∀ n k, B (gridTime T n k) ω = B' (gridTime T n k) ω :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hag _
  filter_upwards [hgrid, hag 0] with ω hω h0 hmem
  obtain ⟨n, k, -, hk⟩ := Set.mem_iUnion.1 hmem
  exact ⟨gridTime T n k, gridTime_le T n k, by rw [hω n k, h0]; exact hk⟩

/-- **Small survival probability.**  A Brownian motion stays strictly above `B 0 - a` on `[0, T]`
with probability at most `a √(2 / (π T))`. -/
theorem measure_forall_gt_neg_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P) {T : ℝ≥0}
    (hT : 0 < T) {a : ℝ} (ha : 0 ≤ a) :
    P {ω | ∀ s ≤ T, -a < B s ω - B 0 ω} ≤ ENNReal.ofReal (a * Real.sqrt (2 / (Real.pi * T))) := by
  obtain ⟨B', hm, hag⟩ := exists_measurable_modification hB
  have hB' : IsPreBrownianReal B' P := hB.toIsPreBrownianReal.congr hag
  have hcore := two_mul_measure_lt_le_measure_iUnion_grid hB hm hag T ha
  set M : Set Ω := ⋃ n : ℕ, {ω | ∃ k ≤ 2 ^ n, B' (gridTime T n k) ω - B' 0 ω ≤ -a} with hM
  have hMm : MeasurableSet M := by
    refine MeasurableSet.iUnion fun n => ?_
    have hset : {ω | ∃ k ≤ 2 ^ n, B' (gridTime T n k) ω - B' 0 ω ≤ -a} =
        ⋃ k ∈ Finset.range (2 ^ n + 1), {ω | B' (gridTime T n k) ω - B' 0 ω ≤ -a} := by
      ext ω
      simp
    rw [hset]
    exact Finset.measurableSet_biUnion _ fun k _ =>
      measurableSet_le ((hm _).sub (hm _)) measurable_const
  have hgrid : ∀ᵐ ω ∂P, ∀ n k, B (gridTime T n k) ω = B' (gridTime T n k) ω :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hag _
  have hF : P {ω | ∀ s ≤ T, -a < B s ω - B 0 ω} ≤ P Mᶜ := by
    refine measure_mono_ae ?_
    filter_upwards [hgrid, hag 0] with ω hω h0 hF hmem
    obtain ⟨n, k, -, hk⟩ := Set.mem_iUnion.1 hmem
    have h := hF (gridTime T n k) (gridTime_le T n k)
    rw [hω n k, h0] at h
    linarith
  have hT0 : T ≠ 0 := ne_of_gt hT
  have hlaw : HasLaw (fun ω => B' T ω - B' 0 ω) (gaussianReal 0 T) P := by
    have h := hB'.hasLaw_sub T 0
    convert h using 2
    ext
    simp
  have hL : P {ω | B' T ω - B' 0 ω < -a} = gaussianReal 0 T (Set.Iio (-a)) := by
    rw [← hlaw.map_eq, Measure.map_apply_of_aemeasurable hlaw.aemeasurable measurableSet_Iio]
    rfl
  have hneg : (gaussianReal 0 T).map (fun x => -x) = gaussianReal 0 T := by
    rw [gaussianReal_map_neg, neg_zero]
  have hsym : gaussianReal 0 T (Set.Ioi a) = gaussianReal 0 T (Set.Iio (-a)) := by
    conv_rhs => rw [← hneg]
    rw [Measure.map_apply measurable_neg measurableSet_Iio]
    congr 1
    ext x
    simp only [Set.mem_Ioi, Set.mem_preimage, Set.mem_Iio, neg_lt_neg_iff]
  have hcov : (1 : ℝ≥0∞) ≤ 2 * gaussianReal 0 T (Set.Iio (-a)) +
      gaussianReal 0 T (Set.Icc (-a) a) := by
    calc (1 : ℝ≥0∞) = gaussianReal 0 T Set.univ := measure_univ.symm
      _ ≤ gaussianReal 0 T (Set.Iio (-a) ∪ Set.Icc (-a) a ∪ Set.Ioi a) := by
          refine measure_mono fun x _ => ?_
          rcases lt_or_ge x (-a) with h | h
          · exact Or.inl (Or.inl h)
          · rcases le_or_gt x a with h' | h'
            · exact Or.inl (Or.inr ⟨h, h'⟩)
            · exact Or.inr h'
      _ ≤ gaussianReal 0 T (Set.Iio (-a)) + gaussianReal 0 T (Set.Icc (-a) a) +
          gaussianReal 0 T (Set.Ioi a) :=
          (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
      _ = 2 * gaussianReal 0 T (Set.Iio (-a)) + gaussianReal 0 T (Set.Icc (-a) a) := by
          rw [hsym]
          ring
  rw [hL] at hcore
  calc P {ω | ∀ s ≤ T, -a < B s ω - B 0 ω} ≤ P Mᶜ := hF
    _ = 1 - P M := prob_compl_eq_one_sub hMm
    _ ≤ 1 - 2 * gaussianReal 0 T (Set.Iio (-a)) := tsub_le_tsub_left hcore 1
    _ ≤ gaussianReal 0 T (Set.Icc (-a) a) := tsub_le_iff_left.2 hcov
    _ ≤ _ := gaussianReal_Icc_le hT0 a

/-- **The survival bound of real Brownian motion** in the form `ReflectionBarrier` of `ShimuraSteps.lean`. -/
theorem reflectionBarrier_holds : ReflectionBarrier := by
  intro Ω _ P _ B hB T hT a ha
  exact measure_forall_gt_neg_le hB hT ha

end MatedCRT.PeanosphereTriplePoints
