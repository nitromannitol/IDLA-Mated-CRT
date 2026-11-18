import MatedCRT.FirstPass.Derived.ConeReferenceClockMarkovTransfer

/-!
# From local to global uniform convergence of the dyadic LQG clocks

The convergence of the dyadic approximating LQG clocks `A^k(b, t)` of Berestycki 2015 (Theorem 1.2)
is local: for a fixed start it holds up to the exit time of a disc, and for the reference cone only
for discs that stay away from the log singularity at the origin. This file chains such local
statements into uniform convergence on every `[0, T]`, for Lebesgue-almost every start:

* deterministically, if a continuous path never visits the origin, the image of `[0, T + 1]` stays at
  a positive distance `ρ` from it; by uniform continuity there is a mesh `h = (L + 1)⁻¹` such that on
  every `[j h, (j + 1) h]` the path stays in a closed disc of radius `r < ρ / 4` around a point of a
  countable dense set, and this disc avoids the origin. Additivity of the clocks under time shifts,
  `A^k(b, s + u) = A^k(b, s) + A^k(θ_s b, u)`, then glues the finitely many local uniform Cauchy
  statements (`uniformCauchySeqOn_Icc_of_local_chain`);
* probabilistically, the local statements needed are indexed by countably many restart times
  `j h`, centers and radii; at a positive restart time they are obtained from the local statement at
  Lebesgue-almost every start by the simple Markov property
  (`ae_planarBrownianMotion_shift_of_ae_start`).

The polarity of the origin for planar Brownian motion (from Lebesgue-almost every start, the path
never visits `0`) enters as an explicit hypothesis.

## Main statements

* `uniformCauchySeqOn_Icc_of_local_chain`: the deterministic chain.
* `measurableSet_localUniformCauchy_lqgClockApprox`: measurability of the local event.
* `ae_uniformCauchySeqOn_lqgClockApprox_of_local`: local uniform Cauchy statements from almost every
  start, for every closed disc avoiding the origin, give uniform Cauchy dyadic clocks on every
  `[0, T]` from almost every start.
* `ae_coneRef_isLQGClock_continuous_monotone_of_local`: for the reference cone, these local
  statements give the LQG clock at every start, which starts at `0` and is continuous and
  nondecreasing.
-/

open MeasureTheory ProbabilityTheory Set HarmonicBalls LQGMetric MarkovProcess
open Filter Topology Metric
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- **Finite chain of local uniform Cauchy pieces.** Let `A k` be additive under time shifts. If a
continuous path `b` never visits the origin, and for every mesh `h = (L + 1)⁻¹`, every restart time
`j h`, and every closed disc of radius `(M + 1)⁻¹` around a point of a dense set `D` which avoids
the origin, the clocks `A k` of the restarted path are uniformly Cauchy on `[0, h]` whenever the
restarted path stays in the disc during `[0, h]`, then the clocks `A k b` are uniformly Cauchy on
every `[0, T]`. -/
theorem uniformCauchySeqOn_Icc_of_local_chain
    (A : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hadd : ∀ k b s t, A k b (s + t) = A k b s + A k (ContinuousPath.shift s b) t)
    {D : Set ℂ} (hD : Dense D) (b : ContinuousPath ℂ) (hb0 : ∀ t, b t ≠ 0)
    (hloc : ∀ L j M : ℕ, ∀ c ∈ D, ((M : ℝ) + 1)⁻¹ < ‖c‖ →
      (∀ t ∈ Icc 0 (LatticeProb.invSuccTime L), ContinuousPath.shift
        ((j : ℝ≥0) * LatticeProb.invSuccTime L) b t ∈ closedBall c ((M : ℝ) + 1)⁻¹) →
      UniformCauchySeqOn (fun k => A k (ContinuousPath.shift
        ((j : ℝ≥0) * LatticeProb.invSuccTime L) b)) atTop (Icc 0 (LatticeProb.invSuccTime L)))
    (T : ℝ≥0) :
    UniformCauchySeqOn (fun k => A k b) atTop (Icc 0 T) := by
  have hA0 : ∀ k b, A k b 0 = 0 := by
    intro k b
    have h := hadd k b 0 0
    rw [add_zero, ContinuousPath.shift_zero] at h
    linarith
  have hK : IsCompact (Icc (0 : ℝ≥0) (T + 1)) := isCompact_Icc
  -- positive distance from the origin on `[0, T + 1]`
  obtain ⟨t₀, -, ht₀⟩ := hK.exists_isMinOn ⟨0, left_mem_Icc.2 zero_le⟩
    b.continuous.norm.continuousOn
  have hρ : 0 < ‖b t₀‖ := norm_pos_iff.2 (hb0 t₀)
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < ‖b t₀‖ / 4)
  rw [one_div] at hM
  have hr : (0 : ℝ) < ((M : ℝ) + 1)⁻¹ := by positivity
  -- uniform continuity on `[0, T + 1]`
  obtain ⟨δ, hδ, hδb⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous b.continuous.continuousOn)
    (((M : ℝ) + 1)⁻¹ / 2) (by positivity)
  obtain ⟨L, hL⟩ := exists_nat_one_div_lt hδ
  have hhR : ((LatticeProb.invSuccTime L : ℝ≥0) : ℝ) = ((L : ℝ) + 1)⁻¹ := by
    simp [LatticeProb.invSuccTime]
  have hhδ : ((LatticeProb.invSuccTime L : ℝ≥0) : ℝ) < δ := by rw [hhR, ← one_div]; exact hL
  have hh1 : LatticeProb.invSuccTime L ≤ 1 :=
    (LatticeProb.invSuccTime_antitone (Nat.zero_le L)).trans (by simp [LatticeProb.invSuccTime])
  have hh0 : 0 < LatticeProb.invSuccTime L := LatticeProb.invSuccTime_pos L
  -- induction along the chain of restart times `j h`
  have key : ∀ j : ℕ, UniformCauchySeqOn (fun k => A k b) atTop
      (Icc 0 T ∩ Icc 0 ((j : ℝ≥0) * LatticeProb.invSuccTime L)) := by
    intro j
    induction j with
    | zero =>
      rw [Metric.uniformCauchySeqOn_iff]
      intro ε hε
      refine ⟨0, fun k₁ _ k₂ _ t ht => ?_⟩
      have ht0 : t = 0 := by
        have h2 := ht.2.2
        simp only [Nat.cast_zero, zero_mul] at h2
        exact le_antisymm h2 zero_le
      simp [ht0, hA0, hε]
    | succ j ih =>
      by_cases hjT : (j : ℝ≥0) * LatticeProb.invSuccTime L ≤ T
      · set s := (j : ℝ≥0) * LatticeProb.invSuccTime L with hsdef
        have hsK : s ∈ Icc (0 : ℝ≥0) (T + 1) := ⟨zero_le, hjT.trans le_self_add⟩
        obtain ⟨c, hcD, hc⟩ := hD.exists_dist_lt (b s)
          (by positivity : (0 : ℝ) < ((M : ℝ) + 1)⁻¹ / 2)
        have hbs : ‖b t₀‖ ≤ ‖b s‖ := isMinOn_iff.1 ht₀ s hsK
        have hcnorm : ((M : ℝ) + 1)⁻¹ < ‖c‖ := by
          have h1 := norm_sub_norm_le (b s) c
          rw [dist_eq_norm] at hc
          linarith
        have hball : ∀ t ∈ Icc 0 (LatticeProb.invSuccTime L),
            ContinuousPath.shift s b t ∈ closedBall c ((M : ℝ) + 1)⁻¹ := by
          intro t ht
          rw [ContinuousPath.shift_apply, mem_closedBall]
          have hstK : s + t ∈ Icc (0 : ℝ≥0) (T + 1) :=
            ⟨zero_le, add_le_add hjT (ht.2.trans hh1)⟩
          have hd : dist (s + t) s < δ := by
            rw [NNReal.dist_eq, NNReal.coe_add, add_sub_cancel_left,
              abs_of_nonneg (NNReal.coe_nonneg t)]
            exact lt_of_le_of_lt (NNReal.coe_le_coe.2 ht.2) hhδ
          have h3 := hδb (s + t) hstK s hsK hd
          linarith [dist_triangle (b (s + t)) (b s) c]
        have hlocal := hloc L j M c hcD hcnorm hball
        rw [Metric.uniformCauchySeqOn_iff] at ih hlocal ⊢
        intro ε hε
        obtain ⟨N₁, hN₁⟩ := ih (ε / 2) (by positivity)
        obtain ⟨N₂, hN₂⟩ := hlocal (ε / 2) (by positivity)
        refine ⟨max N₁ N₂, fun k₁ hk₁ k₂ hk₂ t ht => ?_⟩
        by_cases hts : t ≤ s
        · exact (hN₁ k₁ (le_of_max_le_left hk₁) k₂ (le_of_max_le_left hk₂) t
            ⟨ht.1, ⟨zero_le, hts⟩⟩).trans (half_lt_self hε)
        · rw [not_le] at hts
          obtain ⟨u, rfl⟩ : ∃ u, t = s + u := ⟨t - s, (add_tsub_cancel_of_le hts.le).symm⟩
          have hstep : (((j + 1 : ℕ) : ℝ≥0)) * LatticeProb.invSuccTime L =
              s + LatticeProb.invSuccTime L := by
            rw [hsdef]; push_cast; ring
          have hu : u ∈ Icc 0 (LatticeProb.invSuccTime L) :=
            ⟨zero_le, le_of_add_le_add_left (ht.2.2.trans_eq hstep)⟩
          show dist (A k₁ b (s + u)) (A k₂ b (s + u)) < ε
          rw [hadd k₁ b s u, hadd k₂ b s u]
          calc dist (A k₁ b s + A k₁ (ContinuousPath.shift s b) u)
                (A k₂ b s + A k₂ (ContinuousPath.shift s b) u)
              ≤ dist (A k₁ b s) (A k₂ b s) + dist (A k₁ (ContinuousPath.shift s b) u)
                (A k₂ (ContinuousPath.shift s b) u) := dist_add_add_le _ _ _ _
            _ < ε / 2 + ε / 2 := add_lt_add
                (hN₁ k₁ (le_of_max_le_left hk₁) k₂ (le_of_max_le_left hk₂) s
                  ⟨⟨zero_le, hjT⟩, ⟨zero_le, le_rfl⟩⟩)
                (hN₂ k₁ (le_of_max_le_right hk₁) k₂ (le_of_max_le_right hk₂) u hu)
            _ = ε := add_halves ε
      · exact ih.mono fun t ht => ⟨ht.1, ⟨zero_le, ht.1.2.trans (not_le.1 hjT).le⟩⟩
  obtain ⟨j, hj⟩ := exists_nat_ge (T / LatticeProb.invSuccTime L)
  refine (key j).mono fun t ht => ⟨ht, ⟨zero_le, ?_⟩⟩
  calc t ≤ T := ht.2
    _ = T / LatticeProb.invSuccTime L * LatticeProb.invSuccTime L :=
      (div_mul_cancel₀ T hh0.ne').symm
    _ ≤ (j : ℝ≥0) * LatticeProb.invSuccTime L := by gcongr

/-- The local event "if the path stays in the closed disc `closedBall c r` during `[0, h]`, then the
dyadic approximating clocks are uniformly Cauchy on `[0, h]`" is measurable. -/
theorem measurableSet_localUniformCauchy_lqgClockApprox {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hε (HarmonicBalls.dyadicScale k))) (h : ℝ≥0) (c : ℂ)
    (r : ℝ) :
    MeasurableSet {b : ContinuousPath ℂ | (∀ t ∈ Icc 0 h, b t ∈ closedBall c r) →
      UniformCauchySeqOn (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t)
        atTop (Icc 0 h)} := by
  have hEq : {b : ContinuousPath ℂ | (∀ t ∈ Icc 0 h, b t ∈ closedBall c r) →
      UniformCauchySeqOn (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t)
        atTop (Icc 0 h)} =
      {b | ∃ t ∈ Icc 0 h, r < dist (b t) c} ∪ {b | UniformCauchySeqOn
        (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t) atTop (Icc 0 h)} := by
    ext b
    simp only [mem_ofPred_eq, mem_union, mem_closedBall]
    constructor
    · intro hb
      by_cases hex : ∃ t ∈ Icc 0 h, r < dist (b t) c
      · exact Or.inl hex
      · exact Or.inr (hb fun t ht => not_lt.1 fun hlt => hex ⟨t, ht, hlt⟩)
    · rintro (⟨t, ht, hlt⟩ | hb) hall
      · exact absurd (hall t ht) (not_le.2 hlt)
      · exact hb
  rw [hEq]
  exact (LatticeProb.measurableSet_exists_mem_lt_of_continuous (fun b t => dist (b t) c)
    (fun b => b.continuous.dist continuous_const)
    (fun t => (ContinuousPath.measurable_coordinateProcess t).dist measurable_const) _ _).union
    (measurableSet_uniformCauchySeqOn_lqgClockApprox hcont _)

/-- **Uniform convergence on `[0, T]` from local convergence.** Suppose that from Lebesgue-almost
every start planar Brownian motion never visits the origin, and that for every horizon `h` and every
closed disc `closedBall c r` avoiding the origin (`r < ‖c‖`), from Lebesgue-almost every start the
dyadic approximating clocks are almost surely uniformly Cauchy on `[0, h]` whenever the path stays
in the disc during `[0, h]`. Then for every `T`, from Lebesgue-almost every start the dyadic clocks
are almost surely uniformly Cauchy on `[0, T]`. -/
theorem ae_uniformCauchySeqOn_lqgClockApprox_of_local {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hε (HarmonicBalls.dyadicScale k)))
    (hpolar : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y), ∀ t, b t ≠ 0)
    (hloc : ∀ (h : ℝ≥0) (c : ℂ) (r : ℝ), r < ‖c‖ →
      ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
        (∀ t ∈ Icc 0 h, b t ∈ closedBall c r) →
        UniformCauchySeqOn (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t)
          atTop (Icc 0 h))
    (T : ℝ≥0) :
    ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
      UniformCauchySeqOn (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t)
        atTop (Icc 0 T) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable D := hDc.to_subtype
  have hG : ∀ i : ℕ × ℕ × ℕ × D, ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
      ((i.2.2.1 : ℝ) + 1)⁻¹ < ‖(i.2.2.2 : ℂ)‖ →
      (∀ t ∈ Icc 0 (LatticeProb.invSuccTime i.1),
        ContinuousPath.shift ((i.2.1 : ℝ≥0) * LatticeProb.invSuccTime i.1) b t ∈
          closedBall (i.2.2.2 : ℂ) ((i.2.2.1 : ℝ) + 1)⁻¹) →
      UniformCauchySeqOn (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k)
        (ContinuousPath.shift ((i.2.1 : ℝ≥0) * LatticeProb.invSuccTime i.1) b) t)
        atTop (Icc 0 (LatticeProb.invSuccTime i.1)) := by
    rintro ⟨L, j, M, c, hc⟩
    by_cases hv : ((M : ℝ) + 1)⁻¹ < ‖c‖
    · have hE := hloc (LatticeProb.invSuccTime L) c _ hv
      by_cases hj : (j : ℝ≥0) * LatticeProb.invSuccTime L = 0
      · filter_upwards [hE] with y hy
        filter_upwards [hy] with b hb _
        rw [hj, ContinuousPath.shift_zero]
        exact hb
      · exact ae_of_all _ fun y =>
          (ae_planarBrownianMotion_shift_of_ae_start y hj
            (measurableSet_localUniformCauchy_lqgClockApprox (γ := γ) hcont _ c _) hE).mono
            fun b hb _ => hb
    · exact ae_of_all _ fun y => ae_of_all _ fun b hv' => absurd hv' hv
  filter_upwards [ae_all_iff.2 hG, hpolar] with y hy hy0
  filter_upwards [ae_all_iff.2 hy, hy0] with b hb hb0
  exact uniformCauchySeqOn_Icc_of_local_chain
    (fun k b t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t)
    (fun k b s t => lqgClockApprox_add_eq_add_shift (hcont k) b s t) hDd b hb0
    (fun L j M c hc hv hball => hb ⟨L, j, M, c, hc⟩ hv hball) T

/-- **The LQG clock of the reference cone at every start, from local convergence.** Suppose that from
Lebesgue-almost every start planar Brownian motion never visits the origin. Almost surely, if for
every horizon `h` and every closed disc `closedBall a r` avoiding the origin the dyadic approximating
LQG clocks of the reference cone (built from `c (Y ω)` and `w ω`) are, from Lebesgue-almost every
start, almost surely uniformly Cauchy on `[0, h]` whenever the path stays in the disc, then from
every start `z` their limit `F` after positive times is an LQG clock of the reference cone, and for
almost every path `b` the clock `F(b, ·)` starts at `0`, is continuous and is nondecreasing. -/
theorem ae_coneRef_isLQGClock_continuous_monotone_of_local
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ)
    (hpolar : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y), ∀ t, b t ≠ 0) :
    ∀ᵐ ω ∂P,
      (∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ →
        ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
          (∀ t ∈ Icc 0 h, b t ∈ closedBall a r) →
          UniformCauchySeqOn
            (fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
              (HarmonicBalls.dyadicScale k) b t)
            atTop (Icc 0 h)) →
      ∀ z : ℂ,
        IsLQGClock planarBrownianMotion γ (coneRefCircle γ (c (Y ω)) (w ω)) z
            (fun b => LatticeProb.limitAfterPositiveTimes
              (fun j => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
                (HarmonicBalls.dyadicScale j) b)) ∧
          ∀ᵐ b ∂(planarBrownianMotion z),
            LatticeProb.limitAfterPositiveTimes
                (fun j => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
                  (HarmonicBalls.dyadicScale j) b) 0 = 0 ∧
            Continuous (LatticeProb.limitAfterPositiveTimes
                (fun j => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
                  (HarmonicBalls.dyadicScale j) b)) ∧
            Monotone (LatticeProb.limitAfterPositiveTimes
                (fun j => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
                  (HarmonicBalls.dyadicScale j) b)) := by
  filter_upwards [ae_coneRef_isLQGClock_continuous_monotone_of_ae_start
    hY hp hc hcont hmeas hγ hγ2 w] with ω hω hloc
  have hcontk : ∀ k : ℕ,
      Continuous (coneRefCircle γ (c (Y ω)) (w ω) (HarmonicBalls.dyadicScale k)) := fun k =>
    (continuousOn_coneRefCircle γ (hcont (Y ω)) (w ω)).comp_continuous
      (continuous_const.prodMk continuous_id)
      fun x => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩
  exact hω fun T => ae_uniformCauchySeqOn_lqgClockApprox_of_local hcontk hpolar hloc T

end MatedCRT.FirstPass.Derived
