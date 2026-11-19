import MatedCRT.FirstPass.Derived.RevuzOptionalClockInverse

/-!
# The strong Markov property at the right inverse of a PCAF clock

Let `A` be a positive continuous additive functional of planar Brownian motion with a good clock,
`τ_r = inf {t | r < A_t}` the right inverse of the clock and `θ` the time shift. Since `τ_r`
agrees almost surely with an optional time of the canonical filtration
(`exists_optionalTime_ae_eq_clockInverse`), the strong Markov property applies at `τ_r`
(Revuz–Yor (1999), Theorem III.3.7 and Chapter X, Section 1; Fukushima–Oshima–Takeda (2011),
Section A.2): for measurable `H ≥ 0` on pairs,
`E_z[H(τ_r, θ_{τ_r} ω)] = E_z[∫ H(τ_r, ω') dP_{B_{τ_r}}(ω')]`.
Integrating in the level `r` against any `s`-finite measure (Tonelli) gives the Markov property
against the time-changed variable, which by the change of variables `s = τ_r` is the Markov
property against `dA_s`.

The joint measurability in `(r, ω)` needed for Tonelli is proved for the inverse of the
rational-time regularization `Ā` of the clock, which is nondecreasing along every path; it agrees
with the inverse of `A` almost surely, for every level.

## Main results

* `clockInverse_lt_iff_of_monotone`: `τ_u < c` through the rational times.
* `measurable_clockInverse_uncurry`: joint measurability of `(u, ω) ↦ τ_u ω` for a measurable
  clock nondecreasing along every path.
* `ae_clockInverse_regularize_eq`: almost surely, `Ā` and `A` have the same right inverse.
* `clockInverse_le_iff_le_clock`: `τ_r ≤ t ↔ r ≤ A_t` for a good clock path.
* `lintegral_shift_clockInverse_eq`: the strong Markov property at `τ_r`.
* `lintegral_lintegral_shift_clockInverse_eq`: its integrated form in the level `r`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open _root_.HarmonicBalls

/-- `τ_u < c` through the rational times, for a clock nondecreasing along the path. -/
theorem clockInverse_lt_iff_of_monotone {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {ω : ContinuousPath ℂ} (hmono : Monotone fun t => A t ω) (u c : ℝ≥0) :
    clockInverse A u ω < c ↔
      (∃ q : ℚ≥0, (q : ℝ≥0) < c ∧ u < A q ω) ∨ (0 < c ∧ ∀ q : ℚ≥0, A q ω ≤ u) := by
  unfold clockInverse
  constructor
  · intro h
    rcases Set.eq_empty_or_nonempty {t | u < A t ω} with hne | hne
    · refine Or.inr ⟨lt_of_le_of_lt zero_le h, fun q => not_lt.1 fun hq => ?_⟩
      exact (Set.mem_empty_iff_false _).1
        (hne.subset (show (q : ℝ≥0) ∈ {t | u < A t ω} from hq))
    · obtain ⟨s, hs, hsc⟩ := exists_lt_of_csInf_lt hne h
      obtain ⟨q, hsq, hqc⟩ := exists_nnrat_btwn_nnreal hsc
      have hs' : u < A s ω := hs
      exact Or.inl ⟨q, hqc, lt_of_lt_of_le hs' (hmono hsq.le)⟩
  · rintro (⟨q, hqc, hq⟩ | ⟨hc, hall⟩)
    · exact lt_of_le_of_lt
        (csInf_le (OrderBot.bddBelow _) (show (q : ℝ≥0) ∈ {t | u < A t ω} from hq)) hqc
    · have hempty : {t | u < A t ω} = ∅ := by
        by_contra hT
        obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.2 hT
        obtain ⟨q, hsq, -⟩ := exists_nnrat_btwn_nnreal (lt_add_one s)
        have hs' : u < A s ω := hs
        exact absurd (lt_of_lt_of_le hs' (hmono hsq.le)) (not_lt.2 (hall q))
      rw [hempty, NNReal.sInf_empty]
      exact hc

/-- **Joint measurability of the right inverse of a clock.** If every `A t` is measurable and
`A` is nondecreasing in time along every path, then `(u, ω) ↦ τ_u ω` is measurable. -/
theorem measurable_clockInverse_uncurry {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (hmono : ∀ ω, Monotone fun t => A t ω) :
    Measurable fun p : ℝ≥0 × ContinuousPath ℂ => clockInverse A p.1 p.2 := by
  refine measurable_of_Iio fun c => ?_
  have hset : (fun p : ℝ≥0 × ContinuousPath ℂ => clockInverse A p.1 p.2) ⁻¹' Set.Iio c =
      (⋃ q : ℚ≥0, ({p : ℝ≥0 × ContinuousPath ℂ | (q : ℝ≥0) < c} ∩ {p | p.1 < A q p.2})) ∪
        ({p : ℝ≥0 × ContinuousPath ℂ | 0 < c} ∩ ⋂ q : ℚ≥0, {p | A q p.2 ≤ p.1}) := by
    ext p
    rw [Set.mem_preimage, Set.mem_Iio, clockInverse_lt_iff_of_monotone (hmono p.2)]
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
  rw [hset]
  exact (MeasurableSet.iUnion fun q : ℚ≥0 => (MeasurableSet.const _).inter
      (measurableSet_lt measurable_fst ((hA q).comp measurable_snd))).union
    ((MeasurableSet.const _).inter (MeasurableSet.iInter fun q : ℚ≥0 =>
      measurableSet_le ((hA q).comp measurable_snd) measurable_fst))

/-- Almost surely, the rational-time regularization of a PCAF has the same right inverse as the
PCAF, at every level. -/
theorem ae_clockInverse_regularize_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (z : ℂ) :
    ∀ᵐ ω ∂planarLaw z, ∀ u, clockInverse (regularize A) u ω = clockInverse A u ω := by
  filter_upwards [hA.path z] with ω hp u
  unfold clockInverse
  simp only [regularize_eq_of_continuous_monotone hp.2.1 hp.2.2]

/-- **The right inverse below a time.** Along a path where the clock is continuous, strictly
increasing from `0` and exceeds `r`, `τ_r ≤ t ↔ r ≤ A_t`. -/
theorem clockInverse_le_iff_le_clock {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ω : ContinuousPath ℂ}
    {r t : ℝ≥0} (h0 : A 0 ω = 0) (hc : Continuous fun t => A t ω)
    (hs : StrictMono fun t => A t ω) (hne : ∃ t, r < A t ω) :
    clockInverse A r ω ≤ t ↔ r ≤ A t ω := by
  constructor
  · intro h
    calc r = A (clockInverse A r ω) ω := (apply_clockInverse_eq h0 hc hs.monotone hne).symm
      _ ≤ A t ω := hs.monotone h
  · intro h
    unfold clockInverse
    refine le_of_forall_gt_imp_ge_of_dense fun t' ht' => ?_
    exact csInf_le (OrderBot.bddBelow _)
      (show t' ∈ {u | r < A u ω} from lt_of_le_of_lt h (hs ht'))

/-- **Strong Markov property at the right inverse of a PCAF clock.** For a PCAF of planar
Brownian motion with a good clock, every start `z`, level `r` and measurable `H ≥ 0` on pairs,
`E_z[H(τ_r, θ_{τ_r} ω)] = E_z[∫ H(τ_r, ω') dP_{B_{τ_r}}(ω')]`. -/
theorem lintegral_shift_clockInverse_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) (r : ℝ≥0)
    {H : ℝ≥0 × ContinuousPath ℂ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, H (clockInverse A r ω, ContinuousPath.shift (clockInverse A r ω) ω) ∂planarLaw z =
      ∫⁻ ω, ∫⁻ ω', H (clockInverse A r ω, ω') ∂planarLaw (ω (clockInverse A r ω))
        ∂planarLaw z := by
  obtain ⟨T, hT, hae⟩ := exists_optionalTime_ae_eq_clockInverse hA hG z
  have hfull : (planarLaw z).restrict {ω | T r ω < ⊤} = planarLaw z := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    filter_upwards [hae] with ω h
    show T r ω < ⊤
    rw [h r]
    exact WithTop.coe_lt_top _
  have hu : ∀ᵐ ω ∂planarLaw z, (T r ω).untopD 0 = clockInverse A r ω := by
    filter_upwards [hae] with ω h
    rw [h r, WithTop.untopD_coe]
  have hsm := OptionalTime.lintegral_planarLaw_shift_optionalTime_time z (T r) (hT r) hH
  rw [hfull] at hsm
  calc ∫⁻ ω, H (clockInverse A r ω, ContinuousPath.shift (clockInverse A r ω) ω) ∂planarLaw z
      = ∫⁻ ω, H ((T r ω).untopD 0, ContinuousPath.shift ((T r ω).untopD 0) ω) ∂planarLaw z := by
        refine lintegral_congr_ae ?_
        filter_upwards [hu] with ω h
        rw [h]
    _ = ∫⁻ ω, ∫⁻ ω', H ((T r ω).untopD 0, ω') ∂planarLaw (ω ((T r ω).untopD 0))
          ∂planarLaw z := hsm
    _ = _ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hu] with ω h
        rw [h]

/-- **Strong Markov property at the right inverse, integrated in the level.** For a PCAF of
planar Brownian motion with a good clock, every start `z`, every `s`-finite measure `ν` on the
levels and measurable `H ≥ 0` on pairs,
`E_z ∫ H(τ_r, θ_{τ_r} ω) dν(r) = E_z ∫ ∫ H(τ_r, ω') dP_{B_{τ_r}}(ω') dν(r)`
(levels `r ∈ ℝ` enter through `r⁺`). -/
theorem lintegral_lintegral_shift_clockInverse_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) (ν : Measure ℝ) [SFinite ν]
    {H : ℝ≥0 × ContinuousPath ℂ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, ∫⁻ r, H (clockInverse A r.toNNReal ω,
        ContinuousPath.shift (clockInverse A r.toNNReal ω) ω) ∂ν ∂planarLaw z =
      ∫⁻ ω, ∫⁻ r, ∫⁻ ω', H (clockInverse A r.toNNReal ω, ω')
        ∂planarLaw (ω (clockInverse A r.toNNReal ω)) ∂ν ∂planarLaw z := by
  have hτ' : Measurable fun p : ContinuousPath ℂ × ℝ =>
      clockInverse (regularize A) p.2.toNNReal p.1 :=
    (measurable_clockInverse_uncurry (measurable_regularize hA.meas) (regularize_monotone A)).comp
      ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)
  have hΦ : Measurable fun p : ℝ≥0 × ℂ => ∫⁻ ω', H (p.1, ω') ∂planarLaw p.2 := by
    have h := (hH.comp (measurable_fst.fst.prodMk measurable_snd)).lintegral_kernel_prod_right'
      (κ := Kernel.comap planarBrownianMotion Prod.snd measurable_snd)
    simp only [Kernel.comap_apply] at h
    exact h
  have hL : Measurable fun p : ContinuousPath ℂ × ℝ =>
      H (clockInverse (regularize A) p.2.toNNReal p.1,
        ContinuousPath.shift (clockInverse (regularize A) p.2.toNNReal p.1) p.1) :=
    hH.comp (hτ'.prodMk
      ((ContinuousPath.continuous_shift (alpha := ℂ)).measurable.comp (hτ'.prodMk measurable_fst)))
  have hR : Measurable fun p : ContinuousPath ℂ × ℝ =>
      ∫⁻ ω', H (clockInverse (regularize A) p.2.toNNReal p.1, ω')
        ∂planarLaw (p.1 (clockInverse (regularize A) p.2.toNNReal p.1)) := by
    have heval : Measurable fun p : ContinuousPath ℂ × ℝ =>
        p.1 (clockInverse (regularize A) p.2.toNNReal p.1) :=
      (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
        (measurable_fst.prodMk hτ')
    exact hΦ.comp (hτ'.prodMk heval)
  have hreg := ae_clockInverse_regularize_eq hA z
  calc ∫⁻ ω, ∫⁻ r, H (clockInverse A r.toNNReal ω,
        ContinuousPath.shift (clockInverse A r.toNNReal ω) ω) ∂ν ∂planarLaw z
      = ∫⁻ ω, ∫⁻ r, H (clockInverse (regularize A) r.toNNReal ω,
          ContinuousPath.shift (clockInverse (regularize A) r.toNNReal ω) ω) ∂ν ∂planarLaw z := by
        refine lintegral_congr_ae ?_
        filter_upwards [hreg] with ω h
        simp only [h]
    _ = ∫⁻ r, ∫⁻ ω, H (clockInverse (regularize A) r.toNNReal ω,
          ContinuousPath.shift (clockInverse (regularize A) r.toNNReal ω) ω) ∂planarLaw z ∂ν :=
        lintegral_lintegral_swap hL.aemeasurable
    _ = ∫⁻ r, ∫⁻ ω, ∫⁻ ω', H (clockInverse (regularize A) r.toNNReal ω, ω')
          ∂planarLaw (ω (clockInverse (regularize A) r.toNNReal ω)) ∂planarLaw z ∂ν := by
        refine lintegral_congr fun r => ?_
        calc _ = ∫⁻ ω, H (clockInverse A r.toNNReal ω,
              ContinuousPath.shift (clockInverse A r.toNNReal ω) ω) ∂planarLaw z := by
              refine lintegral_congr_ae ?_
              filter_upwards [hreg] with ω h
              simp only [h]
          _ = _ := lintegral_shift_clockInverse_eq hA hG z r.toNNReal hH
          _ = _ := by
              refine lintegral_congr_ae ?_
              filter_upwards [hreg] with ω h
              simp only [h]
    _ = ∫⁻ ω, ∫⁻ r, ∫⁻ ω', H (clockInverse (regularize A) r.toNNReal ω, ω')
          ∂planarLaw (ω (clockInverse (regularize A) r.toNNReal ω)) ∂ν ∂planarLaw z :=
        (lintegral_lintegral_swap hR.aemeasurable).symm
    _ = _ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hreg] with ω h
        simp only [h]

end MatedCRT
