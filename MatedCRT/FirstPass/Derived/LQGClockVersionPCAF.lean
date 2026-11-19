import MatedCRT.FirstPass.Derived.LQGClockAdaptedVersion
import MatedCRT.FirstPass.Derived.LQGApproxLawConvergence
import MatedCRT.FirstPass.Derived.PlanarBrownianPointPolar
import MatedCRT.FirstPass.Derived.RevuzLebesgueInvariance
import MatedCRT.FirstPass.Derived.ConeReferenceClockMarkovTransfer
import MatedCRT.External.RevuzTimeChange

/-!
# The adapted version of the LQG clock is a positive continuous additive functional with a good clock

Let `F` be the LQG clock of planar Brownian motion from every start `z` for circle averages `hε`
(`HarmonicBalls.IsLQGClock`, convergence in probability of the dyadic approximating clocks), almost surely
a time-change clock.  The adapted version `G` of `F` from `exists_adapted_version_lqgClock` is a positive
continuous additive functional of planar Brownian motion (`MatedCRT.IsPCAF`) with a good clock
(`MatedCRT.GoodClock`), for every start, and agrees with `F` for all times almost surely
(`exists_pcaf_goodClock_lqgClock`).

The additivity `G (t + s) = G t + G s ∘ θ_t` is obtained from the exact additivity of the approximating
clocks (`lqgClockApprox_add_eq_add_shift`) and the convergence in probability of `A_k s ∘ θ_t` to `G s ∘ θ_t`,
which follows from the simple Markov property at the fixed time `t`
(`tendsto_measure_shift_of_forall`): the law of the shifted path is a mixture of planar Brownian motions over
the starts, and the convergence in probability holds from every start.  Only measurable events are used.
-/

namespace MatedCRT

open MeasureTheory Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The natural `σ`-field `F⁰_t` of the path is contained in the Borel `σ`-field of the path space. -/
theorem pathFiltration_le_ambient (t : ℝ≥0) :
    pathFiltration t ≤ (inferInstance : MeasurableSpace (ContinuousPath ℂ)) :=
  (pathFiltration_le_canonicalFiltration t).trans ((ContinuousPath.canonicalFiltration (alpha := ℂ)).le t)

/-- **Convergence in probability transfers through the time shift.** If measurable events `E k` have
planar Brownian probability tending to `0` from every start, then so do their preimages under the shift
`θ_t`, from every start (simple Markov property at the fixed time `t`). -/
theorem tendsto_measure_shift_of_forall {E : ℕ → Set (ContinuousPath ℂ)} (hE : ∀ k, MeasurableSet (E k))
    (h : ∀ y, Tendsto (fun k => planarBrownianMotion y (E k)) atTop (𝓝 0)) (z : ℂ) (t : ℝ≥0) :
    Tendsto (fun k => planarBrownianMotion z (ContinuousPath.shift t ⁻¹' E k)) atTop (𝓝 0) := by
  have key : ∀ k, planarBrownianMotion z (ContinuousPath.shift t ⁻¹' E k) =
      ∫⁻ y, planarBrownianMotion y (E k) ∂(planarGaussian z t) := by
    intro k
    rw [← Measure.map_apply (ContinuousPath.measurable_shift_fixed t) (hE k),
      KilledOccupation.planarBrownianMotion_map_shift,
      Measure.bind_apply (hE k) planarBrownianMotion.measurable.aemeasurable]
  simp_rw [key]
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := planarGaussian z t)
    (F := fun k y => planarBrownianMotion y (E k)) (f := fun _ => (0 : ℝ≥0∞)) (fun _ => (1 : ℝ≥0∞))
    (fun k => ProbabilityTheory.Kernel.measurable_coe _ (hE k))
    (fun k => Filter.Eventually.of_forall fun y => prob_le_one)
    (by simp) (Filter.Eventually.of_forall h)
  simpa using hlim

/-- **Limits in probability of exactly additive functionals are additive.** Let `A k` be measurable
functionals which are exactly additive for the time shift, `A k (s + t) b = A k s b + A k t (θ_s b)`, and
converge in probability to measurable `G` from every start; then `G (s + t) = G s + G t ∘ θ_s` almost
surely from every start. -/
theorem ae_add_of_tendsto_probability {A : ℕ → ℝ≥0 → ContinuousPath ℂ → ℝ}
    {G : ℝ≥0 → ContinuousPath ℂ → ℝ} (hA : ∀ k t, Measurable (A k t)) (hG : ∀ t, Measurable (G t))
    (hadd : ∀ k s t b, A k (s + t) b = A k s b + A k t (ContinuousPath.shift s b))
    (hconv : ∀ y t η, 0 < η →
      Tendsto (fun k => planarBrownianMotion y {b | η ≤ |A k t b - G t b|}) atTop (𝓝 0))
    (z : ℂ) (s t : ℝ≥0) :
    ∀ᵐ b ∂planarBrownianMotion z, G (s + t) b = G s b + G t (ContinuousPath.shift s b) := by
  have hsh : Measurable (ContinuousPath.shift s : ContinuousPath ℂ → ContinuousPath ℂ) :=
    ContinuousPath.measurable_shift_fixed s
  have hnull : ∀ η : ℝ, 0 < η →
      planarBrownianMotion z {b | η ≤ |G (s + t) b - G s b - G t (ContinuousPath.shift s b)|} = 0 := by
    intro η hη
    have hη3 : 0 < η / 3 := by positivity
    have hE3 : ∀ k, MeasurableSet {b : ContinuousPath ℂ | η / 3 ≤ |A k t b - G t b|} := fun k =>
      measurableSet_le measurable_const (((hA k t).sub (hG t)).abs)
    have h1 := hconv z (s + t) (η / 3) hη3
    have h2 := hconv z s (η / 3) hη3
    have h3 := tendsto_measure_shift_of_forall (E := fun k => {b | η / 3 ≤ |A k t b - G t b|})
      hE3 (fun y => hconv y t (η / 3) hη3) z s
    have hsum : Tendsto (fun k => planarBrownianMotion z {b | η / 3 ≤ |A k (s + t) b - G (s + t) b|} +
        planarBrownianMotion z {b | η / 3 ≤ |A k s b - G s b|} +
        planarBrownianMotion z (ContinuousPath.shift s ⁻¹' {b | η / 3 ≤ |A k t b - G t b|}))
        atTop (𝓝 0) := by simpa using (h1.add h2).add h3
    have hsub : ∀ k, {b | η ≤ |G (s + t) b - G s b - G t (ContinuousPath.shift s b)|} ⊆
        {b | η / 3 ≤ |A k (s + t) b - G (s + t) b|} ∪ {b | η / 3 ≤ |A k s b - G s b|} ∪
          ContinuousPath.shift s ⁻¹' {b | η / 3 ≤ |A k t b - G t b|} := by
      intro k b hb
      by_contra hcon
      simp only [Set.mem_union, not_or, Set.mem_preimage] at hcon
      have hb : η ≤ |G (s + t) b - G s b - G t (ContinuousPath.shift s b)| := hb
      have hc1 : |A k (s + t) b - G (s + t) b| < η / 3 := not_le.1 hcon.1.1
      have hc2 : |A k s b - G s b| < η / 3 := not_le.1 hcon.1.2
      have hc3 : |A k t (ContinuousPath.shift s b) - G t (ContinuousPath.shift s b)| < η / 3 :=
        not_le.1 hcon.2
      have hd : G (s + t) b - G s b - G t (ContinuousPath.shift s b) =
          -(A k (s + t) b - G (s + t) b) + (A k s b - G s b) +
            (A k t (ContinuousPath.shift s b) - G t (ContinuousPath.shift s b)) := by
        rw [hadd k s t b]; ring
      rw [hd] at hb
      have := abs_add_three (-(A k (s + t) b - G (s + t) b)) (A k s b - G s b)
        (A k t (ContinuousPath.shift s b) - G t (ContinuousPath.shift s b))
      rw [abs_neg] at this
      linarith
    refine le_antisymm (ge_of_tendsto' hsum fun k => ?_) zero_le
    exact (measure_mono (hsub k)).trans
      ((measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _))
  have hall : ∀ᵐ b ∂planarBrownianMotion z, ∀ n : ℕ,
      ¬ (1 / ((n : ℝ) + 1) ≤ |G (s + t) b - G s b - G t (ContinuousPath.shift s b)|) := by
    rw [ae_all_iff]
    intro n
    exact ae_iff.2 (by simpa only [not_not] using hnull _ (by positivity))
  filter_upwards [hall] with b hb
  by_contra hne
  have hpos : 0 < |G (s + t) b - G s b - G t (ContinuousPath.shift s b)| :=
    abs_pos.2 (fun h0 => hne (by linarith))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  exact hb n hn.le

/-- **The adapted version of the LQG clock is a PCAF with a good clock.**  Let `F` be, from every start `z`, the
LQG clock of planar Brownian motion for circle averages `hε` which are continuous at the dyadic scales, and
almost surely a time-change clock.  Then there is a functional `G` with values in `ℝ≥0`, adapted to the natural
filtration `pathFiltration`, which is a positive continuous additive functional of planar Brownian motion
(`IsPCAF planarLaw G`) with a good clock (`GoodClock planarLaw G`), and which equals `F` at all times almost surely
under planar Brownian motion from every start. -/
theorem exists_pcaf_goodClock_lqgClock {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k))) {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ z : ℂ, IsLQGClock planarBrownianMotion γ hε z F)
    (hT : ∀ z : ℂ, ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b)) :
    ∃ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G ∧ GoodClock planarLaw G ∧
      (∀ t, Measurable[pathFiltration t] (G t)) ∧
      ∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = F b t := by
  obtain ⟨G0, hG0ad, hG0eq⟩ := exists_adapted_version_lqgClock hcont hF
  set G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0 := fun t b => (G0 t b).toNNReal with hGdef
  have hGa : ∀ t, Measurable[pathFiltration t] (G t) := fun t =>
    (hG0ad t).real_toNNReal
  have hGm : ∀ t, Measurable (G t) := fun t => (hGa t).mono (pathFiltration_le_ambient t) le_rfl
  -- the version agrees with the clock, from every start
  have hGeq : ∀ z : ℂ, ∀ᵐ b ∂planarLaw z, IsTimeChangeClock (F b) ∧ ∀ t, (G t b : ℝ) = F b t := by
    intro z
    filter_upwards [hG0eq z, hT z] with b hb hc
    refine ⟨hc, fun t => ?_⟩
    have h0 : 0 ≤ F b t := by
      have := hc.strictMono.monotone (show (0 : ℝ≥0) ≤ t from zero_le)
      rwa [hc.map_zero] at this
    simp only [hGdef, hb t, Real.coe_toNNReal _ h0]
  have hAm : ∀ k t, Measurable (fun b : ContinuousPath ℂ => lqgClockApprox γ hε (dyadicScale k) b t) :=
    fun k t => (LQGClockApproxAdapted.measurable_lqgClockApprox_canonicalFiltration γ
      (hcont k).measurable t).mono ((ContinuousPath.canonicalFiltration (alpha := ℂ)).le t) le_rfl
  have hconv : ∀ y t η, 0 < η → Tendsto (fun k => planarBrownianMotion y
      {b | η ≤ |lqgClockApprox γ hε (dyadicScale k) b t - (G t b : ℝ)|}) atTop (𝓝 0) := by
    intro y t η hη
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) (hF y t η hη)
      (fun k => bot_le) (fun k => ?_)
    have hN : planarBrownianMotion y {b : ContinuousPath ℂ | ¬ (IsTimeChangeClock (F b) ∧ ∀ t, (G t b : ℝ) = F b t)} = 0 := by
      refine ae_iff.1 ?_
      filter_upwards [hGeq y] with b hb
      exact hb
    calc planarBrownianMotion y {b | η ≤ |lqgClockApprox γ hε (dyadicScale k) b t - (G t b : ℝ)|}
        ≤ planarBrownianMotion y ({b | ∃ t' ≤ t, η ≤
            |lqgClockApprox γ hε (dyadicScale k) b t' - F b t'|} ∪
            {b : ContinuousPath ℂ | ¬ (IsTimeChangeClock (F b) ∧ ∀ t, (G t b : ℝ) = F b t)}) := by
          refine measure_mono fun b hb => ?_
          by_cases hbN : IsTimeChangeClock (F b) ∧ ∀ t, (G t b : ℝ) = F b t
          · left
            refine ⟨t, le_rfl, ?_⟩
            have hb' : η ≤ |lqgClockApprox γ hε (dyadicScale k) b t - (G t b : ℝ)| := hb
            rwa [hbN.2 t] at hb'
          · right
            exact hbN
      _ ≤ _ + 0 := (measure_union_le _ _).trans (add_le_add_right hN.le _)
      _ = _ := add_zero _
  have hadd := fun z s t => ae_add_of_tendsto_probability
    (A := fun k t b => lqgClockApprox γ hε (dyadicScale k) b t)
    (G := fun t b => (G t b : ℝ)) (fun k t => hAm k t)
    (fun t => (hGm t).coe_nnreal_real)
    (fun k s t b => FirstPass.Derived.lqgClockApprox_add_eq_add_shift (hcont k) b s t) hconv z s t
  refine ⟨G, ⟨fun t => hGm t, fun z t => ⟨G t, hGa t, Filter.EventuallyEq.rfl⟩, ?_, ?_⟩, ?_, hGa, ?_⟩
  · intro z
    filter_upwards [hGeq z] with b hb
    have h0 : G 0 b = 0 := by
      rw [← NNReal.coe_eq_zero, hb.2 0, hb.1.map_zero]
    refine ⟨h0, ?_, ?_⟩
    · refine continuous_induced_rng.2 ?_
      have : (fun t => (((G t b : ℝ≥0)) : ℝ)) = F b := funext hb.2
      exact (show ((fun x : ℝ≥0 => (x : ℝ)) ∘ fun t => G t b) = F b from this) ▸ hb.1.continuous
    · intro s t hst
      rw [← NNReal.coe_le_coe, hb.2, hb.2]
      exact hb.1.strictMono.monotone hst
  · intro z s t
    filter_upwards [hadd z t s] with b hb
    rw [← NNReal.coe_inj, NNReal.coe_add]
    have hs : LatticeProb.pathShift b t = ContinuousPath.shift t b := congrFun (pathShift_eq_shift t) b
    rw [hs]
    exact_mod_cast hb
  · intro z
    filter_upwards [hGeq z] with b hb
    refine ⟨fun s t hst => ?_, ?_⟩
    · rw [← NNReal.coe_lt_coe, hb.2, hb.2]
      exact hb.1.strictMono hst
    · rw [← NNReal.tendsto_coe_atTop]
      simpa [funext hb.2] using hb.1.tendsto_atTop
  · intro z
    filter_upwards [hGeq z] with b hb
    exact fun t => hb.2 t

section ValidEnvironment

variable {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
  {H : Ω → LQGMetric.DistC}

/-- **In a valid environment, almost surely, the clock has an adapted PCAF version.**  For any version `H` of
the field of a valid environment, for almost every sample `ω` there is a functional `G`, adapted to the natural
filtration of the path, which is a positive continuous additive functional of planar Brownian motion with a good
clock and equals the clock `S.clock ω` at all times, almost surely under planar Brownian motion from every
start. -/
theorem MatedCRTEnv.IsValid.ae_exists_pcaf_goodClock_clock (hS : S.IsValid 𝒮 γ)
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∃ G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsPCAF planarLaw G ∧ GoodClock planarLaw G ∧
      (∀ t, Measurable[pathFiltration t] (G t)) ∧
      ∀ z : ℂ, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = S.clock ω b t := by
  filter_upwards [hS.ae_continuous_coordCircleAverage_dyadicScale hH,
    hS.ae_isLQGClock_coordCircleAverage hH] with ω hcont hclk
  exact exists_pcaf_goodClock_lqgClock hcont (fun z => (hclk z).1) (fun z => (hclk z).2)

end ValidEnvironment

end MatedCRT
