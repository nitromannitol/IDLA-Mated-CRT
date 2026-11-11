import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosure3
import MatedCRT.Proofs.Sec3.KilledOccupation.ConeClockTransfer
import MatedCRT.Proofs.Sec3.KilledOccupation.ConeOriginTails

/-!
# Frozen killed-occupation input of the Green function, with the cone identification of the clock

`frozenLBMGreenOccupationRescaled_closed4` is `frozenLBMGreenOccupationRescaled_closed3` (OccupationClosure3.lean:68)
with its hypothesis `hS6` (identification `S.clock = φ` on `[0, σ]`, tex:370-425) supplied by `hS6_cone`
(ConeClockTransfer.lean), whose origin tail moment `hT0cone` is supplied by `coneOriginTailMoment_of_law`
(ConeOriginTails.lean) from the printed law `ConeUnitDiskGFFLaw` (eq:gff, tex:427-445, PENDING TRUTH CHECK MQ-li-12).

The ordinary Brownian occupation identity is taken in its killed form `KilledBrownianOccupationOnBall` (Step S0,
tex:48-52, cited classical input, MQ-li-8e). The lintegral form `BrownianOccupationOnBall`, which `hS6_cone` consumes,
is obtained from it by `brownianOccupationOnBall_of_killed`, using `lintegral_brownian_occupation_all`
(BaseClockProof.lean) for all measurable nonnegative integrands; no further input is used.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The time measure `timeLeb` restricted to `[0, σ]` is Lebesgue measure on `(0, σ]` pulled back by `toNNReal`
(the change of variables `u = t.toNNReal`; Lebesgue measure has no atoms, so `(0, σ]` and `[0, σ]` agree). -/
lemma lintegral_Icc_timeLeb_eq_Ioc {h : ℝ≥0 → ℝ≥0∞} (hh : Measurable h) (σ : ℝ≥0) :
    ∫⁻ u in Icc 0 σ, h u ∂timeLeb = ∫⁻ t in Ioc (0 : ℝ) (σ : ℝ), h t.toNNReal := by
  have hpre : MeasurableSet (Real.toNNReal ⁻¹' Icc 0 σ) := measurable_real_toNNReal measurableSet_Icc
  have hset : Real.toNNReal ⁻¹' Icc 0 σ ∩ Ici (0 : ℝ) = Icc (0 : ℝ) (σ : ℝ) := by
    ext x
    simp [Real.toNNReal_le_iff_le_coe, and_comm]
  unfold timeLeb
  rw [Measure.restrict_map measurable_real_toNNReal measurableSet_Icc,
    lintegral_map hh measurable_real_toNNReal, Measure.restrict_restrict hpre, hset,
    Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- **Bridge from the killed to the lintegral form of Step S0.** The killed Brownian occupation identity
`KilledBrownianOccupationOnBall` (bounded real integrands, Potential.lean:275) implies the lintegral form
`BrownianOccupationOnBall` (RemovedTail.lean:37, nonnegative extended integrands): the passage is the change of
variables of `lintegral_Icc_timeLeb_eq_Ioc` and the identity `lintegral_brownian_occupation_all`. -/
theorem brownianOccupationOnBall_of_killed {z : ℂ} {r : ℝ}
    (hK : KilledBrownianOccupationOnBall z r) : BrownianOccupationOnBall z r := by
  intro y hy f hf
  have hinner : ∀ b : ContinuousPath ℂ,
      ∫⁻ u in Icc 0 (exitNN z r b), f (b u) ∂timeLeb =
        ∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal, f (b t.toNNReal) := by
    intro b
    exact lintegral_Icc_timeLeb_eq_Ioc (h := fun u : ℝ≥0 => f (b u)) (hf.comp b.continuous.measurable) _
  calc ∫⁻ b, (∫⁻ u in Icc 0 (exitNN z r b), f (b u) ∂timeLeb) ∂planarBrownianMotion y
      = ∫⁻ b, (∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal, f (b t.toNNReal))
          ∂planarBrownianMotion y :=
        lintegral_congr fun b => hinner b
    _ = ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * f x :=
        lintegral_brownian_occupation_all hy hK (integrable_pathExitTime_toReal_planar y z r)
          (measurable_pathExitTime_ball z r) (measurable_greenFunction_ball_left z y r)
          (integrableOn_greenFunction_ball z y r hy) hf
    _ = 2 * ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) * f x := by
        have hm : Measurable fun x : ℂ => ENNReal.ofReal (greenFunction (ball z r) y x) * f x :=
          (measurable_greenFunction_ball_left z y r).ennreal_ofReal.mul hf
        rw [← lintegral_const_mul (2 : ℝ≥0∞) hm]
        refine lintegral_congr fun x => ?_
        show ENNReal.ofReal (2 * greenFunction (ball z r) y x) * f x =
          2 * (ENNReal.ofReal (greenFunction (ball z r) y x) * f x)
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]

/-- **Frozen killed-occupation input of the Green function, cone identification** (`FrozenLBMGreenOccupationRescaled`).
It is `frozenLBMGreenOccupationRescaled_closed3` with the hypothesis `hS6` replaced by its derivation from `hS6_cone`,
and the origin tail moment of `hS6_cone` supplied by `coneOriginTailMoment_of_law` from `hlaw`.

Named inputs (the binders of closure3 except `hS6`, plus three):
* `hlaw : ConeUnitDiskGFFLaw`: the printed law eq:gff (tex:427-445), PENDING TRUTH CHECK (MQ-li-12).
* `hE`: the χ_a-parts converge in probability (tex:373-376, the cut form of lem:occ-base, tex:140-141; G1).
* `hKern`: the base clock `dA` is the kernel `K` of its measurability (MQ-li-8g class, as `hMeas`).
* `hS0` (killed Brownian occupation identity, Step S0, tex:48-52; cited, MQ-li-8e), `hBG`, `hWeight`, `hMeas`,
  `hm0`, `hw`, `hVar`, `hνmeas`, `hconvB1`, `hLjoint`, `hLpath`: as in closure3. -/
theorem frozenLBMGreenOccupationRescaled_closed4 (𝒮 : SpaceFillingSLEModel)
    (ν : (γ : ℝ) → (Ω : Type) → [MeasurableSpace Ω] → MatedCRTEnv Ω → Ω → Measure ℂ)
    (dA : (γ : ℝ) → (Ω : Type) → [MeasurableSpace Ω] → MatedCRTEnv Ω → Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (hm0 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → 0 < S.m₀)
    (hWeight : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → OccWeightIdentity S.P S.μ (ν γ Ω S) γ)
    (hMeas : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ᵐ ω ∂S.P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
        Measurable fun b => ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(dA γ Ω S ω b))
    (hlaw : ConeUnitDiskGFFLaw)
    (hE : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η →
        Tendsto (fun ε => (S.P.prod (planarBrownianMotion y))
          {x | ENNReal.ofReal η < clockDistE γ (fun ω => coneShift γ (S.hcirc ω)) (dA γ Ω S) (exitNN z r) ε a x})
          (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hKern : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∃ K : Kernel (Ω × ContinuousPath ℂ) ℝ≥0, IsSFiniteKernel K ∧
        ∀ x, K x = dA γ Ω S x.1 x.2)
    (hBG : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∃ e : ℝ, 0 < e ∧ BGMassUpperBoundDyadic S.P S.μ e)
    (hS0 : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (z : ℂ) (r : ℝ), 0 < r → ball z r ⊆ ball 0 ρ →
      KilledBrownianOccupationOnBall z r)
    (hw : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ S.hcirc p.1 k p.2)
    (hVar : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ᶠ k in atTop, ∀ x ∈ ball z r, ∫⁻ ω, ENNReal.ofReal (circleWeight γ S.hcirc ω k x) ∂S.P = 1)
    (hνmeas : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν γ Ω S ω))
    (hconvB1 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) →
      (∀ x ∉ ball 0 1, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ S.hcirc ω k)) (∫⁻ x, ρ x ∂(ν γ Ω S ω)) ∂S.P)
        atTop (𝓝 0))
    (hLjoint : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ q : ℂ → ℝ≥0∞, Measurable q →
        Measurable fun p : Ω × ContinuousPath ℂ => limitClockFun (dA γ Ω S) z r p.1 p.2 q)
    (hLpath : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ q : ℂ → ℝ≥0∞, Continuous q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
        ∀ᵐ b ∂planarBrownianMotion y,
          Tendsto (fun k => clockGapMean S.P γ S.hcirc (dA γ Ω S) z r k q b) atTop (𝓝 0)) :
    FrozenLBMGreenOccupationRescaled 𝒮 := by
  have hS6 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, ∀ s ≤ exitNN z r b,
        S.clock ω b s = (weightedClock (dA γ Ω S ω b) (fun u => gammaWeight γ (b u)) (exitNN z r b) s).toReal := by
    intro γ hγ0 hγ2 ρ hρ0 hρ1 Ω _ S hS r z y hr hball hy
    have := hS.isProbabilityMeasure
    -- the base identity of lem:occ-base (closure3's `hBase`, replayed)
    have hBase : BaseOccupationIdentity S.P (planarBrownianMotion y) (ball z r) (greenFunction (ball z r) y)
        (ν γ Ω S) (dA γ Ω S) (exitNN z r) :=
      baseOccupationIdentity_of_GMC_cont' S.P γ S.hcirc z r hy
        (hball.trans (Metric.ball_subset_ball hρ1.le))
        (hS0 ρ hρ0 hρ1 z r hr hball)
        (hw γ hγ0 hγ2 Ω S hS)
        (hVar γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
        (ν γ Ω S) (dA γ Ω S)
        (hνmeas γ hγ0 hγ2 Ω S hS)
        (hconvB1 γ hγ0 hγ2 Ω S hS)
        (hLjoint γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
        (hMeas γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
        (hLpath γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
    obtain ⟨e, he, hBGe⟩ := hBG γ hγ0 hγ2 Ω S hS
    have hS3 : ∀ᵐ ω ∂S.P, ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) ∂(S.μ ω) < ⊤ :=
      ae_greenFunction_lintegral_lt_top S.P S.μ he hBGe hρ1 hr hball (greenDiskFormula z r) hy
    obtain ⟨p, κ, hp0, hp1, hκ⟩ : ∃ p κ : ℝ, 0 < p ∧ p < min 1 (4 / γ ^ 2 - 1) ∧
        κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2 := by
      have h4 : 1 < 4 / γ ^ 2 := by
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < γ ^ 2)]
        nlinarith [mul_pos hγ0 hγ0]
      have hm : 0 < min 1 (4 / γ ^ 2 - 1) := lt_min one_pos (by linarith)
      exact ⟨min 1 (4 / γ ^ 2 - 1) / 2, (2 - γ ^ 2 / 2) * (min 1 (4 / γ ^ 2 - 1) / 2) -
        γ ^ 2 * (min 1 (4 / γ ^ 2 - 1) / 2) ^ 2 / 2, half_pos hm, by linarith, rfl⟩
    obtain ⟨K, hKs, hK⟩ := hKern γ hγ0 hγ2 Ω S hS
    have := hKs
    exact hS6_cone 𝒮 hγ0 hγ2 S hS hp0 hp1 hκ
      (coneOriginTailMoment_of_law hlaw 𝒮 hγ0 hγ2 hp0 hp1 hκ S hS) (dA γ Ω S) hr
      (radius_le_two_of_ball_subset hρ1 hball) (greenDiskFormula z r) hy
      (brownianOccupationOnBall_of_killed (hS0 ρ hρ0 hρ1 z r hr hball)) K hK (ν γ Ω S)
      (hball.trans (Metric.ball_subset_ball hρ1.le)) hBase
      (hMeas γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
      (weight_identity_of_occWeight (hWeight γ hγ0 hγ2 Ω S hS)) hS3
      (hE γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
  exact frozenLBMGreenOccupationRescaled_closed3 𝒮 ν dA hm0 hWeight hMeas hS6 hBG hS0 hw hVar hνmeas hconvB1
    hLjoint hLpath

end MatedCRT.KilledOccupation
