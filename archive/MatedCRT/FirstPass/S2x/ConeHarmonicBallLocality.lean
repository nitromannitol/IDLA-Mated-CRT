import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.Locality

/-!
# Locality of the cone harmonic-ball event (Step `ConeHarmonicBallLocalityStep`, HB22 Proposition 1.3)

* `lqgLimit_restrict_ball_eq` (Fact 2.2 II, deterministic form): two dyadic LQG limits of circle-average processes that
  agree on the circles `∂B_r(z)` with `cl B_r(z) ⊆ B_1` have the same restriction to `B_1`. A test function supported
  in `B_1` sees, at the dyadic scales below its distance to `∂B_1`, only circles inside `B_1`.
* `coneHarmonicBallLocalityStep_of_locality`: the Step follows from two explicit hypotheses, (L) locality of the event
  `HasConeHarmonicBallsUpToHalfBall` on Radon measures through `ν|_{B_1}` (HB22 Proposition 1.3, measure form), and
  (M) measurability of the restricted event `coneHarmonicBallSet γ`. Neither is in MatedCRT/External or proved here.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open _root_.HarmonicBalls

namespace MatedCRT.FirstPass2x

/-- The integral of a test function supported in `tsupport g` against `ε^{γ²/2} e^{γ c_ε} dz` depends only on the
circle averages `c_ε` on `tsupport g`. The density is not assumed measurable: restrict to `tsupport g` first. -/
theorem integral_lqgApprox_congr_of_eqOn {γ : ℝ} {c c' : ℝ → ℂ → ℝ} {ε : ℝ} {g : ℂ → ℝ}
    (hε : ∀ z ∈ tsupport g, c ε z = c' ε z) :
    ∫ z, g z ∂(lqgApprox γ c ε) = ∫ z, g z ∂(lqgApprox γ c' ε) := by
  have hK : MeasurableSet (tsupport g) := (isClosed_tsupport g).measurableSet
  have hg0 : ∀ z ∉ tsupport g, g z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport g h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg0,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := lqgApprox γ c' ε) hg0]
  unfold lqgApprox
  rw [restrict_withDensity hK, restrict_withDensity hK]
  congr 1
  exact withDensity_congr_ae (ae_restrict_of_forall_mem hK fun z hz => by simp only [hε z hz])

/-- **Fact 2.2 II, deterministic form.** Two dyadic LQG limits of circle-average processes which agree on the circles
`∂B_r(z)` with `cl B_r(z) ⊆ B_1` (`unitBallCircleProcess`) have the same restriction to `B_1`. Proof: integrals of test
functions supported in `B_1` agree (dyadic limits, `integral_lqgApprox_congr_of_eqOn`); the restrictions then agree on
open sets through `measure_eq_iSup_ofReal_integral`, and open sets determine a finite measure (`ext_of_generate_finite`). -/
theorem lqgLimit_restrict_ball_eq {γ : ℝ} {c c' : ℝ → ℂ → ℝ} {ν ν' : Measure ℂ}
    (hν : IsLQGLimit γ c ν) (hν' : IsLQGLimit γ c' ν')
    (hc : unitBallCircleProcess c = unitBallCircleProcess c') :
    ν.restrict (ball 0 1) = ν'.restrict (ball 0 1) := by
  have hint : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ ball 0 1 →
      ∫ z, g z ∂ν = ∫ z, g z ∂ν' := by
    intro g hg hgc hgU
    obtain ⟨δ, hδ, hδU⟩ := hgc.isCompact.exists_thickening_subset_open isOpen_ball hgU
    have hk : ∀ᶠ k : ℕ in atTop, dyadicScale k < δ := by
      have h0 : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝 0) := by
        unfold dyadicScale
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      exact h0.eventually (gt_mem_nhds hδ)
    have hcongr : ∀ᶠ k : ℕ in atTop, ∫ z, g z ∂(lqgApprox γ c (dyadicScale k)) =
        ∫ z, g z ∂(lqgApprox γ c' (dyadicScale k)) := by
      filter_upwards [hk] with k hkδ
      apply integral_lqgApprox_congr_of_eqOn
      intro z hz
      have hpos : 0 < dyadicScale k := by unfold dyadicScale; positivity
      have hsub : closedBall z (dyadicScale k) ⊆ ball 0 1 := by
        intro w hw
        apply hδU
        exact mem_thickening_iff.2 ⟨z, hz, lt_of_le_of_lt (mem_closedBall.1 hw) hkδ⟩
      exact congrFun hc ⟨(⟨dyadicScale k, hpos⟩, z), hsub⟩
    have h1 := hν.tendsto_integral g hg hgc
    have h2 := hν'.tendsto_integral g hg hgc
    exact tendsto_nhds_unique h1 (h2.congr' (hcongr.mono fun k hk => hk.symm))
  have hopen : ∀ W : Set ℂ, IsOpen W → ν (W ∩ ball 0 1) = ν' (W ∩ ball 0 1) := by
    intro W hW
    have hV : IsOpen (W ∩ ball 0 1) := hW.inter isOpen_ball
    obtain ⟨g, hgc, hgcs, hgU, hg01, hgt⟩ := MatedCRT.LQGMeasure.exists_approx_indicator hV
    have := hν.isLocallyFiniteMeasure
    have := hν'.isLocallyFiniteMeasure
    have heq : ∀ n, ∫ z, g n z ∂ν = ∫ z, g n z ∂ν' := fun n =>
      hint (g n) (hgc n) (hgcs n) ((hgU n).trans inter_subset_right)
    rw [MatedCRT.LQGMeasure.measure_eq_iSup_ofReal_integral (m := ν) hV hgc hgcs hgU hg01 hgt,
      MatedCRT.LQGMeasure.measure_eq_iSup_ofReal_integral (m := ν') hV hgc hgcs hgU hg01 hgt]
    simp only [heq]
  have := hν.isLocallyFiniteMeasure
  have : IsFiniteMeasure (ν.restrict (ball 0 1)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : ℂ) 1).measure_lt_top⟩
  refine ext_of_generate_finite {s : Set ℂ | IsOpen s} ?_ isPiSystem_isOpen ?_ ?_
  · exact BorelSpace.measurable_eq
  · intro s hs
    have hs' : IsOpen s := hs
    rw [Measure.restrict_apply hs'.measurableSet, Measure.restrict_apply hs'.measurableSet]
    exact hopen s hs'
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    simpa using hopen univ isOpen_univ

/-- The restricted cone harmonic-ball set of Step `ConeHarmonicBallLocalityStep`: the restrictions `unitBallCircleProcess c`
of circle-average processes `c` with a dyadic LQG limit `ν` such that `ν` carries a family of harmonic balls stopped at
`∂B_{1/2}` (`HasConeHarmonicBallsUpToHalfBall`, Lemma 2.4). -/
def coneHarmonicBallSet (γ : ℝ) : Set (UnitBallCircle → ℝ) :=
  {f | ∃ c : ℝ → ℂ → ℝ, unitBallCircleProcess c = f ∧
    ∃ ν : Measure ℂ, IsLQGLimit γ c ν ∧ HasConeHarmonicBallsUpToHalfBall ν}

/-- **`ConeHarmonicBallLocalityStep` from locality and measurability.** Given (L), the event `HasConeHarmonicBallsUpToHalfBall`
depends on a Radon measure only through its restriction to `B_1` (HB22 Proposition 1.3, measure form; paper l.542), and
(M), the restricted event `coneHarmonicBallSet γ` is measurable, the Step holds with `S = coneHarmonicBallSet γ`: the two
a.s. equivalences follow from `lqgLimit_restrict_ball_eq` (for the cone measure, and for the field `fieldCircleAverage γ h`
of the whole-plane GFF) and from (L). -/
theorem coneHarmonicBallLocalityStep_of_locality
    (hL : ∀ ν ν' : Measure ℂ, ν.restrict (ball 0 1) = ν'.restrict (ball 0 1) →
      (HasConeHarmonicBallsUpToHalfBall ν ↔ HasConeHarmonicBallsUpToHalfBall ν'))
    (hM : ∀ γ : ℝ, 0 < γ → γ < 2 → MeasurableSet (coneHarmonicBallSet γ)) :
    ConeHarmonicBallLocalityStep := by
  unfold ConeHarmonicBallLocalityStep
  intro γ hγ0 hγ2
  refine ⟨coneHarmonicBallSet γ, hM γ hγ0 hγ2, ?_, ?_⟩
  · intro Ω _ P hC hcirc μ hcone
    have hω0 : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
    filter_upwards [hω0] with ω hω
    constructor
    · intro hE
      exact ⟨hcirc ω, rfl, μ ω, hω, hE⟩
    · rintro ⟨c, hc, ν, hν, hνE⟩
      exact (hL (μ ω) ν (lqgLimit_restrict_ball_eq hω hν hc.symm)).2 hνE
  · intro Ω _ P hC hcirc μ _ _ hcone
    have hω0 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage γ (hcirc ω)) (μ ω) := hcone
    filter_upwards [hω0] with ω hω
    constructor
    · intro hE
      exact ⟨fieldCircleAverage γ (hcirc ω), rfl, μ ω, hω, hE⟩
    · rintro ⟨c, hc, ν, hν, hνE⟩
      exact (hL (μ ω) ν (lqgLimit_restrict_ball_eq hω hν hc.symm)).2 hνE

end MatedCRT.FirstPass2x
