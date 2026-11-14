import MatedCRT.FirstPass.Derived.LimClockOccupationLimit
import MatedCRT.FirstPass.Derived.LimClockOccupationAtoms
import MatedCRT.FirstPass.Derived.GmcGreenMeasureFinite
import MatedCRT.FirstPass.Derived.GmcGreenMassNearPole
import LatticeProb.Prob.RestrictEqOfBallTests

/-!
# The expected occupation measure of the limiting Liouville clock on the disc

Let `h = h^ℂ - γ log |·|` be built from a whole-plane GFF `h^ℂ` (`0 < γ < 2`), let `D = B_r(z) ⊆ B_ρ(0)`, `y ∈ D`, and
let `n_k → ∞` be a subsequence along which the clock gaps are summable. Write
`m₁ = E_y ∫_0^{σ_D} 1_{(·)}(b_u) dΦ(u)` for the expected occupation measure of the limiting clock `Φ` of Brownian motion
started at `y` and killed on exiting `D` (`limClockOccupationMeasure`), and `m₂ = 1_D · 2 G_D(y, ·) · Γ` for the
Green-weighted γ-LQG measure (`gmcGreenMeasure`).

If the regularized clock integrals of every continuous `g ≥ 0` with compact support in `D ∖ {0, y}` are uniformly
integrable for `P' ⊗ P_y`, then almost surely in the field the two measures agree on the punctured disc `D ∖ {0, y}`.
Since `m₁` has no atoms, `m₁` restricted to `D` is `m₂` restricted to `D ∖ {0, y}`; in particular `m₁(D) < ∞` almost
surely when `y ≠ 0`.

## Main results

* `ae_restrict_limClockOccupationMeasure_eq_gmcGreenMeasure`: a.s. `m₁|_{D ∖ {0,y}} = m₂|_{D ∖ {0,y}}`;
* `ae_restrict_ball_limClockOccupationMeasure_eq`: a.s. `m₁|_D = m₂|_{D ∖ {0,y}}`;
* `ae_limClockOccupationMeasure_ball_lt_top`: for `y ≠ 0`, a.s. `m₁(D) < ∞`.

Proof: the identity of the integrals of one test function (`ae_lintegral_limClockOccupationMeasure_eq_gmcGreenMeasure`)
holds for each of the countably many ball test functions of `D ∖ {0, y}` simultaneously; `m₂` is a.s. finite on the
compact subsets of `D ∖ {y}` (`ae_gmcGreenMeasure_lt_top_gff`), so the restrictions agree
(`LatticeProb.Prob.restrict_eq_of_lintegral_ballTestFn_eq`).
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The punctured disc `B_r(z) ∖ {0, y}` is open. -/
lemma isOpen_ball_sdiff_pair (z y : ℂ) (r : ℝ) : IsOpen (ball z r \ ({0, y} : Set ℂ)) :=
  isOpen_ball.sdiff (Set.toFinite ({0, y} : Set ℂ)).isClosed

/-- **The expected occupation measure of the limiting clock on the punctured disc.** For a whole-plane GFF, if the
regularized clock integrals of every continuous `g ≥ 0` with compact support in `D ∖ {0, y}` are uniformly integrable
for `P' ⊗ P_y`, then for `P'`-almost every `ω'` the expected occupation measure of the limiting clock and the
Green-weighted γ-LQG measure `1_D · 2 G_D(y, ·) · Γ` agree on `D ∖ {0, y}`. -/
theorem ae_restrict_limClockOccupationMeasure_eq_gmcGreenMeasure {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ}
    (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {z y : ℂ} {r : ℝ} (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hB : BrownianOccupationOnBall z r) {n : ℕ → ℕ} (hn : StrictMono n) (hn0 : dyadicScale (n 0) < 1 - ρ)
    (hgapLaw : ∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hui : ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) → HasCompactSupport g →
      tsupport g ⊆ ball z r \ ({0, y} : Set ℂ) →
      UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y))) :
    ∀ᵐ ω' ∂P', (limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y)
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')).restrict (ball z r \ ({0, y} : Set ℂ)) =
      (gmcGreenMeasure γ ρ ρ₂ z y r (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')).restrict
        (ball z r \ ({0, y} : Set ℂ)) := by
  have hyU : y ∉ ball z r \ ({0, y} : Set ℂ) := fun h => h.2 (by simp)
  have htest : ∀ F : Finset (ℕ × ℚ), ∀ᵐ ω' ∂P',
      LatticeProb.Prob.IsBallTestAdmissible (ball z r \ ({0, y} : Set ℂ)) F → ∀ j : ℕ,
      ∫⁻ x, ENNReal.ofReal (LatticeProb.Prob.ballTestFn F j x) ∂limClockOccupationMeasure γ
          (fun k => dyadicScale (n k)) z r (planarBrownianMotion y)
          (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') =
        ∫⁻ x, ENNReal.ofReal (LatticeProb.Prob.ballTestFn F j x) ∂gmcGreenMeasure γ ρ ρ₂ z y r
          (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') := by
    intro F
    by_cases hF : LatticeProb.Prob.IsBallTestAdmissible (ball z r \ ({0, y} : Set ℂ)) F
    · have hsupp := LatticeProb.Prob.tsupport_ballTestFn_subset hF
      have hall := fun j : ℕ =>
        ae_lintegral_limClockOccupationMeasure_eq_gmcGreenMeasure (g := LatticeProb.Prob.ballTestFn F j)
          hG hγ hγ2 hρρ₂ hρ₂ hball hy hB hn hn0 hgapLaw (LatticeProb.Prob.continuous_ballTestFn F j)
          (LatticeProb.Prob.ballTestFn_nonneg F j) (LatticeProb.Prob.hasCompactSupport_ballTestFn F j)
          (fun x hx => ((hsupp j) hx).1) (fun h => hyU (hsupp j h))
          (hui _ (LatticeProb.Prob.continuous_ballTestFn F j) (LatticeProb.Prob.ballTestFn_nonneg F j)
            (LatticeProb.Prob.hasCompactSupport_ballTestFn F j) (hsupp j))
      filter_upwards [ae_all_iff.2 hall] with ω' hω _ j
      exact hω j
    · exact Eventually.of_forall fun _ h => absurd h hF
  filter_upwards [ae_all_iff.2 htest, ae_gmcGreenMeasure_lt_top_gff hG hγ hγ2 hρρ₂ hρ₂] with ω' hω hfin
  exact LatticeProb.Prob.restrict_eq_of_lintegral_ballTestFn_eq (isOpen_ball_sdiff_pair z y r)
    (fun K hK hKU => hfin z y r hy K hK fun h => hyU (hKU h)) hω

/-- **The expected occupation measure of the limiting clock on the disc.** Under the hypotheses of
`ae_restrict_limClockOccupationMeasure_eq_gmcGreenMeasure`, almost surely the expected occupation measure of the
limiting clock restricted to `D` equals the Green-weighted γ-LQG measure restricted to `D ∖ {0, y}` (the occupation
measure has no atoms). -/
theorem ae_restrict_ball_limClockOccupationMeasure_eq {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ}
    (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {z y : ℂ} {r : ℝ} (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hB : BrownianOccupationOnBall z r) {n : ℕ → ℕ} (hn : StrictMono n) (hn0 : dyadicScale (n 0) < 1 - ρ)
    (hgapLaw : ∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hui : ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) → HasCompactSupport g →
      tsupport g ⊆ ball z r \ ({0, y} : Set ℂ) →
      UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y))) :
    ∀ᵐ ω' ∂P', (limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y)
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')).restrict (ball z r) =
      (gmcGreenMeasure γ ρ ρ₂ z y r (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')).restrict
        (ball z r \ ({0, y} : Set ℂ)) := by
  filter_upwards [ae_restrict_limClockOccupationMeasure_eq_gmcGreenMeasure hG hγ hγ2 hρρ₂ hρ₂ hball hy hB hn
    hn0 hgapLaw hui] with ω' hω
  rw [← hω]
  refine (Measure.restrict_congr_set (sdiff_null_ae_eq_self ?_)).symm
  rw [Set.insert_eq]
  exact measure_union_null (limClockOccupationMeasure_planarBrownianMotion_singleton _ _ _ _ _ _ _)
    (limClockOccupationMeasure_planarBrownianMotion_singleton _ _ _ _ _ _ _)

/-- **Finiteness of the expected occupation measure of the limiting clock.** Under the hypotheses of
`ae_restrict_limClockOccupationMeasure_eq_gmcGreenMeasure`, if the starting point `y` is not the singularity `0` of
the field, then almost surely the expected occupation measure of the limiting clock gives finite mass to `D`. -/
theorem ae_limClockOccupationMeasure_ball_lt_top {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ}
    (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {z y : ℂ} {r : ℝ} (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hy0 : y ≠ 0)
    (hB : BrownianOccupationOnBall z r) {n : ℕ → ℕ} (hn : StrictMono n) (hn0 : dyadicScale (n 0) < 1 - ρ)
    (hgapLaw : ∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hui : ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) → HasCompactSupport g →
      tsupport g ⊆ ball z r \ ({0, y} : Set ℂ) →
      UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y))) :
    ∀ᵐ ω' ∂P', limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y)
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (ball z r) < ∞ := by
  filter_upwards [ae_restrict_ball_limClockOccupationMeasure_eq hG hγ hγ2 hρρ₂ hρ₂ hball hy hB hn hn0 hgapLaw hui,
    ae_gmcGreenMeasure_ball_lt_top hG hγ hγ2 hρρ₂ hρ₂ hy hy0] with ω' h1 h2
  have h3 := congrArg (fun m : Measure ℂ => m univ) h1
  simp only [Measure.restrict_apply_univ] at h3
  rw [h3]
  exact (measure_mono fun x hx => hx.1).trans_lt h2

end MatedCRT.KilledOccupation
