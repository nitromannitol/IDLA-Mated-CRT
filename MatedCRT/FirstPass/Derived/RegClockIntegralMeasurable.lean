import MatedCRT.FirstPass.Derived.LimClockAeConvergence

/-!
# Measurability and finiteness of the regularized clock integrals

For the regularized clock measure `F_ε(ψ, b) = ε^{γ²/2} e^{γ ψ̃(ε, b_u)} du` on `[0, σ(b)]` (`regClockMeasure`) and a
function `g` on `ℂ`, the integral `A_ε(ψ, b) = ∫_{[0,σ(b)]} g(b_u) dF_ε(ψ, b)(u)`

* is the Lebesgue integral of `g(b_u)` times the regularized density (`setLIntegral_regClockMeasure_eq`);
* is jointly measurable in `(ψ, b)` for a measurable exit time `σ` and measurable `g`
  (`measurable_setLIntegral_regClockMeasure`), hence in `(ω', b)` for the circle averages of a whole-plane GFF
  (`measurable_prod_setLIntegral_regClockMeasure`);
* is finite when the density is bounded on `[0, σ(b)]` and `g` is bounded above
  (`setLIntegral_regClockMeasure_lt_top`), hence almost surely finite at every scale under the product of a
  whole-plane GFF and an independent planar Brownian motion (`ae_prod_setLIntegral_regClockMeasure_ne_top`).

These are the measurability and finiteness hypotheses of the passage to the limit in the Revuz identity of the
Liouville clock.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The regularized density along a fixed path is measurable in time. -/
lemma measurable_regDensity_path (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ) :
    Measurable fun u : ℝ≥0 =>
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u))) :=
  measurable_ofReal_exp_mul _ γ
    (measurable_comp_pair (F := fun p : (UnitDiskCircleIndex → ℝ) × ℂ => circleAverageRep p.1 ε p.2)
      (measurable_circleAverageRep ε) measurable_const (map_continuous b).measurable)

/-- Lower integrals against the regularized clock measure over `[0, σ(b)]` are lower integrals against Lebesgue
measure on `ℝ≥0` with the regularized density. -/
theorem setLIntegral_regClockMeasure_eq (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (b : ContinuousPath ℂ) {F : ℝ≥0 → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u in Icc 0 (σ b), F u ∂regClockMeasure γ ε ψ σ b =
      ∫⁻ u in Icc 0 (σ b),
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u))) * F u ∂lebNN := by
  unfold regClockMeasure
  rw [restrict_withDensity measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc, inter_self,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_regDensity_path γ ε ψ b) hF]
  rfl

/-- **Joint measurability of the regularized clock integrals.** For a measurable exit time `σ` and a measurable
`g : ℂ → ℝ`, the map `x ↦ ∫_{[0,σ(B x)]} g(B x u) dF_ε(Ψ x, B x)(u)` is measurable whenever the circle-average
family `Ψ` (cylinder σ-algebra on `UnitDiskCircleIndex → ℝ`) and the path `B` (Borel σ-algebra on
`ContinuousPath ℂ`) are measurable functions of `x`. -/
theorem measurable_setLIntegral_regClockMeasure {X : Type*} [MeasurableSpace X] (γ ε : ℝ)
    (σ : ContinuousPath ℂ → ℝ≥0) (hσ : Measurable σ) {Ψ : X → UnitDiskCircleIndex → ℝ} (hΨ : Measurable Ψ)
    {B : X → ContinuousPath ℂ} (hB : Measurable B) {g : ℂ → ℝ} (hg : Measurable g) :
    Measurable fun x : X =>
      ∫⁻ u in Icc 0 (σ (B x)), ENNReal.ofReal (g (B x u)) ∂regClockMeasure γ ε (Ψ x) σ (B x) := by
  have hBu : Measurable fun q : X × ℝ≥0 => B q.1 q.2 :=
    measurable_eval_path.comp (measurable_snd.prodMk (hB.comp measurable_fst))
  have hRep : Measurable fun q : X × ℝ≥0 => circleAverageRep (Ψ q.1) ε (B q.1 q.2) :=
    measurable_comp_pair (F := fun p : (UnitDiskCircleIndex → ℝ) × ℂ => circleAverageRep p.1 ε p.2)
      (measurable_circleAverageRep ε) (hΨ.comp measurable_fst) hBu
  have hval : Measurable fun q : X × ℝ≥0 =>
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep (Ψ q.1) ε (B q.1 q.2))) *
        ENNReal.ofReal (g (B q.1 q.2)) :=
    (measurable_ofReal_exp_mul (ε ^ (γ ^ 2 / 2)) γ hRep).mul (ENNReal.measurable_ofReal.comp (hg.comp hBu))
  have hset : MeasurableSet {q : X × ℝ≥0 | q.2 ≤ σ (B q.1)} :=
    measurableSet_le measurable_snd (hσ.comp (hB.comp measurable_fst))
  have hfun : (fun x : X =>
      ∫⁻ u in Icc 0 (σ (B x)), ENNReal.ofReal (g (B x u)) ∂regClockMeasure γ ε (Ψ x) σ (B x)) =
      fun x => ∫⁻ u, {q : X × ℝ≥0 | q.2 ≤ σ (B q.1)}.indicator
        (fun q => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep (Ψ q.1) ε (B q.1 q.2))) *
          ENNReal.ofReal (g (B q.1 q.2))) (x, u) ∂lebNN := by
    funext x
    rw [setLIntegral_regClockMeasure_eq γ ε (Ψ x) σ (B x) (F := fun u => ENNReal.ofReal (g (B x u)))
      (ENNReal.measurable_ofReal.comp (hg.comp (map_continuous (B x)).measurable)),
      ← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun u => ?_
    by_cases h : u ≤ σ (B x)
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  rw [hfun]
  exact (hval.indicator hset).lintegral_prod_right'

/-- **Finiteness of the regularized clock integrals.** If the regularized density is at most `M` on `[0, σ(b)]`
and `g ≤ C`, then `∫_{[0,σ(b)]} g(b_u) dF_ε(ψ, b)(u) ≤ M · C⁺ · σ(b) < ∞`. -/
theorem setLIntegral_regClockMeasure_lt_top (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (b : ContinuousPath ℂ) {g : ℂ → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, g x ≤ C) {M : ℝ≥0}
    (hM : ∀ u ≤ σ b, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u))) ≤ M) :
    ∫⁻ u in Icc 0 (σ b), ENNReal.ofReal (g (b u)) ∂regClockMeasure γ ε ψ σ b < ∞ := by
  rw [setLIntegral_regClockMeasure_eq γ ε ψ σ b (F := fun u => ENNReal.ofReal (g (b u)))
    (ENNReal.measurable_ofReal.comp (hg.comp (map_continuous b).measurable))]
  calc ∫⁻ u in Icc 0 (σ b), ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u))) *
          ENNReal.ofReal (g (b u)) ∂lebNN
        ≤ ∫⁻ _ in Icc 0 (σ b), (M : ℝ≥0∞) * ENNReal.ofReal C ∂lebNN :=
          setLIntegral_mono measurable_const fun u hu =>
            mul_le_mul' (hM u hu.2) (ENNReal.ofReal_le_ofReal (hgC _))
    _ = (M : ℝ≥0∞) * ENNReal.ofReal C * (σ b : ℝ≥0∞) := by rw [setLIntegral_const, lebNN_Icc]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)
          ENNReal.coe_lt_top

/-- **Measurability on the product space.** For a whole-plane GFF `(hC', hc)` on `(Ω', P')`, the regularized clock
integrals of a measurable `g` along the circle averages of `h = h^ℂ - γ log|·|`, up to the exit time of `B_r(z)`, are
measurable in `(ω', b)`. -/
theorem measurable_prod_setLIntegral_regClockMeasure {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hwp : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    (γ ε r : ℝ) (z : ℂ) {g : ℂ → ℝ} (hg : Measurable g) :
    Measurable fun p : Ω' × ContinuousPath ℂ =>
      ∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
        ∂regClockMeasure γ ε (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1) (exitNN z r) p.2 := by
  have hmeas : ∀ (r' : ℝ) (z' : ℂ), 0 < r' →
      Measurable fun ω => fieldCircleAverage γ (hc ω) r' z' :=
    fun r' z' hr' => (hwp.measurable_circle r' z' hr').sub measurable_const
  have hψ : Measurable fun p : Ω' × ContinuousPath ℂ =>
      clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1 :=
    (measurable_unitDiskCircle _ hmeas).comp measurable_fst
  exact measurable_setLIntegral_regClockMeasure γ ε (exitNN z r) (measurable_exitNN z r) hψ measurable_snd hg

/-- **Almost sure finiteness on the product space.** Under the hypotheses of `ae_prod_regDensity_bdd_and_gap`, for a
measurable `g` bounded above, at every scale `2^{-n_k}` the regularized clock integral of `g` is finite for
`P' ⊗ P_y`-almost every `(ω', b)`. -/
theorem ae_prod_setLIntegral_regClockMeasure_ne_top {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hwp : HarmonicBalls.IsWholePlaneGFF P' hC' hc) (γ ρ r : ℝ) (z y : ℂ) (hball : ball z r ⊆ ball 0 ρ)
    (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : dyadicScale (n 0) < 1 - ρ)
    (hgapLaw : ∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    {g : ℂ → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, g x ≤ C) (k : ℕ) :
    ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      ∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
        ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
          (exitNN z r) p.2 ≠ ∞ := by
  filter_upwards [ae_prod_regDensity_bdd_and_gap hwp γ ρ r z y hball n hn hn0 hgapLaw] with p hp
  obtain ⟨M, hM⟩ := hp.1 k
  exact (setLIntegral_regClockMeasure_lt_top γ _ _ (exitNN z r) p.2 hg hgC hM).ne

end MatedCRT.KilledOccupation
