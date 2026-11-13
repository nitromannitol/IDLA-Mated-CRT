import MatedCRT.FirstPass.Derived.LimClockIntegralConvergence
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockAnnealedCauchy
import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockAgree
import MatedCRT.Proofs.Sec3.KilledOccupation.GMCLimit
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockFinite
import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationAssembly
import LatticeProb.Prob.CauchyInProbabilitySubseq

/-!
# Almost sure convergence of the regularized occupation clocks of a whole-plane GFF

Let `(hC, hc)` be a whole-plane GFF on `(Ω', P')`, `h = h^ℂ - γ log|·|` with circle averages
`fieldCircleAverage γ (hc ω')`, and `b` an independent planar Brownian motion started at `y`, killed on exiting
`D = B_r(z) ⊆ B_ρ(0)`. Along a strictly increasing sequence of dyadic scales `ε_k = 2^{-n_k}` with `ε_0 < 1 - ρ`
whose consecutive regularized clocks satisfy the summable annealed gap bounds, this file proves that for
`P' ⊗ P_y`-almost every `(ω', b)`:

* the regularized densities `ε_k^{γ²/2} e^{γ h_{ε_k}(b_u)}` are bounded on `[0, σ(b)]` for every `k`
  (`ae_prod_regDensity_bdd_and_gap`): almost surely the circle averages are continuous on `(0, ∞) × ℂ`, the circle
  average representative agrees with the continuous field on the closed disk of radius `ρ`, and the path stays in
  `D` before its exit time;
* eventually in `k`, the gap of the clocks at the scales `ε_k`, `ε_{k+1}` is at most `2^{-k}` (first Borel-Cantelli
  lemma, transferred from the coupled law to the product measure);
* consequently, simultaneously for all continuous `g ≥ 0`, `∫_{[0,σ]} g(b_u) dF_k(u) → ∫_{[0,σ]} g(b_u) dΦ(u)`,
  where `F_k` is the regularized clock measure and `Φ` the Stieltjes measure of the limit clock
  (`ae_prod_tendsto_setLIntegral_regClockMeasure`).

This is the almost sure convergence hypothesis of the passage to the limit in the Revuz identity of the Liouville
clock (Garban-Rhodes-Vargas, Liouville Brownian motion, Thm 2.7(1)).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- Along a strictly increasing sequence of indices, the dyadic scales are at most the first one. -/
lemma dyadicScale_le_of_strictMono {n : ℕ → ℕ} (hn : StrictMono n) (k : ℕ) :
    dyadicScale (n k) ≤ dyadicScale (n 0) := by
  unfold dyadicScale
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hn.monotone (Nat.zero_le k))

/-- **Bound on the regularized density along a path.** If the circle averages `hc` are continuous on
`(0, ∞) × ℂ`, `B_r(z) ⊆ B_ρ(0)`, `0 < ε < 1 - ρ`, and the path stays in `B_r(z)` before the time `σ(b)`, then the
regularized density `ε^{γ²/2} e^{γ h_ε(b_u)}` of `h = h^ℂ - γ log|·|` is bounded for `u ∈ [0, σ(b)]`: before `σ(b)`
the circle average representative is the continuous circle average at a point of the compact disk `B̄_ρ(0)`,
and `u = σ(b)` is a single time. -/
theorem exists_regDensity_bound_of_continuousOn (γ : ℝ) {hc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Ioi 0 ×ˢ univ))
    {ρ r ε : ℝ} {z : ℂ} (hball : ball z r ⊆ ball 0 ρ) (hε : 0 < ε) (hερ : ε < 1 - ρ)
    (σ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) (hb : ∀ s : ℝ≥0, s < σ b → b s ∈ ball z r) :
    ∃ M : ℝ≥0, ∀ u ≤ σ b,
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep
        (fun q : UnitDiskCircleIndex => fieldCircleAverage γ hc q.1.1 q.1.2) ε (b u))) ≤ M := by
  set ψ : UnitDiskCircleIndex → ℝ := fun q => fieldCircleAverage γ hc q.1.1 q.1.2 with hψdef
  have hF := continuousOn_fieldCircleAverage (α₀ := γ) hcont
  have hsub : (UnitDiskCircleIndex : Set (ℝ × ℂ)) ⊆ Ioi 0 ×ˢ univ := fun q hq => ⟨hq.1, mem_univ _⟩
  have hψ : Continuous ψ := continuousOn_iff_continuous_domRestrict.1 (hF.mono hsub)
  have hx : Continuous fun x : ℂ => fieldCircleAverage γ hc ε x :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hε, mem_univ x⟩)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn hx.continuousOn
  set v : ℝ := circleAverageRep ψ ε (b (σ b)) with hv
  have hw : ∀ u ≤ σ b, |circleAverageRep ψ ε (b u)| ≤ max C |v| := by
    intro u hu
    rcases hu.lt_or_eq with hlt | heq
    · have hnorm : ‖b u‖ < ρ := mem_ball_zero_iff.1 (hball (hb u hlt))
      rw [circleAverageRep_eq_of_lt (ρ₂ := 1 - ε) (H := fieldCircleAverage γ hc) hψ (fun _ => rfl) hε
        (by linarith) (by linarith)]
      exact (hC (b u) (mem_closedBall_zero_iff.2 hnorm.le)).trans (le_max_left _ _)
    · rw [heq]
      exact le_max_right _ _
  refine ⟨Real.toNNReal (ε ^ (γ ^ 2 / 2) * Real.exp (|γ| * max C |v|)), fun u hu => ?_⟩
  show ENNReal.ofReal _ ≤ ENNReal.ofReal _
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
    (Real.rpow_nonneg hε.le _))
  calc γ * circleAverageRep ψ ε (b u) ≤ |γ * circleAverageRep ψ ε (b u)| := le_abs_self _
    _ = |γ| * |circleAverageRep ψ ε (b u)| := abs_mul _ _
    _ ≤ |γ| * max C |v| := mul_le_mul_of_nonneg_left (hw u hu) (abs_nonneg γ)

/-- **Almost sure hypotheses of the clock convergence.** For a whole-plane GFF `(hC', hc)` on `(Ω', P')`, a planar
Brownian motion `P_y`, `B_r(z) ⊆ B_ρ(0)` and a strictly increasing sequence `n` with `2^{-n_0} < 1 - ρ` along which
the coupled law of the circle averages of `h = h^ℂ - γ log|·|` and the path gives the consecutive clock gaps the
summable bounds `P(gap_k > 2^{-k}) ≤ 2^{-k}`, for `P' ⊗ P_y`-almost every `(ω', b)` the regularized densities are
bounded on `[0, σ(b)]` at every scale `2^{-n_k}`, and eventually the `k`-th gap is at most `2^{-k}`. -/
theorem ae_prod_regDensity_bdd_and_gap {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hwp : HarmonicBalls.IsWholePlaneGFF P' hC' hc) (γ ρ r : ℝ) (z y : ℂ) (hball : ball z r ⊆ ball 0 ρ)
    (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : dyadicScale (n 0) < 1 - ρ)
    (hgapLaw : ∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) :
    ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      (∀ k, ∃ M : ℝ≥0, ∀ u ≤ exitNN z r p.2,
        ENNReal.ofReal ((dyadicScale (n k)) ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep
          (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1) (dyadicScale (n k)) (p.2 u))) ≤ M) ∧
      ∀ᶠ k in atTop, clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1)))
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1, p.2) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  have hmeas : ∀ (r' : ℝ) (z' : ℂ), 0 < r' →
      Measurable fun ω => fieldCircleAverage γ (hc ω) r' z' :=
    fun r' z' hr' => (hwp.measurable_circle r' z' hr').sub measurable_const
  have hf : Measurable fun p : Ω' × ContinuousPath ℂ =>
      (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1, p.2) :=
    measurable_clockAnnealedMap hmeas
  have hgap : ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)), ∀ᶠ k in atTop,
      clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1)))
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1, p.2) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
    ae_of_ae_map hf.aemeasurable (LatticeProb.ae_eventually_le_of_prob_le _
      (fun k => clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1)))) hgapLaw)
  have hcont : ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      ContinuousOn (fun q : ℝ × ℂ => hc p.1 q.1 q.2) (Ioi 0 ×ˢ univ) :=
    Measure.quasiMeasurePreserving_fst.ae hwp.ae_continuousOn_circle
  have hexit : ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      ∀ s : ℝ≥0, s < exitNN z r p.2 → p.2 s ∈ ball z r :=
    Measure.quasiMeasurePreserving_snd.ae
      ((planar_exit_ae_lt_top y z r).mono fun b hb => (exitNN_props_of_lt_top hb).1)
  filter_upwards [hgap, hcont, hexit] with p hg hcp he
  exact ⟨fun k => exists_regDensity_bound_of_continuousOn γ hcp hball (dyadicScale_pos _)
    ((dyadicScale_le_of_strictMono hn k).trans_lt hn0) (exitNN z r) p.2 he, hg⟩

/-- **Almost sure convergence of the regularized clock integrals.** Under the hypotheses of
`ae_prod_regDensity_bdd_and_gap`, for `P' ⊗ P_y`-almost every `(ω', b)`, simultaneously for every continuous
`g ≥ 0` on `ℂ`, the integrals of `g(b_u)` over `[0, σ(b)]` against the regularized clock measures at the scales
`2^{-n_k}` converge to the integral against the Stieltjes measure of the limit clock. -/
theorem ae_prod_tendsto_setLIntegral_regClockMeasure {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hwp : HarmonicBalls.IsWholePlaneGFF P' hC' hc) (γ ρ r : ℝ) (z y : ℂ) (hball : ball z r ⊆ ball 0 ρ)
    (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : dyadicScale (n 0) < 1 - ρ)
    (hgapLaw : ∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) :
    ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)), ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
      Tendsto (fun k => ∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2) atTop
        (𝓝 (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂limClockKernel γ (fun k => dyadicScale (n k)) (exitNN z r)
            (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1, p.2))) := by
  filter_upwards [ae_prod_regDensity_bdd_and_gap hwp γ ρ r z y hball n hn hn0 hgapLaw] with p hp
  intro g hg hg0
  exact tendsto_setLIntegral_regClockMeasure_of_bdd γ (fun k => dyadicScale (n k)) (exitNN z r) _ p.2 hp.1 hp.2
    (h := fun u => g (p.2 u)) (hg.comp p.2.continuous).continuousOn (fun u _ => hg0 _)

end MatedCRT.KilledOccupation
