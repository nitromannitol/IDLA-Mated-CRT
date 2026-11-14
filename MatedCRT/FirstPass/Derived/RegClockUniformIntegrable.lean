import MatedCRT.FirstPass.Derived.RegClockIncrementAnnealed
import MatedCRT.FirstPass.Derived.RegClockIncrementExponent
import MatedCRT.FirstPass.Derived.BrownianOccupationPairMoment
import MatedCRT.FirstPass.Derived.GmcFirstMomentSingular
import MatedCRT.FirstPass.Derived.KilledBrownianOccupationF0Holds
import LatticeProb.Prob.UniformIntegrableDominated

/-!
# Uniform integrability of the regularized Liouville clocks

Let `h = h^ℂ - γ log |·|` be built from a whole-plane GFF `h^ℂ`, `0 < γ < 2`, let `b` be a planar Brownian motion
started at `y`, `σ` its exit time of `D = B_r(z) ⊆ B_ρ(0)`, and let `g ≥ 0` be continuous with compact support in
`D \ {0}`. The regularized clock integrals
`T_ε = ∫_{[0,σ]} g(b_u) ε^{γ²/2} e^{γ h_ε(b_u)} du`
are uniformly integrable on the product of the field space and the path space along every subsequence of the
dyadic scales `2^{-n_k}` with `2^{-n_0} < 1 - ρ`.

The proof follows the `L¹` Cauchy argument for the circle-average approximations of Gaussian multiplicative chaos
(Garban-Rhodes-Vargas, Liouville Brownian motion, Thm 2.7(1); Berestycki, Diffusion in planar Liouville quantum
gravity, §2-3):

* every `T_ε` with `ε < 1 - ρ` has finite mean, at most `2^{γ²} M E[σ]` with `M = sup g(x) |x|^{-γ²}`
  (`lintegral_prod_setLIntegral_regClockMeasure_le`, from the first moment of the circle-average density);
* below the distance from `0` to the support of `g`, the dyadic increments satisfy
  `E |T_{2^{-m-1}} - T_{2^{-m}}| ≤ K 2^{-κ m}` for some `κ > 0`
  (`lintegral_prod_abs_regClock_dyadic_increment_le` and `exists_dyadicIncrementRate_le_rpow`, with the mean
  near-diagonal occupation mass of `exists_lintegral_occupation_prod_norm_sub_lt_le`);
* summable `L¹` increments give one integrable function dominating the whole dyadic sequence, hence uniform
  integrability, which passes to every subsequence.

## Main results

* `uniformIntegrable_setLIntegral_regClockMeasure_dyadic`: the uniform integrability above.
* `frozenLBMGreenOccupationRescaled_of_coneGFFLaw_derived`: the Liouville-clock occupation identity
  `FrozenLBMGreenOccupationRescaled` from the cone field law `ConeUnitDiskGFFLaw` alone.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- **First moment of a regularized clock integral.** For a whole-plane GFF, `γ ≥ 0`, `B_r(z) ⊆ B_ρ(0)`,
`0 < ε ≤ 1` with `ε < 1 - ρ`, and a measurable `g` vanishing off `B_r(z) \ {0}` with singular weight
`g(x) |x|^{-γ²} ≤ M`: `E ∫_{[0,σ]} g(b_u) dF_ε(u) ≤ 2^{γ²} M E[σ]`, the expectation taken over the field and the
Brownian path started at `y`, and `σ` the exit time of `B_r(z)`. -/
theorem lintegral_prod_setLIntegral_regClockMeasure_le {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hwp : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 ≤ γ) {ρ r ε : ℝ} {z : ℂ} (y : ℂ)
    (hball : ball z r ⊆ ball 0 ρ) (hε : 0 < ε) (hερ : ε < 1 - ρ) (hε1 : ε ≤ 1)
    {g : ℂ → ℝ} (hg : Measurable g) (hgr : ∀ x, g x ≠ 0 → x ∈ ball z r ∧ x ≠ 0) {M : ℝ}
    (hM : ∀ x, singularWeight γ g x ≤ M) :
    ∫⁻ p : Ω' × ContinuousPath ℂ, ∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
        ∂regClockMeasure γ ε (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1) (exitNN z r) p.2
        ∂(P'.prod (planarBrownianMotion y)) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 2) * M) *
        ∫⁻ b, (exitNN z r b : ℝ≥0∞) ∂planarBrownianMotion y := by
  have hmeas : ∀ (r' : ℝ) (z' : ℂ), 0 < r' → Measurable fun ω => fieldCircleAverage γ (hc ω) r' z' :=
    fun r' z' hr' => (hwp.measurable_circle r' z' hr').sub measurable_const
  have hΨm : Measurable (clockPsi (fun ω' => fieldCircleAverage γ (hc ω'))) :=
    measurable_unitDiskCircle _ hmeas
  have hf := measurable_prod_setLIntegral_regClockMeasure hwp γ ε r z hg
  have key : ∀ b : ContinuousPath ℂ, ∫⁻ ω', ∫⁻ u in Icc 0 (exitNN z r b), ENNReal.ofReal (g (b u))
      ∂regClockMeasure γ ε (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (exitNN z r) b ∂P' ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 2) * M) * (exitNN z r b : ℝ≥0∞) := by
    intro b
    have hbm : Measurable fun u : ℝ≥0 => b u := (map_continuous b).measurable
    set D : Ω' → ℝ≥0 → ℝ≥0∞ := fun ω' u => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      circleAverageRep (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') ε (b u))) *
        ENNReal.ofReal (g (b u)) with hD
    have hDm : Measurable (Function.uncurry D) := by
      have hRep : Measurable fun q : Ω' × ℝ≥0 =>
          circleAverageRep (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) q.1) ε (b q.2) :=
        measurable_comp_pair (F := fun p : (UnitDiskCircleIndex → ℝ) × ℂ => circleAverageRep p.1 ε p.2)
          (measurable_circleAverageRep ε) (hΨm.comp measurable_fst) (hbm.comp measurable_snd)
      exact (measurable_ofReal_exp_mul (ε ^ (γ ^ 2 / 2)) γ hRep).mul
        (ENNReal.measurable_ofReal.comp (hg.comp (hbm.comp measurable_snd)))
    have e1 : ∀ ω', ∫⁻ u in Icc 0 (exitNN z r b), ENNReal.ofReal (g (b u))
        ∂regClockMeasure γ ε (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (exitNN z r) b =
        ∫⁻ u in Icc 0 (exitNN z r b), D ω' u ∂lebNN := fun ω' =>
      setLIntegral_regClockMeasure_eq γ ε _ (exitNN z r) b (ENNReal.measurable_ofReal.comp (hg.comp hbm))
    have hpt : ∀ u ∈ Icc 0 (exitNN z r b), ∫⁻ ω', D ω' u ∂P' ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 2) * M) := by
      intro u _
      by_cases hgu : g (b u) = 0
      · simp [hD, hgu]
      obtain ⟨hzr, hx0⟩ := hgr _ hgu
      have hxρ : ‖b u‖ < ρ := mem_ball_zero_iff.1 (hball hzr)
      have hae : ∀ᵐ ω' ∂P', D ω' u = ENNReal.ofReal (ε ^ (γ ^ 2 / 2) *
          Real.exp (γ * fieldCircleAverage γ (hc ω') ε (b u))) * ENNReal.ofReal (g (b u)) := by
        filter_upwards [hwp.ae_continuousOn_circle] with ω hcont
        have hF := continuousOn_fieldCircleAverage (α₀ := γ) hcont
        have hsub : (UnitDiskCircleIndex : Set (ℝ × ℂ)) ⊆ Ioi 0 ×ˢ univ := fun q hq => ⟨hq.1, mem_univ _⟩
        have hψ : Continuous (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω) :=
          continuousOn_iff_continuous_domRestrict.1 (hF.mono hsub)
        have hrep : circleAverageRep (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω) ε (b u) =
            fieldCircleAverage γ (hc ω) ε (b u) :=
          circleAverageRep_eq_of_lt hψ (fun _ => rfl) hε hερ.le hxρ
        simp only [hD, hrep]
      have h1 := lintegral_density_fieldCircleAverage_le hwp hγ zero_le_one hε hε1 hx0
        (by linarith : ‖b u‖ ≤ 1)
      rw [show (1 : ℝ) + 1 = 2 by norm_num] at h1
      rw [lintegral_congr_ae hae, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      have hA0 : 0 ≤ Real.exp (γ ^ 2 * Real.log 2) * ‖b u‖ ^ (-γ ^ 2) :=
        mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (norm_nonneg _) _)
      calc _ ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 2) * ‖b u‖ ^ (-γ ^ 2)) *
            ENNReal.ofReal (g (b u)) := by gcongr
        _ = ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 2) * singularWeight γ g (b u)) := by
            rw [← ENNReal.ofReal_mul hA0, singularWeight, Real.rpow_def_of_pos (norm_pos_iff.2 hx0),
              show Real.log ‖b u‖ * -γ ^ 2 = -(γ ^ 2 * Real.log ‖b u‖) by ring]
            ring_nf
        _ ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 2) * M) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hM _) (Real.exp_pos _).le)
    rw [lintegral_congr e1, lintegral_lintegral_swap hDm.aemeasurable]
    calc ∫⁻ u in Icc 0 (exitNN z r b), ∫⁻ ω', D ω' u ∂P' ∂lebNN
        ≤ ∫⁻ _ in Icc 0 (exitNN z r b), ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 2) * M) ∂lebNN :=
          setLIntegral_mono' measurableSet_Icc hpt
      _ = _ := by rw [setLIntegral_const, lebNN_Icc]
  refine (lintegral_prod_symm _ hf.aemeasurable).trans_le ?_
  exact (lintegral_mono fun b => key b).trans_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

/-- **Uniform integrability of the regularized clocks along dyadic scales.** For a whole-plane GFF, `0 < γ < 2`,
`B_r(z) ⊆ B_ρ(0)`, a strictly increasing `n` with `2^{-n_0} < 1 - ρ` and a continuous `g ≥ 0` with compact support
in `B_r(z) \ {0, y}`, the regularized clock integrals `T_{2^{-n_k}}` of `g` (killed at the exit time of `B_r(z)`)
are uniformly integrable on the product of the field space and the Brownian path space from `y`. -/
theorem uniformIntegrable_setLIntegral_regClockMeasure_dyadic {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [hP : IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hwp : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ρ r : ℝ}
    {z y : ℂ} (hball : ball z r ⊆ ball 0 ρ) {n : ℕ → ℕ} (hn : StrictMono n)
    (hn0 : dyadicScale (n 0) < 1 - ρ) {g : ℂ → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    (hgK : HasCompactSupport g) (hgs : tsupport g ⊆ ball z r \ ({0, y} : Set ℂ)) :
    UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y)) := by
  let T : ℝ → Ω' × ContinuousPath ℂ → ℝ := fun ε p =>
    (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
      ∂regClockMeasure γ ε (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1) (exitNN z r) p.2).toReal
  have hTm : ∀ ε, Measurable (T ε) := fun ε =>
    (measurable_prod_setLIntegral_regClockMeasure hwp γ ε r z hg.measurable).ennreal_toReal
  -- the support of `g`
  have hsupp : ∀ x, g x ≠ 0 → x ∈ ball z r ∧ x ≠ 0 := fun x hx => by
    have hx' := hgs (subset_tsupport g hx)
    exact ⟨hx'.1, fun h => hx'.2 (by simp [h])⟩
  have h0 : (0 : ℂ) ∉ tsupport g := fun h => (hgs h).2 (by simp)
  obtain ⟨δ₀, hδ₀, hδ₀b⟩ := Metric.isOpen_iff.1 (isClosed_tsupport g).isOpen_compl 0 h0
  have hgδ : ∀ x, g x ≠ 0 → δ₀ ≤ ‖x‖ := fun x hx =>
    not_lt.1 fun hlt => hδ₀b (mem_ball_zero_iff.2 hlt) (subset_tsupport g hx)
  -- the bound on the singular weight
  have hsw : Continuous (singularWeight γ g) := continuous_singularWeight γ hg hδ₀ hgδ
  have hswK : HasCompactSupport (singularWeight γ g) :=
    hgK.mono fun x hx h0x => hx (by simp [singularWeight, h0x])
  obtain ⟨M, hM⟩ := hsw.bounded_above_of_compact_support hswK
  have hMabs : ∀ x, |singularWeight γ g x| ≤ M := fun x => by rw [← Real.norm_eq_abs]; exact hM x
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMabs 0)
  -- the exponents and the near-diagonal occupation bound
  obtain ⟨δ, θ, c, κ, hδ, hδγ, hθ, hθ1, hκ, hrate⟩ := exists_dyadicIncrementRate_le_rpow hγ0 hγ2
  obtain ⟨C, hC0, hC⟩ := exists_lintegral_occupation_prod_norm_sub_lt_le z y r hθ hθ1
  have hS0 : 0 ≤ (∫⁻ b, (exitNN z r b : ℝ≥0∞) ∂planarBrownianMotion y).toReal := ENNReal.toReal_nonneg
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Real.exp (γ ^ 2 * Real.log 2) - 1) * 2 ^ (2 * (1 - θ)) * (M ^ 2 * C) / 2 +
      1 / 2 + 2 * (M * (∫⁻ b, (exitNN z r b : ℝ≥0∞) ∂planarBrownianMotion y).toReal) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ Real.exp (γ ^ 2 * Real.log 2) - 1 :=
      sub_nonneg.2 (Real.one_le_exp (mul_nonneg (sq_nonneg γ) (Real.log_nonneg (by norm_num))))
    rw [hK]
    exact add_nonneg (add_nonneg (div_nonneg (mul_nonneg (mul_nonneg h1 (by positivity))
      (mul_nonneg (sq_nonneg M) hC0)) (by norm_num)) (by norm_num)) (mul_nonneg (by norm_num) (mul_nonneg hM0 hS0))
  -- dyadic scales
  have hanti : ∀ {a b : ℕ}, a ≤ b → dyadicScale b ≤ dyadicScale a := fun h =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have hds1 : ∀ m, dyadicScale m ≤ 1 := fun m => pow_le_one₀ (by norm_num) (by norm_num)
  have hdsucc : ∀ m, dyadicScale (m + 1) = dyadicScale m / 2 := fun m => by
    show (2 : ℝ)⁻¹ ^ (m + 1) = (2 : ℝ)⁻¹ ^ m / 2
    rw [pow_succ]; ring
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hδ₀ (by norm_num : (2 : ℝ)⁻¹ < 1)
  set N := n 0 with hN
  -- finite first moments
  have hTint : ∀ m, N ≤ m → Integrable (T (dyadicScale m)) (P'.prod (planarBrownianMotion y)) := by
    intro m hm
    refine integrable_toReal_of_lintegral_ne_top
      (measurable_prod_setLIntegral_regClockMeasure hwp γ _ r z hg.measurable).aemeasurable ?_
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_exitNN_ne_top y z r))
      (lintegral_prod_setLIntegral_regClockMeasure_le hwp hγ0.le y hball (dyadicScale_pos m)
        ((hanti hm).trans_lt hn0) (hds1 m) hg.measurable hsupp fun x => (le_abs_self _).trans (hMabs x))
  -- the dyadic increments below `δ₀`
  have hinc : ∀ ε, 0 < ε → ε ≤ δ₀ → ε < 1 - ρ → ε ≤ 1 →
      ∫ p, ‖T (ε / 2) p - T ε p‖ ∂(P'.prod (planarBrownianMotion y)) ≤ K * ε ^ κ := by
    intro ε hε hεδ hερ hε1
    have hgε : ∀ x, g x ≠ 0 → ε ≤ ‖x‖ := fun x hx => hεδ.trans (hgδ x hx)
    have h5c := lintegral_prod_abs_regClock_dyadic_increment_le hwp γ y hball hε hερ hg hg0 hgε
      (fun x hx => (hsupp x hx).1) hMabs (le_add_of_nonneg_right hδ.le) (by linarith)
      (Real.rpow_pos_of_pos hε c) hC0 (hC (2 * ε) (by positivity))
    have h5d := hrate (M ^ 2 * C) (M * (∫⁻ b, (exitNN z r b : ℝ≥0∞) ∂planarBrownianMotion y).toReal)
      (mul_nonneg (sq_nonneg M) hC0) (mul_nonneg hM0 hS0) ε hε hε1
    rw [← hK] at h5d
    have hmI : AEStronglyMeasurable (fun p => ‖T (ε / 2) p - T ε p‖) (P'.prod (planarBrownianMotion y)) :=
      ((hTm (ε / 2)).sub (hTm ε)).norm.aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => norm_nonneg _) hmI]
    refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK0 (Real.rpow_nonneg hε.le _)) ?_
    simp only [Real.norm_eq_abs]
    refine h5c.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← mul_assoc]
    exact h5d
  -- the dyadic sequence from `n 0` on
  let F : ℕ → Ω' × ContinuousPath ℂ → ℝ := fun j => T (dyadicScale (N + j))
  have hFint : ∀ j, Integrable (F j) (P'.prod (planarBrownianMotion y)) := fun j =>
    hTint _ (Nat.le_add_right N j)
  have hq0 : 0 ≤ (2 : ℝ)⁻¹ ^ κ := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2 : ℝ)⁻¹ ^ κ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hκ
  have hpow : ∀ m : ℕ, dyadicScale m ^ κ = ((2 : ℝ)⁻¹ ^ κ) ^ m := fun m => by
    show ((2 : ℝ)⁻¹ ^ m) ^ κ = _
    rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num), mul_comm]
  have hincF : ∀ j, m₀ ≤ j → ∫ p, ‖F (j + 1) p - F j p‖ ∂(P'.prod (planarBrownianMotion y)) ≤
      K * ((2 : ℝ)⁻¹ ^ κ) ^ (N + j) := by
    intro j hj
    show ∫ p, ‖T (dyadicScale (N + j + 1)) p - T (dyadicScale (N + j)) p‖ ∂(P'.prod (planarBrownianMotion y)) ≤ _
    rw [hdsucc, ← hpow]
    exact hinc _ (dyadicScale_pos _) ((hanti (by omega : m₀ ≤ N + j)).trans hm₀.le)
      ((hanti (Nat.le_add_right N j)).trans_lt hn0) (hds1 _)
  have hgeo : Summable fun j : ℕ => K * ((2 : ℝ)⁻¹ ^ κ) ^ (N + (j + m₀)) := by
    refine ((summable_nat_add_iff (N + m₀)).2 ((summable_geometric_of_lt_one hq0 hq1).mul_left K)).congr
      fun j => ?_
    rw [show j + (N + m₀) = N + (j + m₀) by omega]
  have hs : Summable fun j => ∫ p, ‖F (j + 1) p - F j p‖ ∂(P'.prod (planarBrownianMotion y)) := by
    refine (summable_nat_add_iff m₀).1 ?_
    exact Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _)
      (fun j => hincF (j + m₀) (Nat.le_add_left m₀ j)) hgeo
  have hUI := LatticeProb.Prob.UniformIntegrable.comp_index
    (LatticeProb.Prob.uniformIntegrable_of_summable_integral_norm_sub hFint hs) (fun k => n k - N)
  have hfun : (fun k => F (n k - N)) = fun k => T (dyadicScale (n k)) := by
    funext k
    have hk : N ≤ n k := hn.monotone (Nat.zero_le k)
    show T (dyadicScale (N + (n k - N))) = T (dyadicScale (n k))
    rw [Nat.add_sub_cancel' hk]
  rw [hfun] at hUI
  exact hUI

/-- **The Liouville-clock occupation identity from the cone field law.**
`frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation_F0_derived` with its binder `hU` (uniform
integrability of the regularized clock integrals) discharged by
`uniformIntegrable_setLIntegral_regClockMeasure_dyadic`: `FrozenLBMGreenOccupationRescaled` follows from
`ConeUnitDiskGFFLaw` alone. -/
theorem frozenLBMGreenOccupationRescaled_of_coneGFFLaw_derived (𝒮 : SpaceFillingSLEModel)
    (hlaw : ConeUnitDiskGFFLaw) : FrozenLBMGreenOccupationRescaled 𝒮 :=
  frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation_F0_derived 𝒮 hlaw
    fun _ hγ hγ2 _ _ _ _ _ _ _ hball _ _ _ _ _ _ hP hwp _ hn hn0 _ _ hg hg0 hgK hgs =>
      uniformIntegrable_setLIntegral_regClockMeasure_dyadic (hP := hP) hwp hγ hγ2 hball hn hn0 hg hg0 hgK hgs

end MatedCRT.KilledOccupation
