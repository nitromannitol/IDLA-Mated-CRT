import MatedCRT.Proofs.Sec2.LQGMeasureProperties.NonAtomic
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.LQGScaling
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeRadialOriginLimit

/-!
# Fact 2.2 I at every point, from the unit disk and the scale invariance of the quantum cone

`ae_measure_singleton_eq_zero_of_volumeGrowth` (`NonAtomic.lean`) gives the non-atomicity of `μ_h` in the unit disk
from the cited Lemma 2.7. The scale invariance of the `γ`-quantum cone moves the unit disk to the disk `B_{R_b}`:
for `b > 0` the field `h^b = h(R_b ·) + Q log R_b - γ⁻¹ log b` is again a quantum cone (`ConeFieldScalingStep`,
eq:quantum-cone-scaling, DMS14 Proposition 4.13(i)) whose LQG measure is `μ^b = b⁻¹ μ_h(R_b ·)`
(`ConeLQGScalingStep`, Fact 2.2 III and IV for dilations only), so a.s. `μ^b` has no atom in `B_1`, i.e. `μ_h` has no
atom in `B_{R_b}`. Along `b_n = e^{γ n}` the radii `R_{b_n} = sup {r > 0 : h_r(0) + Q log r = n}` are unbounded: the
radial function `r ↦ h_r(0) + Q log r` is continuous and tends to `-∞` at `0⁺` (Definition 2.1), so it is bounded
above on `(0, R]` and its level `n` lies outside `(0, R]` for `n` large (`exists_nat_lt_sSup_level`).

Fixed-point non-atomicity (`μ_h({x}) = 0` a.s. for each fixed `x`, Leonardo Bonanno's
`MatedCRTHarmonic.GMCFacts.ae_measure_singleton_eq_zero` for the whole-plane field) does not give this: the measure
`Lebesgue + δ_U` with `U` uniform in the unit disk has no atom at any fixed point a.s., yet always has an atom.
-/

namespace MatedCRT.LQGMeasure

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Step (scale invariance of the quantum cone, whole field).** For `b > 0` the field
`h^b = h(R_b ·) + Q log R_b - γ⁻¹ log b`, with `R_b` the cone scale radius (eq:cone-scale-radius, line 451), is
again a circle average embedding of the `γ`-quantum cone: there are pairings and circle averages `(hC', hcirc')` on
the same probability space which form a quantum cone (`IsQuantumCone`) and whose circle average process is a.s. that
of `h^b` (`rescaledCircle`). This is eq:quantum-cone-scaling (line 458; DMS14 Proposition 4.13(i)) for the law of the
whole field; the External input `QuantumConeScalingInput` is its form for the circle average processes, and gives
this one once the pairings of the cone are known to be a measurable functional of its circle average process. A
version `(hC', hcirc')` is needed since `ω ↦ h_{R_b r}(R_b z)` is a random variable only up to a null set. -/
def ConeFieldScalingStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc → ∀ b : ℝ, 0 < b →
    ∃ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsQuantumCone γ P hC' hcirc' ∧
      ∀ᵐ ω ∂P, hcirc' ω = rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b

/-- **`ConeLQGScalingStep` from Fact 2.2 IV for dilations** and `R_b > 0`: as `coneLQGScalingStep_of_steps`, without
the other parts of Fact 2.2 (in particular without the non-atomicity, which is derived from it below). -/
theorem coneLQGScalingStep_of_dilation (hIV : LQGMeasureDilationCovariancePart) (hpos : ConeScaleRadiusPosStep) :
    ConeLQGScalingStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone b hb
  filter_upwards [hIV γ hγ0 hγ2 Ω P hC hcirc μ hcone, hpos γ hγ0 hγ2 Ω P hC hcirc hcone.1 hcone.2.1 b hb]
    with ω hω hR
  refine ⟨hR, ?_⟩
  set R := coneScaleRadius γ (hcirc ω) b with hRdef
  have h1 := isLQGLimit_add_const (hω R hR) (-(γ⁻¹ * Real.log b))
  have hc : (fun r z => hcirc ω (R * r) ((R : ℂ) * z) + lqgQ γ * Real.log R + -(γ⁻¹ * Real.log b)) =
      rescaledCircle γ (hcirc ω) R b := by
    funext r z
    show _ = hcirc ω (R * r) ((R : ℂ) * z) + lqgQ γ * Real.log R - γ⁻¹ * Real.log b
    ring
  have hm : ENNReal.ofReal (Real.exp (γ * -(γ⁻¹ * Real.log b))) • (μ ω).map (fun x => (R : ℂ)⁻¹ * x) =
      rescaledMeasure (μ ω) R b := by
    rw [mul_neg, mul_inv_cancel_left₀ hγ0.ne', Real.exp_neg, Real.exp_log hb, rescaledMeasure]
  exact (congrArg₂ (IsLQGLimit γ) hc hm).mp h1

/-- **No atom in `B_{R_b}`.** For `b > 0`, a.s. `R_b > 0` and `μ_h` has no atom in the disk `B_{R_b}`: the rescaled
cone `h^b` with its LQG measure `μ^b = b⁻¹ μ_h(R_b ·)` is a cone field, to which the unit disk case applies. -/
theorem ae_measure_singleton_eq_zero_of_coneScale (h27 : VolumeGrowthStmt) (hfield : ConeFieldScalingStep)
    (hlqg : ConeLQGScalingStep) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hμ : IsConeField γ P hC hcirc μ) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b ∧
      ∀ x : ℂ, ‖x‖ < coneScaleRadius γ (hcirc ω) b → μ ω {x} = 0 := by
  obtain ⟨hC', hcirc', hcone', heq⟩ := hfield γ hγ hγ2 Ω P hC hcirc hμ.1 hμ.2.1 b hb
  have hscal := hlqg γ hγ hγ2 Ω P hC hcirc μ hμ b hb
  have hμ' : IsConeField γ P hC' hcirc'
      (fun ω => rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) := by
    unfold IsConeField
    refine ⟨hμ.1, hcone', ?_⟩
    unfold IsLQGMeasure
    filter_upwards [heq, hscal] with ω h1 h2
    rw [h1]
    exact h2.2
  filter_upwards [ae_measure_singleton_eq_zero_of_volumeGrowth h27 hγ hγ2 hμ', hscal] with ω h1 h2
  refine ⟨h2.1, fun x hx => ?_⟩
  set R := coneScaleRadius γ (hcirc ω) b with hRdef
  have hR0 : 0 < R := h2.1
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0.ne'
  have hxR : (R : ℂ)⁻¹ * x ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR0.le,
      inv_mul_lt_iff₀ hR0, mul_one]
    exact hx
  have h3 := h1 _ hxR
  have hpre : (fun y : ℂ => (R : ℂ)⁻¹ * y) ⁻¹' {(R : ℂ)⁻¹ * x} = {x} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h => mul_left_cancel₀ (inv_ne_zero hRc) h, fun h => h ▸ rfl⟩
  have hmeas : Measurable fun y : ℂ => (R : ℂ)⁻¹ * y := measurable_id.const_mul _
  rw [rescaledMeasure, Measure.smul_apply, Measure.map_apply hmeas (measurableSet_singleton _), hpre,
    smul_eq_mul] at h3
  have hb' : ENNReal.ofReal b⁻¹ ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 hb
  exact (mul_eq_zero.1 h3).resolve_left hb'

/-- **Levels of a function tending to `-∞` at `0⁺`.** If `F` is continuous on `(0, ∞)`, tends to `-∞` at `0⁺`, and
each level set `{r > 0 : F r = n}` (`n ∈ ℕ`) has a positive supremum, then these suprema are unbounded. -/
theorem exists_nat_lt_sSup_level {F : ℝ → ℝ} (hF : ContinuousOn F (Ioi 0)) (h0 : Tendsto F (𝓝[>] 0) atBot)
    (hpos : ∀ n : ℕ, 0 < sSup {r : ℝ | 0 < r ∧ F r = n}) (R : ℝ) :
    ∃ n : ℕ, R < sSup {r : ℝ | 0 < r ∧ F r = n} := by
  obtain ⟨u, hu, hFu⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 (h0.eventually (eventually_le_atBot 0)))
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := u) (b := R)).bddAbove_image
    (hF.mono fun r hr => lt_of_lt_of_le hu hr.1)
  obtain ⟨n, hn⟩ := exists_nat_gt (max K 0)
  refine ⟨n, ?_⟩
  have hS : 0 < sSup {r : ℝ | 0 < r ∧ F r = n} := hpos n
  have hne : {r : ℝ | 0 < r ∧ F r = n}.Nonempty := by
    rcases Set.eq_empty_or_nonempty {r : ℝ | 0 < r ∧ F r = n} with h | h
    · rw [h, Real.sSup_empty] at hS
      exact absurd hS (lt_irrefl 0)
    · exact h
  have hbdd : BddAbove {r : ℝ | 0 < r ∧ F r = n} := by
    by_contra h
    rw [Real.sSup_of_not_bddAbove h] at hS
    exact lt_irrefl 0 hS
  obtain ⟨r, hr0, hrn⟩ := hne
  refine lt_of_lt_of_le ?_ (le_csSup hbdd ⟨hr0, hrn⟩)
  by_contra hRr'
  have hRr : r ≤ R := not_lt.1 hRr'
  have hle : F r ≤ max K 0 := by
    rcases lt_or_ge r u with hru | hur
    · have hd : dist r 0 < u := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hr0]
        exact hru
      exact (hFu hd hr0).trans (le_max_right _ _)
    · exact (hK ⟨r, ⟨hur, hRr⟩, rfl⟩).trans (le_max_left _ _)
  rw [hrn] at hle
  exact absurd hn (not_lt.2 hle)

/-- **Fact 2.2 I, non-atomicity at every point**, from the cited Lemma 2.7 (BG20 Lemma A.1), the scale invariance of
the quantum cone (`ConeFieldScalingStep`) and the LQG measure of the rescaled cone (`ConeLQGScalingStep`). -/
theorem lqgMeasureNonAtomicPart_of_scaling (h27 : VolumeGrowthStmt) (hfield : ConeFieldScalingStep)
    (hlqg : ConeLQGScalingStep) : LQGMeasureNonAtomicPart := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hμ
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) (Real.exp (γ * n)) ∧
      ∀ x : ℂ, ‖x‖ < coneScaleRadius γ (hcirc ω) (Real.exp (γ * n)) → μ ω {x} = 0 := fun n =>
    ae_measure_singleton_eq_zero_of_coneScale h27 hfield hlqg hγ hγ2 hμ (Real.exp_pos _)
  filter_upwards [ae_all_iff.2 hn, hμ.2.1.ae_radial_expression_tendsto_origin hγ hγ2,
    hμ.2.1.ae_continuousOn_circle] with ω hω hlim hcont
  have hF : ContinuousOn (fun r : ℝ => hcirc ω r 0 + lqgQ γ * Real.log r) (Ioi 0) := by
    have hpair : ContinuousOn (fun r : ℝ => ((r, (0 : ℂ)) : ℝ × ℂ)) (Ioi 0) := by fun_prop
    have h1 : ContinuousOn (fun r : ℝ => hcirc ω r 0) (Ioi 0) :=
      hcont.comp hpair (fun r hr => ⟨hr, mem_univ _⟩)
    exact h1.add (continuousOn_const.mul (Real.continuousOn_log.mono fun r hr =>
      Set.mem_compl_singleton_iff.2 (Set.mem_Ioi.1 hr).ne'))
  have hlev : ∀ n : ℕ, coneScaleRadius γ (hcirc ω) (Real.exp (γ * n)) =
      sSup {r : ℝ | 0 < r ∧ hcirc ω r 0 + lqgQ γ * Real.log r = n} := by
    intro n
    rw [coneScaleRadius, Real.log_exp, inv_mul_cancel_left₀ hγ.ne']
  refine ⟨fun x => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_lt_sSup_level hF hlim (fun n => lt_of_lt_of_eq (hω n).1 (hlev n)) ‖x‖
  exact (hω n).2 x (lt_of_lt_of_eq hn (hlev n).symm)

/-- **Fact 2.2 I, non-atomicity**, from the cited Lemma 2.7, the cited conformal covariance for the non-dyadic
dilations (`LQGMeasureNonDyadicDilationPart`, DS11 Proposition 2.1, SW16), the scale invariance of the quantum cone
(`ConeFieldScalingStep`) and `R_b > 0` (`ConeScaleRadiusPosStep`). -/
theorem lqgMeasureNonAtomicPart_of_citedInputs (h27 : VolumeGrowthStmt) (hfield : ConeFieldScalingStep)
    (hND : LQGMeasureNonDyadicDilationPart) (hpos : ConeScaleRadiusPosStep) : LQGMeasureNonAtomicPart :=
  lqgMeasureNonAtomicPart_of_scaling h27 hfield
    (coneLQGScalingStep_of_dilation (lqgMeasureDilationCovariancePart_of_nonDyadic hND) hpos)

/-- **Fact 2.2 without a cited non-atomicity**: from the cited Lemma 2.7 and conformal covariance for the non-dyadic
dilations, and the field steps `ConeCircleAverageLocalityStep`, `ConeFieldScalingStep`, `ConeScaleRadiusPosStep`. -/
theorem lqgMeasureProperties_of_volumeGrowth (h27 : VolumeGrowthStmt) (hND : LQGMeasureNonDyadicDilationPart)
    (hCL : ConeCircleAverageLocalityStep) (hfield : ConeFieldScalingStep) (hpos : ConeScaleRadiusPosStep) :
    LQGMeasurePropertiesStmt :=
  lqgMeasureProperties_of_citedInputs (lqgMeasureNonAtomicPart_of_citedInputs h27 hfield hND hpos) hCL hND

end MatedCRT.LQGMeasure
