import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionAffineCircleLaw

/-!
# Fixed-affine measure identification (steps3:649-675)

Internal module; it cites no literature input. It formalizes the written component "Identification for the fixed
affine map" of `notes/wpn-steps3/steps3.tex` (lines 649-675, sha256 `d34cf930...`). For `a ≠ 0`, `R = |a|` and the
normalizing constant `C_a = e^{γ h_∘(R,0)} R^{γ(Q-α)}` (`affineFactor`):

* `lqgApprox_normalized_eq` (steps3 eq:fixed-factor-approx): for every `r > 0`,
  `M^a_r = C_a⁻¹ (x ↦ x/a)_* M_{|a| r}`, with the Jacobian `|a|²` of `z ↦ z/a` (`volume_map_divEquiv`) and the
  normalization `C_a`. Its density identity is the proved export `affineCircleArray_eq_normalized`
  (`InsertionAffineCircleLaw`, the deterministic circle identity at `b = 0`).
* `measure_eq_of_avoid_zero`: two locally finite measures on `ℂ` that agree on the test functions vanishing near `0`
  and give no mass to `{0}` are equal. Agreement away from `0` alone does not fix the atom; the hypotheses
  `ν {0} = 0` are supplied by the no-atom export in the next statement.
* `insertion_affine_dilation_measure_ae` (steps3 eq:affine-dilation-measure): on a full-probability event,
  `C_a μ^a = (x ↦ x/a)_* μ` on `ℂ`. Away from `0` the convergence comes from the checked punctured all-scale consumer
  `punctured_allScales_of_steps_interior`; its explicit hypotheses `SheffieldWangCircleAverageAllScaleInteriorStmt`
  and `LocalDirichletHarmonicDecompositionStep` are kept as they are. The atoms of `μ` and of `μ^a` vanish by the
  unconditional no-atom export, applied to `μ^a` through its normalized field.

The no-atom export needs the normalized field `h^a_∘` (`normalizedCircleProc a (hcirc ω)`) to be the circle process
of a whole-plane GFF. For real `a = R > 0` this is `normalized_isWholePlaneGFF_ofReal` (from
`Field.isWholePlaneGFF_affine`). For complex `a` it is the rotation invariance of the whole-plane GFF
(steps3:520-531, "This also proves the assertion for complex rotations"), taken as the explicit hypothesis `hRot` of
`normalized_isWholePlaneGFF_of_rotation`; it is not proved in this file.

The existence of the dyadic limit `μ^a` (steps3 `μ^a := 𝓜(h^a)`, eq:normalized-measure-law) is an input hypothesis
`hμa`; the law transfer that produces it is outside this file.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

noncomputable section

/-- The normalizing constant `C_a = e^{γ h_∘(R,0)} R^{γ(Q-α)}` of steps3 eq:fixed-factor-approx, with `R = |a|` and
`Q = lqgQ γ`, in exponential form `exp (γ (h_∘(R,0) + (Q-α) log R))`. -/
def affineFactor (γ α : ℝ) (a : ℂ) (h : ℝ → ℂ → ℝ) : ℝ :=
  Real.exp (γ * (h ‖a‖ 0 + (lqgQ γ - α) * Real.log ‖a‖))

theorem affineFactor_pos (γ α : ℝ) (a : ℂ) (h : ℝ → ℂ → ℝ) : 0 < affineFactor γ α a h :=
  Real.exp_pos _

/-- The dilation `z ↦ z / a` (written `z ↦ a⁻¹ z`) of the plane as a measurable equivalence, `a ≠ 0`. -/
def divEquiv (a : ℂ) (ha : a ≠ 0) : ℂ ≃ᵐ ℂ where
  toFun x := a⁻¹ * x
  invFun z := a * z
  left_inv x := by
    dsimp only
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  right_inv z := by
    dsimp only
    rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  measurable_toFun := (continuous_const.mul continuous_id).measurable
  measurable_invFun := (continuous_const.mul continuous_id).measurable

theorem divEquiv_apply (a : ℂ) (ha : a ≠ 0) (x : ℂ) : divEquiv a ha x = a⁻¹ * x := rfl

theorem divEquiv_symm_apply (a : ℂ) (ha : a ≠ 0) (z : ℂ) : (divEquiv a ha).symm z = a * z := rfl

/-- The unit complex number `a / |a|` as an element of the circle group. -/
def unitOf (a : ℂ) (ha : a ≠ 0) : Circle :=
  ⟨a / (‖a‖ : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg a), div_self (norm_pos_iff.2 ha).ne'])⟩

/-- **Jacobian of the dilation** (steps3:653): `volume.map (z ↦ z/a) = |a|² • volume`. -/
theorem volume_map_divEquiv {a : ℂ} (ha : a ≠ 0) :
    Measure.map (divEquiv a ha) volume = ENNReal.ofReal (‖a‖ ^ 2) • volume := by
  have hR : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hR' : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  set u : Circle := unitOf a ha with hu
  have hu' : ((u : Circle) : ℂ) = a / (‖a‖ : ℂ) := rfl
  have hcomp : (⇑(divEquiv a ha))
      = (fun y : ℂ => ‖a‖⁻¹ • y) ∘ (fun x : ℂ => (((u⁻¹ : Circle)) : ℂ) * x) := by
    funext x
    simp only [Function.comp_apply, divEquiv_apply, Circle.coe_inv, hu', Complex.real_smul]
    push_cast
    field_simp
  have hrot : Measure.map (fun x : ℂ => (((u⁻¹ : Circle)) : ℂ) * x) volume = volume := by
    have hfun : ⇑(rotation (u⁻¹)) = fun x : ℂ => (((u⁻¹ : Circle)) : ℂ) * x := by
      funext x
      exact rotation_apply _ _
    rw [← hfun]
    exact (rotation (u⁻¹)).measurePreserving.map_eq
  have hm1 : Measurable (fun x : ℂ => (((u⁻¹ : Circle)) : ℂ) * x) :=
    (continuous_const.mul continuous_id).measurable
  have hm2 : Measurable (fun y : ℂ => ‖a‖⁻¹ • y) := measurable_const_smul _
  rw [hcomp, ← Measure.map_map hm2 hm1, hrot, Measure.map_addHaar_smul (μ := volume) (inv_ne_zero hR.ne'),
    Complex.finrank_real_complex]
  congr 2
  rw [inv_pow, inv_inv, abs_of_nonneg (sq_nonneg _)]

/-- Change of variables for a density under a measurable equivalence:
`e_* (ν.withDensity G) = (e_* ν).withDensity (G ∘ e⁻¹)`. -/
theorem map_withDensity_measurableEquiv (e : ℂ ≃ᵐ ℂ) (G : ℂ → ℝ≥0∞) :
    Measure.map e (volume.withDensity G) = (Measure.map e volume).withDensity (fun z => G (e.symm z)) := by
  ext B hB
  rw [Measure.map_apply e.measurable hB, withDensity_apply _ (e.measurable hB), withDensity_apply _ hB,
    ← lintegral_indicator hB, lintegral_map_equiv, ← lintegral_indicator (e.measurable hB)]
  congr 1
  funext x
  by_cases hx : e x ∈ B
  · rw [Set.indicator_of_mem (show x ∈ e ⁻¹' B from hx), Set.indicator_of_mem hx]
    simp
  · rw [Set.indicator_of_notMem (show x ∉ e ⁻¹' B from hx), Set.indicator_of_notMem hx]

/-- Pulling a finite constant through a density: `c • μ.withDensity G = μ.withDensity (c G)`. -/
theorem smul_withDensity_fun (c : ℝ≥0∞) (hc : c ≠ ∞) (μ : Measure ℂ) (G : ℂ → ℝ≥0∞) :
    c • μ.withDensity G = μ.withDensity (fun z => c * G z) := by
  ext B hB
  rw [Measure.smul_apply, withDensity_apply _ hB, withDensity_apply _ hB, smul_eq_mul,
    lintegral_const_mul' c G hc]

/-- The real identity behind eq:fixed-factor-approx. With `A = H(Rr, az)`, `H^a(r,z) = H_a`, `p = h_∘(R,0)` and
`hA : A + Q log R = H_a + p + (Q-α) log R` (the affine circle export at `b = 0`),
`r^{γ²/2} e^{γ H_a} = C_a⁻¹ R² (Rr)^{γ²/2} e^{γ A}`, using `γ Q = 2 + γ²/2`. -/
theorem affine_density_identity {γ α : ℝ} (hγ : 0 < γ) {R r A Ha p : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hA : A + lqgQ γ * Real.log R = Ha + p + (lqgQ γ - α) * Real.log R) :
    r ^ (γ ^ 2 / 2) * Real.exp (γ * Ha)
      = (Real.exp (γ * (p + (lqgQ γ - α) * Real.log R)))⁻¹ * R ^ 2 * ((R * r) ^ (γ ^ 2 / 2) * Real.exp (γ * A)) := by
  have hγ0 : γ ≠ 0 := hγ.ne'
  have hQ : γ * lqgQ γ = 2 + γ ^ 2 / 2 := by
    unfold lqgQ
    field_simp
  have hR2 : R ^ 2 = Real.exp (2 * Real.log R) := by
    rw [two_mul, Real.exp_add, Real.exp_log hR]
    ring
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos (mul_pos hR hr), Real.log_mul hR.ne' hr.ne', hR2,
    ← Real.exp_neg]
  simp only [← Real.exp_add]
  congr 1
  linear_combination (-γ) * hA + Real.log R * hQ

/-- **Fixed-factor approximation identity** (steps3 eq:fixed-factor-approx). For `a ≠ 0`, `h` a circle-average
process, `r > 0`, the normalized approximation `M^a_r` of the field `H^a = fieldCircleAverage α (normalizedCircleProc a h)`
is `C_a⁻¹ (x ↦ x/a)_*` of the approximation `M_{|a| r}` of `H = fieldCircleAverage α h`. -/
theorem lqgApprox_normalized_eq {γ α : ℝ} (hγ : 0 < γ) {a : ℂ} (ha : a ≠ 0) (h : ℝ → ℂ → ℝ) {r : ℝ}
    (hr : 0 < r) :
    lqgApprox γ (fieldCircleAverage α (normalizedCircleProc a h)) r
      = ENNReal.ofReal ((affineFactor γ α a h)⁻¹) •
          Measure.map (fun x : ℂ => x / a) (lqgApprox γ (fieldCircleAverage α h) (‖a‖ * r)) := by
  have hR : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hfun : (fun x : ℂ => x / a) = ⇑(divEquiv a ha) := by
    funext x
    rw [divEquiv_apply, div_eq_inv_mul]
  rw [hfun]
  unfold lqgApprox
  rw [map_withDensity_measurableEquiv, volume_map_divEquiv ha, withDensity_smul_measure, smul_smul,
    smul_withDensity_fun _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  congr 1
  funext z
  simp only [divEquiv_symm_apply]
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 (affineFactor_pos γ α a h).le),
    ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 (affineFactor_pos γ α a h).le) (sq_nonneg _))]
  congr 1
  have hexp := affineCircleArray_eq_normalized (α := α) (Q := lqgQ γ) (b := 0) ha h hr z
  simp only [affineCircleArray, zero_div, add_zero] at hexp
  unfold affineFactor
  exact affine_density_identity hγ hR hr hexp

/-- **Atomless uniqueness away from the origin.** Two locally finite measures on `ℂ` that give no mass to `{0}` and
agree on every continuous compactly supported test function vanishing near `0` are equal. The proof uses cutoffs
`ψ_ε` (equal to `1` on `|z| ≤ ε/2`, to `0` on `|z| ≥ ε`); `∫ f ψ_ε dν → ν({0}) f(0) = 0`. -/
theorem measure_eq_of_avoid_zero {ν₁ ν₂ : Measure ℂ} [IsFiniteMeasureOnCompacts ν₁]
    [IsFiniteMeasureOnCompacts ν₂] (h₁ : ν₁ {0} = 0) (h₂ : ν₂ {0} = 0)
    (hyp : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ ({0}ᶜ : Set ℂ) →
      ∫ z, g z ∂ν₁ = ∫ z, g z ∂ν₂) :
    ν₁ = ν₂ := by
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  have hf : Continuous (f : ℂ → ℝ) := f.continuous
  have hfc : HasCompactSupport (f : ℂ → ℝ) := f.hasCompactSupport
  set ψ : ℝ → ℂ → ℝ := fun ε z => max 0 (min 1 (2 - 2 * ‖z‖ / ε)) with hψdef
  have hψc : ∀ ε : ℝ, Continuous (ψ ε) := fun ε =>
    continuous_const.max (continuous_const.min (continuous_const.sub
      ((continuous_const.mul continuous_norm).div_const ε)))
  have hψ_nonneg : ∀ ε z, 0 ≤ ψ ε z := fun ε z => le_max_left _ _
  have hψ_le : ∀ ε z, ψ ε z ≤ 1 := fun ε z => max_le zero_le_one (min_le_left _ _)
  have hψ_one : ∀ ε, 0 < ε → ∀ z, ‖z‖ ≤ ε / 2 → ψ ε z = 1 := by
    intro ε hε z hz
    have h1 : 2 * ‖z‖ / ε ≤ 1 := by
      rw [div_le_one₀ hε]
      linarith
    have h2 : (1 : ℝ) ≤ 2 - 2 * ‖z‖ / ε := by linarith
    simp only [hψdef, min_eq_left h2, max_eq_right zero_le_one]
  have hψ_zero : ∀ ε, 0 < ε → ∀ z, ε ≤ ‖z‖ → ψ ε z = 0 := by
    intro ε hε z hz
    have h1 : 2 ≤ 2 * ‖z‖ / ε := by
      rw [le_div_iff₀ hε]
      linarith
    have h2 : min 1 (2 - 2 * ‖z‖ / ε) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
    simp only [hψdef]
    exact max_eq_left h2
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  -- the piece `f (1 - ψ_ε)` is an admissible test function
  have hcut : ∀ ε, 0 < ε → Continuous (fun z => f z * (1 - ψ ε z)) ∧
      HasCompactSupport (fun z => f z * (1 - ψ ε z)) ∧
      tsupport (fun z => f z * (1 - ψ ε z)) ⊆ ({0}ᶜ : Set ℂ) := by
    intro ε hε
    refine ⟨hf.mul (continuous_const.sub (hψc ε)), hfc.mul_right, ?_⟩
    have hsupp : Function.support (fun z => f z * (1 - ψ ε z)) ⊆ {z : ℂ | ε / 2 ≤ ‖z‖} := by
      intro z hz
      show ε / 2 ≤ ‖z‖
      by_contra hlt
      have hlt' : ‖z‖ < ε / 2 := not_le.1 hlt
      exact hz (by simp [hψ_one ε hε z hlt'.le])
    have hclosed : tsupport (fun z => f z * (1 - ψ ε z)) ⊆ {z : ℂ | ε / 2 ≤ ‖z‖} :=
      closure_minimal hsupp (isClosed_le continuous_const continuous_norm)
    intro z hz hz0
    have h1 : ε / 2 ≤ ‖z‖ := hclosed hz
    rw [mem_singleton_iff] at hz0
    rw [hz0, norm_zero] at h1
    linarith
  have hdec : ∀ ε, 0 < ε → ∫ z, f z ∂ν₁ - ∫ z, f z ∂ν₂
      = (∫ z, f z * ψ ε z ∂ν₁) - ∫ z, f z * ψ ε z ∂ν₂ := by
    intro ε hε
    obtain ⟨hgc, hgk, hgs⟩ := hcut ε hε
    have hg : ∫ z, f z * (1 - ψ ε z) ∂ν₁ = ∫ z, f z * (1 - ψ ε z) ∂ν₂ := hyp _ hgc hgk hgs
    have hsplit : ∀ (ν : Measure ℂ) [IsFiniteMeasureOnCompacts ν], ∫ z, f z ∂ν
        = (∫ z, f z * (1 - ψ ε z) ∂ν) + ∫ z, f z * ψ ε z ∂ν := by
      intro ν _
      have hi1 : Integrable (fun z => f z * (1 - ψ ε z)) ν :=
        hgc.integrable_of_hasCompactSupport hgk
      have hi2 : Integrable (fun z => f z * ψ ε z) ν :=
        (hf.mul (hψc ε)).integrable_of_hasCompactSupport hfc.mul_right
      rw [← integral_add hi1 hi2]
      congr 1
      funext z
      ring
    rw [hsplit ν₁, hsplit ν₂, hg]
    ring
  have hlim : ∀ (ν : Measure ℂ) [IsFiniteMeasureOnCompacts ν], ν {0} = 0 →
      Tendsto (fun ε : ℝ => ∫ z, f z * ψ ε z ∂ν) (𝓝[>] 0) (𝓝 0) := by
    intro ν _ h0
    have hzero : ∫ z, ({0} : Set ℂ).indicator (f : ℂ → ℝ) z ∂ν = 0 := by
      rw [integral_indicator (measurableSet_singleton 0), Measure.restrict_eq_zero.2 h0, integral_zero_measure]
    have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ z ∂ν, ‖f z * ψ ε z‖ ≤ ‖f z‖ := hev.mono fun ε _ =>
      ae_of_all _ fun z => by
        show ‖f z * ψ ε z‖ ≤ ‖f z‖
        rw [norm_mul]
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        rw [Real.norm_of_nonneg (hψ_nonneg ε z)]
        exact hψ_le ε z
    have hpt : ∀ᵐ z ∂ν, Tendsto (fun ε : ℝ => f z * ψ ε z) (𝓝[>] 0)
        (𝓝 (({0} : Set ℂ).indicator (f : ℂ → ℝ) z)) := by
      refine ae_of_all _ fun z => ?_
      by_cases hz : z = 0
      · subst hz
        have hconst : ∀ ε, 0 < ε → f 0 * ψ ε 0 = f 0 := fun ε hε => by
          rw [hψ_one ε hε 0 (by simp [le_of_lt (half_pos hε)]), mul_one]
        rw [Set.indicator_of_mem (mem_singleton (0 : ℂ))]
        exact tendsto_const_nhds.congr' (hev.mono fun ε hε => (hconst ε hε).symm)
      · have hlt : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < ‖z‖ := gt_mem_nhds (norm_pos_iff.2 hz)
        have hlt' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ‖z‖ := nhdsWithin_le_nhds hlt
        rw [Set.indicator_of_notMem (notMem_singleton_iff.2 hz)]
        refine tendsto_const_nhds.congr' ((hev.and hlt').mono fun ε hε => ?_)
        simp [hψ_zero ε hε.1 z hε.2.le]
    have key := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
      (F := fun ε z => f z * ψ ε z) (fun z => ‖f z‖)
      (Eventually.of_forall fun ε => (hf.mul (hψc ε)).aestronglyMeasurable) hbound
      (hf.norm.integrable_of_hasCompactSupport hfc.norm) hpt
    rwa [hzero] at key
  have hD : Tendsto (fun ε : ℝ => (∫ z, f z * ψ ε z ∂ν₁) - ∫ z, f z * ψ ε z ∂ν₂) (𝓝[>] 0) (𝓝 0) := by
    have := (hlim ν₁ h₁).sub (hlim ν₂ h₂)
    rwa [sub_zero] at this
  have hconst : Tendsto (fun _ : ℝ => ∫ z, f z ∂ν₁ - ∫ z, f z ∂ν₂) (𝓝[>] 0) (𝓝 0) :=
    hD.congr' (hev.mono fun ε hε => (hdec ε hε).symm)
  exact sub_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds hconst)

/-- **Fixed-affine measure identification** (steps3:649-675, eq:affine-dilation-measure). For a fixed `a ≠ 0`, on a
full-probability event, `C_a μ^a = (x ↦ x/a)_* μ` as measures on `ℂ`, where `μ^a` is the dyadic insertion limit of the
normalized field `H^a` (hypothesis `hμa`) and `μ` that of `H` (hypothesis `hμ`). The convergence away from `0` uses the
checked punctured all-scale consumer; the atoms at `0` are null by the unconditional no-atom export. The normalized
field must be a whole-plane GFF (hypothesis `hNorm`; see `normalized_isWholePlaneGFF_ofReal` and
`normalized_isWholePlaneGFF_of_rotation`). -/
theorem insertion_affine_dilation_measure_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hWP : IsWholePlaneGFF P hC hcirc)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hSWI : SheffieldWangCircleAverageAllScaleInteriorStmt.{0})
    (hDec : LocalDirichletHarmonicDecompositionStep)
    {a : ℂ} (ha : a ≠ 0)
    (hNorm : ∃ hCn : Ω → (ℂ → ℝ) → ℝ,
      IsWholePlaneGFF P hCn (fun ω => normalizedCircleProc a (hcirc ω)))
    {μa : Ω → Measure ℂ}
    (hμa : IsLQGMeasureOfField P γ α (fun ω => normalizedCircleProc a (hcirc ω)) μa) :
    ∀ᵐ ω ∂P, ENNReal.ofReal (affineFactor γ α a (hcirc ω)) • μa ω
      = Measure.map (fun x : ℂ => x / a) (μ ω) := by
  have hP := punctured_allScales_of_steps_interior hγ hγ2 hWP hμ hSWI hDec
  have hNo : ∀ᵐ ω ∂P, μ ω {0} = 0 := insertion_no_atom_zero_ae_unconditional hγ hαQ hWP hμ
  obtain ⟨hCn, hGn⟩ := hNorm
  have hNoa : ∀ᵐ ω ∂P, μa ω {0} = 0 := insertion_no_atom_zero_ae_unconditional hγ hαQ hGn hμa
  have hμaL : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (normalizedCircleProc a (hcirc ω))) (μa ω) := hμa
  have hμL : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  filter_upwards [hP, hNo, hNoa, hμaL, hμL] with ω hPω hNoω hNoaω hμaω hμω
  have hR : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hC0 : affineFactor γ α a (hcirc ω) ≠ 0 := (affineFactor_pos γ α a (hcirc ω)).ne'
  have hdc : Continuous (fun x : ℂ => x / a) := continuous_id.div_const a
  -- Step 1: the identity for test functions vanishing near the atom (dyadic approximations of μ^a)
  have htest : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ ({0}ᶜ : Set ℂ) →
      ∫ z, g z ∂(μa ω) = (affineFactor γ α a (hcirc ω))⁻¹ * ∫ z, g (z / a) ∂(μ ω) := by
    intro g hg hgc hgs
    have hdiv : Continuous (fun x : ℂ => g (x / a)) := hg.comp hdc
    have hdivc : HasCompactSupport (fun x : ℂ => g (x / a)) := by
      refine HasCompactSupport.intro (K := (fun y : ℂ => a * y) '' tsupport g)
        (hgc.isCompact.image (continuous_const.mul continuous_id)) ?_
      intro x hx
      show g (x / a) = 0
      by_contra hne
      exact hx ⟨x / a, subset_tsupport g hne, by field_simp⟩
    have hdivs : tsupport (fun x : ℂ => g (x / a)) ⊆ ({0}ᶜ : Set ℂ) := by
      have key : tsupport (fun x : ℂ => g (x / a)) ⊆ (fun x : ℂ => x / a) ⁻¹' tsupport g :=
        closure_minimal (fun x hx => subset_tsupport g hx)
          ((isClosed_tsupport g).preimage hdc)
      intro x hx
      have h1 : x / a ∈ tsupport g := key hx
      have h2 : x / a ≠ 0 := hgs h1
      show x ≠ 0
      intro h0
      apply h2
      rw [h0, zero_div]
    have h1 := hμaω.tendsto_integral g hg hgc
    have h2 : ∀ k : ℕ, ∫ z, g z ∂(lqgApprox γ (fieldCircleAverage α (normalizedCircleProc a (hcirc ω)))
          (dyadicScale k))
        = (affineFactor γ α a (hcirc ω))⁻¹ *
            ∫ z, g (z / a) ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) (‖a‖ * dyadicScale k)) := by
      intro k
      rw [lqgApprox_normalized_eq hγ ha (hcirc ω) (dyadicScale_pos k), integral_smul_measure,
        integral_map hdc.aemeasurable hg.aestronglyMeasurable,
        ENNReal.toReal_ofReal (inv_nonneg.2 (affineFactor_pos γ α a (hcirc ω)).le), smul_eq_mul]
    have h3 : Tendsto (fun k : ℕ => ∫ z, g (z / a) ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω))
          (‖a‖ * dyadicScale k))) atTop (𝓝 (∫ z, g (z / a) ∂(μ ω))) := by
      have hlim : Tendsto (fun k : ℕ => ‖a‖ * dyadicScale k) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hR (dyadicScale_pos k)⟩
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul ‖a‖
        simpa [dyadicScale] using this
      exact (hPω _ hdiv hdivc hdivs).comp hlim
    exact tendsto_nhds_unique (h1.congr h2) (h3.const_mul (affineFactor γ α a (hcirc ω))⁻¹)
  -- Step 2: finiteness of both sides and vanishing of the atoms at `0`
  have := hμω.isLocallyFiniteMeasure
  have := hμaω.isLocallyFiniteMeasure
  have hmap_fin : IsFiniteMeasureOnCompacts (Measure.map (fun x : ℂ => x / a) (μ ω)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hdc.measurable hK.measurableSet]
    have hpre : (fun x : ℂ => x / a) ⁻¹' K = (fun y : ℂ => a * y) '' K := by
      ext x
      constructor
      · intro hx
        exact ⟨x / a, hx, by field_simp⟩
      · rintro ⟨y, hy, rfl⟩
        rw [mem_preimage, mul_div_cancel_left₀ y ha]
        exact hy
    rw [hpre]
    exact (hK.image (continuous_const.mul continuous_id)).measure_lt_top
  have hsmul_fin : IsFiniteMeasureOnCompacts (ENNReal.ofReal (affineFactor γ α a (hcirc ω)) • μa ω) :=
    ⟨fun K hK => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top⟩
  have hatom1 : (ENNReal.ofReal (affineFactor γ α a (hcirc ω)) • μa ω) {0} = 0 := by
    rw [Measure.smul_apply, hNoaω, smul_zero]
  have hatom2 : Measure.map (fun x : ℂ => x / a) (μ ω) {0} = 0 := by
    rw [Measure.map_apply hdc.measurable (measurableSet_singleton 0)]
    have hpre0 : (fun x : ℂ => x / a) ⁻¹' {0} = {0} := by
      ext x
      simp [ha]
    rw [hpre0, hNoω]
  -- Step 3: agreement on test functions, then the atom-free uniqueness
  refine measure_eq_of_avoid_zero hatom1 hatom2 ?_
  intro g hg hgc hgs
  rw [integral_smul_measure, ENNReal.toReal_ofReal (affineFactor_pos γ α a (hcirc ω)).le, smul_eq_mul,
    integral_map hdc.aemeasurable hg.aestronglyMeasurable, htest g hg hgc hgs,
    ← mul_assoc, mul_inv_cancel₀ hC0, one_mul]

/-- The real case `a = R > 0` of the normalized field: `h^a_∘ = Field.affHcirc R 0` is a whole-plane GFF
(`Field.isWholePlaneGFF_affine`), so the hypothesis `hNorm` of `insertion_affine_dilation_measure_ae` holds. -/
theorem normalized_isWholePlaneGFF_ofReal {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hWP : IsWholePlaneGFF P hC hcirc)
    {R : ℝ} (hR : 0 < R) :
    ∃ hCn : Ω → (ℂ → ℝ) → ℝ, IsWholePlaneGFF P hCn (fun ω => normalizedCircleProc (R : ℂ) (hcirc ω)) := by
  refine ⟨MatedCRT.Field.affHC R 0 hC hcirc, ?_⟩
  have heq : (fun ω => normalizedCircleProc (R : ℂ) (hcirc ω)) = MatedCRT.Field.affHcirc R 0 hcirc := by
    funext ω s v
    simp [normalizedCircleProc, MatedCRT.Field.affHcirc, Complex.norm_real, Real.norm_of_nonneg hR.le]
  rw [heq]
  exact MatedCRT.Field.isWholePlaneGFF_affine hWP hR 0

/-- The complex case `a ≠ 0`, granted the rotation invariance `hRot` of the whole-plane GFF at the unit
`u = a / |a|` (steps3:520-531: the rotated pairings `h ↦ h(u⁻¹ ·)` and rotated circles `h_r(u ·)`). Then the
normalized field `h^a_∘` is a whole-plane GFF. This residual is not proved in this file. -/
theorem normalized_isWholePlaneGFF_of_rotation {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {a : ℂ} (ha : a ≠ 0)
    (hRot : IsWholePlaneGFF P (fun ω φ => hC ω (fun y => φ ((a / (‖a‖ : ℂ))⁻¹ * y)))
      (fun ω r z => hcirc ω r (a / (‖a‖ : ℂ) * z))) :
    ∃ hCn : Ω → (ℂ → ℝ) → ℝ, IsWholePlaneGFF P hCn (fun ω => normalizedCircleProc a (hcirc ω)) := by
  have hR : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hR0 : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  refine ⟨MatedCRT.Field.affHC ‖a‖ 0 (fun ω φ => hC ω (fun y => φ ((a / (‖a‖ : ℂ))⁻¹ * y)))
    (fun ω r z => hcirc ω r (a / (‖a‖ : ℂ) * z)), ?_⟩
  have heq : (fun ω => normalizedCircleProc a (hcirc ω))
      = MatedCRT.Field.affHcirc ‖a‖ 0 (fun ω r z => hcirc ω r (a / (‖a‖ : ℂ) * z)) := by
    funext ω s v
    simp only [normalizedCircleProc, MatedCRT.Field.affHcirc, add_zero, mul_zero]
    rw [show a / (‖a‖ : ℂ) * ((‖a‖ : ℂ) * v) = a * v by field_simp]
  rw [heq]
  exact MatedCRT.Field.isWholePlaneGFF_affine hRot hR 0

/-- The translation `z ↦ z - p` of the plane as a measurable equivalence. -/
def transEquiv (p : ℂ) : ℂ ≃ᵐ ℂ where
  toFun z := z - p
  invFun z := z + p
  left_inv z := by simp
  right_inv z := by simp
  measurable_toFun := (continuous_id.sub continuous_const).measurable
  measurable_invFun := (continuous_id.add continuous_const).measurable

theorem transEquiv_symm_apply (p z : ℂ) : (transEquiv p).symm z = z + p := rfl

theorem transEquiv_map_volume (p : ℂ) : Measure.map (transEquiv p) volume = volume :=
  (measurePreserving_sub_right volume p).map_eq

/-- **Translated approximation identity** (steps3:673-675). For `a ≠ 0`, `b ∈ ℂ` and `r > 0`, the approximating measure of
the affine circle array `affineCircleArray α Q a b h` (steps3 eq:affine-circle-array, with `Q = lqgQ γ`) is
`C_a (z ↦ z - b/a)_* M^a_r`, where `M^a_r = lqgApprox γ (fieldCircleAverage α (normalizedCircleProc a h)) r`. -/
theorem lqgApprox_affineArray_eq {γ α : ℝ} {a b : ℂ} (ha : a ≠ 0) (h : ℝ → ℂ → ℝ) {r : ℝ}
    (hr : 0 < r) :
    lqgApprox γ (affineCircleArray α (lqgQ γ) a b h) r
      = ENNReal.ofReal (affineFactor γ α a h) •
          Measure.map (fun z : ℂ => z - b / a)
            (lqgApprox γ (fieldCircleAverage α (normalizedCircleProc a h)) r) := by
  have hfun : (fun z : ℂ => z - b / a) = ⇑(transEquiv (b / a)) := rfl
  rw [hfun]
  unfold lqgApprox
  rw [map_withDensity_measurableEquiv, transEquiv_map_volume, smul_withDensity_fun _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [transEquiv_symm_apply]
  rw [← ENNReal.ofReal_mul (affineFactor_pos γ α a h).le]
  congr 1
  have hexp := affineCircleArray_eq_normalized (α := α) (Q := lqgQ γ) (b := b) ha h hr z
  rw [hexp]
  unfold affineFactor
  simp only [mul_add, Real.exp_add]
  ring

end

end MatedCRT
