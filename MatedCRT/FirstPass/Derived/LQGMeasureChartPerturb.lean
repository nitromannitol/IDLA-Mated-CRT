import MatedCRT.FirstPass.Derived.LQGMeasureChartSmooth
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea3
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.PartitionOfUnity

/-!
# Continuous perturbations, locality and patching of the smooth and circle approximations

Deterministic facts on the approximations of the LQG measure on an open set `V ⊆ ℂ`, used in the localization step of
the coordinate change of the LQG measure for all inverse charts (`LQGMeasureChartStmt`): adding a continuous function
`b` to the field multiplies a limiting measure by `e^{γ b}`, the approximations are local, and vague limits on the
sets of an open cover patch together by a finite partition of unity. The approximations are those of
Sheffield–Wang, *Field-measure correspondence in Liouville quantum gravity almost surely commutes with all conformal
maps simultaneously* (arXiv:1605.06171v2), §3.2 after (3.4) (`smoothApprox`), and the circle-average approximations
`ε^{γ²/2} e^{γ h_ε(z)} dz` of Duplantier–Sheffield, *Liouville quantum gravity and KPZ* (arXiv:0808.1560v2),
Proposition 1.1 (p. 5) (`HarmonicBalls.lqgApprox`), along the scales `ε = 2^{-k}`; vague convergence in `V` is
`QuantumZipper.IsVagueLimitOn V`.

* `isVagueLimitOn_withDensity_exp`: if `μ_k → ν` vaguely in `V`, `β` is continuous on `V` and the measurable functions
  `β_k` converge to `β` uniformly on the compact subsets of `V`, then `e^{γ β_k} μ_k → e^{γ β} ν` vaguely in `V`.
  The densities converge uniformly on the support of each test function and the masses `∫ |g| dμ_k` stay bounded;
  no finiteness of the `μ_k` is needed (a test function is integrable for `μ_k` exactly when it is for `e^{γ β_k} μ_k`).
* `isVagueLimitOn_smoothApprox_add` (continuous addition, smooth approximations): if `G' u = G u + ∫ b u` for the
  translates `u = f_ε(z - ·)` with `B̄_ε(z) ⊆ V`, then the smooth approximations of `G'` converge to `e^{γ b} ν`
  whenever those of `G` converge to `ν` (`(b ∗ f_ε)(z) → b(z)` uniformly on compact subsets of `V`).
* `isVagueLimitOn_lqgApprox_add` (continuous addition, circle approximations): the same for circle averages
  `h'_ε(z) = h_ε(z) + b_ε(z)` on the circles inside `V`.
* `smoothApprox_restrict_eq_of_subset`, `isVagueLimitOn_smoothApprox_of_subset` (locality): for open `W ⊆ V` and
  functionals agreeing on the translates supported in `W`, the smooth approximations on `W` and on `V` agree on the
  centres `z` with `B̄_ε(z) ⊆ W`; hence a vague limit `ν` in `V` gives the vague limit `ν|_W` in `W`.
* `isVagueLimitOn_of_forall_mem_isVagueLimitOn_restrict` (patching): vague limits `ν|_W` in the sets `W` of an open
  cover of `V` give the vague limit `ν` in `V`, by a finite partition of unity on the support of each test function.
  The approximating measures are assumed eventually finite on each compact subset of `V` (true for the smooth
  approximations of a distribution, `smoothApprox_lt_top`); without it the statement fails, since a test function
  that is not integrable has integral `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT

namespace LQGMeasureChart

/-! ### Measure-theoretic preliminaries -/

/-- `2^{-k} → 0`. -/
theorem tendsto_dyadicScale_nhds_zero : Tendsto HarmonicBalls.dyadicScale atTop (𝓝 0) :=
  show Tendsto (fun k : ℕ => (2 : ℝ)⁻¹ ^ k) atTop (𝓝 0) from
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Multiplying an arbitrary (possibly non-measurable) density by a measurable density with values in `(0, ∞)`
amounts to taking the density with respect to the first density measure. -/
theorem withDensity_mul_of_measurable_right {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {F D : α → ℝ≥0∞} (hD : Measurable D) (hD0 : ∀ x, D x ≠ 0) (hDtop : ∀ x, D x ≠ ∞) :
    μ.withDensity (F * D) = (μ.withDensity F).withDensity D := by
  obtain ⟨F₁, hF₁m, hF₁le, hF₁eq⟩ := exists_measurable_le_withDensity_eq (μ := μ) F
  obtain ⟨H, hHm, hHle, hHeq⟩ := exists_measurable_le_withDensity_eq (μ := μ) (F * D)
  have mono : ∀ {ν₁ ν₂ : Measure α}, ν₁ ≤ ν₂ → ν₁.withDensity D ≤ ν₂.withDensity D := by
    intro ν₁ ν₂ h
    refine Measure.le_iff.2 fun s hs => ?_
    rw [withDensity_apply _ hs, withDensity_apply _ hs]
    exact lintegral_mono' (Measure.restrict_mono subset_rfl h) le_rfl
  refine le_antisymm ?_ ?_
  · have hH : H = H * D⁻¹ * D := by
      funext x
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [mul_assoc, ENNReal.inv_mul_cancel (hD0 x) (hDtop x), mul_one]
    rw [← hHeq, hH, withDensity_mul μ (hHm.mul hD.inv) hD]
    refine mono (withDensity_mono (ae_of_all _ fun x => ?_))
    have h1 := hHle x
    simp only [Pi.mul_apply, Pi.inv_apply] at h1 ⊢
    calc H x * (D x)⁻¹ ≤ F x * D x * (D x)⁻¹ := mul_le_mul_of_nonneg_right h1 zero_le
      _ = F x := by rw [mul_assoc, ENNReal.mul_inv_cancel (hD0 x) (hDtop x), mul_one]
  · rw [← hF₁eq, ← withDensity_mul μ hF₁m hD]
    exact withDensity_mono (ae_of_all _ fun x => mul_le_mul_of_nonneg_right (hF₁le x) zero_le)

/-- A continuous function with compact support, vanishing off a set of finite measure, is integrable. -/
theorem integrable_of_support_subset_of_lt_top {m : Measure ℂ} {φ : ℂ → ℝ} {K : Set ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hK : Function.support φ ⊆ K) (hm : m K < ⊤) : Integrable φ m := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  exact (integrableOn_iff_integrable_of_support_subset hK).1
    (Measure.integrableOn_of_bounded hm.ne hφ.aestronglyMeasurable (ae_of_all _ hC))

/-- The indicator of a function continuous on an open set is measurable. -/
theorem measurable_indicator_of_continuousOn {V : Set ℂ} (hV : IsOpen V) {b : ℂ → ℝ} (hb : ContinuousOn b V) :
    Measurable (V.indicator b) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hb.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hV.measurableSet

/-- If two positive bounded functions are `δ`-close on the support of `g`, the integrals of `h₁ g` and `h₂ g` are
`δ ∫ |g|`-close, for every measure (a function that is not integrable has integral `0`; integrability of `g`, `h₁ g`
and `h₂ g` are equivalent). -/
theorem abs_integral_mul_sub_integral_mul_le {μ : Measure ℂ} {g h₁ h₂ : ℂ → ℝ} {c C δ : ℝ} (hc : 0 < c)
    (hδ : 0 ≤ δ) (hg : Continuous g) (hm₁ : AEStronglyMeasurable (fun z => h₁ z * g z) μ)
    (hm₂ : AEStronglyMeasurable (fun z => h₂ z * g z) μ) (hb₁ : ∀ z ∈ tsupport g, h₁ z ∈ Icc c C)
    (hb₂ : ∀ z ∈ tsupport g, h₂ z ∈ Icc c C) (hd : ∀ z ∈ tsupport g, |h₁ z - h₂ z| ≤ δ) :
    |∫ z, h₁ z * g z ∂μ - ∫ z, h₂ z * g z ∂μ| ≤ δ * ∫ z, |g z| ∂μ := by
  have up : ∀ h : ℂ → ℝ, AEStronglyMeasurable (fun z => h z * g z) μ → (∀ z ∈ tsupport g, h z ∈ Icc c C) →
      Integrable g μ → Integrable (fun z => h z * g z) μ := by
    intro h hm hb hgi
    refine (hgi.abs.const_mul C).mono' hm (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ tsupport g
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hc.trans_le (hb z hz).1)]
      exact mul_le_mul_of_nonneg_right (hb z hz).2 (abs_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have down : ∀ h : ℂ → ℝ, (∀ z ∈ tsupport g, h z ∈ Icc c C) → Integrable (fun z => h z * g z) μ →
      Integrable g μ := by
    intro h hb hi
    refine (hi.norm.const_mul c⁻¹).mono' hg.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ tsupport g
    · have hpos : 0 < h z := hc.trans_le (hb z hz).1
      rw [norm_mul, Real.norm_of_nonneg hpos.le]
      calc ‖g z‖ = c⁻¹ * (c * ‖g z‖) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
        _ ≤ c⁻¹ * (h z * ‖g z‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hb z hz).1 (norm_nonneg _))
            (inv_nonneg.2 hc.le)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  by_cases hgi : Integrable g μ
  · rw [← integral_sub (up h₁ hm₁ hb₁ hgi) (up h₂ hm₂ hb₂ hgi), ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hgi.abs.const_mul δ) (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ tsupport g
    · rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hd z hz) (abs_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  · rw [integral_undef fun hi => hgi (down h₁ hb₁ hi), integral_undef fun hi => hgi (down h₂ hb₂ hi), sub_zero,
      abs_zero]
    exact mul_nonneg hδ (integral_nonneg fun z => abs_nonneg _)

/-! ### Vague limits in an open set: restriction, congruence, patching -/

/-- Vague limits in `U` only see the approximating measures on compact subsets of `U`, for large `k`. -/
theorem isVagueLimitOn_of_eventually_restrict_eq {U : Set ℂ} {μs μs' : ℕ → Measure ℂ} {ν : Measure ℂ}
    (h : QuantumZipper.IsVagueLimitOn U μs ν)
    (hμ : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, (μs' k).restrict K = (μs k).restrict K) :
    QuantumZipper.IsVagueLimitOn U μs' ν := by
  obtain ⟨h0, hfin, ht⟩ := h
  refine ⟨h0, hfin, fun g hg hgc hgU => (ht g hg hgc hgU).congr' ?_⟩
  have e : ∀ m : Measure ℂ, ∫ z in tsupport g, g z ∂m = ∫ z, g z ∂m := fun m =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => image_eq_zero_of_notMem_tsupport hz
  filter_upwards [hμ _ hgc hgU] with k hk
  rw [← e (μs k), ← e (μs' k), hk]

/-- A vague limit `ν` in `V` restricts to the vague limit `ν|_W` in an open subset `W ⊆ V`. -/
theorem isVagueLimitOn_restrict_of_subset {V W : Set ℂ} (hW : IsOpen W) (hWV : W ⊆ V) {μs : ℕ → Measure ℂ}
    {ν : Measure ℂ} (h : QuantumZipper.IsVagueLimitOn V μs ν) :
    QuantumZipper.IsVagueLimitOn W μs (ν.restrict W) := by
  obtain ⟨-, hfin, ht⟩ := h
  refine ⟨?_, fun K hK hKW => (Measure.restrict_apply_le W K).trans_lt (hfin K hK (hKW.trans hWV)),
    fun g hg hgc hgW => ?_⟩
  · rw [Measure.restrict_apply' hW.measurableSet, compl_inter_self, measure_empty]
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := W) (μ := ν) fun z hz =>
      image_eq_zero_of_notMem_tsupport fun hz' => hz (hgW hz')]
    exact ht g hg hgc (hgW.trans hWV)

/-- **Multiplying vague limits by uniformly converging exponential densities.** If `μ_k → ν` vaguely in the open set
`V`, `β` is continuous on `V`, and the measurable functions `β_k` converge to `β` uniformly on every compact subset of
`V`, then `e^{γ β_k} μ_k → e^{γ β} ν` vaguely in `V`. -/
theorem isVagueLimitOn_withDensity_exp {V : Set ℂ} (hV : IsOpen V) {μs : ℕ → Measure ℂ} {ν : Measure ℂ}
    (h : QuantumZipper.IsVagueLimitOn V μs ν) (γ : ℝ) {β : ℂ → ℝ} (hβ : ContinuousOn β V) {βs : ℕ → ℂ → ℝ}
    (hβs : ∀ k, Measurable (βs k)) (hlim : ∀ K, IsCompact K → K ⊆ V → TendstoUniformlyOn βs β atTop K) :
    QuantumZipper.IsVagueLimitOn V
      (fun k => (μs k).withDensity fun z => ENNReal.ofReal (Real.exp (γ * βs k z)))
      (ν.withDensity fun z => ENNReal.ofReal (Real.exp (γ * β z))) := by
  obtain ⟨h0, hfin, ht⟩ := h
  have hνV : ν.restrict V = ν := Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h0)
  have hγβ : ContinuousOn (fun z => γ * β z) V := continuousOn_const.mul hβ
  have hmeas : AEMeasurable (fun z => ENNReal.ofReal (Real.exp (γ * β z))) ν := by
    rw [← hνV]
    exact (hγβ.rexp.aemeasurable hV.measurableSet).ennreal_ofReal
  refine ⟨withDensity_absolutelyContinuous ν _ h0, fun K hK hKV => ?_, fun g hg hgc hgV => ?_⟩
  · obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hγβ.mono hKV)
    rw [withDensity_apply _ hK.measurableSet]
    calc ∫⁻ z in K, ENNReal.ofReal (Real.exp (γ * β z)) ∂ν
        ≤ ∫⁻ _ in K, ENNReal.ofReal (Real.exp C) ∂ν :=
          setLIntegral_mono measurable_const fun z hz =>
            ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ((Real.le_norm_self _).trans (hC z hz)))
      _ = ENNReal.ofReal (Real.exp C) * ν K := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin K hK hKV)
  -- bounds on the support `tsupport g`
  have hK : IsCompact (tsupport g) := hgc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hβ.mono hgV)
  have hunif := hlim _ hK hgV
  have hβK : ∀ z ∈ tsupport g, β z ∈ Icc (-(C + 1)) (C + 1) := fun z hz => by
    have h2 := hC z hz
    rw [Real.norm_eq_abs] at h2
    obtain ⟨b1, b2⟩ := abs_le.1 h2
    constructor <;> linarith
  have hev : ∀ᶠ k in atTop, ∀ z ∈ tsupport g, βs k z ∈ Icc (-(C + 1)) (C + 1) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif 1 one_pos] with k hk z hz
    have h1 := hk z hz
    have h2 := hC z hz
    rw [Real.dist_eq] at h1
    rw [Real.norm_eq_abs] at h2
    obtain ⟨a1, a2⟩ := abs_lt.1 h1
    obtain ⟨b1, b2⟩ := abs_le.1 h2
    constructor <;> linarith
  have huc : UniformContinuousOn (fun x => Real.exp (γ * x)) (Icc (-(C + 1)) (C + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (by fun_prop)
  have hexp : TendstoUniformlyOn (fun k z => Real.exp (γ * βs k z)) (fun z => Real.exp (γ * β z)) atTop
      (tsupport g) :=
    huc.comp_tendstoUniformlyOn_eventually hev hβK hunif
  have hbd : ∀ x ∈ Icc (-(C + 1)) (C + 1),
      Real.exp (γ * x) ∈ Icc (Real.exp (-(|γ| * (C + 1)))) (Real.exp (|γ| * (C + 1))) := by
    intro x hx
    have h1 : |x| ≤ C + 1 := abs_le.2 hx
    have h2 : |γ * x| ≤ |γ| * (C + 1) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg γ)
    obtain ⟨h3, h4⟩ := abs_le.1 h2
    exact ⟨Real.exp_le_exp.2 h3, Real.exp_le_exp.2 h4⟩
  -- the limit test function `e^{γ β} g`
  have hg₁V : tsupport (fun z => Real.exp (γ * β z) * g z) ⊆ V := tsupport_mul_subset_right.trans hgV
  have hg₁c : Continuous fun z => Real.exp (γ * β z) * g z :=
    (hγβ.rexp.mul hg.continuousOn).continuous_of_tsupport_subset hV hg₁V
  have hB := ht _ hg₁c hgc.mul_left hg₁V
  have habsV : tsupport (fun z => |g z|) ⊆ V := by
    have hs : Function.support (fun z => |g z|) ⊆ Function.support g := fun z hz => by simpa using hz
    exact (closure_mono hs).trans hgV
  have habs := ht (fun z => |g z|) hg.abs hgc.abs habsV
  have hdiff : Tendsto (fun k => ∫ z, Real.exp (γ * βs k z) * g z ∂μs k -
      ∫ z, Real.exp (γ * β z) * g z ∂μs k) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    have hL0 : 0 ≤ ∫ z, |g z| ∂ν := integral_nonneg fun z => abs_nonneg (g z)
    set L := ∫ z, |g z| ∂ν + 1 with hLdef
    have hL : 0 < L := by linarith
    have h1 := Metric.tendstoUniformlyOn_iff.1 hexp (η / (2 * L)) (by positivity)
    have h3 := habs.eventually (gt_mem_nhds (show ∫ z, |g z| ∂ν < L by linarith))
    filter_upwards [h1, hev, h3] with k hk1 hk2 hk3
    rw [Real.dist_eq, sub_zero]
    have key := abs_integral_mul_sub_integral_mul_le (μ := μs k) (Real.exp_pos (-(|γ| * (C + 1))))
      (div_nonneg hη.le (by positivity) : 0 ≤ η / (2 * L)) hg
      ((((hβs k).const_mul γ).exp.mul hg.measurable).aestronglyMeasurable) hg₁c.aestronglyMeasurable
      (fun z hz => hbd _ (hk2 z hz)) (fun z hz => hbd _ (hβK z hz)) (fun z hz => by
        have := hk1 z hz
        rw [Real.dist_eq, abs_sub_comm] at this
        exact this.le)
    have hhalf : η / (2 * L) * L = η / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hL.ne']
    calc _ ≤ η / (2 * L) * ∫ z, |g z| ∂μs k := key
      _ ≤ η / (2 * L) * L := mul_le_mul_of_nonneg_left hk3.le (by positivity)
      _ < η := by rw [hhalf]; linarith
  have hA : ∀ k, ∫ z, g z ∂((μs k).withDensity fun z => ENNReal.ofReal (Real.exp (γ * βs k z))) =
      ∫ z, Real.exp (γ * βs k z) * g z ∂μs k := by
    intro k
    rw [integral_withDensity_eq_integral_toReal_smul (((hβs k).const_mul γ).exp.ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have hlimit : ∫ z, g z ∂(ν.withDensity fun z => ENNReal.ofReal (Real.exp (γ * β z))) =
      ∫ z, Real.exp (γ * β z) * g z ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  simp only [hA, hlimit]
  have hsum := hB.add hdiff
  rw [add_zero] at hsum
  exact hsum.congr fun k => by ring

/-- **Patching vague limits.** If every point of `V` has an open neighbourhood `W ⊆ V` in which the measures `μ_k`
converge vaguely to `ν|_W`, `ν` is concentrated on `V` and finite on its compact subsets, and the `μ_k` are eventually
finite on each compact subset of `V`, then `μ_k → ν` vaguely in `V` (a finite partition of unity on the support of
each test function). -/
theorem isVagueLimitOn_of_forall_mem_isVagueLimitOn_restrict {V : Set ℂ} {μs : ℕ → Measure ℂ} {ν : Measure ℂ}
    (hloc : ∀ x ∈ V, ∃ W : Set ℂ, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      QuantumZipper.IsVagueLimitOn W μs (ν.restrict W))
    (h0 : ν Vᶜ = 0) (hfin : ∀ K, IsCompact K → K ⊆ V → ν K < ⊤)
    (hμfin : ∀ K, IsCompact K → K ⊆ V → ∀ᶠ k in atTop, μs k K < ⊤) :
    QuantumZipper.IsVagueLimitOn V μs ν := by
  refine ⟨h0, hfin, fun g hg hgc hgV => ?_⟩
  choose! W hWo hxW hWV hWlim using hloc
  have hK : IsCompact (tsupport g) := hgc
  obtain ⟨t, htK, hKt⟩ :=
    hK.elim_nhds_subcover W fun x hx => (hWo x (hgV hx)).mem_nhds (hxW x (hgV hx))
  have hxV : ∀ i : Fin t.card, ((t.equivFin.symm i : ℂ)) ∈ V := fun i => hgV (htK _ (t.equivFin.symm i).2)
  obtain ⟨ρ, hρW, hρ1, -, -⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (s := fun i : Fin t.card => W (t.equivFin.symm i)) (fun i => hWo _ (hxV i)) hK (fun x hx => by
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hKt hx)
      refine mem_iUnion.2 ⟨t.equivFin ⟨y, hy⟩, ?_⟩
      simpa using hxy)
  have hdecomp : ∀ z, g z = ∑ i, ρ i z * g z := by
    intro z
    by_cases hz : z ∈ tsupport g
    · have h1 : ∑ i, ρ i z = 1 := by simpa using hρ1 hz
      rw [← Finset.sum_mul, h1, one_mul]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hgi : ∀ i, Continuous fun z => ρ i z * g z := fun i => (ρ i).continuous.mul hg
  have hgic : ∀ i, HasCompactSupport fun z => ρ i z * g z := fun i => hgc.mul_left
  have hgiW : ∀ i, tsupport (fun z => ρ i z * g z) ⊆ W (t.equivFin.symm i) := fun i =>
    tsupport_mul_subset_left.trans (hρW i)
  have hsupp : ∀ i, Function.support (fun z => ρ i z * g z) ⊆ tsupport g := fun i =>
    (Function.support_mul_subset_right _ _).trans (subset_tsupport g)
  have hlim : ∀ i, Tendsto (fun k => ∫ z, ρ i z * g z ∂μs k) atTop (𝓝 (∫ z, ρ i z * g z ∂ν)) := by
    intro i
    have h := (hWlim _ (hxV i)).2.2 _ (hgi i) (hgic i) (hgiW i)
    rwa [setIntegral_eq_integral_of_forall_compl_eq_zero (s := W (t.equivFin.symm i)) (μ := ν)
      fun z hz => image_eq_zero_of_notMem_tsupport fun hz' => hz (hgiW i hz')] at h
  have hsum : ∀ m : Measure ℂ, m (tsupport g) < ⊤ → ∫ z, g z ∂m = ∑ i, ∫ z, ρ i z * g z ∂m := by
    intro m hm
    calc ∫ z, g z ∂m = ∫ z, ∑ i, ρ i z * g z ∂m := integral_congr_ae (ae_of_all _ hdecomp)
      _ = ∑ i, ∫ z, ρ i z * g z ∂m := integral_finsetSum _ fun i _ =>
        integrable_of_support_subset_of_lt_top (hgi i) (hgic i) (hsupp i) hm
  rw [hsum ν (hfin _ hgc hgV)]
  refine (tendsto_finsetSum _ fun i _ => hlim i).congr' ?_
  filter_upwards [hμfin _ hgc hgV] with k hk
  exact (hsum _ hk).symm

/-! ### The translates `f_ε(z - ·)` of a bump function -/

theorem continuous_mollScale {f : ℂ → ℝ} (hf : IsMollifier f) (ε : ℝ) : Continuous (mollScale f ε) :=
  show Continuous fun v : ℂ => (ε ^ 2)⁻¹ * f (v / (ε : ℂ)) from
    continuous_const.mul (hf.contDiff.continuous.comp (continuous_id.div_const _))

theorem mollScale_nonneg {f : ℂ → ℝ} (hf : IsMollifier f) (ε : ℝ) (v : ℂ) : 0 ≤ mollScale f ε v :=
  mul_nonneg (inv_nonneg.2 (sq_nonneg ε)) (hf.nonneg _)

/-- `f_ε(z - ·)` is supported in `B_ε(z)`. -/
theorem tsupport_mollScale_sub_subset {f : ℂ → ℝ} (hf : IsMollifier f) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    tsupport (fun w => mollScale f ε (z - w)) ⊆ ball z ε := by
  have hS : IsClosed {w : ℂ | (z - w) / (ε : ℂ) ∈ tsupport f} :=
    (isClosed_tsupport f).preimage (by fun_prop)
  refine (closure_minimal (fun w hw => ?_) hS).trans fun w hw => ?_
  · show (z - w) / (ε : ℂ) ∈ tsupport f
    refine subset_tsupport f (Function.mem_support.2 fun h0 => Function.mem_support.1 hw ?_)
    simp [mollScale, h0]
  · have hw' : (z - w) / (ε : ℂ) ∈ tsupport f := hw
    have h1 : (z - w) / (ε : ℂ) ∈ ball (0 : ℂ) 1 := hf.tsupport_subset hw'
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hε.le, div_lt_one hε] at h1
    rw [mem_ball, dist_comm, dist_eq_norm]
    exact h1

theorem hasCompactSupport_mollScale_sub {f : ℂ → ℝ} (hf : IsMollifier f) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    HasCompactSupport fun w => mollScale f ε (z - w) :=
  IsCompact.of_isClosed_subset (isCompact_closedBall z ε) (isClosed_tsupport _)
    ((tsupport_mollScale_sub_subset hf hε z).trans ball_subset_closedBall)

/-- `∫ f_ε(z - w) dw = 1`. -/
theorem integral_mollScale_sub {f : ℂ → ℝ} (hf : IsMollifier f) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ∫ w, mollScale f ε (z - w) = 1 := by
  rw [integral_sub_left_eq_self (mollScale f ε) volume z]
  have hsmul : ∀ v : ℂ, v / (ε : ℂ) = ε⁻¹ • v := fun v => by
    rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
  simp only [mollScale, hsmul]
  rw [integral_const_mul, Measure.integral_comp_inv_smul volume f ε, Complex.finrank_real_complex,
    hf.integral_eq_one, smul_eq_mul, mul_one, abs_of_pos (pow_pos hε 2), inv_mul_cancel₀ (pow_pos hε 2).ne']

/-- Inside `V`, the convolution with `f_ε(z - ·)` does not see the values off `V`. -/
theorem integral_indicator_mul_mollScale {f : ℂ → ℝ} (hf : IsMollifier f) {V : Set ℂ} (b : ℂ → ℝ) {ε : ℝ}
    (hε : 0 < ε) {z : ℂ} (hzV : closedBall z ε ⊆ V) :
    ∫ w, V.indicator b w * mollScale f ε (z - w) = ∫ w, b w * mollScale f ε (z - w) := by
  congr 1
  funext w
  by_cases hw : w ∈ V
  · rw [indicator_of_mem hw]
  · have hm0 : mollScale f ε (z - w) = 0 := image_eq_zero_of_notMem_tsupport (f := fun w => mollScale f ε (z - w))
      fun h => hw (hzV (ball_subset_closedBall (tsupport_mollScale_sub_subset hf hε z h)))
    simp [hm0]

/-- The convolution of the zero extension of `b` with `f_ε`, as a function of the centre, is measurable. -/
theorem measurable_integral_indicator_mul_mollScale {f : ℂ → ℝ} (hf : IsMollifier f) {V : Set ℂ} (hV : IsOpen V)
    {b : ℂ → ℝ} (hb : ContinuousOn b V) (ε : ℝ) :
    Measurable fun z => ∫ w, V.indicator b w * mollScale f ε (z - w) := by
  have hm : Measurable fun p : ℂ × ℂ => V.indicator b p.2 * mollScale f ε (p.1 - p.2) :=
    ((measurable_indicator_of_continuousOn hV hb).comp measurable_snd).mul
      ((continuous_mollScale hf ε).measurable.comp (measurable_fst.sub measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- `|(b ∗ f_ε)(z) - b(z)| ≤ η` if `|b(w) - b(z)| ≤ η` on `B_ε(z)` and `B̄_ε(z) ⊆ V`. -/
theorem abs_integral_indicator_mul_mollScale_sub_le {f : ℂ → ℝ} (hf : IsMollifier f) {V : Set ℂ} (hV : IsOpen V)
    {b : ℂ → ℝ} (hb : ContinuousOn b V) {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hzV : closedBall z ε ⊆ V) {η : ℝ}
    (hη : ∀ w ∈ ball z ε, |b w - b z| ≤ η) :
    |(∫ w, V.indicator b w * mollScale f ε (z - w)) - b z| ≤ η := by
  have hsupp := tsupport_mollScale_sub_subset hf hε z
  have hmc : Continuous fun w => mollScale f ε (z - w) :=
    (continuous_mollScale hf ε).comp (continuous_const.sub continuous_id)
  have hmcs := hasCompactSupport_mollScale_sub hf hε z
  have hmi : Integrable (fun w => mollScale f ε (z - w)) := hmc.integrable_of_hasCompactSupport hmcs
  have hind : ContinuousOn (V.indicator b) V := hb.congr fun w hw => indicator_of_mem hw b
  have hpc : Continuous fun w => V.indicator b w * mollScale f ε (z - w) :=
    (hind.mul hmc.continuousOn).continuous_of_tsupport_subset hV
      (tsupport_mul_subset_right.trans (hsupp.trans (ball_subset_closedBall.trans hzV)))
  have hpi : Integrable (fun w => V.indicator b w * mollScale f ε (z - w)) :=
    hpc.integrable_of_hasCompactSupport hmcs.mul_left
  have heq : (∫ w, V.indicator b w * mollScale f ε (z - w)) - b z =
      ∫ w, (V.indicator b w - b z) * mollScale f ε (z - w) := by
    simp_rw [sub_mul]
    rw [integral_sub hpi (hmi.const_mul (b z)), integral_const_mul, integral_mollScale_sub hf hε z, mul_one]
  have hpt : ∀ w, ‖(V.indicator b w - b z) * mollScale f ε (z - w)‖ ≤ η * mollScale f ε (z - w) := by
    intro w
    rw [norm_mul, Real.norm_of_nonneg (mollScale_nonneg hf _ _), Real.norm_eq_abs]
    by_cases hw : w ∈ ball z ε
    · rw [indicator_of_mem (hzV (ball_subset_closedBall hw))]
      exact mul_le_mul_of_nonneg_right (hη w hw) (mollScale_nonneg hf _ _)
    · have hm0 : mollScale f ε (z - w) = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun w => mollScale f ε (z - w)) fun h => hw (hsupp h)
      simp [hm0]
  rw [heq, ← Real.norm_eq_abs]
  calc ‖∫ w, (V.indicator b w - b z) * mollScale f ε (z - w)‖ ≤ ∫ w, η * mollScale f ε (z - w) :=
        norm_integral_le_of_norm_le (hmi.const_mul η) (ae_of_all _ hpt)
    _ = η := by rw [integral_const_mul, integral_mollScale_sub hf hε z, mul_one]

/-- `(b ∗ f_{2^{-k}})(z) → b(z)` uniformly on every compact subset of `V`, for `b` continuous on `V`. -/
theorem tendstoUniformlyOn_integral_indicator_mul_mollScale {f : ℂ → ℝ} (hf : IsMollifier f) {V : Set ℂ}
    (hV : IsOpen V) {b : ℂ → ℝ} (hb : ContinuousOn b V) {K : Set ℂ} (hK : IsCompact K) (hKV : K ⊆ V) :
    TendstoUniformlyOn (fun k z => ∫ w, V.indicator b w * mollScale f (HarmonicBalls.dyadicScale k) (z - w)) b
      atTop K := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hV hKV
  have hu := hK.cthickening.uniformContinuousOn_of_continuous (hb.mono hsub)
  rw [Metric.uniformContinuousOn_iff] at hu
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  obtain ⟨θ, hθ, hθu⟩ := hu (η / 2) (by positivity)
  filter_upwards [tendsto_dyadicScale_nhds_zero.eventually (gt_mem_nhds (lt_min hθ hδ))] with k hk z hz
  show dist (b z) (∫ w, V.indicator b w * mollScale f (HarmonicBalls.dyadicScale k) (z - w)) < η
  have hε := HarmonicBalls.dyadicScale_pos k
  have hk1 : HarmonicBalls.dyadicScale k < θ := hk.trans_le (min_le_left _ _)
  have hk2 : HarmonicBalls.dyadicScale k < δ := hk.trans_le (min_le_right _ _)
  have hball : closedBall z (HarmonicBalls.dyadicScale k) ⊆ cthickening δ K := fun w hw =>
    mem_cthickening_of_dist_le w z δ K hz ((mem_closedBall.1 hw).trans hk2.le)
  have h := abs_integral_indicator_mul_mollScale_sub_le hf hV hb hε (hball.trans hsub) (η := η / 2)
    fun w hw => by
      have := hθu w (hball (ball_subset_closedBall hw)) z (self_subset_cthickening K hz)
        ((mem_ball.1 hw).trans hk1)
      rw [Real.dist_eq] at this
      exact this.le
  rw [Real.dist_eq, abs_sub_comm]
  linarith

end LQGMeasureChart

open LQGMeasureChart

/-! ### Continuous additions -/

/-- **Adding a continuous function, smooth approximations.** Let `f` be a bump function, `V` open, `b` continuous on
`V`, and `G'(u) = G(u) + ∫ b u` for the translates `u = f_ε(z - ·)` with `B̄_ε(z) ⊆ V`. If the smooth approximations
of `G` in `V` converge vaguely in `V` to `ν` along `ε = 2^{-k}`, then those of `G'` converge vaguely in `V` to
`e^{γ b} ν`. -/
theorem isVagueLimitOn_smoothApprox_add {γ : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) {V : Set ℂ} (hV : IsOpen V)
    {b : ℂ → ℝ} (hb : ContinuousOn b V) {G G' : (ℂ → ℝ) → ℝ}
    (hG' : ∀ ε : ℝ, 0 < ε → ∀ z, closedBall z ε ⊆ V →
      G' (fun w => mollScale f ε (z - w)) = G (fun w => mollScale f ε (z - w)) + ∫ w, b w * mollScale f ε (z - w))
    {ν : Measure ℂ}
    (h : QuantumZipper.IsVagueLimitOn V (fun k => smoothApprox γ f V G (HarmonicBalls.dyadicScale k)) ν) :
    QuantumZipper.IsVagueLimitOn V (fun k => smoothApprox γ f V G' (HarmonicBalls.dyadicScale k))
      (ν.withDensity fun z => ENNReal.ofReal (Real.exp (γ * b z))) := by
  have hβs : ∀ k : ℕ, Measurable fun z =>
      ∫ w, V.indicator b w * mollScale f (HarmonicBalls.dyadicScale k) (z - w) := fun k =>
    measurable_integral_indicator_mul_mollScale hf hV hb _
  have heq : ∀ k, smoothApprox γ f V G' (HarmonicBalls.dyadicScale k) =
      (smoothApprox γ f V G (HarmonicBalls.dyadicScale k)).withDensity fun z =>
        ENNReal.ofReal (Real.exp (γ * ∫ w, V.indicator b w * mollScale f (HarmonicBalls.dyadicScale k) (z - w))) := by
    intro k
    have hε := HarmonicBalls.dyadicScale_pos k
    unfold smoothApprox
    rw [← withDensity_mul_of_measurable_right (((hβs k).const_mul γ).exp.ennreal_ofReal)
      (fun z => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne') (fun z => ENNReal.ofReal_ne_top)]
    congr 1
    funext z
    simp only [Pi.mul_apply]
    split_ifs with hz
    · have hexp : smoothExponent γ f G' (HarmonicBalls.dyadicScale k) z =
          smoothExponent γ f G (HarmonicBalls.dyadicScale k) z +
            γ * ∫ w, V.indicator b w * mollScale f (HarmonicBalls.dyadicScale k) (z - w) := by
        simp only [smoothExponent]
        rw [hG' _ hε z hz, integral_indicator_mul_mollScale hf b hε hz]
        ring
      rw [hexp, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    · rw [zero_mul]
  simp only [heq]
  exact isVagueLimitOn_withDensity_exp hV h γ hb
    (βs := fun k z => ∫ w, V.indicator b w * mollScale f (HarmonicBalls.dyadicScale k) (z - w)) hβs
    fun K hK hKV => tendstoUniformlyOn_integral_indicator_mul_mollScale hf hV hb hK hKV

/-- **Adding a continuous function, circle approximations.** Let `V` be open, `b` continuous on `V`, and
`h'_ε(z) = h_ε(z) + b_ε(z)` (circle averages) whenever `B̄_ε(z) ⊆ V`. If the circle approximations
`ε^{γ²/2} e^{γ h_ε(z)} dz` converge vaguely in `V` to `ν` along `ε = 2^{-k}`, then those of `h'` converge vaguely in
`V` to `e^{γ b} ν`. -/
theorem isVagueLimitOn_lqgApprox_add {γ : ℝ} {V : Set ℂ} (hV : IsOpen V) {b : ℂ → ℝ} (hb : ContinuousOn b V)
    {hc hc' : ℝ → ℂ → ℝ}
    (hc'eq : ∀ ε : ℝ, 0 < ε → ∀ z, closedBall z ε ⊆ V → hc' ε z = hc ε z + Real.circleAverage b z ε)
    {ν : Measure ℂ}
    (h : QuantumZipper.IsVagueLimitOn V (fun k => HarmonicBalls.lqgApprox γ hc (HarmonicBalls.dyadicScale k)) ν) :
    QuantumZipper.IsVagueLimitOn V (fun k => HarmonicBalls.lqgApprox γ hc' (HarmonicBalls.dyadicScale k))
      (ν.withDensity fun z => ENNReal.ofReal (Real.exp (γ * b z))) := by
  have hbm := measurable_indicator_of_continuousOn hV hb
  have hind : ContinuousOn (V.indicator b) V := hb.congr fun w hw => indicator_of_mem hw b
  have hβs : ∀ k : ℕ, Measurable fun z => Real.circleAverage (V.indicator b) z (HarmonicBalls.dyadicScale k) :=
    fun k => MatedCRTHarmonic.MoTPort.ConeArea3.measurable_circleAverage hbm _
  have hunif : ∀ K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k z => Real.circleAverage (V.indicator b) z (HarmonicBalls.dyadicScale k)) b atTop K :=
    fun K hK hKV =>
      (MatedCRTHarmonic.MoTPort.ConeArea3.tendstoUniformlyOn_circleAverage hV hind hK hKV).congr_right
        fun z hz => indicator_of_mem (hKV hz) b
  refine isVagueLimitOn_of_eventually_restrict_eq (isVagueLimitOn_withDensity_exp hV h γ hb
    (βs := fun k z => Real.circleAverage (V.indicator b) z (HarmonicBalls.dyadicScale k)) hβs hunif)
    fun K hK hKV => ?_
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hV hKV
  filter_upwards [tendsto_dyadicScale_nhds_zero.eventually (gt_mem_nhds hδ)] with k hk
  have hε := HarmonicBalls.dyadicScale_pos k
  try dsimp only
  unfold HarmonicBalls.lqgApprox
  rw [← withDensity_mul_of_measurable_right (((hβs k).const_mul γ).exp.ennreal_ofReal)
      (fun z => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne') (fun z => ENNReal.ofReal_ne_top),
    restrict_withDensity hK.measurableSet, restrict_withDensity hK.measurableSet]
  refine withDensity_congr_ae ((ae_restrict_iff' hK.measurableSet).2 (ae_of_all _ fun z hz => ?_))
  have hzV : closedBall z (HarmonicBalls.dyadicScale k) ⊆ V := fun w hw =>
    hsub (mem_cthickening_of_dist_le w z δ K hz ((mem_closedBall.1 hw).trans hk.le))
  have hcirc : Real.circleAverage b z (HarmonicBalls.dyadicScale k) =
      Real.circleAverage (V.indicator b) z (HarmonicBalls.dyadicScale k) :=
    Real.circleAverage_congr_sphere fun w hw =>
      (indicator_of_mem (hzV (sphere_subset_closedBall (by rwa [abs_of_pos hε] at hw))) b).symm
  simp only [Pi.mul_apply]
  rw [hc'eq _ hε z hzV, hcirc, mul_add, Real.exp_add, ← mul_assoc,
    ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)]

/-! ### Locality -/

/-- **Locality of the smooth approximations.** For `W ⊆ V` and functionals `G`, `G'` agreeing on the translates
`f_ε(z - ·)` with `z ∈ K`, if `B̄_ε(z) ⊆ W` for `z ∈ K`, the smooth approximations of `G'` on `W` and of `G` on `V`
agree on `K`. -/
theorem smoothApprox_restrict_eq_of_subset {γ : ℝ} {f : ℂ → ℝ} {V W : Set ℂ} (hWV : W ⊆ V)
    {G G' : (ℂ → ℝ) → ℝ} {ε : ℝ} {K : Set ℂ} (hK : MeasurableSet K) (hKW : ∀ z ∈ K, closedBall z ε ⊆ W)
    (hGG' : ∀ z ∈ K, G' (fun w => mollScale f ε (z - w)) = G (fun w => mollScale f ε (z - w))) :
    (smoothApprox γ f W G' ε).restrict K = (smoothApprox γ f V G ε).restrict K := by
  unfold smoothApprox
  rw [restrict_withDensity hK, restrict_withDensity hK]
  refine withDensity_congr_ae ((ae_restrict_iff' hK).2 (ae_of_all _ fun z hz => ?_))
  simp only [ite_eq_left (hKW z hz), ite_eq_left ((hKW z hz).trans hWV), smoothExponent, hGG' z hz]

/-- **Locality of vague limits of the smooth approximations.** For open `W ⊆ V` and functionals `G`, `G'` agreeing
on the translates `f_ε(z - ·)` with `B̄_ε(z) ⊆ W`, if the smooth approximations of `G` in `V` converge vaguely in `V`
to `ν`, then those of `G'` in `W` converge vaguely in `W` to `ν|_W`. -/
theorem isVagueLimitOn_smoothApprox_of_subset {γ : ℝ} {f : ℂ → ℝ} {V W : Set ℂ} (hW : IsOpen W) (hWV : W ⊆ V)
    {G G' : (ℂ → ℝ) → ℝ}
    (hGG' : ∀ ε : ℝ, 0 < ε → ∀ z, closedBall z ε ⊆ W →
      G' (fun w => mollScale f ε (z - w)) = G (fun w => mollScale f ε (z - w)))
    {ν : Measure ℂ}
    (h : QuantumZipper.IsVagueLimitOn V (fun k => smoothApprox γ f V G (HarmonicBalls.dyadicScale k)) ν) :
    QuantumZipper.IsVagueLimitOn W (fun k => smoothApprox γ f W G' (HarmonicBalls.dyadicScale k))
      (ν.restrict W) := by
  refine isVagueLimitOn_of_eventually_restrict_eq (isVagueLimitOn_restrict_of_subset hW hWV h)
    fun K hK hKW => ?_
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hW hKW
  filter_upwards [tendsto_dyadicScale_nhds_zero.eventually (gt_mem_nhds hδ)] with k hk
  have hball : ∀ z ∈ K, closedBall z (HarmonicBalls.dyadicScale k) ⊆ W := fun z hz w hw =>
    hsub (mem_cthickening_of_dist_le w z δ K hz ((mem_closedBall.1 hw).trans hk.le))
  exact smoothApprox_restrict_eq_of_subset hWV hK.measurableSet hball
    fun z hz => hGG' _ (HarmonicBalls.dyadicScale_pos k) z (hball z hz)

/-- **Locality of vague limits of the smooth approximations**, for functionals agreeing on all functions supported
in `W`. -/
theorem isVagueLimitOn_smoothApprox_of_subset_of_eq {γ : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) {V W : Set ℂ}
    (hW : IsOpen W) (hWV : W ⊆ V) {G G' : (ℂ → ℝ) → ℝ} (hGG' : ∀ u : ℂ → ℝ, tsupport u ⊆ W → G' u = G u)
    {ν : Measure ℂ}
    (h : QuantumZipper.IsVagueLimitOn V (fun k => smoothApprox γ f V G (HarmonicBalls.dyadicScale k)) ν) :
    QuantumZipper.IsVagueLimitOn W (fun k => smoothApprox γ f W G' (HarmonicBalls.dyadicScale k))
      (ν.restrict W) :=
  isVagueLimitOn_smoothApprox_of_subset hW hWV (fun _ hε z hz =>
    hGG' _ ((tsupport_mollScale_sub_subset hf hε z).trans (ball_subset_closedBall.trans hz))) h

end MatedCRT
