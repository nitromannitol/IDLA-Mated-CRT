import MatedCRT.FirstPass.Derived.LQGMeasureChartSmooth
import MatedCRT.FirstPass.Derived.ChartTransportedMeasure

/-!
# The chart field as a distribution on the unit disc and its local form

Let `ψ` be an inverse chart of a bounded open set `U` (`IsInverseChart U z ψ`), with conformal map
`φ = chartMap U ψ : 𝔻 → U`. The chart field `h ∘ φ + Q log |φ'|` of a distribution `h` on `ℂ` is given by its
pairings `chartFieldPairing γ h U z ψ` with the test functions on the unit disc: `⟨h, (f ∘ ψ) |ψ'|²⟩ +
Q ∫ log |φ'| f` (the field of Sheffield–Wang (2016), arXiv:1605.06171v2, (1.6), with the pairing of Proposition 2.3
and Remark 3.3; the coordinate change of Duplantier–Sheffield (2011), arXiv:0808.1560v2, Proposition 2.1). This file
formalizes the first step ("the chart") of the coordinate change of the LQG measure for all inverse charts:

* `chartFieldDist`, `chartFieldDist_apply`: these pairings are a distribution on the unit disc. The transport
  `f ↦ (f ∘ ψ) |ψ'|²` (`chartTestCLM`) is continuous on the test functions: on the test functions supported in a
  compact `K ⊆ 𝔻` it maps into the test functions supported in the compact `closure U ∩ ψ⁻¹(K) ⊆ U`, with the
  derivative bounds of the chain rule and the Leibniz rule (`norm_iteratedFDeriv_chartTestFun_le`); and `log |φ'|` is
  continuous on the disc.
* `chartFieldPairing_eq_pullbackPairing`: on test functions supported in the image `ψ(B(c, r))` of a disc
  `B(c, r) ⊆ U`, the chart field is the field `pullbackPairing` of the restriction of `h` to `B(c, r)`, with the
  conformal map `ψ : B(c, r) → ψ(B(c, r))`.
* `IsInverseChart.integral_mul_chartTestFun`: the change of variables `w = ψ(x)` (Jacobian `|ψ'|²`),
  `∫ b(x) (u ∘ ψ)(x) |ψ'(x)|² 1_U(x) dx = ∫ b(φ(w)) u(w) dw`.
* `LQGMeasureChart.pairFun_restrictTo`: the pairing of the restriction of `h` to an open set `V` with a smooth
  function compactly supported in `V` is the pairing of `h`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped Distributions ContDiff

namespace MatedCRT

namespace LQGMeasureChart

/-- **The pairing of a restriction.** For `u` smooth with compact support in the open set `V`, the pairing of the
restriction `h|_V` with `u` is the pairing of `h` with `u`. -/
theorem pairFun_restrictTo (V : TopologicalSpace.Opens ℂ) (H : LQGMetric.DistC) {u : ℂ → ℝ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (huV : tsupport u ⊆ V) :
    pairFun (LQGMetric.restrictTo V H) u = H ⟨u, hu, huc, fun _ _ => trivial⟩ := by
  rw [pairFun, dite_eq_left ⟨hu, huc, huV⟩]
  show H (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) ⟨u, hu, huc, huV⟩) = _
  refine congrArg (⇑H) (TestFunction.ext fun x => ?_)
  simp [TestFunction.monoCLM_apply]
  rfl

/-- Uniform bounds on compact sets for the derivatives up to order `n` of a smooth function on an open set. -/
theorem exists_bound_iteratedFDerivWithin_of_isCompact {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℂ → F} {s K : Set ℂ} (hg : ContDiffOn ℝ ∞ g s) (hs : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s)
    (n : ℕ) : ∃ C, 0 ≤ C ∧ ∀ j ≤ n, ∀ x ∈ K, ‖iteratedFDerivWithin ℝ j g s x‖ ≤ C := by
  have h1 : ∀ j : ℕ, ∃ C, ∀ x ∈ K, ‖iteratedFDerivWithin ℝ j g s x‖ ≤ C := fun j =>
    hK.exists_bound_of_continuousOn
      ((hg.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast le_top) hs.uniqueDiffOn).mono hKs)
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := h1 0
    refine ⟨max C 0, le_max_right _ _, fun j hj x hx => ?_⟩
    rw [Nat.le_zero.1 hj]
    exact (hC x hx).trans (le_max_left _ _)
  | succ n ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    obtain ⟨C', hC'⟩ := h1 (n + 1)
    refine ⟨max C C', hC0.trans (le_max_left _ _), fun j hj x hx => ?_⟩
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · exact (hC j (Nat.lt_succ_iff.1 hlt) x hx).trans (le_max_left _ _)
    · rw [le_antisymm hj hge]
      exact (hC' x hx).trans (le_max_right _ _)

end LQGMeasureChart

open LQGMeasureChart

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-! ### The transported test functions -/

/-- The compact set `closure U ∩ ψ⁻¹(K)`, which contains the supports of the transported test functions
`(f ∘ ψ) |ψ'|²` of the test functions `f` supported in `K`. -/
def chartCompact (U : Set ℂ) (ψ : C(ℂ, ℂ)) (hUb : Bornology.IsBounded U) (K : TopologicalSpace.Compacts ℂ) :
    TopologicalSpace.Compacts ℂ :=
  ⟨closure U ∩ ψ ⁻¹' K, hUb.isCompact_closure.inter_right (K.isCompact.isClosed.preimage ψ.continuous)⟩

/-- **Derivative bounds for the transported test functions** (chain rule and Leibniz rule on the compact set
`closure U ∩ ψ⁻¹(K) ⊆ U`): the `i`-th derivative of `(f ∘ ψ) |ψ'|²` is bounded by a constant times the sup of the
`C^j` norms of `f`, `j ≤ i`, for the test functions `f` supported in a compact `K ⊆ 𝔻`. -/
theorem norm_iteratedFDeriv_chartTestFun_le (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {K : TopologicalSpace.Compacts ℂ} (hK : (K : Set ℂ) ⊆ unitDiscOpens) (i : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ f : 𝓓_{K}(ℂ, ℝ), ∀ x ∈ closure U ∩ ψ ⁻¹' K,
      ‖iteratedFDeriv ℝ i (chartTestFun U ψ f) x‖ ≤ C * ((Finset.Iic i).sup fun j => N[ℝ]_{K, j}) f := by
  obtain ⟨hKc, hKU⟩ := isCompact_closure_inter_preimage hψ hU hUb K.isCompact hK
  have hψd : ContDiffOn ℝ ∞ ψ U := (hψ.differentiableOn.contDiffOn hU).restrict_scalars ℝ
  have hψ'd : ContDiffOn ℝ ∞ (deriv ψ) U :=
    ((hψ.differentiableOn.deriv hU).contDiffOn hU).restrict_scalars ℝ
  have hqd : ContDiffOn ℝ ∞ (fun y => ‖deriv ψ y‖ ^ 2) U := (contDiff_norm_sq ℝ).comp_contDiffOn hψ'd
  obtain ⟨B, -, hB⟩ := exists_bound_iteratedFDerivWithin_of_isCompact hψd hU hKc hKU i
  obtain ⟨E, hE0, hE⟩ := exists_bound_iteratedFDerivWithin_of_isCompact hqd hU hKc hKU i
  obtain ⟨D, hD1, hDB⟩ : ∃ D : ℝ, 1 ≤ D ∧ B ≤ D := ⟨max B 1, le_max_right _ _, le_max_left _ _⟩
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  refine ⟨∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * (Nat.factorial k * D ^ k) * E,
    Finset.sum_nonneg fun k _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD0 _))) hE0, fun f x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hS0 : 0 ≤ ((Finset.Iic i).sup fun j => N[ℝ]_{K, j}) f := apply_nonneg _ _
  have hfd : ContDiffOn ℝ ∞ (⇑f ∘ ⇑ψ) U := f.contDiff.comp_contDiffOn hψd
  have heq : iteratedFDeriv ℝ i (chartTestFun U ψ f) x =
      iteratedFDerivWithin ℝ i (fun y => (⇑f ∘ ⇑ψ) y * ‖deriv ψ y‖ ^ 2) U x := by
    rw [iteratedFDerivWithin_of_isOpen i hU hxU]
    have hev : chartTestFun U ψ f =ᶠ[𝓝 x] fun y => (⇑f ∘ ⇑ψ) y * ‖deriv ψ y‖ ^ 2 := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact indicator_of_mem hy _
    exact (hev.iteratedFDeriv ℝ i).eq_of_nhds
  have hcomp : ∀ k ≤ i, ‖iteratedFDerivWithin ℝ k (⇑f ∘ ⇑ψ) U x‖ ≤
      Nat.factorial k * ((Finset.Iic i).sup fun j => N[ℝ]_{K, j}) f * D ^ k := fun k hk =>
    norm_iteratedFDerivWithin_comp_le f.contDiff.contDiffOn hψd (by exact_mod_cast le_top) uniqueDiffOn_univ
      hU.uniqueDiffOn (mapsTo_univ _ _) hxU
      (fun j hj => by
        rw [iteratedFDerivWithin_univ]
        exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
          (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 (hj.trans hk))))
      (fun j hj1 hjk => (hB j (hjk.trans hk) x hx).trans (hDB.trans (le_self_pow₀ hD1 (by omega))))
  rw [heq]
  calc ‖iteratedFDerivWithin ℝ i (fun y => (⇑f ∘ ⇑ψ) y * ‖deriv ψ y‖ ^ 2) U x‖
      ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * ‖iteratedFDerivWithin ℝ k (⇑f ∘ ⇑ψ) U x‖ *
          ‖iteratedFDerivWithin ℝ (i - k) (fun y => ‖deriv ψ y‖ ^ 2) U x‖ :=
        norm_iteratedFDerivWithin_mul_le hfd hqd hU.uniqueDiffOn hxU (by exact_mod_cast le_top)
    _ ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
          (Nat.factorial k * ((Finset.Iic i).sup fun j => N[ℝ]_{K, j}) f * D ^ k) * E := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hki : k ≤ i := Finset.mem_range_succ_iff.1 hk
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hcomp k hki) (Nat.cast_nonneg _))
          (hE (i - k) (Nat.sub_le i k) x hx) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hS0) (pow_nonneg hD0 _)))
    _ = (∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * (Nat.factorial k * D ^ k) * E) *
          ((Finset.Iic i).sup fun j => N[ℝ]_{K, j}) f := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- The transport `f ↦ (f ∘ ψ) |ψ'|²` from the test functions supported in a compact `K ⊆ 𝔻` to the test functions
supported in `closure U ∩ ψ⁻¹(K)`, as a continuous linear map. -/
noncomputable def chartTestSupportedIn (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {K : TopologicalSpace.Compacts ℂ} (hK : (K : Set ℂ) ⊆ unitDiscOpens) :
    𝓓_{K}(ℂ, ℝ) →L[ℝ] 𝓓_{chartCompact U ψ hUb K}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.mkCLM ℝ (fun f => chartTestFun U ψ f)
    (fun f g x => by by_cases hx : x ∈ U <;> simp [chartTestFun, hx, add_mul])
    (fun c f x => by by_cases hx : x ∈ U <;> simp [chartTestFun, hx, mul_assoc])
    (fun f => contDiff_chartTestFun hψ hU hUb (TestFunction.ofSupportedIn hK f))
    (fun f x hx => show chartTestFun U ψ f x = 0 from chartTestFun_eq_zero_of_notMem (⇑f) fun h =>
      hx (show x ∈ closure U ∩ ψ ⁻¹' (K : Set ℂ) from ⟨h.1, f.tsupport_subset h.2⟩))
    (fun i _ => by
      obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_chartTestFun_le hψ hU hUb hK i
      exact ⟨Finset.Iic i, C, hC0, fun f x hx => hC f x hx⟩)

/-- **The transport of test functions by an inverse chart**, `f ↦ (f ∘ ψ) |ψ'|²` from the test functions on the unit
disc to the test functions on `ℂ`, as a continuous linear map. -/
noncomputable def chartTestCLM (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    𝓓(unitDiscOpens, ℝ) →L[ℝ] LQGMetric.TestC :=
  TestFunction.mkCLM ℝ (chartTest hψ hU hUb)
    (fun f g => TestFunction.ext fun x => by
      by_cases hx : x ∈ U <;> simp [chartTest_apply, chartTestFun, hx, add_mul])
    (fun c f => TestFunction.ext fun x => by
      by_cases hx : x ∈ U <;> simp [chartTest_apply, chartTestFun, hx, mul_assoc])
    (fun K hK =>
      ((TestFunction.continuous_ofSupportedIn (Ω := ⊤) (K := chartCompact U ψ hUb K) (n := ⊤)
        (fun _ _ => trivial)).comp (chartTestSupportedIn hψ hU hUb hK).continuous).congr
        fun f => TestFunction.ext fun x => rfl)

theorem chartTestCLM_apply (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (f : 𝓓(unitDiscOpens, ℝ)) : chartTestCLM hψ hU hUb f = chartTest hψ hU hUb f :=
  rfl

/-! ### The chart field as a distribution -/

/-- `log |φ'|` is locally integrable on the unit disc, `φ = chartMap U ψ`. -/
theorem IsInverseChart.locallyIntegrableOn_log_norm_deriv_chartMap (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    LocallyIntegrableOn (fun w => Real.log ‖deriv (chartMap U ψ) w‖) (unitDiscOpens : Set ℂ) volume := by
  have hd := hψ.differentiableOn_chartMap hU hUb
  have hcont : ContinuousOn (fun w => Real.log ‖deriv (chartMap U ψ) w‖) (ball (0 : ℂ) 1) :=
    ((hd.deriv isOpen_ball).continuousOn.norm).log fun w hw => norm_ne_zero_iff.2 (by
      rw [(hψ.hasDerivAt_chartMap hU hUb hw).deriv]
      exact inv_ne_zero (hψ.deriv_ne_zero hU (hψ.chartMap_mem hw)))
  exact hcont.locallyIntegrableOn measurableSet_ball

/-- **The chart field `h ∘ φ + Q log |φ'|` as a distribution on the unit disc**, for an inverse chart `ψ` of a
bounded open set `U` with `φ = chartMap U ψ`: `f ↦ ⟨h, (f ∘ ψ) |ψ'|²⟩ + Q ∫ log |φ'| f`. -/
noncomputable def chartFieldDist (γ : ℝ) (H : LQGMetric.DistC) (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) : LQGMetric.DistOn unitDiscOpens :=
  (show LQGMetric.DistOn unitDiscOpens from H.comp (chartTestCLM hψ hU hUb)) +
    MatedCRTHarmonic.MatedCRT.lqgQ γ •
      Distribution.ofFun unitDiscOpens (fun w => Real.log ‖deriv (chartMap U ψ) w‖) volume ⊤

/-- The pairings of `chartFieldDist` are the pairings `chartFieldPairing` of the chart field. -/
theorem chartFieldDist_apply (γ : ℝ) (H : LQGMetric.DistC) (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (f : 𝓓(unitDiscOpens, ℝ)) :
    chartFieldDist γ H hψ hU hUb f = chartFieldPairing γ H U z ψ f := by
  rw [chartFieldPairing, dite_eq_left ⟨hψ, hU, hUb⟩]
  have h2 : (∫ w, Real.log ‖deriv (chartMap U ψ) w‖ * f w) =
      Distribution.ofFun unitDiscOpens (fun w => Real.log ‖deriv (chartMap U ψ) w‖) volume ⊤ f := by
    rw [Distribution.ofFun_apply (hψ.locallyIntegrableOn_log_norm_deriv_chartMap hU hUb)]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    show Real.log ‖deriv (chartMap U ψ) w‖ * f w = f w • Real.log ‖deriv (chartMap U ψ) w‖
    rw [smul_eq_mul, mul_comm]
  rw [h2]
  rfl

/-- **The chart field is a distribution on the unit disc**: for an inverse chart `ψ` of a bounded open set `U`, the
pairings `chartFieldPairing γ H U z ψ` are those of a distribution on the unit disc. -/
theorem exists_distOn_eq_chartFieldPairing (γ : ℝ) (H : LQGMetric.DistC) (hψ : IsInverseChart U z ψ)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ g : LQGMetric.DistOn unitDiscOpens, ∀ f, g f = chartFieldPairing γ H U z ψ f :=
  ⟨chartFieldDist γ H hψ hU hUb, chartFieldDist_apply γ H hψ hU hUb⟩

/-! ### The local form on sub-discs -/

/-- On the image `ψ(B(c, r))` of a disc `B(c, r) ⊆ U`, the conformal map `φ = chartMap U ψ` agrees near every point
with the inverse of `ψ` on `B(c, r)`. -/
theorem IsInverseChart.chartMap_eventuallyEq_invFunOn (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {c : ℂ} {r : ℝ} (hcr : ball c r ⊆ U) {w : ℂ} (hw : w ∈ ψ '' ball c r) :
    chartMap U ψ =ᶠ[𝓝 w] Function.invFunOn ψ (ball c r) := by
  obtain ⟨y, hy, rfl⟩ := hw
  have hopen : IsOpen (ball (0 : ℂ) 1 ∩ chartMap U ψ ⁻¹' ball c r) :=
    (hψ.continuousOn_chartMap hU hUb).isOpen_inter_preimage isOpen_ball isOpen_ball
  have hmem : ψ y ∈ ball (0 : ℂ) 1 ∩ chartMap U ψ ⁻¹' ball c r := by
    refine ⟨hψ.mapsTo_ball (hcr hy), ?_⟩
    rw [mem_preimage, hψ.chartMap_apply (hcr hy)]
    exact hy
  filter_upwards [hopen.mem_nhds hmem] with w' hw'
  have h0 : chartMap U ψ w' ∈ ball c r := hw'.2
  have h1 : ψ (chartMap U ψ w') = w' := hψ.apply_chartMap hw'.1
  obtain ⟨h2, h3⟩ := Function.invFunOn_pos (f := ⇑ψ) (s := ball c r) ⟨chartMap U ψ w', h0, h1⟩
  exact (hψ.injOn.mono subset_closure) (hcr h0) (hcr h2) (h1.trans h3.symm)

/-- **The chart field on a sub-disc.** For a disc `B(c, r) ⊆ U` and a test function `f` on the unit disc supported in
`ψ(B(c, r))`, the pairing of the chart field with `f` is the pairing of the field `h|_{B(c,r)} ∘ φ + Q log |φ'|` of
the conformal map `ψ : B(c, r) → ψ(B(c, r))` (Sheffield–Wang (2016), (1.6)). -/
theorem chartFieldPairing_eq_pullbackPairing (γ : ℝ) (H : LQGMetric.DistC) (hψ : IsInverseChart U z ψ)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) {c : ℂ} {r : ℝ} (hcr : ball c r ⊆ U)
    (f : 𝓓(unitDiscOpens, ℝ)) (hf : tsupport f ⊆ ψ '' ball c r) :
    chartFieldPairing γ H U z ψ f = pullbackPairing γ (LQGMetric.restrictTo (disc c r) H) ψ f := by
  have hmem : ∀ x ∈ closure U, ψ x ∈ ψ '' ball c r → x ∈ ball c r := by
    rintro x hx ⟨y, hy, hxy⟩
    exact hψ.injOn (subset_closure (hcr hy)) hx hxy ▸ hy
  have hfun : chartTestFun U ψ f = (ball c r).indicator fun x => f (ψ x) * ‖deriv ψ x‖ ^ 2 := by
    funext x
    by_cases hx : x ∈ ball c r
    · simp only [chartTestFun, indicator_of_mem (hcr hx), indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      by_cases hxU : x ∈ U
      · have h0 : f (ψ x) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hx (hmem x (subset_closure hxU) (hf h))
        simp only [chartTestFun, indicator_of_mem hxU, h0, zero_mul]
      · exact indicator_of_notMem hxU _
  have hsupp : tsupport (chartTestFun U ψ f) ⊆ ball c r := by
    obtain ⟨hKc, -⟩ := isCompact_closure_inter_preimage hψ hU hUb f.hasCompactSupport f.tsupport_subset
    refine (closure_minimal (fun x hx => ?_) hKc.isClosed).trans fun x hx =>
      hmem x hx.1 (hf (show ψ x ∈ tsupport f from hx.2))
    by_contra hn
    exact hx (chartTestFun_eq_zero_of_notMem _ hn)
  have hlog : ∫ w, Real.log ‖deriv (chartMap U ψ) w‖ * f w =
      ∫ w, Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖ * f w := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    by_cases hw : f w = 0
    · simp only [hw, mul_zero]
    · show Real.log ‖deriv (chartMap U ψ) w‖ * f w =
        Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖ * f w
      rw [(hψ.chartMap_eventuallyEq_invFunOn hU hUb hcr (hf (subset_tsupport (⇑f) hw))).deriv_eq]
  have hD : (disc c r : Set ℂ) = ball c r := rfl
  rw [chartFieldPairing, dite_eq_left ⟨hψ, hU, hUb⟩, pullbackPairing, hD, ← hfun,
    pairFun_restrictTo (disc c r) H (contDiff_chartTestFun hψ hU hUb f) (hasCompactSupport_chartTestFun hψ hU hUb f)
      hsupp, hlog]
  rfl

/-! ### The change of variables -/

/-- **Change of variables for the transported test functions.** For an inverse chart `ψ` of the open set `U` with
conformal map `φ = chartMap U ψ` and `u` supported in the unit disc, by the change of variables `w = ψ(x)` with
Jacobian `|ψ'(x)|²`: `∫ b(x) (u ∘ ψ)(x) |ψ'(x)|² 1_U(x) dx = ∫ b(φ(w)) u(w) dw`. -/
theorem IsInverseChart.integral_mul_chartTestFun (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (b u : ℂ → ℝ)
    (hu : tsupport u ⊆ ball (0 : ℂ) 1) :
    ∫ x, b x * chartTestFun U ψ u x = ∫ w, b (chartMap U ψ w) * u w := by
  have hinj : InjOn ψ U := hψ.injOn.mono subset_closure
  have hderiv : ∀ x ∈ U, HasFDerivWithinAt ψ (fderiv ℝ ψ x) U x := fun x hx =>
    ((hψ.differentiableOn.differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have h1 : ∫ x, b x * chartTestFun U ψ u x = ∫ x in U, b x * (u (ψ x) * ‖deriv ψ x‖ ^ 2) := by
    rw [← integral_indicator hU.measurableSet]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    unfold chartTestFun
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero]
  have h2 : ∫ w, b (chartMap U ψ w) * u w = ∫ w in ball (0 : ℂ) 1, b (chartMap U ψ w) * u w :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hw (hu h), mul_zero]).symm
  rw [h1, h2, ← hψ.image_eq,
    integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hU.measurableSet hderiv hinj]
  refine setIntegral_congr_fun hU.measurableSet fun x hx => ?_
  have hd : DifferentiableAt ℂ ψ x := hψ.differentiableOn.differentiableAt (hU.mem_nhds hx)
  simp only [smul_eq_mul]
  rw [QuantumZipper.abs_det_fderiv_eq_normSq hd, hψ.chartMap_apply hx]
  ring

end MatedCRT
