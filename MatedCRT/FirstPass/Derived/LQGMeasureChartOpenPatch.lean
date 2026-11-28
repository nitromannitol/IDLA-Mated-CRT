import MatedCRT.FirstPass.Derived.LQGMeasureChartDiscProperty
import MatedCRT.FirstPass.Derived.LQGMeasureChartOpenProperty

/-!
# Patching the coordinate change of the LQG measure from rational discs to open sets

If a field `h` has the chart property (`ChartProp`) with the measure `μ` on every disc with rational centre and radius
avoiding the cone point `0`, and on every disc centred at `0` with rational radius, then it has it on every open set
(`OpenChartProp`): for every open `V` and every conformal map `ψ` from `V` onto a bounded open set, the smooth
approximations of `h ∘ φ + Q log |φ'|` on `ψ(V)` (Sheffield–Wang, arXiv:1605.06171v2, (1.6) and §3.2) converge vaguely
in `ψ(V)` along `2^{-k}` to `ψ_*(μ|_V)`. This is the patching part of the first localization step of the coordinate
change of the LQG measure for all inverse charts: the sets `ψ(B)` of the rational discs `B ⊆ V` cover `ψ(V)`, so a
finite partition of unity on the support of each test function gives the limit on `ψ(V)`.

* `pullbackPairing_eq_pullbackPairingOn`: on functions supported in `ψ(B)` for a disc `B ⊆ V`, the pairings of the
  pulled-back field on the disc and on `V` agree (locality of the transported test functions; the inverses of `ψ` on
  `B` and on `V` agree on `ψ(B)`).
* `continuousAt_pairFun_transport`, `smoothApprox_pullbackPairingOn_lt_top`: the smoothed pulled-back field is
  continuous in the centre (the transported translates form a continuous family of test functions, through a smooth
  cutoff), so the smooth approximations on `ψ(V)` are eventually finite on the compact subsets of `ψ(V)`.
* `openChartProp_of_chartProp`: the patching theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT

namespace LQGMeasureChart

open LQGMetric

/-! ## Inverses of injective holomorphic maps -/

/-- An injective holomorphic map `ψ` on an open set `V` has a continuous inverse `φ` on `ψ(V)`. -/
theorem exists_inverse_of_injOn_isOpen {V : Set ℂ} (hV : IsOpen V) {ψ : ℂ → ℂ} (hinj : InjOn ψ V)
    (hψ : DifferentiableOn ℂ ψ V) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (ψ '' V) ∧ MapsTo φ (ψ '' V) V ∧ ∀ x ∈ V, φ (ψ x) = x :=
  ⟨(QuantumZipper.CA.univalentOPH hV hψ hinj).symm,
    (QuantumZipper.CA.univalentOPH hV hψ hinj).continuousOn_symm,
    fun _ hw => (QuantumZipper.CA.univalentOPH hV hψ hinj).map_target hw,
    fun _ hx => QuantumZipper.CA.univalentOPH_symm_apply_apply hV hψ hinj hx⟩

/-- The inverses of `ψ` on `B ⊆ V` and on `V` agree on `ψ(B)`. -/
theorem invFunOn_eq_of_subset {V B : Set ℂ} {ψ : ℂ → ℂ} (hinj : InjOn ψ V) (hBV : B ⊆ V) {w : ℂ}
    (hw : w ∈ ψ '' B) : Function.invFunOn ψ B w = Function.invFunOn ψ V w := by
  have h1 := Function.invFunOn_pos hw
  have h2 := Function.invFunOn_pos (image_mono hBV hw)
  exact hinj (hBV h1.1) h2.1 (h1.2.trans h2.2.symm)

/-- `log |φ'|` for the inverse `φ` of an injective holomorphic map on an open set `V` is bounded on the compact subsets
of `ψ(V)`. -/
theorem exists_bound_log_deriv_invFunOn {V : Set ℂ} (hV : IsOpen V) {ψ : ℂ → ℂ} (hinj : InjOn ψ V)
    (hψ : DifferentiableOn ℂ ψ V) {L : Set ℂ} (hL : IsCompact L) (hLW : L ⊆ ψ '' V) :
    ∃ M : ℝ, ∀ w ∈ L, |Real.log ‖deriv (Function.invFunOn ψ V) w‖| ≤ M := by
  set e := QuantumZipper.CA.univalentOPH hV hψ hinj with he
  have hWo : IsOpen (ψ '' V) := QuantumZipper.CA.isOpen_image_of_injOn' hV hψ hinj
  have hinv : ∀ w ∈ ψ '' V, Function.invFunOn ψ V w = e.symm w := fun w hw => by
    have h1 := Function.invFunOn_pos hw
    exact hinj h1.1 (e.map_target hw)
      (h1.2.trans (QuantumZipper.CA.univalentOPH_apply_symm_apply hV hψ hinj hw).symm)
  have hder : ∀ w ∈ ψ '' V, deriv (Function.invFunOn ψ V) w = (deriv ψ (e.symm w))⁻¹ := fun w hw => by
    rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hWo.mem_nhds hw) hinv)]
    exact (QuantumZipper.CA.hasDerivAt_univalentOPH_symm hV hψ hinj hw).deriv
  have hne : ∀ w ∈ ψ '' V, deriv ψ (e.symm w) ≠ 0 := fun w hw =>
    QuantumZipper.CA.deriv_ne_zero_of_injOn hV hψ hinj (e.map_target hw)
  have hdc : ContinuousOn (fun w => deriv ψ (e.symm w)) (ψ '' V) :=
    ((hψ.analyticOnNhd hV).deriv.continuousOn).comp e.continuousOn_symm fun w hw => e.map_target hw
  have hc : ContinuousOn (fun w => Real.log ‖(deriv ψ (e.symm w))⁻¹‖) (ψ '' V) :=
    ((hdc.inv₀ hne).norm).log fun w hw => norm_ne_zero_iff.2 (inv_ne_zero (hne w hw))
  have hc' : ContinuousOn (fun w => Real.log ‖deriv (Function.invFunOn ψ V) w‖) (ψ '' V) :=
    hc.congr fun w hw => by simp only [hder w hw]
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn (hc'.mono hLW)
  exact ⟨M, fun w hw => by simpa only [Real.norm_eq_abs] using hM w hw⟩

/-! ## Locality of the pulled-back field -/

/-- **Locality of the pulled-back field.** For a disc `B = B(c, r) ⊆ V` and `ψ` injective holomorphic on `V`, the
pairings of `h|_B ∘ φ + Q log |φ'|` and of `h ∘ φ + Q log |φ'|` (on `ψ(V)`) agree on the translates `f_ε(z − ·)` with
`B̄_ε(z) ⊆ ψ(B)`. -/
theorem pullbackPairing_eq_pullbackPairingOn {γ : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) (h : DistC)
    {V : Set ℂ} {ψ : ℂ → ℂ} (hinj : InjOn ψ V) (hψ : DifferentiableOn ℂ ψ V) {c : ℂ} {r : ℝ}
    (hBV : ball c r ⊆ V) (hWBo : IsOpen (ψ '' ball c r)) {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : closedBall z ε ⊆ ψ '' ball c r) :
    pullbackPairing γ (restrictTo (disc c r) h) ψ (fun w => mollScale f ε (z - w)) =
      pullbackPairingOn γ h V ψ (fun w => mollScale f ε (z - w)) := by
  have hv0 : ∀ w, w ∉ closedBall z ε → mollScale f ε (z - w) = 0 := fun w hw =>
    image_eq_zero_of_notMem_tsupport (f := fun w => mollScale f ε (z - w)) (x := w) fun h' =>
      hw (ball_subset_closedBall (tsupport_mollScale_sub_subset hf hε z h'))
  obtain ⟨φB, hφBc, hφBm, hφBψ⟩ := exists_inverse_of_injOn (hinj.mono hBV) (hψ.mono hBV)
  have hadm := transport_admissible (hψ.mono hBV) hφBc hφBm hφBψ (contDiff_mollScale_sub_left hf ε z)
    (isCompact_closedBall z ε) hz hv0
  have hind : (V.indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2) =
      (ball c r).indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2 := by
    funext x
    by_cases hxB : x ∈ ball c r
    · rw [indicator_of_mem hxB, indicator_of_mem (hBV hxB)]
    · rw [indicator_of_notMem hxB]
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem hxV]
        have h0 : mollScale f ε (z - ψ x) = 0 := hv0 _ fun hzx => by
          obtain ⟨y, hyB, hyx⟩ := hz hzx
          exact hxB (hinj (hBV hyB) hxV hyx ▸ hyB)
        rw [h0, zero_mul]
      · exact indicator_of_notMem hxV _
  let ψC : TestC := ⟨(ball c r).indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2, hadm.1,
    hadm.2.1, fun _ _ => trivial⟩
  have hp1 : pairFun (restrictTo (disc c r) h)
      ((ball c r).indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2) = h ψC := by
    refine (dite_eq_left hadm).trans ?_
    exact restrictTo_apply_eq_of_coe h _ ψC fun _ => rfl
  have hp2 : pairFun (V := ⊤) h
      ((ball c r).indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2) = h ψC :=
    dite_eq_left ⟨hadm.1, hadm.2.1, fun _ _ => trivial⟩
  have hlog : ∫ w, Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖ * mollScale f ε (z - w) =
      ∫ w, Real.log ‖deriv (Function.invFunOn ψ V) w‖ * mollScale f ε (z - w) := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    by_cases hw : w ∈ closedBall z ε
    · show Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖ * mollScale f ε (z - w) =
        Real.log ‖deriv (Function.invFunOn ψ V) w‖ * mollScale f ε (z - w)
      rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hWBo.mem_nhds (hz hw))
        fun w' hw' => invFunOn_eq_of_subset hinj hBV hw')]
    · show Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖ * mollScale f ε (z - w) =
        Real.log ‖deriv (Function.invFunOn ψ V) w‖ * mollScale f ε (z - w)
      rw [hv0 w hw, mul_zero, mul_zero]
  show pairFun (restrictTo (disc c r) h)
      ((ball c r).indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2) +
      (2 / γ + γ / 2) * ∫ w, Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖ * mollScale f ε (z - w) =
    pairFun (V := ⊤) h (V.indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2) +
      (2 / γ + γ / 2) * ∫ w, Real.log ‖deriv (Function.invFunOn ψ V) w‖ * mollScale f ε (z - w)
  rw [hind, hp1, hp2, hlog]

/-! ## Continuity of the smoothed pulled-back field and finiteness of the approximations -/

/-- **Continuity of the smoothed pulled-back field in the centre.** For `ψ` injective holomorphic on the open set `V`
and `B̄(z₀, ε + δ) ⊆ ψ(V)`, the pairing of `h` with the transported translate `1_V f_ε(z − ψ(·)) |ψ'|²` is continuous in
`z` at `z₀`: through a smooth cutoff equal to `1` on `φ(B̄(z₀, ε + δ))`, the transported translates with
`z ∈ B̄(z₀, δ)` form a continuous family of test functions supported in a fixed compact subset of `V`. -/
theorem continuousAt_pairFun_transport {V : Set ℂ} (hV : IsOpen V) {ψ : ℂ → ℂ} (hinj : InjOn ψ V)
    (hψ : DifferentiableOn ℂ ψ V) (h : DistC) {f : ℂ → ℝ} (hf : IsMollifier f) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) {z₀ : ℂ} (hz₀ : closedBall z₀ (ε + δ) ⊆ ψ '' V) :
    ContinuousAt (fun z => pairFun (V := ⊤) h (V.indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2))
      z₀ := by
  obtain ⟨φ, hφc, hφm, hφψ⟩ := exists_inverse_of_injOn_isOpen hV hinj hψ
  set L : Set ℂ := closedBall z₀ (ε + δ) with hLdef
  have hKc : IsCompact (φ '' L) := (isCompact_closedBall _ _).image_of_continuousOn (hφc.mono hz₀)
  have hKV : φ '' L ⊆ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact hφm (hz₀ hw)
  obtain ⟨δ₂, hδ₂, hsub⟩ := hKc.exists_cthickening_subset_open hV hKV
  have hclV : closure (thickening δ₂ (φ '' L)) ⊆ V :=
    (closure_thickening_subset_cthickening δ₂ _).trans hsub
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    isOpen_thickening hKc.isClosed (self_subset_thickening hδ₂ (φ '' L))
  have hm : ContDiff ℝ (⊤ : ℕ∞) (mollScale f ε) := by
    show ContDiff ℝ (⊤ : ℕ∞) fun v => (ε ^ 2)⁻¹ * f (v / (ε : ℂ))
    exact contDiff_const.mul (hf.contDiff.comp (contDiff_id.div_const (ε : ℂ)))
  -- the smooth family
  let Φ : ℂ → ℂ → ℝ := fun z y => χ y * (mollScale f ε (z - ψ y) * ‖deriv ψ y‖ ^ 2)
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ) := by
    rw [contDiff_iff_contDiffAt]
    rintro ⟨z, y⟩
    by_cases hy : y ∈ V
    · have hA : AnalyticAt ℂ ψ y := hψ.analyticAt (hV.mem_nhds hy)
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) ψ y := hA.contDiffAt.restrict_scalars ℝ
      have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (deriv ψ) y := hA.deriv.contDiffAt.restrict_scalars ℝ
      show ContDiffAt ℝ (⊤ : ℕ∞)
        (fun p : ℂ × ℂ => χ p.2 * (mollScale f ε (p.1 - ψ p.2) * ‖deriv ψ p.2‖ ^ 2)) (z, y)
      exact (hχ.contDiffAt.comp (z, y) contDiffAt_snd).mul
        ((hm.contDiffAt.comp (z, y) (contDiffAt_fst.sub (h1.comp (z, y) contDiffAt_snd))).mul
          ((contDiff_norm_sq ℝ).contDiffAt.comp (z, y) (h2.comp (z, y) contDiffAt_snd)))
    · have hyN : y ∉ closure (thickening δ₂ (φ '' L)) := fun h' => hy (hclV h')
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.isOpen_preimage _ isClosed_closure.isOpen_compl).mem_nhds
        (show ((z, y) : ℂ × ℂ) ∈ Prod.snd ⁻¹' (closure (thickening δ₂ (φ '' L)))ᶜ from hyN)] with p hp
      have hχ0 : χ p.2 = 0 := by
        by_contra hne
        have hmem : p.2 ∈ Function.support χ := hne
        rw [hχs] at hmem
        exact hp (subset_closure hmem)
      show χ p.2 * (mollScale f ε (p.1 - ψ p.2) * ‖deriv ψ p.2‖ ^ 2) = 0
      rw [hχ0, zero_mul]
  -- the family vanishes off `φ(L)` for centres in `B̄(z₀, δ)`
  have hzero : ∀ x ∈ closedBall z₀ δ, ∀ y, y ∉ φ '' L → V.indicator
      (fun y => mollScale f ε (x - ψ y) * ‖deriv ψ y‖ ^ 2) y = 0 ∧ Φ x y = 0 := by
    intro x hx y hy
    have hm0 : y ∈ V → mollScale f ε (x - ψ y) = 0 := fun hyV => by
      by_contra hne
      have h1 : ψ y ∈ ball x ε :=
        tsupport_mollScale_sub_subset hf hε x (subset_tsupport _ (show ψ y ∈ Function.support
          (fun w => mollScale f ε (x - w)) from hne))
      have h2 : ψ y ∈ L := by
        rw [hLdef, mem_closedBall]
        rw [mem_ball] at h1
        rw [mem_closedBall] at hx
        linarith [dist_triangle (ψ y) x z₀]
      exact hy ⟨ψ y, h2, hφψ y hyV⟩
    constructor
    · by_cases hyV : y ∈ V
      · rw [indicator_of_mem hyV, hm0 hyV, zero_mul]
      · exact indicator_of_notMem hyV _
    · show χ y * (mollScale f ε (x - ψ y) * ‖deriv ψ y‖ ^ 2) = 0
      by_cases hyV : y ∈ V
      · rw [hm0 hyV, zero_mul, mul_zero]
      · have hχ0 : χ y = 0 := by
          by_contra hne
          have hmem : y ∈ Function.support χ := hne
          rw [hχs] at hmem
          exact hyV (hclV (subset_closure hmem))
        rw [hχ0, zero_mul]
  have hagree : ∀ x ∈ closedBall z₀ δ,
      (V.indicator fun y => mollScale f ε (x - ψ y) * ‖deriv ψ y‖ ^ 2) = Φ x := by
    intro x hx
    funext y
    by_cases hyK : y ∈ φ '' L
    · rw [indicator_of_mem (hKV hyK)]
      show mollScale f ε (x - ψ y) * ‖deriv ψ y‖ ^ 2 = χ y * (mollScale f ε (x - ψ y) * ‖deriv ψ y‖ ^ 2)
      rw [(hχ1 y).1 hyK, one_mul]
    · rw [(hzero x hx y hyK).1, (hzero x hx y hyK).2]
  -- the continuous family of test functions
  let X := closedBall z₀ δ
  have : CompactSpace X := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let K : TopologicalSpace.Compacts ℂ := ⟨φ '' L, hKc⟩
  let Ψ : X → ℂ → ℝ := fun x y => Φ x y
  have hs : ∀ x : X, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ x) := fun x =>
    hΦ.comp (contDiff_const.prodMk contDiff_id)
  have hK : ∀ x : X, ∀ y ∉ (K : Set ℂ), Ψ x y = 0 := fun x y hy => (hzero x x.2 y hy).2
  have hD : ∀ i : ℕ, Continuous fun p : X × ℂ => iteratedFDeriv ℝ i (Ψ p.1) p.2 := fun i =>
    (LQGMetric.continuous_iteratedFDeriv_snd hΦ i).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hc := LQGMetric.continuous_testFamK K Ψ hs hK hD
  let T : X → TestC := fun x =>
    TestFunction.ofSupportedIn (show (K : Set ℂ) ⊆ ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) from fun _ _ => trivial)
      (LQGMetric.testFamK K Ψ hs hK x)
  have hTc : Continuous T := (TestFunction.continuous_ofSupportedIn _).comp hc
  have heq : ∀ x : X, pairFun (V := ⊤) h
      (V.indicator fun y => mollScale f ε ((x : ℂ) - ψ y) * ‖deriv ψ y‖ ^ 2) = h (T x) := by
    intro x
    rw [hagree x x.2]
    exact (dite_eq_left ⟨(T x).contDiff, (T x).hasCompactSupport, (T x).tsupport_subset⟩).trans rfl
  have h2 : Continuous fun x : X => pairFun (V := ⊤) h
      (V.indicator fun y => mollScale f ε ((x : ℂ) - ψ y) * ‖deriv ψ y‖ ^ 2) :=
    ((map_continuous h).comp hTc).congr fun x => (heq x).symm
  exact ((continuousOn_iff_continuous_domRestrict (f := fun z => pairFun (V := ⊤) h
    (V.indicator fun y => mollScale f ε (z - ψ y) * ‖deriv ψ y‖ ^ 2)) (s := X)).2 h2).continuousAt
    (closedBall_mem_nhds _ hδ)

/-- **The smooth approximations on `ψ(V)` are eventually finite on compact subsets of `ψ(V)`.** -/
theorem smoothApprox_pullbackPairingOn_lt_top {γ : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) {V : Set ℂ}
    (hV : IsOpen V) {ψ : ℂ → ℂ} (hinj : InjOn ψ V) (hψ : DifferentiableOn ℂ ψ V) (h : DistC) {K : Set ℂ}
    (hK : IsCompact K) (hKW : K ⊆ ψ '' V) :
    ∀ᶠ k in atTop, smoothApprox γ f (ψ '' V) (pullbackPairingOn γ h V ψ) (HarmonicBalls.dyadicScale k) K < ⊤ := by
  classical
  have hWo : IsOpen (ψ '' V) := QuantumZipper.CA.isOpen_image_of_injOn' hV hψ hinj
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hWo hKW
  obtain ⟨M₂, hM₂⟩ := exists_bound_log_deriv_invFunOn hV hinj hψ (hK.cthickening (r := δ)) hsub
  filter_upwards [tendsto_dyadicScale_nhds_zero.eventually (gt_mem_nhds (half_pos hδ))] with k hk
  set ε := HarmonicBalls.dyadicScale k with hεdef
  have hε : 0 < ε := HarmonicBalls.dyadicScale_pos k
  have hball : ∀ z ∈ K, closedBall z (ε + δ / 2) ⊆ ψ '' V := fun z hz =>
    ((closedBall_subset_closedBall (by linarith)).trans (closedBall_subset_cthickening hz δ)).trans hsub
  have hcont : ContinuousOn (fun z => pairFun (V := ⊤) h
      (V.indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2)) K := fun z hz =>
    (continuousAt_pairFun_transport hV hinj hψ h hf hε (half_pos hδ) (hball z hz)).continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn hcont
  set B : ℝ := |γ| * (|M₁| + |2 / γ + γ / 2| * |M₂|) + γ ^ 2 / 2 * (Real.log ε + mollConst f) with hB
  have hdens : ∀ z ∈ K, (if closedBall z ε ⊆ ψ '' V then
      ENNReal.ofReal (Real.exp (smoothExponent γ f (pullbackPairingOn γ h V ψ) ε z)) else 0) ≤
      ENNReal.ofReal (Real.exp B) := by
    intro z hz
    have hzε : closedBall z ε ⊆ ψ '' V :=
      (closedBall_subset_closedBall (by linarith)).trans (hball z hz)
    rw [ite_eq_left hzε]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : |pairFun (V := ⊤) h (V.indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2)| ≤ |M₁| := by
      have h1' := hM₁ z hz
      rw [Real.norm_eq_abs] at h1'
      exact h1'.trans (le_abs_self M₁)
    have h2 : |∫ w, Real.log ‖deriv (Function.invFunOn ψ V) w‖ * mollScale f ε (z - w)| ≤ |M₂| := by
      have hint : Integrable fun w => |M₂| * mollScale f ε (z - w) :=
        ((continuous_mollScale hf ε).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
          (hasCompactSupport_mollScale_sub hf hε z) |>.const_mul _
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le hint (ae_of_all _ fun w => ?_)).trans (le_of_eq ?_)
      · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mollScale_nonneg hf ε _)]
        by_cases hw : w ∈ closedBall z ε
        · exact mul_le_mul_of_nonneg_right ((hM₂ w (closedBall_subset_cthickening hz δ
            ((closedBall_subset_closedBall (by linarith)) hw))).trans (le_abs_self M₂))
            (mollScale_nonneg hf ε _)
        · have h0 : mollScale f ε (z - w) = 0 :=
            image_eq_zero_of_notMem_tsupport (f := fun w => mollScale f ε (z - w)) (x := w) fun h' =>
              hw (ball_subset_closedBall (tsupport_mollScale_sub_subset hf hε z h'))
          rw [h0, mul_zero, mul_zero]
      · rw [integral_const_mul, integral_mollScale_sub hf hε z, mul_one]
    show γ * pullbackPairingOn γ h V ψ (fun w => mollScale f ε (z - w)) +
        γ ^ 2 / 2 * (Real.log ε + mollConst f) ≤ B
    have hG : pullbackPairingOn γ h V ψ (fun w => mollScale f ε (z - w)) =
        pairFun (V := ⊤) h (V.indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2) +
          (2 / γ + γ / 2) * ∫ w, Real.log ‖deriv (Function.invFunOn ψ V) w‖ * mollScale f ε (z - w) := rfl
    have h3 : γ * pullbackPairingOn γ h V ψ (fun w => mollScale f ε (z - w)) ≤
        |γ| * (|M₁| + |2 / γ + γ / 2| * |M₂|) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, hG]
      refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 ?_)) (abs_nonneg γ)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    rw [hB]
    linarith
  unfold smoothApprox
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, (if closedBall z ε ⊆ ψ '' V then
        ENNReal.ofReal (Real.exp (smoothExponent γ f (pullbackPairingOn γ h V ψ) ε z)) else 0)
      ≤ ∫⁻ _ in K, ENNReal.ofReal (Real.exp B) :=
        lintegral_mono_ae ((ae_restrict_iff' hK.measurableSet).2 (ae_of_all _ hdens))
    _ = ENNReal.ofReal (Real.exp B) * volume K := by
        rw [lintegral_const, Measure.restrict_apply_univ]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-! ## Rational discs -/

/-- Every point of an open set lies in a disc inside the set on which the chart property holds: a rational disc
avoiding `0` for points other than `0`, a disc centred at `0` with rational radius for `0`. -/
theorem exists_disc_chartProp {γ : ℝ} {f : ℂ → ℝ} {h : DistC} {μ : Measure ℂ}
    (h1 : ∀ (a b r : ℚ), 0 < r → (0 : ℂ) ∉ closedBall ((a : ℂ) + (b : ℂ) * Complex.I) r →
      ChartProp γ f ((a : ℂ) + (b : ℂ) * Complex.I) r h μ)
    (h2 : ∀ r : ℚ, 0 < r → ChartProp γ f 0 r h μ) {V : Set ℂ} (hV : IsOpen V) {x : ℂ} (hx : x ∈ V) :
    ∃ (c : ℂ) (r : ℝ), x ∈ ball c r ∧ ball c r ⊆ V ∧ ChartProp γ f c r h μ := by
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV x hx
  by_cases hx0 : x = 0
  · subst hx0
    obtain ⟨ρ, hρ0, hρε⟩ := exists_rat_btwn hε
    exact ⟨0, ρ, mem_ball_self (by exact_mod_cast hρ0),
      (ball_subset_ball hρε.le).trans hεV, h2 ρ (by exact_mod_cast hρ0)⟩
  · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hm : 0 < min ε ‖x‖ / 3 := by positivity
    obtain ⟨ρ, hρ0, hρm⟩ := exists_rat_btwn hm
    have hρq : (0 : ℚ) < ρ := by exact_mod_cast hρ0
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x.re - ρ / 2 < x.re + ρ / 2 by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x.im - ρ / 2 < x.im + ρ / 2 by linarith)
    have hcx : ‖((a : ℂ) + (b : ℂ) * Complex.I) - x‖ < ρ := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
      have hre : (((a : ℂ) + (b : ℂ) * Complex.I) - x).re = (a : ℝ) - x.re := by simp
      have him : (((a : ℂ) + (b : ℂ) * Complex.I) - x).im = (b : ℝ) - x.im := by simp
      rw [hre, him]
      have h3 : |(a : ℝ) - x.re| < ρ / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
      have h4 : |(b : ℝ) - x.im| < ρ / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
      linarith
    have hmin1 : min ε ‖x‖ ≤ ε := min_le_left _ _
    have hmin2 : min ε ‖x‖ ≤ ‖x‖ := min_le_right _ _
    refine ⟨(a : ℂ) + (b : ℂ) * Complex.I, ρ, ?_, ?_, h1 a b ρ hρq ?_⟩
    · rw [mem_ball, dist_eq_norm, norm_sub_rev]
      exact hcx
    · intro y hy
      apply hεV
      rw [mem_ball] at hy ⊢
      have := dist_triangle y ((a : ℂ) + (b : ℂ) * Complex.I) x
      rw [dist_eq_norm ((a : ℂ) + (b : ℂ) * Complex.I) x] at this
      linarith
    · intro h0
      rw [mem_closedBall, dist_zero_left] at h0
      have := norm_sub_norm_le x ((a : ℂ) + (b : ℂ) * Complex.I)
      rw [norm_sub_rev] at this
      linarith

/-! ## The patching theorem -/

/-- **Patching the chart property from rational discs to open sets.** Let `μ` be finite on compact sets and let the
field `h` have the chart property with `μ` on every disc with rational centre and radius whose closure avoids `0`, and
on every disc centred at `0` with rational radius. Then `h` has the chart property with `μ` on every open set: the
smooth approximations of `h ∘ φ + Q log |φ'|` on `ψ(V)` converge vaguely in `ψ(V)` to `ψ_*(μ|_V)`. -/
theorem openChartProp_of_chartProp {γ : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) {h : DistC} {μ : Measure ℂ}
    (hμ : ∀ K, IsCompact K → μ K < ⊤)
    (h1 : ∀ (a b r : ℚ), 0 < r → (0 : ℂ) ∉ closedBall ((a : ℂ) + (b : ℂ) * Complex.I) r →
      ChartProp γ f ((a : ℂ) + (b : ℂ) * Complex.I) r h μ)
    (h2 : ∀ r : ℚ, 0 < r → ChartProp γ f 0 r h μ) : OpenChartProp γ f h μ := by
  intro V hV ψ hinj hψ hbdd
  have hWo : IsOpen (ψ '' V) := QuantumZipper.CA.isOpen_image_of_injOn' hV hψ hinj
  have hVm : MeasurableSet V := hV.measurableSet
  have hψae : AEMeasurable ψ (μ.restrict V) := hψ.continuousOn.aemeasurable hVm
  obtain ⟨φ, hφc, -, hφψ⟩ := exists_inverse_of_injOn_isOpen hV hinj hψ
  have hνA : ∀ A, MeasurableSet A → ((μ.restrict V).map ψ) A = μ (V ∩ ψ ⁻¹' A) := fun A hA => by
    rw [Measure.map_apply_of_aemeasurable hψae hA, Measure.restrict_apply' hVm, Set.inter_comm]
  refine ⟨(μ.restrict V).map ψ, isVagueLimitOn_of_forall_mem_isVagueLimitOn_restrict ?_ ?_ ?_
    (fun K hK hKW => smoothApprox_pullbackPairingOn_lt_top hf hV hinj hψ h hK hKW),
    fun A hA _ => hνA A hA⟩
  · -- the limits on the images of the rational discs
    rintro _ ⟨x₀, hx₀V, rfl⟩
    obtain ⟨c, r, hx₀B, hBV, hCP⟩ := exists_disc_chartProp h1 h2 hV hx₀V
    obtain ⟨νB, hνB, hνBA⟩ := hCP ψ (hinj.mono hBV) (hψ.mono hBV) (hbdd.subset (image_mono hBV))
    have hWBo : IsOpen (ψ '' ball c r) :=
      QuantumZipper.CA.isOpen_image_of_injOn hV hψ hinj isOpen_ball hBV
    refine ⟨ψ '' ball c r, hWBo, mem_image_of_mem ψ hx₀B, image_mono hBV, ?_⟩
    have hrB : νB.restrict (ψ '' ball c r) = νB :=
      Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hνB.1)
    have heqν : νB = ((μ.restrict V).map ψ).restrict (ψ '' ball c r) := by
      ext s hs
      have hpre : ball c r ∩ ψ ⁻¹' (s ∩ ψ '' ball c r) = V ∩ ψ ⁻¹' (s ∩ ψ '' ball c r) := by
        ext x
        constructor
        · rintro ⟨hxB, hxs⟩
          exact ⟨hBV hxB, hxs⟩
        · rintro ⟨hxV, hxs, y, hyB, hyx⟩
          exact ⟨hinj (hBV hyB) hxV hyx ▸ hyB, hxs, y, hyB, hyx⟩
      rw [← hrB, Measure.restrict_apply hs, Measure.restrict_apply hs,
        hνBA _ (hs.inter hWBo.measurableSet) inter_subset_right, hνA _ (hs.inter hWBo.measurableSet), hpre]
    rw [← heqν]
    refine isVagueLimitOn_of_eventually_restrict_eq hνB fun K hK hKB => ?_
    obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hWBo hKB
    filter_upwards [tendsto_dyadicScale_nhds_zero.eventually (gt_mem_nhds hδ)] with k hk
    have hball : ∀ z ∈ K, closedBall z (HarmonicBalls.dyadicScale k) ⊆ ψ '' ball c r := fun z hz w hw =>
      hsub (mem_cthickening_of_dist_le w z δ K hz ((mem_closedBall.1 hw).trans hk.le))
    exact (smoothApprox_restrict_eq_of_subset (image_mono hBV) hK.measurableSet hball fun z hz =>
      pullbackPairing_eq_pullbackPairingOn hf h hinj hψ hBV hWBo (HarmonicBalls.dyadicScale_pos k)
        (hball z hz)).symm
  · -- the limit is concentrated on `ψ(V)`
    rw [hνA _ hWo.measurableSet.compl]
    exact measure_mono_null (fun x hx => (hx.2 (mem_image_of_mem ψ hx.1)).elim) measure_empty
  · -- the limit is finite on compact subsets of `ψ(V)`
    intro K hK hKW
    rw [hνA K hK.measurableSet]
    refine (measure_mono fun x hx => ?_).trans_lt (hμ _ (hK.image_of_continuousOn (hφc.mono hKW)))
    exact ⟨ψ x, hx.2, hφψ x hx.1⟩

end LQGMeasureChart

end MatedCRT
