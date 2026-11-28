import MatedCRT.FirstPass.Derived.ZeroConePolygonalPhaseClock
import LatticeProb.Prob.DyadicCellMass

/-!
# Root squares of the area measure and its tilt by a bump

Let `q` be a dyadic system, compatible and off the grid at the origin, whose chain of squares `S_j` at the origin
exhausts the plane, and let `μ` be a measure finite on compact sets. The root square of mass `m` is the square
`S_{rootGen μ q m}` of the chain (`ZeroConeRoot.rootGen`).

* `rootGen_tiltArea_eq`: for a continuous nonnegative `g` with compact support, tilting `μ` by `e^g` adds the
  constant `D = ∫ (e^g - 1) dμ` to the masses of all squares of the chain containing the support of `g`, so tha
  `rootGen (e^g μ) q (m + D) = rootGen μ q m` for `m` large.
* `tendsto_volume_inter_rootSquare_div`: if `μ` has infinite total mass, then the root squares exhaust the plane
  as the mass `m` tends to infinity, so for a bounded set `K` the fraction of the root square covered by `K`
  tends to `0`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open LatticeProb.DyadicOffset (squareAt IsOffGrid IsCompatible squareAt_mono volume_squareAt isCompact_squareAt)

/-- The mass of the `j`-th square of the chain at the origin is the measure of that square. -/
theorem chainMass_eq {ν : Measure ℂ} (hν : ∀ K : Set ℂ, IsCompact K → ν K < ⊤) (q : ZeroConeRoot.DyCoord)
    (j : ℤ) : ZeroConeRoot.chainMass ν q j = ν (squareAt q.1 q.2.1 q.2.2 j 0) := by
  rw [ZeroConeRoot.chainMass, ZeroConeRoot.sqMass_eq hν, squareAt, Complex.zero_re, Complex.zero_im]

/-- The tilt of a measure finite on compact sets by a function bounded above is finite on compact sets. -/
theorem tiltArea_lt_top {g : ℂ → ℝ} {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] {M : ℝ}
    (hM : ∀ z, g z ≤ M) {K : Set ℂ} (hK : IsCompact K) : tiltArea g μ K < ⊤ :=
  lt_of_le_of_lt (tiltArea_le hM hK.measurableSet)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top)

/-- **Target 7.** Let `q` be a dyadic system, compatible and off the grid at the origin, whose chain of squares a
the origin eventually contains every ball, and `g ≥ 0` continuous with compact support. If `μ` is finite on compac
sets, then for every mass `m` at least the mass `m₀` of a square of the chain containing the support of `g`,
the root generation of `e^g μ` at mass `m + D`, `D = ∫ (e^g - 1) dμ`, is the root generation of `μ` at mass `m`. -/
theorem rootGen_tiltArea_eq {g : ℂ → ℝ} {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z)
    {q : ZeroConeRoot.DyCoord} (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2)
    (hw : IsOffGrid q.1 q.2.1 q.2.2 0)
    (hexh : ∀ R : ℝ, ∃ j : ℤ, Metric.closedBall (0 : ℂ) R ⊆ squareAt q.1 q.2.1 q.2.2 j 0) :
    ∃ m₀ : ℝ≥0∞, m₀ ≠ ⊤ ∧ ∀ m : ℝ≥0∞, m₀ ≤ m → m ≠ ⊤ →
      ZeroConeRoot.rootGen (tiltArea g μ) q (m + ENNReal.ofReal (∫ z, (Real.exp (g z) - 1) ∂μ)) =
        ZeroConeRoot.rootGen μ q m := by
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg
  have hMg : ∀ z, g z ≤ M := fun z => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM z)
  have hfinμ : ∀ K : Set ℂ, IsCompact K → μ K < ⊤ := fun K hK => hK.measure_lt_top
  have hfinν : ∀ K : Set ℂ, IsCompact K → tiltArea g μ K < ⊤ := fun K hK => tiltArea_lt_top hMg hK
  -- the function `e^g - 1`
  have hfc : Continuous fun z => Real.exp (g z) - 1 := by fun_prop
  have hfsupp : HasCompactSupport fun z => Real.exp (g z) - 1 := by
    refine HasCompactSupport.intro (K := tsupport g) hgc fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp
  have hfint : Integrable (fun z => Real.exp (g z) - 1) μ := hfc.integrable_of_hasCompactSupport hfsupp
  have hfnn : ∀ z, 0 ≤ Real.exp (g z) - 1 := fun z => sub_nonneg.2 (Real.one_le_exp (hg0 z))
  have hD : ENNReal.ofReal (∫ z, (Real.exp (g z) - 1) ∂μ) = ∫⁻ z, ENNReal.ofReal (Real.exp (g z) - 1) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hfint (ae_of_all _ hfnn)
  set D' : ℝ≥0∞ := ENNReal.ofReal (∫ z, (Real.exp (g z) - 1) ∂μ)
  have hD'top : D' ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the chain of squares at the origin
  have hmono : Monotone fun j : ℤ => squareAt q.1 q.2.1 q.2.2 j 0 := squareAt_mono h₁ h₂ hw
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨j₀, hj₀⟩ := hexh R
  have hsupp : ∀ j : ℤ, j₀ ≤ j → tsupport g ⊆ squareAt q.1 q.2.1 q.2.2 j 0 := fun j hj =>
    (hR.trans hj₀).trans (hmono hj)
  -- the tilted mass of the squares containing the suppor
  have hν : ∀ j : ℤ, j₀ ≤ j → ZeroConeRoot.chainMass (tiltArea g μ) q j = ZeroConeRoot.chainMass μ q j + D' := by
    intro j hj
    rw [chainMass_eq hfinν, chainMass_eq hfinμ]
    have hS : MeasurableSet (squareAt q.1 q.2.1 q.2.2 j 0) := (isCompact_squareAt j 0).measurableSe
    rw [tiltArea_apply g μ hS]
    have h1 : ∀ z, ENNReal.ofReal (Real.exp (g z)) = 1 + ENNReal.ofReal (Real.exp (g z) - 1) := by
      intro z
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (hfnn z)]
      congr 1
      ring
    simp_rw [h1]
    rw [lintegral_add_left measurable_const, setLIntegral_one, hD, setLIntegral_eq_of_support_subset]
    intro z hz
    apply hsupp j hj
    refine subset_tsupport g ?_
    intro hgz
    apply hz
    simp [hgz]
  have hmonoμ : ∀ j j' : ℤ, j ≤ j' → ZeroConeRoot.chainMass μ q j ≤ ZeroConeRoot.chainMass μ q j' := by
    intro j j' hjj
    rw [chainMass_eq hfinμ, chainMass_eq hfinμ]
    exact measure_mono (hmono hjj)
  have hmonoν : ∀ j j' : ℤ, j ≤ j' →
      ZeroConeRoot.chainMass (tiltArea g μ) q j ≤ ZeroConeRoot.chainMass (tiltArea g μ) q j' := by
    intro j j' hjj
    rw [chainMass_eq hfinν, chainMass_eq hfinν]
    exact measure_mono (hmono hjj)
  refine ⟨ZeroConeRoot.chainMass μ q j₀, ?_, fun m hm _ => ?_⟩
  · rw [chainMass_eq hfinμ]
    exact (hfinμ _ (isCompact_squareAt j₀ 0)).ne
  · unfold ZeroConeRoot.rootGen
    congr 1
    ext j
    simp only [mem_setOf_eq]
    rcases le_total j₀ j with hj | hj
    · rw [hν j hj]
      exact ENNReal.add_le_add_iff_right hD'top
    · refine ⟨fun _ => (hmonoμ j j₀ hj).trans hm, fun _ => ?_⟩
      calc ZeroConeRoot.chainMass (tiltArea g μ) q j ≤ ZeroConeRoot.chainMass (tiltArea g μ) q j₀ :=
            hmonoν j j₀ hj
        _ = ZeroConeRoot.chainMass μ q j₀ + D' := hν j₀ le_rfl
        _ ≤ m + D' := by gcongr

/-- The root generation tends to infinity with the mass, when the measure is finite on compact sets, has infinite
total mass, and the chain of squares at the origin exhausts the plane. -/
theorem tendsto_rootGen_nnreal {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμ : μ univ = ⊤)
    {q : ZeroConeRoot.DyCoord} (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2)
    (hw : IsOffGrid q.1 q.2.1 q.2.2 0)
    (hexh : ∀ R : ℝ, ∃ j : ℤ, Metric.closedBall (0 : ℂ) R ⊆ squareAt q.1 q.2.1 q.2.2 j 0) :
    Tendsto (fun m : ℝ≥0 => ZeroConeRoot.rootGen μ q (m : ℝ≥0∞)) atTop atTop := by
  have hfinμ : ∀ K : Set ℂ, IsCompact K → μ K < ⊤ := fun K hK => hK.measure_lt_top
  have hmono : Monotone fun j : ℤ => squareAt q.1 q.2.1 q.2.2 j 0 := squareAt_mono h₁ h₂ hw
  have hunion : (⋃ j : ℤ, squareAt q.1 q.2.1 q.2.2 j 0) = univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨j, hj⟩ := hexh ‖z‖
    exact mem_iUnion.2 ⟨j, hj (by simp)⟩
  have hlim : Tendsto (fun j : ℤ => ZeroConeRoot.chainMass μ q j) atTop (𝓝 ⊤) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion, hμ] at h
    refine h.congr fun j => ?_
    rw [chainMass_eq hfinμ]
    rfl
  have hbdd : ∀ m : ℝ≥0, BddAbove {j : ℤ | ZeroConeRoot.chainMass μ q j ≤ (m : ℝ≥0∞)} := by
    intro m
    obtain ⟨N, hN⟩ := eventually_atTop.1 (ENNReal.tendsto_nhds_top_iff_nnreal.1 hlim m)
    refine ⟨N, fun j hj => ?_⟩
    by_contra hjN
    exact absurd (hN j (not_le.1 hjN).le) (not_lt.2 hj)
  refine tendsto_atTop.2 fun J => eventually_atTop.2 ⟨(ZeroConeRoot.chainMass μ q J).toNNReal, fun m hm => ?_⟩
  have hfin : ZeroConeRoot.chainMass μ q J ≠ ⊤ := by
    rw [chainMass_eq hfinμ]
    exact (hfinμ _ (isCompact_squareAt J 0)).ne
  have hJ : ZeroConeRoot.chainMass μ q J ≤ (m : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal hfin]
    exact_mod_cast hm
  exact le_csSup (hbdd m) hJ

/-- **Target 8.** If `μ` is finite on compact sets with infinite total mass and the chain of squares at the origin
exhausts the plane, then for a bounded set `K` the fraction of the root square of mass `m` covered by `K` tends to
`0` as `m → ∞` through the nonnegative reals (in particular along `m = n + 1`, `n : ℕ`, see
`tendsto_volume_inter_rootSquare_div_nat`). -/
theorem tendsto_volume_inter_rootSquare_div {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμ : μ univ = ⊤)
    {q : ZeroConeRoot.DyCoord} (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2)
    (hw : IsOffGrid q.1 q.2.1 q.2.2 0)
    (hexh : ∀ R : ℝ, ∃ j : ℤ, Metric.closedBall (0 : ℂ) R ⊆ squareAt q.1 q.2.1 q.2.2 j 0)
    {K : Set ℂ} (hK : Bornology.IsBounded K) :
    Tendsto (fun m : ℝ≥0 =>
      volume (K ∩ squareAt q.1 q.2.1 q.2.2 (ZeroConeRoot.rootGen μ q (m : ℝ≥0∞)) 0) /
        volume (squareAt q.1 q.2.1 q.2.2 (ZeroConeRoot.rootGen μ q (m : ℝ≥0∞)) 0)) atTop (𝓝 0) := by
  have hroot := tendsto_rootGen_nnreal hμ h₁ h₂ hw hexh
  have hside : Tendsto (fun j : ℤ => ENNReal.ofReal ((2 : ℝ) ^ (q.1 + (j : ℝ)))) atTop (𝓝 ⊤) := by
    refine ENNReal.tendsto_ofReal_atTop.comp ?_
    refine (tendsto_rpow_atTop_of_base_gt_one 2 one_lt_two).comp ?_
    exact tendsto_atTop_add_const_left _ _ tendsto_intCast_atTop_atTop
  have hvol : Tendsto (fun j : ℤ => volume (squareAt q.1 q.2.1 q.2.2 j 0)) atTop (𝓝 ⊤) := by
    have h := ENNReal.Tendsto.mul hside (Or.inl ENNReal.top_ne_zero) hside (Or.inl ENNReal.top_ne_zero)
    rw [ENNReal.top_mul_top] at h
    refine h.congr fun j => ?_
    rw [volume_squareAt]
  have hinv : Tendsto (fun j : ℤ => (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_inv.tendsto ⊤).comp hvol
    rwa [ENNReal.inv_top] at h
  have hKfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hup : Tendsto (fun j : ℤ => volume K * (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hinv (Or.inr hKfin)
    rwa [mul_zero] at h
  have hratio : Tendsto (fun j : ℤ => volume (K ∩ squareAt q.1 q.2.1 q.2.2 j 0) /
      volume (squareAt q.1 q.2.1 q.2.2 j 0)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le _) fun j => ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_right' (measure_mono inter_subset_left) _
  exact hratio.comp hroo

/-- The case `m = n + 1`, `n : ℕ`, of `tendsto_volume_inter_rootSquare_div`. -/
theorem tendsto_volume_inter_rootSquare_div_nat {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    (hμ : μ univ = ⊤) {q : ZeroConeRoot.DyCoord} (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2)
    (hw : IsOffGrid q.1 q.2.1 q.2.2 0)
    (hexh : ∀ R : ℝ, ∃ j : ℤ, Metric.closedBall (0 : ℂ) R ⊆ squareAt q.1 q.2.1 q.2.2 j 0)
    {K : Set ℂ} (hK : Bornology.IsBounded K) :
    Tendsto (fun n : ℕ =>
      volume (K ∩ squareAt q.1 q.2.1 q.2.2 (ZeroConeRoot.rootGen μ q ((n : ℝ≥0∞) + 1)) 0) /
        volume (squareAt q.1 q.2.1 q.2.2 (ZeroConeRoot.rootGen μ q ((n : ℝ≥0∞) + 1)) 0)) atTop (𝓝 0) := by
  have h := (tendsto_volume_inter_rootSquare_div hμ h₁ h₂ hw hexh hK).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1) : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0)) atTop atTop)
  refine h.congr fun n => ?_
  simp [Function.comp]

end MatedCRT.ZeroConePolygonal
