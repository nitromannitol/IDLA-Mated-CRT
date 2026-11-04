import MatedCRT.Proofs.Sec2.LQGMeasureProperties.ConformalCovariance
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Locality

/-!
# Fact 2.2 II (locality of the LQG measure) from the locality of circle averages

`μ_h(U)` is the supremum of `∫ g_n dμ_h` over a fixed sequence of continuous functions `0 ≤ g_n ≤ 1` with compact
support in `U` which is eventually `1` at each point of `U` (Urysohn on a compact exhaustion of `U`;
`measure_eq_iSup_ofReal_integral`, Fatou). Each `∫ g dμ_h` is the limit of the circle average approximations
`∫ g(x) ε^{γ²/2} e^{γ h_ε(x)} dx` (eq:measure-lim), which for small `ε` only involve circles with closed disks in `U`.
These circle averages are a.s. `σ(h|_U)`-measurable (`ConeCircleAverageLocalityStep`) at the countably many dyadic
points, and the a.s. continuity of the circle average process gives a jointly measurable version
(`AnnulusLocality.gridVersion`, from the proof of Lemma 6.4).
-/

namespace MatedCRT.LQGMeasure

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls AnnulusLocality
open scoped ENNReal NNReal

/-- A fixed sequence of continuous functions `0 ≤ g_n ≤ 1` with compact support in an open `U`, eventually equal to `1`
at each point of `U` (Urysohn's lemma on the compact sets `F_n ∩ cl B_n`, `F_n` closed exhausting `U`). -/
theorem exists_approx_indicator {U : Set ℂ} (hU : IsOpen U) :
    ∃ g : ℕ → ℂ → ℝ, (∀ n, Continuous (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧ (∀ n, tsupport (g n) ⊆ U) ∧
      (∀ n x, 0 ≤ g n x ∧ g n x ≤ 1) ∧ ∀ x ∈ U, ∀ᶠ n in atTop, g n x = 1 := by
  obtain ⟨F, hFc, hFU, hFun, hFm⟩ := hU.exists_iUnion_isClosed
  have hK : ∀ n : ℕ, IsCompact (F n ∩ closedBall 0 n) := fun n =>
    (isCompact_closedBall (0 : ℂ) n).inter_left (hFc n)
  have hKU : ∀ n : ℕ, F n ∩ closedBall 0 n ⊆ U := fun n => inter_subset_left.trans (hFU n)
  have hL : ∀ n : ℕ, ∃ L, IsCompact L ∧ F n ∩ closedBall 0 n ⊆ interior L ∧ L ⊆ U := fun n =>
    exists_compact_between (hK n) hU (hKU n)
  choose L hLc hKL hLU using hL
  have hf : ∀ n : ℕ, ∃ f : C(ℂ, ℝ), EqOn f 1 (F n ∩ closedBall 0 n) ∧ EqOn f 0 (interior (L n))ᶜ ∧
      HasCompactSupport f ∧ ∀ x, f x ∈ Icc 0 1 := fun n =>
    exists_continuous_one_zero_of_isCompact (hK n) isOpen_interior.isClosed_compl
      (disjoint_compl_right_iff_subset.2 (hKL n))
  choose f hf1 hf0 hfc hf01 using hf
  refine ⟨fun n => f n, fun n => (f n).continuous, hfc, fun n => ?_, fun n x => hf01 n x, fun x hx => ?_⟩
  · show closure (Function.support (f n)) ⊆ U
    refine (closure_minimal (fun x hx => ?_) (hLc n).isClosed).trans (hLU n)
    by_contra hxL
    exact (Function.mem_support.1 hx) (hf0 n fun hi => hxL (interior_subset hi))
  · rw [← hFun, mem_iUnion] at hx
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := exists_nat_ge ‖x‖
    filter_upwards [eventually_ge_atTop (max N M)] with n hn
    refine hf1 n ⟨hFm (le_of_max_le_left hn) hN, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hM.trans (by exact_mod_cast le_of_max_le_right hn)

/-- **The mass of an open set from test functions.** For a locally finite `m` and functions `g_n` as in
`exists_approx_indicator`, `m(U) = sup_n ∫ g_n dm` (Fatou). -/
theorem measure_eq_iSup_ofReal_integral {m : Measure ℂ} [IsLocallyFiniteMeasure m] {U : Set ℂ} (hU : IsOpen U)
    {g : ℕ → ℂ → ℝ} (hgc : ∀ n, Continuous (g n)) (hgcs : ∀ n, HasCompactSupport (g n))
    (hgU : ∀ n, tsupport (g n) ⊆ U) (hg01 : ∀ n x, 0 ≤ g n x ∧ g n x ≤ 1)
    (hgt : ∀ x ∈ U, ∀ᶠ n in atTop, g n x = 1) :
    m U = ⨆ n, ENNReal.ofReal (∫ x, g n x ∂m) := by
  have hlin : ∀ n, ENNReal.ofReal (∫ x, g n x ∂m) = ∫⁻ x, ENNReal.ofReal (g n x) ∂m := fun n =>
    ofReal_integral_eq_lintegral_ofReal ((hgc n).integrable_of_hasCompactSupport (hgcs n))
      (Eventually.of_forall fun x => (hg01 n x).1)
  simp only [hlin]
  refine le_antisymm ?_ (iSup_le fun n => ?_)
  · calc m U = ∫⁻ x, U.indicator 1 x ∂m := (lintegral_indicator_one hU.measurableSet).symm
      _ ≤ ∫⁻ x, liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂m := lintegral_mono fun x => ?_
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂m) atTop :=
          lintegral_liminf_le fun n => (hgc n).measurable.ennreal_ofReal
      _ ≤ ⨆ n, ∫⁻ x, ENNReal.ofReal (g n x) ∂m := liminf_le_of_le (by isBoundedDefault) fun b hb => by
          obtain ⟨n, hn⟩ := hb.exists
          exact hn.trans (le_iSup (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂m) n)
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, Pi.one_apply]
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hgt x hx] with n hn
      rw [hn, ENNReal.ofReal_one]
    · rw [indicator_of_notMem hx]
      exact zero_le
  · calc ∫⁻ x, ENNReal.ofReal (g n x) ∂m ≤ ∫⁻ x, U.indicator 1 x ∂m := lintegral_mono fun x => ?_
      _ = m U := lintegral_indicator_one hU.measurableSet
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (hg01 n x).2
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hgU n h)),
        ENNReal.ofReal_zero]

/-- **One test function.** For `g` continuous with compact support in an open `U`, `∫ g dμ_h` is a.s. equal to a
`σ(h|_U)`-measurable random variable. -/
theorem ae_eq_integral_of_circleLocality {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (hD : ConeCircleAverageLocalityStep) {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    ∃ Y : Ω → ℝ, Measurable[fieldSigmaAlgebra 0 hC U] Y ∧ ∀ᵐ ω ∂P, ∫ u, g u ∂μ ω = Y ω := by
  have hPprob : IsProbabilityMeasure P := hcone.1
  have hcq : IsQuantumCone γ P hC hcirc := hcone.2.1
  obtain ⟨δ, hδ, hδU⟩ := IsCompact.exists_cthickening_subset_open hgc hU hgU
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (2 : ℝ)⁻¹ ^ k₀ < δ / 2 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  -- the scales `ε_k = 2^{-(k + k₀)}`
  set ε : ℕ → ℝ := fun k => dyadicScale (k + k₀) with hεdef
  have hε : ∀ k, 0 < ε k := fun k => dyadicScale_pos _
  have hεδ : ∀ k, ε k < δ / 2 := fun k => by
    simp only [hεdef, dyadicScale]
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left k₀ k)).trans_lt hk₀
  -- `σ(h|_U)`-measurable versions of the circle averages
  have hV : ∀ (k : ℕ) (p : ℂ), ∃ V : Ω → ℝ, Measurable[fieldSigmaAlgebra 0 hC U] V ∧
      (closedBall p (ε k) ⊆ U → (fun ω => hcirc ω (ε k) p) =ᵐ[P] V) := by
    intro k p
    by_cases hp : closedBall p (ε k) ⊆ U
    · obtain ⟨D, hDm, hDe⟩ := hD γ hγ hγ2 Ω P hC hcirc hPprob hcq U hU (ε k) p (hε k) hp
      exact ⟨D, hDm, fun _ => hDe⟩
    · exact ⟨fun _ => 0, measurable_const, fun h => absurd h hp⟩
  choose V hVm hVe using hV
  let I : ℕ → Ω → ℝ := fun k ω =>
    ∫ x, g x * ((ε k) ^ (γ ^ 2 / 2) * Real.exp (γ * gridVersion (V k) ω x))
  refine ⟨fun ω => limsup (fun k => I k ω) atTop, ?_, ?_⟩
  · exact measurable_limsup_of (m := fieldSigmaAlgebra 0 hC U) (I := I) (fun k =>
      measurable_integral_gridVersion (m := fieldSigmaAlgebra 0 hC U) (hVm k) hg _ _)
  -- the good event
  have h3 : ∀ᵐ ω ∂P, ∀ (k j : ℕ) (a : ℤ × ℤ), closedBall (gridPt j a) (ε k) ⊆ U →
      V k (gridPt j a) ω = hcirc ω (ε k) (gridPt j a) := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun j => ae_all_iff.2 fun a => ?_
    by_cases hp : closedBall (gridPt j a) (ε k) ⊆ U
    · filter_upwards [hVe k _ hp] with ω hω _
      exact hω.symm
    · exact Eventually.of_forall fun ω h => absurd h hp
  have hlqg : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
  filter_upwards [hlqg, ae_continuous_circle hcq, h3] with ω hlim hcont hgrid
  have hcx : ∀ k, Continuous fun x => hcirc ω (ε k) x := fun k => hcont _ (hε k)
  -- the version agrees with the circle averages on `tsupport g`
  have hver : ∀ k, ∀ x ∈ tsupport g, gridVersion (V k) ω x = hcirc ω (ε k) x := by
    intro k x hx
    have hq := tendsto_gridPt x
    have hev : ∀ᶠ j in atTop, hcirc ω (ε k) (gridPt j (gridIdx j x)) = V k (gridPt j (gridIdx j x)) ω := by
      have hsmall : ∀ᶠ j in atTop, dist (gridPt j (gridIdx j x)) x < δ / 2 :=
        (tendsto_iff_dist_tendsto_zero.1 hq).eventually (gt_mem_nhds (by positivity))
      filter_upwards [hsmall] with j hj
      refine (hgrid k j _ fun y hy => hδU ?_).symm
      refine mem_cthickening_of_dist_le y x δ _ hx ?_
      have := dist_triangle y (gridPt j (gridIdx j x)) x
      rw [mem_closedBall] at hy
      linarith [hεδ k]
    have ht : Tendsto (fun j => V k (gridPt j (gridIdx j x)) ω) atTop (𝓝 (hcirc ω (ε k) x)) :=
      Tendsto.congr' hev (((hcx k).tendsto x).comp hq)
    exact ht.limsup_eq
  -- the integrals of the version are the circle average approximations of `μ_h`
  have hI : ∀ k, I k ω = ∫ x, g x ∂(lqgApprox γ (hcirc ω) (ε k)) := by
    intro k
    rw [integral_lqgApprox (hε k).le (hcx k).measurable]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport g
    · simp only [hver k x hx]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
  have hlimk : Tendsto (fun k => I k ω) atTop (𝓝 (∫ x, g x ∂(μ ω))) :=
    Tendsto.congr (fun k => (hI k).symm) ((hlim.tendsto_integral g hg hgc).comp (tendsto_add_atTop_nat k₀))
  exact hlimk.limsup_eq.symm

/-- **Fact 2.2 II** (locality) from the locality of circle averages. -/
theorem lqgMeasureLocalityPart_of_circleLocality (hD : ConeCircleAverageLocalityStep) :
    LQGMeasureLocalityPart := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hμ U hU
  obtain ⟨g, hgc, hgcs, hgU, hg01, hgt⟩ := exists_approx_indicator hU
  have hY : ∀ n, ∃ Y : Ω → ℝ, Measurable[fieldSigmaAlgebra 0 hC U] Y ∧ ∀ᵐ ω ∂P, ∫ u, g n u ∂μ ω = Y ω :=
    fun n => ae_eq_integral_of_circleLocality hγ hγ2 hμ hD hU (hgc n) (hgcs n) (hgU n)
  choose Y hYm hYe using hY
  refine ⟨fun ω => ⨆ n, ENNReal.ofReal (Y n ω), Measurable.iSup fun n => (hYm n).ennreal_ofReal, ?_⟩
  filter_upwards [ae_all_iff.2 hYe, ae_isLocallyFiniteMeasure hμ] with ω hω hfin
  simp only [← hω]
  exact measure_eq_iSup_ofReal_integral hU hgc hgcs hgU hg01 hgt

/-- **Fact 2.2 from its cited parts and the field step**: non-atomicity (I, cited), the locality of circle averages
(field step for II) and the dilation case of conformal covariance (IV, cited). Local finiteness (I), locality (II)
given the field step, Weyl scaling (III), and translations and rotations (IV) are proved from the definition of the
LQG measure as a vague dyadic limit. -/
theorem lqgMeasureProperties_of_steps (hNA : LQGMeasureNonAtomicPart) (hCL : ConeCircleAverageLocalityStep)
    (hD : LQGMeasureDilationCovariancePart) : LQGMeasurePropertiesStmt :=
  lqgMeasureProperties_of_citedParts hNA (lqgMeasureLocalityPart_of_circleLocality hCL) hD

end MatedCRT.LQGMeasure
