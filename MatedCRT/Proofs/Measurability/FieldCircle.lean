import MatedCRT.Proofs.Measurability.ConePairing

/-!
# A `σ(h)`-measurable version of the circle average process at dyadic radii

For the field `h` of the environment, `circleField S r z = limsup_k (h, φ_k)` (`φ_k = circBump k z r`) is
`σ(h)`-measurable and almost surely equal to `h_r(z)` when `|z| ≠ r` (`ae_circleField_eq`, from
`ae_tendsto_circBump_of_isQuantumCone`). Along the grid `gridPt m a b = ((3a+1) + (3b+1)i)/(3·2^m)`, which avoids every
circle `|w| = 2^{-n}` (`norm_gridPt_ne`, a congruence modulo `3`), the limsup of the grid values
(`gridVersion`) is jointly measurable in `(ω, z)` and, by continuity of the circle average process, almost surely equal
to `h_{2^{-n}}(z)` for all `n` and `z` at once (`ae_gridVersion_eq`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real ENNReal
open _root_.HarmonicBalls

namespace MatedCRT
namespace FieldCircle

open CirclePairing LQGMetric.CircleAvg

/-! ### The grid -/

/-- The grid point `((3a+1) + (3b+1)i) / (3·2^m)`. -/
def gridPt (m : ℕ) (a b : ℤ) : ℂ := ⟨(3 * a + 1) / (3 * 2 ^ m), (3 * b + 1) / (3 * 2 ^ m)⟩

/-- No grid point lies on a circle `|w| = 2^{-n}`: `((3a+1)² + (3b+1)²) 4ⁿ ≢ 9 · 4^m (mod 3)`. -/
lemma norm_gridPt_ne (m n : ℕ) (a b : ℤ) : ‖gridPt m a b‖ ≠ (2 : ℝ)⁻¹ ^ n := by
  intro h
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  have hm : (0 : ℝ) < 2 ^ m := by positivity
  have h2 : ‖gridPt m a b‖ ^ 2 * ((2 : ℝ) ^ n) ^ 2 = 1 := by
    rw [h, inv_pow, ← mul_pow, inv_mul_cancel₀ hn.ne', one_pow]
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  simp only [gridPt] at h2
  have hR : (((3 * a + 1) ^ 2 + (3 * b + 1) ^ 2) * ((2 : ℤ) ^ n) ^ 2 : ℤ) = ((9 * ((2 : ℤ) ^ m) ^ 2 : ℤ) : ℝ) := by
    push_cast
    field_simp at h2
    linear_combination h2
  have hZ : ((3 * a + 1) ^ 2 + (3 * b + 1) ^ 2) * ((2 : ℤ) ^ n) ^ 2 = 9 * ((2 : ℤ) ^ m) ^ 2 := by
    exact_mod_cast hR
  have h3 := congrArg (fun x : ℤ => (x : ZMod 3)) hZ
  push_cast at h3
  have e3 : (3 : ZMod 3) = 0 := rfl
  have e9 : (9 : ZMod 3) = 0 := rfl
  have e4 : ((2 : ZMod 3) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm n 2, pow_mul]
    have : (2 : ZMod 3) ^ 2 = 1 := rfl
    rw [this, one_pow]
  rw [e3, e9, e4] at h3
  simp only [zero_mul, zero_add, one_pow, mul_one] at h3
  exact absurd h3 (by decide)

/-- The grid approximation of `z` at level `m`. -/
def gridApprox (m : ℕ) (z : ℂ) : ℂ := gridPt m ⌊z.re * 2 ^ m⌋ ⌊z.im * 2 ^ m⌋

lemma abs_gridCoord_sub_le (x : ℝ) (m : ℕ) :
    |(3 * (⌊x * 2 ^ m⌋ : ℝ) + 1) / (3 * 2 ^ m) - x| ≤ 2 * (2 : ℝ)⁻¹ ^ m := by
  have hm : (0 : ℝ) < 2 ^ m := by positivity
  have h1 := Int.floor_le (x * 2 ^ m)
  have h2 := Int.lt_floor_add_one (x * 2 ^ m)
  have e : (3 * (⌊x * 2 ^ m⌋ : ℝ) + 1) / (3 * 2 ^ m) - x =
      (3 * (⌊x * 2 ^ m⌋ : ℝ) + 1 - 3 * (x * 2 ^ m)) / (3 * 2 ^ m) := by
    field_simp
  have hinv : (2 : ℝ)⁻¹ ^ m * 2 ^ m = 1 := by rw [inv_pow, inv_mul_cancel₀ hm.ne']
  have h6 : 2 * (2 : ℝ)⁻¹ ^ m * (3 * 2 ^ m) = 6 := by
    rw [show 2 * (2 : ℝ)⁻¹ ^ m * (3 * 2 ^ m) = 6 * ((2 : ℝ)⁻¹ ^ m * 2 ^ m) by ring, hinv, mul_one]
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 * 2 ^ m), div_le_iff₀ (by positivity), h6]
  exact abs_le.2 ⟨by linarith, by linarith⟩

lemma tendsto_gridApprox (z : ℂ) : Tendsto (fun m => gridApprox m z) atTop (𝓝 z) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb : ∀ m : ℕ, dist (gridApprox m z) z ≤ 4 * (2 : ℝ)⁻¹ ^ m := by
    intro m
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h1 := abs_gridCoord_sub_le z.re m
    have h2 := abs_gridCoord_sub_le z.im m
    simp only [gridApprox, gridPt, Complex.sub_re, Complex.sub_im]
    linarith
  have h0 : Tendsto (fun m : ℕ => 4 * (2 : ℝ)⁻¹ ^ m) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).const_mul 4
    rwa [mul_zero] at this
  exact squeeze_zero (fun _ => dist_nonneg) hb h0

/-! ### The grid version of a family of random variables -/

section Grid

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma measurable_grid (X : ℂ → Ω → ℝ) (hX : ∀ w, Measurable (X w)) (m : ℕ) :
    Measurable fun p : Ω × ℂ => X (gridApprox m p.2) p.1 := by
  have hF : Measurable fun q : Ω × (ℤ × ℤ) => X (gridPt m q.2.1 q.2.2) q.1 :=
    measurable_from_prod_countable_left fun ab => hX (gridPt m ab.1 ab.2)
  exact hF.comp (measurable_fst.prodMk
    ((Int.measurable_floor.comp ((Complex.measurable_re.comp measurable_snd).mul_const _)).prodMk
      (Int.measurable_floor.comp ((Complex.measurable_im.comp measurable_snd).mul_const _))))

/-- `limsup_m X(gridApprox m z)`. -/
def gridVersion (X : ℂ → Ω → ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  limsup (fun m => X (gridApprox m z) ω) atTop

lemma measurable_gridVersion (X : ℂ → Ω → ℝ) (hX : ∀ w, Measurable (X w)) :
    Measurable (Function.uncurry (gridVersion X)) :=
  Measurable.limsup fun m => measurable_grid X hX m

omit mΩ in
lemma gridVersion_eq {X : ℂ → Ω → ℝ} {ω : Ω} {f : ℂ → ℝ} (hf : Continuous f)
    (hX : ∀ m a b, X (gridPt m a b) ω = f (gridPt m a b)) (z : ℂ) : gridVersion X ω z = f z := by
  have ht : Tendsto (fun m => X (gridApprox m z) ω) atTop (𝓝 (f z)) :=
    ((hf.tendsto z).comp (tendsto_gridApprox z)).congr fun m => (hX m _ _).symm
  exact ht.limsup_eq

end Grid

/-! ### The field -/

variable {Ω : Type} [MeasurableSpace Ω]

lemma measurable_hC_fieldSigma (S : MatedCRTEnv Ω) {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    Measurable[S.fieldSigma] fun ω => S.hC ω φ := by
  have hle : MeasurableSpace.comap (fun ω => fieldPairing 0 (S.hC ω) φ) (inferInstance : MeasurableSpace ℝ) ≤
      S.fieldSigma := by
    unfold MatedCRTEnv.fieldSigma fieldSigmaAlgebra
    exact le_iSup₂ (f := fun φ (_ : IsTestFunction univ φ) =>
      MeasurableSpace.comap (fun ω => fieldPairing 0 (S.hC ω) φ) (inferInstance : MeasurableSpace ℝ)) φ hφ
  have hm : Measurable[S.fieldSigma] fun ω => fieldPairing 0 (S.hC ω) φ := measurable_iff_comap_le.2 hle
  have e : (fun ω => fieldPairing 0 (S.hC ω) φ) = fun ω => S.hC ω φ :=
    funext fun ω => by simp [fieldPairing]
  rwa [e] at hm

/-- The `σ(h)`-measurable version `limsup_k (h, φ_k)` of the circle average `h_r(z)`. -/
def circleField (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  limsup (fun k => S.hC ω (circBump k z r)) atTop

lemma measurable_circleField (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) :
    Measurable[S.fieldSigma] (circleField S r z) :=
  Measurable.limsup fun k => measurable_hC_fieldSigma S (isTestFunction_circBump k z r)

lemma ae_circleField_eq {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) {r : ℝ}
    (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≠ r) : ∀ᵐ ω ∂S.P, circleField S r z ω = S.hcirc ω r z :=
  (ae_tendsto_circBump_of_isQuantumCone hS.isQuantumCone hr hz).mono fun _ h => h.limsup_eq

/-- The jointly `σ(h) ⊗ 𝓑(ℂ)`-measurable version of `(ω, z) ↦ h_{2^{-n}}(z)`. -/
def dyadicCircleVersion (S : MatedCRTEnv Ω) (n : ℕ) : Ω → ℂ → ℝ :=
  gridVersion fun w => circleField S ((2 : ℝ)⁻¹ ^ n) w

lemma measurable_dyadicCircleVersion (S : MatedCRTEnv Ω) (n : ℕ) :
    Measurable[S.fieldSigma.prod (inferInstance : MeasurableSpace ℂ)]
      (Function.uncurry (dyadicCircleVersion S n)) :=
  measurable_gridVersion (mΩ := S.fieldSigma) _ fun w => measurable_circleField S _ w

/-- **Almost surely `h_{2^{-n}}(z)` equals its `σ(h)`-measurable version for all `n` and `z`.** -/
theorem ae_dyadicCircleVersion_eq {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ n : ℕ, ∀ z : ℂ, dyadicCircleVersion S n ω z = S.hcirc ω ((2 : ℝ)⁻¹ ^ n) z := by
  have hgrid : ∀ᵐ ω ∂S.P, ∀ n m : ℕ, ∀ a b : ℤ,
      circleField S ((2 : ℝ)⁻¹ ^ n) (gridPt m a b) ω = S.hcirc ω ((2 : ℝ)⁻¹ ^ n) (gridPt m a b) := by
    simp only [ae_all_iff]
    intro n m a b
    exact ae_circleField_eq hS (by positivity) (norm_gridPt_ne m n a b)
  filter_upwards [hgrid, hS.isQuantumCone.ae_continuousOn_circle] with ω h1 h2 n z
  have hc : Continuous fun w => S.hcirc ω ((2 : ℝ)⁻¹ ^ n) w := by
    rw [← continuousOn_univ]
    exact h2.comp (continuous_const.prodMk continuous_id).continuousOn
      fun w _ => ⟨mem_Ioi.2 (by positivity), mem_univ _⟩
  exact gridVersion_eq hc (fun m a b => h1 n m a b) z

end FieldCircle
end MatedCRT
