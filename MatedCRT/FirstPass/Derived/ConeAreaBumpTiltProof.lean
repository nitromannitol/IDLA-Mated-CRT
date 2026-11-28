import MatedCRT.FirstPass.Derived.ConeOffsetDensityProof
import LatticeProb.Gauss.GaussianSpaceShift
import LatticeProb.Gauss.CameronMartinLimitShift
import LatticeProb.LQG.RadialLateralIndep
import LatticeProb.LQG.AreaReparamMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.Lateral
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OConeZero
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4D
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4I
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.FieldDecomp
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.RadialPath

/-!
# Quasi-invariance of the area measure of a quantum cone under smooth tilts

`ConeAreaBumpTilt γ` (`ConeOffsetDensityProof.lean`) states: for the circle-average embedding `h` of the
`β`-quantum cone (`β ∈ {0, γ}`), built from a whole-plane GFF `X` and two Brownian motions `B, B'`, its
`γ`-LQG area measure `μ_h`, a random curve `e` independent of `(X, B, B')`, and a smooth `f` with compact support
in `B_1(0) \ {0}`, the law of `(e, μ_h)` is absolutely continuous with respect to the law of `(e, e^{γ f} μ_h)`.
This file proves it (`coneAreaBumpTilt`), following the written argument.

* **The Gaussian shifts.** Write `f = f_lat + f̄`, `f̄` the rotation average of `f` (`symmTest`) and
  `g(t) = f̄(e^{-t})`. The cone field depends on `X` only through its lateral part `L` (whose pairings are
  `L(φ) = X(φ − φ̄)` almost surely, `ae_lateralPart_apply`). The shift `(L, B, B') ↦ (L + f_lat, B + g, B')`
  is a Cameron–Martin shift of the centred Gaussian family `(L(φ), B_t, B'_t)`: the covariances of the
  coordinates with `X(−Δ f_lat/(2π)) + Σ_k δ_k (B_{t_{k+1}} − B_{t_k})` (a discretized Wiener integral of `g'`)
  converge to the shift, and these variables form a Cauchy sequence in `L²` (`measure_coneShift_eq_zero_iff`,
  from `LatticeProb.Gauss.measure_add_eq_zero_iff_of_tendsto_covariance_of_cauchy`). The independent curve
  is integrated out by Fubini.
* **The area measure.** The shifted data give the cone field `h + f` (`coneFieldOfData_shift`), whose area
  measure is `e^{γ f} μ_h` (Weyl scaling, `MoTPort.ConeArea3.isVagueLimitOn_areaApproxC_add_ofFunC`).
* **Measurability.** The area measure is read off the data `(L, B, B')` by a Borel map (`coneAreaOf`): the
  vague limit on the measurable set of data whose approximations carry the countable certificate
  `AreaCertUniv` (eventual finiteness and convergence of countably many test integrals on dilated windows,
  `MoTPort.ConeArea4.AreaCert`), and `0` elsewhere. Almost surely the cone data and the shifted data lie in it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b

/-! ### Independent Gaussian families -/

section GaussSum

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Two independent Gaussian processes form a jointly Gaussian process. -/
theorem isGaussianProcess_sumElim_of_indepFun {S T : Type*} {Y₁ : S → Ω → ℝ} {Y₂ : T → Ω → ℝ}
    (h₁ : IsGaussianProcess Y₁ P) (h₂ : IsGaussianProcess Y₂ P)
    (hind : IndepFun (fun ω s => Y₁ s ω) (fun ω t => Y₂ t ω) P) :
    IsGaussianProcess (Sum.elim Y₁ Y₂) P := by
  classical
  constructor
  intro I
  have g₁ := h₁.hasGaussianLaw I.toLeft
  have g₂ := h₂.hasGaussianLaw I.toRight
  have hind' : IndepFun (fun ω => I.toLeft.restrict (Y₁ · ω)) (fun ω => I.toRight.restrict (Y₂ · ω)) P :=
    hind.comp (φ := fun f : S → ℝ => I.toLeft.restrict f) (ψ := fun f : T → ℝ => I.toRight.restrict f)
      (Measurable.of_eval fun i => measurable_pi_apply (i : S))
      (Measurable.of_eval fun i => measurable_pi_apply (i : T))
  have hG := IndepFun.hasGaussianLaw g₁ g₂ hind'
  let L : ((I.toLeft → ℝ) × (I.toRight → ℝ)) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun i => match i with
      | ⟨Sum.inl s, h⟩ => (ContinuousLinearMap.proj
          (⟨s, Finset.mem_toLeft.2 h⟩ : I.toLeft)).comp (ContinuousLinearMap.fst ℝ _ _)
      | ⟨Sum.inr t, h⟩ => (ContinuousLinearMap.proj
          (⟨t, Finset.mem_toRight.2 h⟩ : I.toRight)).comp (ContinuousLinearMap.snd ℝ _ _)
  have e : (fun ω => I.restrict (fun i => Sum.elim Y₁ Y₂ i ω)) =
      fun ω => L (I.toLeft.restrict (Y₁ · ω), I.toRight.restrict (Y₂ · ω)) := by
    funext ω; funext i
    rcases i with ⟨i | i, h⟩ <;> rfl
  rw [e]
  exact hG.map_fun L

omit [IsProbabilityMeasure P] in
theorem covariance_congr_ae' {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') :
    cov[X, Y; P] = cov[X', Y'; P] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  exact integral_congr_ae (by filter_upwards [hX, hY] with ω h1 h2; rw [h1, h2])

theorem covariance_eq_zero_of_indepFun' {X Y : Ω → ℝ} (h : IndepFun X Y P) (hX : MemLp X 2 P)
    (hY : MemLp Y 2 P) : cov[X, Y; P] = 0 := by
  rw [covariance_eq_sub hX hY]
  have := h.integral_fun_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable
  rw [show P[X * Y] = ∫ ω, X ω * Y ω ∂P from rfl, this, sub_self]

end GaussSum

/-! ### Piecewise linear interpolation on a grid -/

section Grid

/-- The grid point `k / (n + 1)`. -/
def gridPt (n k : ℕ) : ℝ := k / ((n : ℝ) + 1)

theorem gridPt_nonneg (n k : ℕ) : 0 ≤ gridPt n k := by unfold gridPt; positivity

theorem gridPt_zero (n : ℕ) : gridPt n 0 = 0 := by simp [gridPt]

theorem gridPt_succ_sub (n k : ℕ) : gridPt n (k + 1) - gridPt n k = 1 / ((n : ℝ) + 1) := by
  unfold gridPt; push_cast; ring

theorem gridPt_mono (n : ℕ) {j k : ℕ} (h : j ≤ k) : gridPt n j ≤ gridPt n k := by
  unfold gridPt
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

theorem gridPt_lt_succ (n k : ℕ) : gridPt n k < gridPt n (k + 1) := by
  have h1 := gridPt_succ_sub n k
  have h2 : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- The slope of `g` on the `k`-th grid cell. -/
def gridSlope (g : ℝ → ℝ) (n k : ℕ) : ℝ := (g (gridPt n (k + 1)) - g (gridPt n k)) * ((n : ℝ) + 1)

/-- The number of grid cells covering `[0, T]`. -/
def gridLen (T : ℝ) (n : ℕ) : ℕ := ⌈T * ((n : ℝ) + 1)⌉₊

theorem le_gridPt_gridLen (T : ℝ) (n : ℕ) : T ≤ gridPt n (gridLen T n) := by
  unfold gridPt gridLen
  rw [le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

theorem gridPt_gridLen_le {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : gridPt n (gridLen T n) ≤ T + 1 := by
  unfold gridPt gridLen
  have h1 : (⌈T * ((n : ℝ) + 1)⌉₊ : ℝ) < T * ((n : ℝ) + 1) + 1 := Nat.ceil_lt_add_one (by positivity)
  rw [div_le_iff₀ (by positivity)]
  have e : (T + 1) * ((n : ℝ) + 1) = T * ((n : ℝ) + 1) + ((n : ℝ) + 1) := by ring
  rw [e]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Piecewise linear interpolation of `g` at the grid points: the covariance of a Brownian motion at time `x`
with the discretized Wiener integral of `g'`. -/
def gridInterp (g : ℝ → ℝ) (T : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (gridLen T n), gridSlope g n k * (min x (gridPt n (k + 1)) - min x (gridPt n k))

theorem gridInterp_zero (g : ℝ → ℝ) (T : ℝ) (n : ℕ) : gridInterp g T n 0 = 0 := by
  unfold gridInterp
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [min_eq_left (gridPt_nonneg n (k + 1)), min_eq_left (gridPt_nonneg n k), sub_self, mul_zero]

theorem continuous_gridInterp (g : ℝ → ℝ) (T : ℝ) (n : ℕ) : Continuous (gridInterp g T n) := by
  unfold gridInterp
  exact continuous_finsetSum _ fun k _ => continuous_const.mul
    ((continuous_id.min continuous_const).sub (continuous_id.min continuous_const))

theorem hasDerivWithinAt_min_Ici (c x : ℝ) :
    HasDerivWithinAt (fun y => min y c) (if x < c then (1 : ℝ) else 0) (Ici x) x := by
  by_cases h : x < c
  · rw [ite_eq_left h]
    have h1 : HasDerivWithinAt (fun y : ℝ => y) 1 (Ici x) x := hasDerivWithinAt_id x _
    refine h1.congr_of_eventuallyEq ?_ (min_eq_left h.le)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds h)] with y hy
    exact min_eq_left (le_of_lt hy)
  · rw [ite_eq_right h]
    have h1 : HasDerivWithinAt (fun _ : ℝ => c) 0 (Ici x) x := hasDerivWithinAt_const x _ c
    refine h1.congr_of_eventuallyEq ?_ (min_eq_right (not_lt.1 h))
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact min_eq_right ((not_lt.1 h).trans hy)

theorem hasDerivWithinAt_gridInterp (g : ℝ → ℝ) (T : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivWithinAt (gridInterp g T n) (∑ k ∈ Finset.range (gridLen T n), gridSlope g n k *
      ((if x < gridPt n (k + 1) then (1 : ℝ) else 0) - (if x < gridPt n k then 1 else 0))) (Ici x) x := by
  unfold gridInterp
  exact HasDerivWithinAt.fun_sum fun k _ => ((hasDerivWithinAt_min_Ici _ x).sub
    (hasDerivWithinAt_min_Ici _ x)).const_mul _

theorem gridPt_floor_le {n : ℕ} {x : ℝ} (hx : 0 ≤ x) : gridPt n ⌊x * ((n : ℝ) + 1)⌋₊ ≤ x := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold gridPt; rw [div_le_iff₀ hn]; exact Nat.floor_le (by positivity)

theorem lt_gridPt_floor_succ {n : ℕ} (x : ℝ) : x < gridPt n (⌊x * ((n : ℝ) + 1)⌋₊ + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold gridPt; rw [lt_div_iff₀ hn]; push_cast; exact Nat.lt_floor_add_one _

theorem gridDeriv_eq (g : ℝ → ℝ) (T : ℝ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∑ k ∈ Finset.range (gridLen T n), gridSlope g n k *
      ((if x < gridPt n (k + 1) then (1 : ℝ) else 0) - (if x < gridPt n k then 1 else 0))) =
      if ⌊x * ((n : ℝ) + 1)⌋₊ < gridLen T n then gridSlope g n ⌊x * ((n : ℝ) + 1)⌋₊ else 0 := by
  have hjle := gridPt_floor_le (n := n) hx
  have hjlt := lt_gridPt_floor_succ (n := n) x
  set j := ⌊x * ((n : ℝ) + 1)⌋₊ with hj
  have hterm : ∀ k, k ≠ j → ((if x < gridPt n (k + 1) then (1 : ℝ) else 0) -
      (if x < gridPt n k then 1 else 0)) = 0 := by
    intro k hk
    rcases lt_or_gt_of_ne hk with hkj | hkj
    · have h1 : gridPt n (k + 1) ≤ x := (gridPt_mono n hkj).trans hjle
      have h2 : gridPt n k ≤ x := (gridPt_mono n (Nat.le_succ k)).trans h1
      rw [ite_eq_right (not_lt.2 h1), ite_eq_right (not_lt.2 h2), sub_self]
    · have h1 : x < gridPt n k := hjlt.trans_le (gridPt_mono n hkj)
      have h2 : x < gridPt n (k + 1) := h1.trans (gridPt_lt_succ n k)
      rw [ite_eq_left h1, ite_eq_left h2, sub_self]
  by_cases hjN : j < gridLen T n
  · rw [ite_eq_left hjN, Finset.sum_eq_single j (fun k _ hk => by rw [hterm k hk, mul_zero])
      (fun h => absurd (Finset.mem_range.2 hjN) h)]
    rw [ite_eq_left hjlt, ite_eq_right (not_lt.2 hjle), sub_zero, mul_one]
  · rw [ite_eq_right hjN]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkj : k ≠ j := fun h => hjN (h ▸ Finset.mem_range.1 hk)
    rw [hterm k hkj, mul_zero]

/-- The slope on a grid cell is a value of the derivative inside the cell. -/
theorem exists_gridSlope_eq {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (n k : ℕ) :
    ∃ ξ ∈ Ioo (gridPt n k) (gridPt n (k + 1)), gridSlope g n k = g' ξ := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g g' (gridPt_lt_succ n k) hgc.continuousOn
    (fun y _ => hg y)
  refine ⟨ξ, hξ, ?_⟩
  rw [hξe, gridSlope, gridPt_succ_sub]
  field_simp

/-- **The interpolation error is Lipschitz with a small constant** on fine grids, when `g'` is uniformly
continuous on `[0, T + 1]` and vanishes on `[T, ∞)`. -/
theorem abs_gridErr_sub_le {g g' : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'T : ∀ x, T ≤ x → g' x = 0)
    {ε η : ℝ} (hε : 0 ≤ ε)
    (hu : ∀ x ∈ Icc (0 : ℝ) (T + 1), ∀ y ∈ Icc (0 : ℝ) (T + 1), |x - y| < η → |g' x - g' y| ≤ ε)
    {n : ℕ} (hn : 1 / ((n : ℝ) + 1) < η) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    |(gridInterp g T n b - g b) - (gridInterp g T n a - g a)| ≤ ε * (b - a) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have key := norm_image_sub_le_of_norm_deriv_right_le_segment
    (f := fun x => gridInterp g T n x - g x)
    (f' := fun x => (∑ k ∈ Finset.range (gridLen T n), gridSlope g n k *
      ((if x < gridPt n (k + 1) then (1 : ℝ) else 0) - (if x < gridPt n k then 1 else 0))) - g' x)
    (C := ε) (((continuous_gridInterp g T n).sub hgc).continuousOn)
    (fun x _ => (hasDerivWithinAt_gridInterp g T n x).sub (hg x).hasDerivWithinAt) ?_ b ⟨hab, le_rfl⟩
  · rw [Real.norm_eq_abs] at key
    exact key
  intro x hx
  have hx0 : 0 ≤ x := ha.trans hx.1
  rw [gridDeriv_eq g T n hx0, Real.norm_eq_abs]
  have hjle := gridPt_floor_le (n := n) hx0
  have hjlt := lt_gridPt_floor_succ (n := n) x
  set j := ⌊x * ((n : ℝ) + 1)⌋₊ with hj
  by_cases hjN : j < gridLen T n
  · rw [ite_eq_left hjN]
    obtain ⟨ξ, hξ, hslope⟩ := exists_gridSlope_eq hg n j
    rw [hslope]
    have hTle : gridPt n (j + 1) ≤ T + 1 :=
      (gridPt_mono n (Nat.succ_le_of_lt hjN)).trans (gridPt_gridLen_le hT n)
    have hxI : x ∈ Icc (0 : ℝ) (T + 1) := ⟨hx0, hjlt.le.trans hTle⟩
    have hξI : ξ ∈ Icc (0 : ℝ) (T + 1) := ⟨(gridPt_nonneg n j).trans hξ.1.le, hξ.2.le.trans hTle⟩
    have hd : |ξ - x| < η := by
      have h1 := gridPt_succ_sub n j
      rw [abs_lt]; constructor <;> linarith [hξ.1, hξ.2]
    exact hu ξ hξI x hxI hd
  · rw [ite_eq_right hjN]
    have hxT : T ≤ x :=
      (le_gridPt_gridLen T n).trans ((gridPt_mono n (not_lt.1 hjN)).trans hjle)
    rw [hg'T x hxT, sub_zero, abs_zero]
    exact hε

/-- The slopes are bounded by a bound of `|g'|` on `[0, T + 1]`. -/
theorem abs_gridSlope_le {g g' : ℝ → ℝ} {T G1 : ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hG1 : ∀ x ∈ Icc (0 : ℝ) (T + 1), |g' x| ≤ G1) (hg'T : ∀ x, T ≤ x → g' x = 0) (hG0 : 0 ≤ G1)
    (n k : ℕ) : |gridSlope g n k| ≤ G1 := by
  obtain ⟨ξ, hξ, hslope⟩ := exists_gridSlope_eq hg n k
  rw [hslope]
  by_cases hξT : ξ ≤ T + 1
  · exact hG1 ξ ⟨(gridPt_nonneg n k).trans hξ.1.le, hξT⟩
  · rw [hg'T ξ (by linarith), abs_zero]
    exact hG0

/-- A sum of slopes against increments of a function which is `κ`-Lipschitz on `[0, ∞)`. -/
theorem abs_sum_gridSlope_mul_le {g g' : ℝ → ℝ} {T G1 κ : ℝ} (hT : 0 ≤ T)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hG1 : ∀ x ∈ Icc (0 : ℝ) (T + 1), |g' x| ≤ G1) (hg'T : ∀ x, T ≤ x → g' x = 0) (hG0 : 0 ≤ G1)
    (hκ : 0 ≤ κ) {E : ℝ → ℝ} (hE : ∀ a b, 0 ≤ a → a ≤ b → |E b - E a| ≤ κ * (b - a)) (n : ℕ) :
    |∑ k ∈ Finset.range (gridLen T n), gridSlope g n k * (E (gridPt n (k + 1)) - E (gridPt n k))| ≤
      G1 * κ * (T + 1) := by
  calc |∑ k ∈ Finset.range (gridLen T n), gridSlope g n k * (E (gridPt n (k + 1)) - E (gridPt n k))|
      ≤ ∑ k ∈ Finset.range (gridLen T n),
          |gridSlope g n k * (E (gridPt n (k + 1)) - E (gridPt n k))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (gridLen T n), G1 * κ * (gridPt n (k + 1) - gridPt n k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, mul_assoc]
        exact mul_le_mul (abs_gridSlope_le hg hG1 hg'T hG0 n k)
          (hE _ _ (gridPt_nonneg n k) (gridPt_lt_succ n k).le) (abs_nonneg _) hG0
    _ = G1 * κ * gridPt n (gridLen T n) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (gridPt n), gridPt_zero, sub_zero]
    _ ≤ G1 * κ * (T + 1) := mul_le_mul_of_nonneg_left (gridPt_gridLen_le hT n) (mul_nonneg hG0 hκ)

end Grid

/-! ### Sums of Brownian increments -/

section Increments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `∑_{k < N} δ_k (W(p_{k+1}) − W(p_k))`. -/
def incSum (W : Ω → C(ℝ≥0, ℝ)) (δ : ℕ → ℝ) (p : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N, δ k * (W ω (p (k + 1)) - W ω (p k))

omit [IsProbabilityMeasure P] in
theorem memLp_incSum {W : Ω → C(ℝ≥0, ℝ)} (hW2 : ∀ t, MemLp (fun ω => W ω t) 2 P) (δ : ℕ → ℝ)
    (p : ℕ → ℝ≥0) (N : ℕ) : MemLp (incSum W δ p N) 2 P := by
  unfold incSum
  exact memLp_finsetSum _ fun k _ => ((hW2 _).sub (hW2 _)).const_mul (δ k)

theorem covariance_incSum_right {W : Ω → C(ℝ≥0, ℝ)} (hW2 : ∀ t, MemLp (fun ω => W ω t) 2 P)
    {V : Ω → ℝ} (hV : MemLp V 2 P) (δ : ℕ → ℝ) (p : ℕ → ℝ≥0) (N : ℕ) :
    cov[V, incSum W δ p N; P] = ∑ k ∈ Finset.range N,
      δ k * (cov[V, fun ω => W ω (p (k + 1)); P] - cov[V, fun ω => W ω (p k); P]) := by
  unfold incSum
  rw [covariance_fun_sum_right' (X := fun k ω => δ k * (W ω (p (k + 1)) - W ω (p k)))
    (fun k _ => ((hW2 _).sub (hW2 _)).const_mul (δ k)) hV]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cov[V, fun ω => δ k * (W ω (p (k + 1)) - W ω (p k)); P] = _
  rw [covariance_const_mul_right, covariance_fun_sub_right hV (hW2 _) (hW2 _)]

end Increments

/-! ### The Cameron–Martin shift of the lateral part and the radial Brownian motion -/

section Shift

/-- The coordinates of the data `(l, b, b')`: the pairings of `l` with test functions and the values of `b, b'`. -/
def coneRead (y : LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) : LQGMetric.TestC ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ
  | Sum.inl φ => y.1 φ
  | Sum.inr (Sum.inl t) => y.2.1 t
  | Sum.inr (Sum.inr t) => y.2.2 t

theorem measurable_of_measurable_coneRead {Z E : Type*} {m : MeasurableSpace Z} [MeasurableSpace E]
    {q : Z → (LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) × E}
    (h : Measurable fun z => (coneRead (q z).1, (q z).2)) : Measurable q := by
  have h1 : Measurable fun z => coneRead (q z).1 := h.fst
  have h2 : Measurable fun z => (q z).2 := h.snd
  show Measurable fun z => (((q z).1.1, ((q z).1.2.1, (q z).1.2.2)), (q z).2)
  refine Measurable.prodMk (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)) h2
  · exact LQGMetric.GFFInv.measurable_distC_iff.2 fun φ =>
      (measurable_pi_apply (Sum.inl φ)).comp h1
  · exact ContinuousMap.measurable_iff_eval.2 fun t =>
      (measurable_pi_apply (Sum.inr (Sum.inl t))).comp h1
  · exact ContinuousMap.measurable_iff_eval.2 fun t =>
      (measurable_pi_apply (Sum.inr (Sum.inr t))).comp h1

/-- Every measurable set of data and marks is an event of the coordinates and the mark. -/
theorem exists_measurableSet_coneRead_preimage {E : Type*} [MeasurableSpace E]
    {U : Set ((LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) × E)} (hU : MeasurableSet U) :
    ∃ U' : Set ((LQGMetric.TestC ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ) × E), MeasurableSet U' ∧
      (fun p : (LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) × E => (coneRead p.1, p.2)) ⁻¹' U' = U := by
  have hid : Measurable[MeasurableSpace.comap
      (fun p : (LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) × E => (coneRead p.1, p.2)) inferInstance]
      (id : (LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) × E → _) :=
    measurable_of_measurable_coneRead (m := MeasurableSpace.comap _ inferInstance) (q := id)
      (comap_measurable _)
  exact MeasurableSpace.measurableSet_comap.1 (hid hU)

/-- The shift of the coordinates. -/
def coneShift (fL : LQGMetric.TestC) (g : ℝ → ℝ) : LQGMetric.TestC ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ
  | Sum.inl φ => ∫ x, φ x * fL x
  | Sum.inr (Sum.inl t) => g t
  | Sum.inr (Sum.inr _) => 0

/-- The jointly Gaussian family: lateral pairings, pairings with mean-zero tests, and the two Brownian motions. -/
def coneGauss {Ω : Type*} (X : Ω → LQGMetric.DistC) (Bc B'c : Ω → C(ℝ≥0, ℝ)) :
    (LQGMetric.TestC ⊕ LQGMetric.TestC0) ⊕ (ℝ≥0 ⊕ ℝ≥0) → Ω → ℝ
  | Sum.inl (Sum.inl φ), ω => CellScaling.lateralPart (X ω) φ
  | Sum.inl (Sum.inr ψ), ω => X ω ψ.1
  | Sum.inr (Sum.inl t), ω => Bc ω t
  | Sum.inr (Sum.inr t), ω => B'c ω t

/-- The lateral test function `φ − φ̄`. -/
def latTest0 (φ : LQGMetric.TestC) : LQGMetric.TestC0 :=
  ⟨φ - GMCFacts.symmTest φ, GMCFacts.integral_sub_symmTest φ⟩

theorem distC_add_apply (a b : LQGMetric.DistC) (φ : LQGMetric.TestC) : (a + b) φ = a φ + b φ := rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Cameron–Martin for the cone data.** Let `X` be a whole-plane GFF, `B, B'` Brownian motions with continuous
versions `Bc, B'c`, `X` independent of `(B, B')`, `B` independent of `B'`, and `e` independent of `(X, B, B')`.
Let `fL` be a test function with `∫ φ̄ fL = 0` for every test function `φ` (zero averages on centred circles),
and `g` a `C¹` function with `g(0) = 0` and `g' = 0` on `[T, ∞)`. Then the data `(L + fL, Bc + g, B'c)`
(`L` the lateral part of `X`) and `(L, Bc, B'c)`, together with `e`, have the same null events. -/
theorem measure_coneShift_eq_zero_iff {X : Ω → LQGMetric.DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hX : LQGMetric.IsWholePlaneGFF X P) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P)
    (hBB' : IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P)
    {Bc B'c : Ω → C(ℝ≥0, ℝ)} (hBcm : Measurable Bc) (hB'cm : Measurable B'c)
    (hBc : ∀ᵐ ω ∂P, ∀ t, Bc ω t = B t ω) (hB'c : ∀ᵐ ω ∂P, ∀ t, B'c ω t = B' t ω)
    {E : Type*} [MeasurableSpace E] {e : Ω → E} (he : Measurable e)
    (heind : IndepFun e (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω))) P)
    (fL : LQGMetric.TestC) (hfL : ∀ φ : LQGMetric.TestC, ∫ x, GMCFacts.symmTest φ x * fL x = 0)
    {g g' : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hg : ∀ x, HasDerivAt g (g' x) x) (hg0 : g 0 = 0)
    (hg'T : ∀ x, T ≤ x → g' x = 0) (hg'c : ContinuousOn g' (Icc 0 (T + 1)))
    (gC : C(ℝ≥0, ℝ)) (hgC : ∀ t, gC t = g t)
    {U : Set ((LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) × E)} (hU : MeasurableSet U) :
    P {ω | ((CellScaling.lateralPart (X ω) + CellScaling.ofFunC ⇑fL, (Bc ω + gC, B'c ω)), e ω) ∈ U} = 0 ↔
      P {ω | ((CellScaling.lateralPart (X ω), (Bc ω, B'c ω)), e ω) ∈ U} = 0 := by
  classical
  /- basic facts on the Brownian versions -/
  have hBcev : ∀ t, Measurable fun ω => Bc ω t := fun t => (ContinuousMap.measurable_eval t).comp hBcm
  have hB'cev : ∀ t, Measurable fun ω => B'c ω t := fun t => (ContinuousMap.measurable_eval t).comp hB'cm
  have hBae : ∀ t, (fun ω => B t ω) =ᵐ[P] fun ω => Bc ω t := fun t => hBc.mono fun ω h => (h t).symm
  have hB'ae : ∀ t, (fun ω => B' t ω) =ᵐ[P] fun ω => B'c ω t := fun t => hB'c.mono fun ω h => (h t).symm
  have hcovB : ∀ s t : ℝ≥0, cov[fun ω => Bc ω s, fun ω => Bc ω t; P] = min (s : ℝ) t := by
    intro s t
    rw [← covariance_congr_ae' (hBae s) (hBae t), hB.covariance_eval]
    exact NNReal.coe_min s t
  have hpathB : (fun ω t => B t ω) =ᵐ[P] fun ω t => Bc ω t := by
    filter_upwards [hBc] with ω h; funext t; exact (h t).symm
  have hpathB' : (fun ω t => B' t ω) =ᵐ[P] fun ω t => B'c ω t := by
    filter_upwards [hB'c] with ω h; funext t; exact (h t).symm
  /- independence -/
  have hXBc : ∀ (u : LQGMetric.DistC → ℝ), Measurable u → ∀ t,
      IndepFun (fun ω => u (X ω)) (fun ω => Bc ω t) P := fun u hu t =>
    (hind.comp hu ((measurable_pi_apply t).comp measurable_fst)).congr (ae_eq_refl _) (hBae t)
  have hXB'c : ∀ (u : LQGMetric.DistC → ℝ), Measurable u → ∀ t,
      IndepFun (fun ω => u (X ω)) (fun ω => B'c ω t) P := fun u hu t =>
    (hind.comp hu ((measurable_pi_apply t).comp measurable_snd)).congr (ae_eq_refl _) (hB'ae t)
  have hBB'c : ∀ s t, IndepFun (fun ω => Bc ω s) (fun ω => B'c ω t) P := fun s t =>
    (hBB'.comp (measurable_pi_apply s) (measurable_pi_apply t)).congr (hBae s) (hB'ae t)
  /- the Gaussian family -/
  have hGB : IsGaussianProcess (fun t ω => Bc ω t) P :=
    hB.isGaussianProcess.congr fun t => hBae t
  have hGB' : IsGaussianProcess (fun t ω => B'c ω t) P :=
    hB'.isGaussianProcess.congr fun t => hB'ae t
  have hGBB : IsGaussianProcess (Sum.elim (fun t ω => Bc ω t) (fun t ω => B'c ω t)) P :=
    isGaussianProcess_sumElim_of_indepFun hGB hGB' (hBB'.congr hpathB hpathB')
  have hmXψ : Measurable fun x : LQGMetric.DistC => fun ψ : LQGMetric.TestC0 => x ψ.1 :=
    measurable_pi_iff.2 fun ψ => LQGMetric.GFFInv.measurable_pair ψ.1
  have hmSum : Measurable fun q : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
      fun p : ℝ≥0 ⊕ ℝ≥0 => Sum.elim q.1 q.2 p := by
    refine measurable_pi_iff.2 fun p => ?_
    rcases p with t | t
    · exact (measurable_pi_apply t).comp measurable_fst
    · exact (measurable_pi_apply t).comp measurable_snd
  have hXBB : IndepFun (fun ω (ψ : LQGMetric.TestC0) => X ω ψ.1)
      (fun ω p => Sum.elim (fun t ω => Bc ω t) (fun t ω => B'c ω t) p ω) P := by
    refine (hind.comp hmXψ hmSum).congr (ae_eq_refl _) ?_
    filter_upwards [hBc, hB'c] with ω h1 h2
    funext p
    rcases p with t | t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hG0 : IsGaussianProcess (Sum.elim (fun (ψ : LQGMetric.TestC0) ω => X ω ψ.1)
      (Sum.elim (fun t ω => Bc ω t) (fun t ω => B'c ω t))) P :=
    isGaussianProcess_sumElim_of_indepFun hX.gaussian hGBB hXBB
  let σ : (LQGMetric.TestC ⊕ LQGMetric.TestC0) ⊕ (ℝ≥0 ⊕ ℝ≥0) → LQGMetric.TestC0 ⊕ (ℝ≥0 ⊕ ℝ≥0) :=
    Sum.elim (Sum.elim (fun φ => Sum.inl (latTest0 φ)) Sum.inl) Sum.inr
  have hG : IsGaussianProcess (coneGauss X Bc B'c) P := by
    refine (hG0.comp_right σ).congr fun i => ?_
    rcases i with (φ | ψ) | (t | t)
    · filter_upwards [GMCFacts.ae_lateralPart_apply hX φ] with ω hω
      exact hω.symm
    · exact ae_eq_refl _
    · exact ae_eq_refl _
    · exact ae_eq_refl _
  have hlat : ∀ φ : LQGMetric.TestC, Measurable fun ω => CellScaling.lateralPart (X ω) φ := fun φ =>
    (LQGMetric.GFFInv.measurable_pair φ).comp (ConeScaling.measurable_lateralPart.comp hX.measurable)
  have hGm : ∀ i, Measurable (coneGauss X Bc B'c i) := by
    rintro ((φ | ψ) | (t | t))
    · exact hlat φ
    · exact (LQGMetric.GFFInv.measurable_pair ψ.1).comp hX.measurable
    · exact hBcev t
    · exact hB'cev t
  have hlatae : ∀ φ : LQGMetric.TestC, (fun ω => CellScaling.lateralPart (X ω) φ) =ᵐ[P]
      fun ω => X ω (latTest0 φ).1 := fun φ => GMCFacts.ae_lateralPart_apply hX φ
  have hGc : ∀ i, P[coneGauss X Bc B'c i] = 0 := by
    rintro ((φ | ψ) | (t | t))
    · exact (integral_congr_ae (hlatae φ)).trans (hX.centered (latTest0 φ))
    · exact hX.centered ψ
    · exact (integral_congr_ae (hBae t).symm).trans (hB.integral_eval t)
    · exact (integral_congr_ae (hB'ae t).symm).trans (hB'.integral_eval t)
  set M : Submodule ℝ (Ω → ℝ) := Submodule.span ℝ (Set.range (coneGauss X Bc B'c)) with hMdef
  have hM : LatticeProb.GaussianClosure.IsCentredGaussianSpace P (M : Set (Ω → ℝ)) :=
    LatticeProb.Gauss.isCentredGaussianSpace_span_range hG hGm hGc
  have hmem : ∀ i, coneGauss X Bc B'c i ∈ M := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hG2 : ∀ i, MemLp (coneGauss X Bc B'c i) 2 P := fun i => hM.memLp (hmem i)
  have hBc2 : ∀ t, MemLp (fun ω => Bc ω t) 2 P := fun t => hG2 (Sum.inr (Sum.inl t))
  have hB'c2 : ∀ t, MemLp (fun ω => B'c ω t) 2 P := fun t => hG2 (Sum.inr (Sum.inr t))
  /- the coordinates, the shift and the Cameron–Martin variables -/
  let R : LQGMetric.TestC ⊕ (ℝ≥0 ⊕ ℝ≥0) → Ω → ℝ := fun i ω => coneRead
    (CellScaling.lateralPart (X ω), (Bc ω, B'c ω)) i
  have hRG : ∀ i, R i = coneGauss X Bc B'c (Sum.elim (fun φ => Sum.inl (Sum.inl φ)) Sum.inr i) := by
    rintro (φ | t | t) <;> rfl
  have hR : ∀ i, R i ∈ M := fun i => (hRG i) ▸ hmem _
  have hR2 : ∀ i, MemLp (R i) 2 P := fun i => hM.memLp (hR i)
  let ρ₀ : LQGMetric.TestC0 := LQGMetric.cmTest0 fL
  let pN : ℕ → ℕ → ℝ≥0 := fun n k => (gridPt n k).toNNReal
  have hpN : ∀ n k, ((pN n k : ℝ≥0) : ℝ) = gridPt n k := fun n k => Real.coe_toNNReal _ (gridPt_nonneg n k)
  let W : ℕ → Ω → ℝ := fun n => incSum Bc (gridSlope g n) (pN n) (gridLen T n)
  have hW2 : ∀ n, MemLp (W n) 2 P := fun n => memLp_incSum hBc2 _ _ _
  have hWM : ∀ n, W n ∈ M := by
    intro n
    have e : W n = ∑ k ∈ Finset.range (gridLen T n), gridSlope g n k •
        (coneGauss X Bc B'c (Sum.inr (Sum.inl (pN n (k + 1)))) -
          coneGauss X Bc B'c (Sum.inr (Sum.inl (pN n k)))) := by
      funext ω
      simp only [W, incSum, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rfl
    rw [e]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmem _) (hmem _))
  let ζ : ℕ → Ω → ℝ := fun n => coneGauss X Bc B'c (Sum.inl (Sum.inr ρ₀)) + W n
  have hζ : ∀ n, ζ n ∈ M := fun n => Submodule.add_mem _ (hmem _) (hWM n)
  /- covariances with the Brownian coordinates -/
  have hcovBW : ∀ (s : ℝ≥0) n, cov[fun ω => Bc ω s, W n; P] = gridInterp g T n s := by
    intro s n
    rw [covariance_incSum_right hBc2 (hBc2 s)]
    unfold gridInterp
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcovB, hcovB, hpN, hpN]
  have hcovB'W : ∀ (s : ℝ≥0) n, cov[fun ω => B'c ω s, W n; P] = 0 := by
    intro s n
    rw [covariance_incSum_right hBc2 (hB'c2 s)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [covariance_eq_zero_of_indepFun' (hBB'c _ s).symm (hB'c2 s) (hBc2 _),
      covariance_eq_zero_of_indepFun' (hBB'c _ s).symm (hB'c2 s) (hBc2 _), sub_self, mul_zero]
  have hcovuW : ∀ (u : LQGMetric.DistC → ℝ), Measurable u → MemLp (fun ω => u (X ω)) 2 P → ∀ n,
      cov[fun ω => u (X ω), W n; P] = 0 := by
    intro u hu hu2 n
    rw [covariance_incSum_right hBc2 hu2]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [covariance_eq_zero_of_indepFun' (hXBc u hu _) hu2 (hBc2 _),
      covariance_eq_zero_of_indepFun' (hXBc u hu _) hu2 (hBc2 _), sub_self, mul_zero]
  /- the uniform continuity of `g'` and the bounds -/
  have hg'u : ∀ ε > 0, ∃ η > 0, ∀ x ∈ Icc (0 : ℝ) (T + 1), ∀ y ∈ Icc (0 : ℝ) (T + 1),
      |x - y| < η → |g' x - g' y| ≤ ε := by
    intro ε hε
    obtain ⟨η, hη, h⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hg'c) ε hε
    exact ⟨η, hη, fun x hx y hy hxy => (h x hx y hy (by rwa [Real.dist_eq])).le⟩
  obtain ⟨G1, hG1⟩ := isCompact_Icc.exists_bound_of_continuousOn hg'c
  have hG1' : ∀ x ∈ Icc (0 : ℝ) (T + 1), |g' x| ≤ |G1| := fun x hx =>
    (Real.norm_eq_abs _ ▸ hG1 x hx).trans (le_abs_self G1)
  have herr : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ a b, 0 ≤ a → a ≤ b →
      |(gridInterp g T n b - g b) - (gridInterp g T n a - g a)| ≤ ε * (b - a) := by
    intro ε hε
    obtain ⟨η, hη, hu⟩ := hg'u ε hε
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hη
    refine ⟨n₀, fun n hn a b ha hab => abs_gridErr_sub_le hT hg hg'T hε.le hu ?_ ha hab⟩
    refine lt_of_le_of_lt ?_ hn₀
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
  /- the covariance limits -/
  have hcovlim : ∀ i, Tendsto (fun n => cov[R i, ζ n; P]) atTop (𝓝 (coneShift fL g i)) := by
    rintro (φ | t | t)
    · have hu : Measurable fun x : LQGMetric.DistC => CellScaling.lateralPart x φ :=
        (LQGMetric.GFFInv.measurable_pair φ).comp ConeScaling.measurable_lateralPart
      have hval : ∀ n, cov[R (Sum.inl φ), ζ n; P] = ∫ x, φ x * fL x := by
        intro n
        rw [covariance_add_right (hR2 _) (hG2 _) (hW2 n)]
        have h1 : cov[R (Sum.inl φ), W n; P] = 0 := hcovuW _ hu (hR2 (Sum.inl φ)) n
        rw [h1, add_zero]
        show cov[fun ω => CellScaling.lateralPart (X ω) φ, fun ω => X ω (LQGMetric.cmTest fL); P] = _
        rw [covariance_congr_ae' (hlatae φ) (ae_eq_refl _)]
        rw [show (fun ω => X ω (LQGMetric.cmTest fL)) = fun ω => X ω ρ₀.1 from rfl,
          hX.covariance_eq (latTest0 φ) ρ₀]
        rw [show ρ₀.1 = LQGMetric.cmTest fL from rfl, LQGMetric.logCov_cmTest_right]
        have hint : ∀ u : LQGMetric.TestC, Integrable (fun x => u x * fL x) := fun u =>
          (u.continuous.mul fL.continuous).integrable_of_hasCompactSupport u.hasCompactSupport.mul_right
        have e : (fun x => (latTest0 φ).1 x * fL x) =
            fun x => φ x * fL x - GMCFacts.symmTest φ x * fL x := by
          funext x
          rw [show (latTest0 φ).1 x = φ x - GMCFacts.symmTest φ x from rfl]
          ring
        rw [e, integral_sub (hint φ) (hint _), hfL φ, sub_zero]
      simp_rw [hval]
      exact tendsto_const_nhds
    · have hval : ∀ n, cov[R (Sum.inr (Sum.inl t)), ζ n; P] = gridInterp g T n t := by
        intro n
        rw [covariance_add_right (hR2 _) (hG2 _) (hW2 n)]
        show cov[fun ω => Bc ω t, fun ω => X ω ρ₀.1; P] + cov[fun ω => Bc ω t, W n; P] = _
        rw [covariance_eq_zero_of_indepFun' (hXBc _ (LQGMetric.GFFInv.measurable_pair ρ₀.1) t).symm
          (hBc2 t) (hG2 (Sum.inl (Sum.inr ρ₀))), zero_add, hcovBW]
      simp_rw [hval]
      show Tendsto (fun n => gridInterp g T n t) atTop (𝓝 (g t))
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨n₀, hn₀⟩ := herr (ε / ((t : ℝ) + 1)) (by positivity)
      refine ⟨n₀, fun n hn => ?_⟩
      have h1 := hn₀ n hn 0 t le_rfl t.2
      rw [gridInterp_zero, hg0, sub_zero, sub_zero, sub_zero] at h1
      rw [Real.dist_eq]
      calc |gridInterp g T n t - g t| ≤ ε / ((t : ℝ) + 1) * t := h1
        _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [t.2]
    · have hval : ∀ n, cov[R (Sum.inr (Sum.inr t)), ζ n; P] = 0 := by
        intro n
        rw [covariance_add_right (hR2 _) (hG2 _) (hW2 n)]
        show cov[fun ω => B'c ω t, fun ω => X ω ρ₀.1; P] + cov[fun ω => B'c ω t, W n; P] = _
        rw [covariance_eq_zero_of_indepFun' (hXB'c _ (LQGMetric.GFFInv.measurable_pair ρ₀.1) t).symm
          (hB'c2 t) (hG2 (Sum.inl (Sum.inr ρ₀))), zero_add, hcovB'W]
      simp_rw [hval]
      exact tendsto_const_nhds
  /- the Cauchy property -/
  have hcauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N, ∫ ω, (ζ n ω - ζ k ω) ^ 2 ∂P < ε := by
    intro ε hε
    set G1' := |G1|
    have hG1'0 : 0 ≤ G1' := abs_nonneg _
    obtain ⟨n₀, hn₀⟩ := herr (ε / (4 * (G1' + 1) * (T + 1))) (by positivity)
    refine ⟨n₀, fun n hn k hk => ?_⟩
    set κ := ε / (4 * (G1' + 1) * (T + 1)) with hκ
    have hκ0 : 0 ≤ κ := by positivity
    let D : Ω → ℝ := fun ω => W n ω - W k ω
    have hD2 : MemLp D 2 P := (hW2 n).sub (hW2 k)
    have hDM : D ∈ M := Submodule.sub_mem _ (hWM n) (hWM k)
    have hD0 : P[D] = 0 := LatticeProb.Gauss.integral_eq_zero_of_isCentredGaussianSpace hM hDM
    have hsq : ∫ ω, (ζ n ω - ζ k ω) ^ 2 ∂P = cov[D, D; P] := by
      unfold covariance
      rw [hD0]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [ζ, D, Pi.add_apply, sub_zero]
      ring
    rw [hsq]
    have hED : ∀ s : ℝ≥0, cov[fun ω => Bc ω s, D; P] =
        (gridInterp g T n s - g s) - (gridInterp g T k s - g s) := by
      intro s
      rw [covariance_fun_sub_right (hBc2 s) (hW2 n) (hW2 k), hcovBW, hcovBW]
      ring
    let Ef : ℝ → ℝ := fun s => (gridInterp g T n s - g s) - (gridInterp g T k s - g s)
    have hEf : ∀ a b, 0 ≤ a → a ≤ b → |Ef b - Ef a| ≤ (2 * κ) * (b - a) := by
      intro a b ha hab
      have h1 := hn₀ n hn a b ha hab
      have h2 := hn₀ k hk a b ha hab
      have e : Ef b - Ef a = ((gridInterp g T n b - g b) - (gridInterp g T n a - g a)) -
          ((gridInterp g T k b - g b) - (gridInterp g T k a - g a)) := by simp only [Ef]; ring
      rw [e]
      calc _ ≤ |(gridInterp g T n b - g b) - (gridInterp g T n a - g a)| +
            |(gridInterp g T k b - g b) - (gridInterp g T k a - g a)| := abs_sub _ _
        _ ≤ κ * (b - a) + κ * (b - a) := add_le_add h1 h2
        _ = (2 * κ) * (b - a) := by ring
    have hcovWD : ∀ m, cov[W m, D; P] = ∑ j ∈ Finset.range (gridLen T m),
        gridSlope g m j * (Ef (gridPt m (j + 1)) - Ef (gridPt m j)) := by
      intro m
      rw [covariance_comm, covariance_incSum_right hBc2 hD2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [covariance_comm, covariance_comm D, hED, hED, hpN, hpN]
    have hsplit : cov[D, D; P] = cov[W n, D; P] - cov[W k, D; P] :=
      covariance_fun_sub_left (hW2 n) (hW2 k) hD2
    rw [hsplit, hcovWD, hcovWD]
    have hb1 := abs_sum_gridSlope_mul_le hT hg hG1' hg'T hG1'0 (by positivity) hEf n
    have hb2 := abs_sum_gridSlope_mul_le hT hg hG1' hg'T hG1'0 (by positivity) hEf k
    have hlt : 2 * (G1' * (2 * κ) * (T + 1)) < ε := by
      rw [hκ]
      have hpos : 0 < 4 * (G1' + 1) * (T + 1) := by positivity
      have e : 2 * (G1' * (2 * (ε / (4 * (G1' + 1) * (T + 1)))) * (T + 1)) =
          ε * (G1' / (G1' + 1)) := by field_simp; ring
      rw [e]
      have : G1' / (G1' + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
      nlinarith
    calc _ ≤ |∑ j ∈ Finset.range (gridLen T n), gridSlope g n j * (Ef (gridPt n (j + 1)) - Ef (gridPt n j)) -
          ∑ j ∈ Finset.range (gridLen T k), gridSlope g k j * (Ef (gridPt k (j + 1)) - Ef (gridPt k j))| :=
          le_abs_self _
      _ ≤ G1' * (2 * κ) * (T + 1) + G1' * (2 * κ) * (T + 1) := (abs_sub _ _).trans (add_le_add hb1 hb2)
      _ < ε := by linarith
  /- the Cameron–Martin equivalence of null sets for the coordinates -/
  have hCM : ∀ S : Set (LQGMetric.TestC ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ), MeasurableSet S →
      (P {ω | (fun i => R i ω + coneShift fL g i) ∈ S} = 0 ↔ P {ω | (fun i => R i ω) ∈ S} = 0) :=
    fun S hS => LatticeProb.Gauss.measure_add_eq_zero_iff_of_tendsto_covariance_of_cauchy hM hR hζ
      hcauchy hcovlim hS
  /- the mark `e` -/
  have hRm : Measurable fun ω i => R i ω := measurable_pi_iff.2 fun i => (hM _ (hR i)).1
  have hRcm : Measurable fun ω i => R i ω + coneShift fL g i :=
    measurable_pi_iff.2 fun i => (hM _ (hR i)).1.add_const _
  let Φ : LQGMetric.DistC × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) → (LQGMetric.TestC ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ) :=
    fun y i => match i with
      | Sum.inl φ => CellScaling.lateralPart y.1 φ
      | Sum.inr (Sum.inl t) => y.2.1 t
      | Sum.inr (Sum.inr t) => y.2.2 t
  have hΦ : Measurable Φ := by
    refine measurable_pi_iff.2 fun i => ?_
    rcases i with φ | t | t
    · exact (LQGMetric.GFFInv.measurable_pair φ).comp
        (ConeScaling.measurable_lateralPart.comp measurable_fst)
    · exact (measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)
    · exact (measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)
  have hRΦ : (fun ω => Φ (X ω, (fun t => B t ω), (fun t => B' t ω))) =ᵐ[P] fun ω i => R i ω := by
    filter_upwards [hBc, hB'c] with ω h1 h2
    funext i
    rcases i with φ | t | t
    · rfl
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hRe : IndepFun (fun ω i => R i ω) e P :=
    ((heind.comp measurable_id hΦ).congr (ae_eq_refl _) hRΦ).symm
  have hRce : IndepFun (fun ω i => R i ω + coneShift fL g i) e P :=
    hRe.comp (φ := fun (x : LQGMetric.TestC ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ) i => x i + coneShift fL g i) (ψ := id)
      (Measurable.of_eval fun i => (measurable_pi_apply i).add measurable_const) measurable_id
  have hCMe : ∀ U' : Set ((LQGMetric.TestC ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ) × E), MeasurableSet U' →
      (P {ω | ((fun i => R i ω + coneShift fL g i), e ω) ∈ U'} = 0 ↔
        P {ω | ((fun i => R i ω), e ω) ∈ U'} = 0) := by
    intro U' hU'
    rw [LatticeProb.Gauss.measure_pair_eq_lintegral_of_indepFun hRcm he hRce hU',
      LatticeProb.Gauss.measure_pair_eq_lintegral_of_indepFun hRm he hRe hU']
    have hmeas : ∀ {Q : Ω → (LQGMetric.TestC ⊕ (ℝ≥0 ⊕ ℝ≥0) → ℝ)}, Measurable Q →
        Measurable fun ω' => P {ω | (Q ω, e ω') ∈ U'} := by
      intro Q hQ
      have e1 : (fun ω' => P {ω | (Q ω, e ω') ∈ U'}) =
          fun ω' => (P.map Q) ((fun r => (r, e ω')) ⁻¹' U') := by
        funext ω'
        rw [Measure.map_apply hQ (measurable_prodMk_right hU')]
        rfl
      rw [e1]
      exact (measurable_measure_prodMk_right hU').comp he
    rw [lintegral_eq_zero_iff (hmeas hRcm), lintegral_eq_zero_iff (hmeas hRm)]
    constructor
    · intro H
      filter_upwards [H] with ω' hω'
      exact (hCM _ (measurable_prodMk_right hU')).1 hω'
    · intro H
      filter_upwards [H] with ω' hω'
      exact (hCM _ (measurable_prodMk_right hU')).2 hω'
  /- back to the data -/
  obtain ⟨U', hU', hUU'⟩ := exists_measurableSet_coneRead_preimage hU
  have hshift : ∀ ω, coneRead (CellScaling.lateralPart (X ω) + CellScaling.ofFunC ⇑fL,
      (Bc ω + gC, B'c ω)) = fun i => R i ω + coneShift fL g i := by
    intro ω
    funext i
    rcases i with φ | t | t
    · show (CellScaling.lateralPart (X ω) + CellScaling.ofFunC ⇑fL) φ = _
      rw [distC_add_apply, ConeScaling.ofFunC_apply_of_li fL.continuous.locallyIntegrable]
      rfl
    · show (Bc ω + gC) t = Bc ω t + g t
      rw [ContinuousMap.add_apply, hgC]
    · show B'c ω t = B'c ω t + 0
      rw [add_zero]
  have e1 : {ω | ((CellScaling.lateralPart (X ω) + CellScaling.ofFunC ⇑fL, (Bc ω + gC, B'c ω)), e ω) ∈ U} =
      {ω | ((fun i => R i ω + coneShift fL g i), e ω) ∈ U'} := by
    ext ω
    rw [← hUU']
    simp only [mem_preimage, mem_ofPred_eq]
    rw [hshift]
  have e2 : {ω | ((CellScaling.lateralPart (X ω), (Bc ω, B'c ω)), e ω) ∈ U} =
      {ω | ((fun i => R i ω), e ω) ∈ U'} := by
    ext ω
    rw [← hUU']
    rfl
  rw [e1, e2]
  exact hCMe U' hU'

end Shift

/-! ### The bump: its rotation average and the radial profile -/

section Bump

variable {fT : LQGMetric.TestC}

theorem symmTest_eq_zero_of_one_le_norm (hfs : tsupport ⇑fT ⊆ ball (0 : ℂ) 1 \ {0}) {z : ℂ}
    (hz : 1 ≤ ‖z‖) : GMCFacts.symmTest fT z = 0 := by
  rw [GMCFacts.symmTest_apply, GMCFacts.rotSymm]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun θ _ => ?_),
    intervalIntegral.integral_zero, mul_zero]
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have h1 := (hfs h).1
  rw [mem_ball, dist_zero_right, norm_mul, GMCFacts.norm_exp_ofReal_mul_I', one_mul] at h1
  linarith

theorem exists_symmTest_eq_zero_near_zero (hfs : tsupport ⇑fT ⊆ ball (0 : ℂ) 1 \ {0}) :
    ∃ r₀ > 0, ∀ z : ℂ, ‖z‖ < r₀ → GMCFacts.symmTest fT z = 0 := by
  have h0 : (0 : ℂ) ∈ (tsupport ⇑fT)ᶜ := fun h => (hfs h).2 rfl
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 (isClosed_tsupport _).isOpen_compl 0 h0
  refine ⟨r₀, hr₀, fun z hz => ?_⟩
  rw [GMCFacts.symmTest_apply, GMCFacts.rotSymm]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun θ _ => ?_),
    intervalIntegral.integral_zero, mul_zero]
  refine image_eq_zero_of_notMem_tsupport fun h => hball ?_ h
  rw [mem_ball, dist_zero_right, norm_mul, GMCFacts.norm_exp_ofReal_mul_I', one_mul]
  exact hz

/-- The radial profile `g(t) = f̄(e^{−t})` of a test function `f` (`f̄` its rotation average). -/
def bumpRad (fT : LQGMetric.TestC) (t : ℝ) : ℝ := GMCFacts.symmTest fT ((Real.exp (-t) : ℝ) : ℂ)

theorem contDiff_bumpRad (fT : LQGMetric.TestC) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bumpRad fT) :=
  (GMCFacts.symmTest fT).contDiff.comp
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_neg))

theorem bumpRad_eq_zero_of_nonpos (hfs : tsupport ⇑fT ⊆ ball (0 : ℂ) 1 \ {0}) {t : ℝ} (ht : t ≤ 0) :
    bumpRad fT t = 0 := by
  refine symmTest_eq_zero_of_one_le_norm hfs ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.one_le_exp (by linarith)

theorem bumpRad_eq_zero_of_lt {r₀ : ℝ} (hr₀pos : 0 < r₀)
    (hr₀ : ∀ z : ℂ, ‖z‖ < r₀ → GMCFacts.symmTest fT z = 0) {t : ℝ} (ht : -Real.log r₀ < t) :
    bumpRad fT t = 0 := by
  refine hr₀ _ ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (Real.exp_lt_exp.2 (by linarith)).trans_eq (Real.exp_log hr₀pos)

theorem deriv_bumpRad_eq_zero {r₀ : ℝ} (hr₀pos : 0 < r₀)
    (hr₀ : ∀ z : ℂ, ‖z‖ < r₀ → GMCFacts.symmTest fT z = 0) {t : ℝ} (ht : -Real.log r₀ < t) :
    deriv (bumpRad fT) t = 0 := by
  have h : bumpRad fT =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact bumpRad_eq_zero_of_lt hr₀pos hr₀ hs
  rw [h.deriv_eq, deriv_const]

theorem bumpRad_radial (hfs : tsupport ⇑fT ⊆ ball (0 : ℂ) 1 \ {0}) {r₀ : ℝ} (hr₀pos : 0 < r₀)
    (hr₀ : ∀ z : ℂ, ‖z‖ < r₀ → GMCFacts.symmTest fT z = 0) (z : ℂ) :
    bumpRad fT (-Real.log ‖z‖) = GMCFacts.symmTest fT z := by
  by_cases hz : z = 0
  · subst hz
    rw [norm_zero, Real.log_zero, neg_zero, bumpRad_eq_zero_of_nonpos hfs le_rfl,
      hr₀ 0 (by rw [norm_zero]; exact hr₀pos)]
  · unfold bumpRad
    rw [neg_neg, Real.exp_log (norm_pos_iff.2 hz)]
    exact (GMCFacts.symmTest_radial fT z).symm

/-- The lateral part `f − f̄` of a test function is orthogonal to every radial test function. -/
theorem integral_symmTest_mul_lat (fT φ : LQGMetric.TestC) :
    ∫ x, GMCFacts.symmTest φ x * (fT - GMCFacts.symmTest fT) x = 0 := by
  have hint : ∀ u v : LQGMetric.TestC, Integrable (fun x => u x * v x) := fun u v =>
    (u.continuous.mul v.continuous).integrable_of_hasCompactSupport u.hasCompactSupport.mul_right
  have hrot : GMCFacts.IsRotInv ⇑(GMCFacts.symmTest φ) := GMCFacts.isRotInv_rotSymm ⇑φ
  have h1 := GMCFacts.integral_symmTest_mul fT hrot (GMCFacts.symmTest φ).continuous.locallyIntegrable
  have e : (fun x => GMCFacts.symmTest φ x * (fT - GMCFacts.symmTest fT) x) =
      fun x => GMCFacts.symmTest φ x * fT x - GMCFacts.symmTest φ x * GMCFacts.symmTest fT x := by
    funext x
    rw [show (fT - GMCFacts.symmTest fT) x = fT x - GMCFacts.symmTest fT x from rfl]
    ring
  rw [e, integral_sub (hint _ _) (hint _ _)]
  have e2 : ∫ x, GMCFacts.symmTest φ x * fT x = ∫ x, fT x * GMCFacts.symmTest φ x := by
    congr 1; funext x; ring
  have e3 : ∫ x, GMCFacts.symmTest φ x * GMCFacts.symmTest fT x =
      ∫ x, GMCFacts.symmTest fT x * GMCFacts.symmTest φ x := by
    congr 1; funext x; ring
  rw [e2, e3, h1, sub_self]

end Bump

/-! ### The cone field of the data and its shift -/

section Field

/-- The cone field with lateral part `y.1` and radial path read off the Brownian pair `y.2`. -/
def coneFieldOfData (γ β : ℝ) (y : LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) : LQGMetric.DistC :=
  ConeScaling.fieldOf y.1 (ConeScaling.radMap γ β y.2)

theorem measurable_coneFieldOfData (γ β : ℝ) : Measurable (coneFieldOfData γ β) :=
  ConeScaling.measurable_fieldOf.comp
    (measurable_fst.prodMk ((ConeScaling.measurable_radMap γ β).comp measurable_snd))

theorem ofFunC_add' {u v : ℂ → ℝ} (hu : LocallyIntegrable u volume) (hv : LocallyIntegrable v volume) :
    CellScaling.ofFunC (fun z => u z + v z) = CellScaling.ofFunC u + CellScaling.ofFunC v := by
  unfold CellScaling.ofFunC
  exact Distribution.ofFun_add
    (by rw [TopologicalSpace.Opens.coe_top]; exact hu.locallyIntegrableOn Set.univ)
    (by rw [TopologicalSpace.Opens.coe_top]; exact hv.locallyIntegrableOn Set.univ)

/-- **The shifted data carry the cone field plus the bump**: adding `f − f̄` to the lateral part and
`t ↦ f̄(e^{−t})` to the inward Brownian motion adds `f` to the cone field. -/
theorem coneFieldOfData_shift {γ β : ℝ} {fT : LQGMetric.TestC} (hfs : tsupport ⇑fT ⊆ ball (0 : ℂ) 1 \ {0})
    {y : LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))} (hy : y.2 ∈ ConeScaling.radGood γ β)
    (hli : LocallyIntegrable (ConeScaling.radialOf (ConeScaling.radMap γ β y.2)) volume)
    (gC : C(ℝ≥0, ℝ)) (hgC : ∀ t, gC t = bumpRad fT t) :
    coneFieldOfData γ β (y.1 + CellScaling.ofFunC ⇑(fT - GMCFacts.symmTest fT), (y.2.1 + gC, y.2.2)) =
      coneFieldOfData γ β y + CellScaling.ofFunC ⇑fT := by
  obtain ⟨r₀, hr₀pos, hr₀⟩ := exists_symmTest_eq_zero_near_zero hfs
  have hg0 : bumpRad fT 0 = 0 := bumpRad_eq_zero_of_nonpos hfs le_rfl
  have hmem : (y.2.1 + gC, y.2.2) ∈ ConeScaling.radGood γ β := by
    refine ⟨?_, hy.2.1, hy.2.2⟩
    show (y.2.1 + gC) 0 = 0
    rw [ContinuousMap.add_apply, hy.1, hgC, NNReal.coe_zero, hg0, add_zero]
  let Gw : C(ℝ, ℝ) := ⟨bumpRad fT, (contDiff_bumpRad fT).continuous⟩
  have hw : ConeScaling.radMap γ β (y.2.1 + gC, y.2.2) = ConeScaling.radMap γ β y.2 + Gw := by
    ext t
    rw [ContinuousMap.add_apply, ConeScaling.radMap_apply, ConeScaling.radMap_apply, ite_eq_left hmem,
      ite_eq_left hy]
    show CellScaling.coneRadial γ β ⇑(y.2.1 + gC) ⇑y.2.2 t =
      CellScaling.coneRadial γ β ⇑y.2.1 ⇑y.2.2 t + bumpRad fT t
    unfold CellScaling.coneRadial
    by_cases ht : 0 ≤ t
    · rw [ite_eq_left ht, ite_eq_left ht, ContinuousMap.add_apply, hgC, Real.coe_toNNReal t ht]
      ring
    · rw [ite_eq_right ht, ite_eq_right ht, bumpRad_eq_zero_of_nonpos hfs (le_of_lt (not_le.1 ht)),
        add_zero]
  have hradial : ConeScaling.radialOf (ConeScaling.radMap γ β y.2 + Gw) =
      fun z => ConeScaling.radialOf (ConeScaling.radMap γ β y.2) z + GMCFacts.symmTest fT z := by
    funext z
    show (ConeScaling.radMap γ β y.2 + Gw) (-Real.log ‖z‖) = _
    rw [ContinuousMap.add_apply]
    show _ + bumpRad fT (-Real.log ‖z‖) = _
    rw [bumpRad_radial hfs hr₀pos hr₀ z]
    rfl
  have hfS : LocallyIntegrable ⇑(GMCFacts.symmTest fT) volume :=
    (GMCFacts.symmTest fT).continuous.locallyIntegrable
  have hfL : LocallyIntegrable ⇑(fT - GMCFacts.symmTest fT) volume :=
    (fT - GMCFacts.symmTest fT).continuous.locallyIntegrable
  have hf : CellScaling.ofFunC ⇑fT = CellScaling.ofFunC ⇑(fT - GMCFacts.symmTest fT) +
      CellScaling.ofFunC ⇑(GMCFacts.symmTest fT) := by
    rw [← ofFunC_add' hfL hfS]
    congr 1
    funext z
    show fT z = fT z - GMCFacts.symmTest fT z + GMCFacts.symmTest fT z
    ring
  dsimp only [coneFieldOfData, ConeScaling.fieldOf]
  rw [hw, hradial, ofFunC_add' hli hfS, hf]
  abel

end Field

/-! ### The area measure: Weyl scaling and a Borel version -/

section Area

/-- The `γ`-LQG area measure is the vague limit of the dyadic approximations whenever one exists. -/
theorem lqgArea_eq_of_isVagueLimitOn {γ : ℝ} {h : LQGMetric.DistC} {μ : Measure ℂ}
    (hμ : QuantumZipper.IsVagueLimitOn univ (MoTPort.areaApproxC γ h) μ) :
    CellScaling.lqgArea γ h = μ := by
  rw [LQGCone.lqgArea_eq_qAreaC]
  exact MoTPort.ConeArea.qAreaC_eq_of_isVagueLimitOn hμ

/-- Adding a continuous function bounded above by `M` multiplies the approximations by at most `e^{γ M}`. -/
theorem areaApproxC_add_ofFunC_le {γ : ℝ} (hγ : 0 < γ) {h : LQGMetric.DistC}
    (hc : MoTPort.ConeArea.HasCircleAvgs h) {f : ℂ → ℝ} (hfc : Continuous f) {M : ℝ} (hM : ∀ z, f z ≤ M)
    (k : ℕ) (K : Set ℂ) (hK : MeasurableSet K) :
    MoTPort.areaApproxC γ (h + CellScaling.ofFunC f) k K ≤
      ENNReal.ofReal (Real.exp (γ * M)) * MoTPort.areaApproxC γ h k K := by
  have e : CellScaling.ofFunC f = MoTPort.ofFunC f := rfl
  rw [e]
  unfold MoTPort.areaApproxC
  rw [withDensity_apply _ hK, withDensity_apply _ hK, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae (hc k)] with z hz
  obtain ⟨a, ha⟩ := hz
  rw [MoTPort.ConeArea3.circleAvg_add_ofFunC hfc.locallyIntegrable isOpen_univ hfc.continuousOn
    (QuantumZipper.radius_pos k) (subset_univ _) ha]
  have hbound : Real.circleAverage f z (QuantumZipper.radius k) ≤ M :=
    Real.circleAverage_mono_on_of_le_circle hfc.continuousOn.circleIntegrable' fun x _ => hM x
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hr : 0 ≤ QuantumZipper.radius k ^ (γ ^ 2 / 2) :=
    Real.rpow_nonneg (QuantumZipper.radius_pos k).le _
  have h1 : Real.exp (γ * (LQGMetric.circleAvg h (QuantumZipper.radius k) z +
      Real.circleAverage f z (QuantumZipper.radius k))) ≤
      Real.exp (γ * M) * Real.exp (γ * LQGMetric.circleAvg h (QuantumZipper.radius k) z) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  calc QuantumZipper.radius k ^ (γ ^ 2 / 2) * Real.exp (γ * (LQGMetric.circleAvg h (QuantumZipper.radius k) z +
        Real.circleAverage f z (QuantumZipper.radius k)))
      ≤ QuantumZipper.radius k ^ (γ ^ 2 / 2) *
        (Real.exp (γ * M) * Real.exp (γ * LQGMetric.circleAvg h (QuantumZipper.radius k) z)) :=
        mul_le_mul_of_nonneg_left h1 hr
    _ = Real.exp (γ * M) * (QuantumZipper.radius k ^ (γ ^ 2 / 2) *
        Real.exp (γ * LQGMetric.circleAvg h (QuantumZipper.radius k) z)) := by ring

/-- **Weyl scaling of the area measure**: if the approximations of `h` converge vaguely on `ℂ` to `μ` and are
eventually finite on compacts, so are those of `h + f` for a bounded continuous `f`, with limit `e^{γ f} μ`. -/
theorem areaGood_add_ofFunC {γ : ℝ} (hγ : 0 < γ) {h : LQGMetric.DistC}
    (hc : MoTPort.ConeArea.HasCircleAvgs h)
    (hgood : MoTPort.ConeArea4.AreaGood univ (MoTPort.areaApproxC γ h))
    {f : ℂ → ℝ} (hfc : Continuous f) (hfb : ∃ M, ∀ z, f z ≤ M) {μ : Measure ℂ}
    (hμ : QuantumZipper.IsVagueLimitOn univ (MoTPort.areaApproxC γ h) μ) :
    MoTPort.ConeArea4.AreaGood univ (MoTPort.areaApproxC γ (h + CellScaling.ofFunC f)) ∧
      QuantumZipper.IsVagueLimitOn univ (MoTPort.areaApproxC γ (h + CellScaling.ofFunC f))
        (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) := by
  have hlim := MoTPort.ConeArea3.isVagueLimitOn_areaApproxC_add_ofFunC isOpen_univ hμ hc hfc.measurable
    hfc.locallyIntegrable hfc.continuousOn
  obtain ⟨M, hM⟩ := hfb
  refine ⟨⟨⟨_, hlim⟩, fun K hK _ => ?_⟩, hlim⟩
  filter_upwards [hgood.2 K hK (subset_univ K)] with k hk
  exact (areaApproxC_add_ofFunC_le hγ hc hfc hM k K hK.measurableSet).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hk)

/-- The window map `w ↦ 2^m w − 2^m c₀` of `MoTPort.ConeArea4.ball_subset_image_U₀`. -/
def certHomeo (m : ℕ) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (((2 : ℝ) ^ m : ℝ) : ℂ) (by exact_mod_cast (pow_pos two_pos m).ne')).trans
    (Homeomorph.addRight (-((((2 : ℝ) ^ m : ℝ) : ℂ) * MoTPort.ConeArea4.c₀)))

/-- The countable certificate of vague convergence on `ℂ` with eventual finiteness on compacts: the
certificate `AreaCert U₀` of the approximations transported by every window map. -/
def AreaCertUniv (μs : ℕ → Measure ℂ) : Prop :=
  ∀ m : ℕ, MoTPort.ConeArea4.AreaCert MoTPort.ConeArea4.U₀ (fun k => (μs k).map (certHomeo m).symm)

theorem areaGood_univ_of_areaCertUniv {μs : ℕ → Measure ℂ} (h : AreaCertUniv μs) :
    MoTPort.ConeArea4.AreaGood univ μs := by
  refine MoTPort.ConeArea4.areaGood_univ_of_balls fun m => ?_
  have h1 := MoTPort.ConeArea4.areaGood_of_cert MoTPort.ConeArea4.isOpen_U₀ MoTPort.ConeArea4.U₀_subset_H
    MoTPort.ConeArea4.compl_U₀_nonempty (h m)
  have h2 := MoTPort.ConeArea4.areaGood_map MoTPort.ConeArea4.isOpen_U₀ h1 (certHomeo m)
  have e : (fun k => ((μs k).map (certHomeo m).symm).map (certHomeo m)) = μs := by
    funext k
    rw [Measure.map_map (certHomeo m).measurable (certHomeo m).symm.measurable,
      Homeomorph.self_comp_symm, Measure.map_id]
  rw [e] at h2
  exact MoTPort.ConeArea4.areaGood_mono isOpen_ball (MoTPort.ConeArea4.ball_subset_image_U₀ m) h2

theorem areaCertUniv_of_areaGood {μs : ℕ → Measure ℂ} (h : MoTPort.ConeArea4.AreaGood univ μs) :
    AreaCertUniv μs := fun m => by
  have h1 := MoTPort.ConeArea4.areaGood_map isOpen_univ h (certHomeo m).symm
  rw [Set.image_univ_of_surjective (certHomeo m).symm.surjective] at h1
  exact MoTPort.ConeArea4.cert_of_areaGood MoTPort.ConeArea4.isBounded_U₀
    (MoTPort.ConeArea4.areaGood_mono MoTPort.ConeArea4.isOpen_U₀ (subset_univ _) h1)

theorem measurableSet_areaCertUniv (γ : ℝ) :
    MeasurableSet {x : LQGMetric.DistC | AreaCertUniv (MoTPort.areaApproxC γ x)} := by
  unfold AreaCertUniv
  simp only [ofPred_forall]
  refine MeasurableSet.iInter fun m => ?_
  unfold MoTPort.ConeArea4.AreaCert
  simp only [ofPred_and, ofPred_forall, eventually_atTop]
  refine MeasurableSet.inter (MeasurableSet.iInter fun n => MeasurableSet.biInter
    LQGMetric.GMCIdent3.denseF_countable fun g hg => ?_) (MeasurableSet.iInter fun n => ?_)
  · have hφ : Continuous fun z => QuantumZipper.LQGMeas.openBump MoTPort.ConeArea4.U₀ n z * g z :=
      (QuantumZipper.LQGMeas.continuous_openBump _ n).mul (LQGMetric.GMCIdent3.denseF_dense.1 g hg).1
    have hmeas : ∀ k, Measurable fun x : LQGMetric.DistC =>
        ∫ z, QuantumZipper.LQGMeas.openBump MoTPort.ConeArea4.U₀ n z * g z
          ∂((MoTPort.areaApproxC γ x k).map (certHomeo m).symm) := by
      intro k
      have e : ∀ x : LQGMetric.DistC, ∫ z, QuantumZipper.LQGMeas.openBump MoTPort.ConeArea4.U₀ n z * g z
          ∂((MoTPort.areaApproxC γ x k).map (certHomeo m).symm) =
          ∫ z, (fun z => QuantumZipper.LQGMeas.openBump MoTPort.ConeArea4.U₀ n z * g z)
            ((certHomeo m).symm z) ∂(MoTPort.areaApproxC γ x k) := fun x =>
        integral_map (certHomeo m).symm.measurable.aemeasurable hφ.aestronglyMeasurable
      simp_rw [e]
      exact MoTPort.ConeArea4.measurable_integral_areaApproxC γ k
        (hφ.comp (certHomeo m).symm.continuous).measurable
    exact StronglyMeasurable.measurableSet_exists_tendsto fun k => (hmeas k).stronglyMeasurable
  · simp only [ofPred_exists, ofPred_forall]
    refine MeasurableSet.iUnion fun (N : ℕ) => MeasurableSet.iInter fun (k : ℕ) =>
      MeasurableSet.iInter fun (_ : N ≤ k) => ?_
    have hm : Measurable fun x : LQGMetric.DistC => (MoTPort.areaApproxC γ x k).map (certHomeo m).symm :=
      (Measure.measurable_map _ (certHomeo m).symm.measurable).comp
        (MoTPort.ConeArea.measurable_areaApproxC γ k)
    exact measurableSet_lt ((Measure.measurable_coe
      (MoTPort.ConeArea4.isClosed_cutSet _ n).measurableSet).comp hm) measurable_const

open Classical in
/-- **The area measure as a Borel function of the data**: the `γ`-LQG area measure of the cone field of the
data when its approximations carry the certificate `AreaCertUniv`, and `0` otherwise. -/
def coneAreaOf (γ β : ℝ) (y : LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) : Measure ℂ :=
  if AreaCertUniv (MoTPort.areaApproxC γ (coneFieldOfData γ β y)) then
    CellScaling.lqgArea γ (coneFieldOfData γ β y) else 0

theorem measurable_coneAreaOf (γ β : ℝ) : Measurable (coneAreaOf γ β) := by
  classical
  set S := {y : LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) |
    AreaCertUniv (MoTPort.areaApproxC γ (coneFieldOfData γ β y))} with hSdef
  have hS : MeasurableSet S := (measurable_coneFieldOfData γ β) (measurableSet_areaCertUniv γ)
  refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
  · have hlim : ∀ y : S, ∃ μ, CellScaling.IsVagueLimitC
        (CellScaling.lqgAreaApprox γ (coneFieldOfData γ β y.1)) μ := by
      intro y
      have hy : AreaCertUniv (MoTPort.areaApproxC γ (coneFieldOfData γ β y.1)) := y.2
      obtain ⟨⟨μ, hμ⟩, -⟩ := areaGood_univ_of_areaCertUniv hy
      exact ⟨μ, LQGCone.vagueLimitC_iff_vagueLimitOn_univ.2 hμ⟩
    have hinc : Measurable fun y : S => (⟨coneFieldOfData γ β y.1, hlim y⟩ :
        {h : LQGMetric.DistC | ∃ μ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ}) :=
      ((measurable_coneFieldOfData γ β).comp measurable_subtype_coe).subtype_mk
    convert (LatticeProb.LQG.measurable_lqgArea_subtype γ).comp hinc using 1
    funext y
    have hy : AreaCertUniv (MoTPort.areaApproxC γ (coneFieldOfData γ β y.1)) := y.2
    simp only [Set.domRestrict_apply, Function.comp_apply, coneAreaOf]
    exact ite_eq_left hy
  · convert (measurable_const : Measurable fun _ : (Sᶜ : Set _) => (0 : Measure ℂ)) using 1
    funext y
    have hy : ¬ AreaCertUniv (MoTPort.areaApproxC γ (coneFieldOfData γ β y.1)) := y.2
    simp only [Set.domRestrict_apply, coneAreaOf]
    exact ite_eq_right hy

/-- **The cone field has circle averages and good area approximations**, almost surely: for a whole-plane GFF
`X` and independent Brownian motions `B, B'`, `X` independent of the radial process, and `α < Q`, the
approximations of `coneField X (coneRadial γ α B B')` converge vaguely on `ℂ` and are eventually finite on
compacts (the proof of `LQGCone.ae_isVagueLimitC_coneField`). -/
theorem ae_areaGood_coneField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} {X : Ω → LQGMetric.DistC} {B B' : ℝ≥0 → Ω → ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < QuantumZipper.Qc γ) (hX : LQGMetric.IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P)
    (hXA : IndepFun X (fun ω t => LQGCone.motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t) P) :
    ∀ᵐ ω ∂P, MoTPort.ConeArea.HasCircleAvgs
        (CellScaling.coneField (X ω) (CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω))) ∧
      MoTPort.ConeArea4.AreaGood univ (MoTPort.areaApproxC γ
        (CellScaling.coneField (X ω) (CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω)))) := by
  let W : ℝ := 2 * γ * (QuantumZipper.Qc γ - α)
  have hW : 0 < W := by
    have : 0 < QuantumZipper.Qc γ - α := by linarith
    positivity
  have hconeAlpha : MoTPort.coneAlpha γ W = α := by
    dsimp [MoTPort.coneAlpha, W]
    field_simp
    ring
  let A : ℝ → Ω → ℝ := fun t ω => LQGCone.motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t
  have hA : MoTPort.IsConeProcess α (QuantumZipper.Qc γ) A P :=
    LQGCone.isConeProcess_motConeRadial hB hB' hBB'
  have hAlpha : MoTPort.IsConeProcess (MoTPort.coneAlpha γ W) (QuantumZipper.Qc γ) A P := by
    rw [hconeAlpha]
    exact hA
  have hpunct := MoTPort.ConeArea4.ae_isVagueLimitOn_coneField_punctured hX hA hγ hγ2
  have haway := MoTPort.ConeArea4.ae_fin_away_coneField hX hA hγ hγ2
  have htight := MoTPort.ConeArea6.b3' hγ hγ2 hW Ω _ P X A inferInstance hX hAlpha hXA
  have hcirc := LQGCone.ae_hasCircleAvgs_coneField hX hA
  filter_upwards [hpunct, haway, htight, hcirc] with ω hp hf ht hc
  obtain ⟨μ, hμ⟩ := hp
  have hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop, MoTPort.areaApproxC γ
      (MoTPort.coneField (MoTPort.lateralPartC (X ω)) (fun t => A t ω) (QuantumZipper.Qc γ)) k K < ⊤ :=
    fun K hK => MoTPort.ConeArea4.fin_of_away_of_tight hf ht hK
  have hfull := MoTPort.ConeArea2.isVagueLimitOn_univ_of_punctured hμ hfin ht
  rw [LQGCone.coneField_eq_motConeField]
  exact ⟨hc, ⟨μ, hfull⟩, fun K hK _ => hfin K hK⟩

end Area

/-! ### The quasi-invariance -/

/-- **`ConeAreaBumpTilt` holds**: for the `β`-quantum cone (`β ∈ {0, γ}`, `0 < γ < 2`), a random curve `e`
independent of the field and the radial Brownian motions, and a smooth `f` with compact support in
`B_1(0) \ {0}`, the law of `(e, μ_h)` is absolutely continuous with respect to the law of `(e, e^{γ f} μ_h)`. -/
theorem coneAreaBumpTilt (γ : ℝ) : ConeAreaBumpTilt γ := by
  intro Ω _ P _ β X B B' e hγ hβ hX hB hB' hind he heind f hf hfs
  obtain ⟨hXBB, hBB'⟩ := hind
  have hγ0 : 0 < γ := hγ.1
  have hγ2 : γ < 2 := hγ.2
  /- the bump as a test function, its lateral part and its radial profile -/
  let fT : LQGMetric.TestC :=
    { toFun := f
      contDiff' := hf
      hasCompactSupport' := IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 1)
        (isClosed_tsupport f) (hfs.trans (sdiff_subset.trans ball_subset_closedBall))
      tsupport_subset' := subset_univ _ }
  have hfs' : tsupport ⇑fT ⊆ ball (0 : ℂ) 1 \ {0} := hfs
  obtain ⟨r₀, hr₀pos, hr₀⟩ := exists_symmTest_eq_zero_near_zero hfs'
  set T : ℝ := max 0 (-Real.log r₀) + 1 with hTdef
  have hT : 0 ≤ T := by have := le_max_left 0 (-Real.log r₀); linarith
  have hgs := contDiff_bumpRad fT
  have hgd : Differentiable ℝ (bumpRad fT) := hgs.differentiable (by simp)
  have hg : ∀ x, HasDerivAt (bumpRad fT) (deriv (bumpRad fT) x) x := fun x => (hgd x).hasDerivAt
  have hg0 : bumpRad fT 0 = 0 := bumpRad_eq_zero_of_nonpos hfs' le_rfl
  have hg'T : ∀ x, T ≤ x → deriv (bumpRad fT) x = 0 := fun x hx =>
    deriv_bumpRad_eq_zero hr₀pos hr₀ (by have := le_max_right 0 (-Real.log r₀); linarith)
  have hg'c : ContinuousOn (deriv (bumpRad fT)) (Icc 0 (T + 1)) :=
    (hgs.continuous_deriv (by simp)).continuousOn
  let gC : C(ℝ≥0, ℝ) := ⟨fun t => bumpRad fT t, hgs.continuous.comp NNReal.continuous_coe⟩
  /- continuous versions of the Brownian motions and the data -/
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version hB
  obtain ⟨B'c, hB'cm, hB'c⟩ := ConeScaling.exists_continuousMap_version hB'
  let Z : Ω → LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) := fun ω =>
    (CellScaling.lateralPart (X ω), (Bc ω, B'c ω))
  let Z' : Ω → LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) := fun ω =>
    (CellScaling.lateralPart (X ω) + CellScaling.ofFunC ⇑(fT - GMCFacts.symmTest fT), (Bc ω + gC, B'c ω))
  have hlatm : Measurable fun ω => CellScaling.lateralPart (X ω) :=
    ConeScaling.measurable_lateralPart.comp hX.measurable
  have hZm : Measurable Z := hlatm.prodMk (hBcm.prodMk hB'cm)
  have hZ'm : Measurable Z' := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ hB'cm)
    · refine LQGMetric.GFFInv.measurable_distC_iff.2 fun φ => ?_
      exact ((LQGMetric.GFFInv.measurable_pair φ).comp hlatm).add_const
        (CellScaling.ofFunC ⇑(fT - GMCFacts.symmTest fT) φ)
    · exact ContinuousMap.measurable_iff_eval.2 fun t =>
        ((ContinuousMap.measurable_eval t).comp hBcm).add_const (gC t)
  /- the Cameron–Martin equivalence of null events -/
  have hCM := fun (U : Set ((LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) × C(ℝ, ℂ)))
      (hU : MeasurableSet U) =>
    measure_coneShift_eq_zero_iff hX hB hB' hXBB hBB' hBcm hB'cm hBc hB'c he heind
      (fT - GMCFacts.symmTest fT) (fun φ => integral_symmTest_mul_lat fT φ) hT hg hg0 hg'T hg'c gC
      (fun _ => rfl) hU
  /- the radial path of the cone -/
  have hβQ : 0 < CellScaling.lqgQ γ - β := by
    rcases hβ with h | h <;> rw [h]
    · unfold CellScaling.lqgQ
      have h1 : 0 < 2 / γ := by positivity
      have h2 : 0 < γ / 2 := by positivity
      linarith
    · exact CellScaling.lqgQ_sub_pos hγ0 hγ2
  have hQ : CellScaling.lqgQ γ = QuantumZipper.Qc γ := by dsimp [CellScaling.lqgQ, QuantumZipper.Qc]
  have hβQc : β < QuantumZipper.Qc γ := by rw [← hQ]; linarith
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ β (Bc ω, B'c ω)
  have hgoodBB : ∀ᵐ ω ∂P, (Bc ω, B'c ω) ∈ ConeScaling.radGood γ β ∧
      ∀ t, W ω t = CellScaling.coneRadial γ β (fun s => B s ω) (fun s => B' s ω) t := by
    filter_upwards [hBc, hB'c, hB.eval_zero_ae_eq_zero, hB'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift hB' hβQ] with ω h1 h2 h3 h4 hdrift
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B s ω := funext h1
    have e2 : (⇑(B'c ω) : ℝ≥0 → ℝ) = fun s => B' s ω := funext h2
    have hmem : (Bc ω, B'c ω) ∈ ConeScaling.radGood γ β := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ CellScaling.coneDrift γ β (⇑(B'c ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    refine ⟨hmem, fun t => ?_⟩
    show ConeScaling.radMap γ β (Bc ω, B'c ω) t = _
    rw [ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]
  have hXW : IndepFun X W P := by
    have hpath : (fun ω => ((fun t => B t ω), (fun t => B' t ω))) =ᵐ[P]
        fun ω => ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(B'c ω) : ℝ≥0 → ℝ)) := by
      filter_upwards [hBc, hB'c] with ω h1 h2
      ext t
      · exact (h1 t).symm
      · exact (h2 t).symm
    have hXC : IndepFun X (fun ω => (Bc ω, B'c ω)) P :=
      ConeScaling.indepFun_pair_continuousMap_of_coe (hXBB.congr (ae_eq_refl _) hpath)
    exact hXC.comp measurable_id (ConeScaling.measurable_radMap γ β)
  have hXA := IGLaw.indepFun_motConeRadial_alpha hXW (hgoodBB.mono fun ω h => h.2)
  have hcone := ae_areaGood_coneField hγ0 hγ2 hβQc hX hB hB' hBB' hXA
  have hli := MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile
    (LQGCone.isConeProcess_motConeRadial (γ := γ) (α := β) hB hB' hBB')
  /- the bound of the bump -/
  have hfb : ∃ M, ∀ z, f z ≤ M := by
    obtain ⟨C, hC⟩ := fT.continuous.bounded_above_of_compact_support fT.hasCompactSupport
    exact ⟨C, fun z => (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hC z)⟩
  /- the two area measures as Borel functions of the data -/
  have hae : ∀ᵐ ω ∂P, coneAreaOf γ β (Z ω) = quantumConeArea γ β X B B' ω ∧
      coneAreaOf γ β (Z' ω) = (quantumConeArea γ β X B B' ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * f z))) := by
    filter_upwards [hgoodBB, hcone, hli] with ω hBBω hconeω hliω
    obtain ⟨hmem, hWeq⟩ := hBBω
    obtain ⟨hc, hgood⟩ := hconeω
    have hF : coneFieldOfData γ β (Z ω) =
        CellScaling.coneField (X ω) (CellScaling.coneRadial γ β (fun s => B s ω) (fun s => B' s ω)) :=
      (IGLaw.coneField_eq_fieldOf_alpha γ β (X ω) hWeq).symm
    obtain ⟨μ, hμ⟩ := hgood.1
    have hlqg : CellScaling.lqgArea γ
        (CellScaling.coneField (X ω) (CellScaling.coneRadial γ β (fun s => B s ω) (fun s => B' s ω))) = μ :=
      lqgArea_eq_of_isVagueLimitOn hμ
    have hliW : LocallyIntegrable (ConeScaling.radialOf (W ω)) volume := by
      have e : ConeScaling.radialOf (W ω) = fun z : ℂ => QuantumZipper.Qc γ * (-Real.log ‖z‖) +
          LQGCone.motConeRadial γ β (fun s => B s ω) (fun s => B' s ω) (-Real.log ‖z‖) := by
        funext z
        rw [ConeScaling.radialOf, hWeq, LQGCone.coneRadial_eq_Q_add_motConeRadial, hQ]
      rw [e]
      exact hliω
    have hZ'F : coneFieldOfData γ β (Z' ω) = CellScaling.coneField (X ω)
        (CellScaling.coneRadial γ β (fun s => B s ω) (fun s => B' s ω)) + CellScaling.ofFunC f := by
      rw [← hF]
      exact coneFieldOfData_shift (y := Z ω) hfs' hmem hliW gC (fun _ => rfl)
    obtain ⟨hgood', hlim'⟩ := areaGood_add_ofFunC (f := f) hγ0 hc hgood fT.continuous hfb hμ
    have hcert : AreaCertUniv (MoTPort.areaApproxC γ (coneFieldOfData γ β (Z ω))) := by
      rw [hF]; exact areaCertUniv_of_areaGood hgood
    have hcert' : AreaCertUniv (MoTPort.areaApproxC γ (coneFieldOfData γ β (Z' ω))) := by
      rw [hZ'F]; exact areaCertUniv_of_areaGood hgood'
    refine ⟨?_, ?_⟩
    · unfold coneAreaOf
      rw [ite_eq_left hcert, hF]
      rfl
    · unfold coneAreaOf
      rw [ite_eq_left hcert', hZ'F, lqgArea_eq_of_isVagueLimitOn hlim']
      exact congrArg (fun ν : Measure ℂ => ν.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z)))
        hlqg.symm
  /- the absolute continuity -/
  have hm1 : Measurable fun ω => (e ω, coneAreaOf γ β (Z ω)) :=
    he.prodMk ((measurable_coneAreaOf γ β).comp hZm)
  have hm2 : Measurable fun ω => (e ω, coneAreaOf γ β (Z' ω)) :=
    he.prodMk ((measurable_coneAreaOf γ β).comp hZ'm)
  have hae1 : (fun ω => (e ω, quantumConeArea γ β X B B' ω)) =ᵐ[P]
      fun ω => (e ω, coneAreaOf γ β (Z ω)) := hae.mono fun ω h => congrArg (Prod.mk (e ω)) h.1.symm
  have hae2 : (fun ω => (e ω, (quantumConeArea γ β X B B' ω).withDensity
      (fun z => ENNReal.ofReal (Real.exp (γ * f z))))) =ᵐ[P]
      fun ω => (e ω, coneAreaOf γ β (Z' ω)) := hae.mono fun ω h => congrArg (Prod.mk (e ω)) h.2.symm
  rw [Measure.map_congr hae1, Measure.map_congr hae2]
  refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
  rw [Measure.map_apply hm2 hS] at h0
  rw [Measure.map_apply hm1 hS]
  have hU : MeasurableSet ((fun p : (LQGMetric.DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) × C(ℝ, ℂ) =>
      (p.2, coneAreaOf γ β p.1)) ⁻¹' S) :=
    (measurable_snd.prodMk ((measurable_coneAreaOf γ β).comp measurable_fst)) hS
  exact (hCM _ hU).1 h0

end MatedCRT
