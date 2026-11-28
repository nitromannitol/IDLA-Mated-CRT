import MatedCRT.FirstPass.Derived.LQGMeasureChartSmooth
import MatedCRT.FirstPass.Derived.HN9OfChartField
import MatedCRT.Proofs.Measurability.VagueWholePlane
import LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# The Borel map from fields on the unit disc to LQG measures

The measure map of the coordinate change of the LQG measure for all inverse charts: a Borel map `chartMeasure γ` from
arbitrary assignments of real numbers to the test functions on the unit disc `𝔻` to measures on `ℂ`, which sends the
pairings of a distribution `g` on `𝔻` to the vague limit in `𝔻` of the smooth approximations
`e^{γ g ∗ f_ε(z) + (γ²/2)(log ε + C)} dz` of Sheffield–Wang (2016), *Field-measure correspondence in Liouville quantum
gravity almost surely commutes with all conformal maps simultaneously* (arXiv:1605.06171v2), §3.2 after (3.4), along
the scales `ε = 2^{-k}`, whenever this limit exists (the weak convergence in `D` of Theorem 1.1 there).

* `discDecode`, `measurable_discDecode`, `discDecode_coe`: an assignment is read on the countable family of integer
  combinations of a determining family of test functions and decoded by the measurable left inverse of the coordinate
  map (`LQGMetric.pairJInv`); the zero distribution off the range. The decoder is measurable for the product σ-algebra
  on all assignments and recovers every distribution.
* `stdMollifier`, `isMollifier_stdMollifier`: a concrete bump function `z ↦ c · s(1/4 - ‖z‖²)` (`s` the smooth
  transition function), smooth, radial, supported in `closedBall 0 (1/2)` and of integral `1`.
* `continuousAt_pairFun_mollScale_of_ball`, `measurable_smoothApprox`, `measurable_integral_smoothApprox`,
  `smoothApprox_lt_top`: for a distribution `g` on an open set `V`, the smoothed field `z ↦ ⟨g, f_ε(z - ·)⟩` is
  continuous at the centres `z` with `B_ε(z) ⊆ V` (continuity of translation into the test functions supported in a
  fixed compact); it is measurable in `g`; hence the density of the smooth approximation is jointly measurable in the
  field and the centre (Carathéodory), the smooth approximation is a measurable function of `g` for the Giry
  σ-algebra, its integrals are measurable, and it is finite on compact sets.
* `discVagueLimit`, `measurableSet_exists_isVagueLimitOn_ball`, `measurable_discVagueLimit`: a chosen vague limit in
  the unit disc. The event that it exists is a countable intersection of convergence events (a countable dense family
  of test functions cut off by continuous bumps exhausting the disc), and the chosen limit is measurable (masses of
  open subsets of the disc are suprema of limits of integrals).
* `chartMeasure`, `measurable_chartMeasure`, `chartMeasure_eq_of_isVagueLimitOn`: the measure map, its measurability,
  and its value on the pairings of a distribution whose smooth approximations converge (uniqueness of vague limits).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped Distributions ENNReal NNReal

namespace MatedCRT

namespace LQGMeasureChart

/-! ### The decoder -/

/-- **The decoder.** An assignment `a` of real numbers to the test functions on the unit disc is read on the integer
combinations `LQGMetric.comb` of the determining family and decoded by the measurable left inverse
`LQGMetric.pairJInv` of the coordinate map (the zero distribution off its range). -/
def discDecode (a : 𝓓(unitDiscOpens, ℝ) → ℝ) : LQGMetric.DistOn unitDiscOpens :=
  LQGMetric.pairJInv unitDiscOpens fun c => a (LQGMetric.comb unitDiscOpens c)

/-- The decoder is measurable for the product σ-algebra on the assignments. -/
theorem measurable_discDecode : Measurable discDecode :=
  (LQGMetric.measurable_pairJInv unitDiscOpens).comp
    (Measurable.of_eval fun c => measurable_pi_apply (LQGMetric.comb unitDiscOpens c))

/-- The decoder recovers every distribution from its pairings. -/
theorem discDecode_coe (g : LQGMetric.DistOn unitDiscOpens) : discDecode ⇑g = g :=
  LQGMetric.pairJInv_pairJ unitDiscOpens g

/-! ### A concrete bump function -/

/-- The radial bump `z ↦ s(1/4 - ‖z‖²)`, `s` the smooth transition function. -/
def stdBump (z : ℂ) : ℝ :=
  Real.smoothTransition (1 / 4 - ‖z‖ ^ 2)

theorem contDiff_stdBump : ContDiff ℝ (⊤ : ℕ∞) stdBump :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem stdBump_eq_zero {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : stdBump z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith [norm_nonneg z])

theorem hasCompactSupport_stdBump : HasCompactSupport stdBump :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (1 / 2)) fun z hz =>
    stdBump_eq_zero (show 1 / 2 < ‖z‖ by simpa using hz).le

theorem integral_stdBump_pos : 0 < ∫ z, stdBump z :=
  Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) contDiff_stdBump.continuous
    hasCompactSupport_stdBump (fun z => Real.smoothTransition.nonneg _)
    (Real.smoothTransition.pos_of_pos (by norm_num)).ne'

/-- **A bump function** in the sense of Sheffield–Wang (2016), p. 2: the normalization of `stdBump`. -/
def stdMollifier (z : ℂ) : ℝ :=
  (∫ w, stdBump w)⁻¹ * stdBump z

theorem stdMollifier_eq_zero {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : stdMollifier z = 0 := by
  rw [stdMollifier, stdBump_eq_zero hz, mul_zero]

/-- `stdMollifier` is a bump function: smooth, nonnegative, radial, with compact support in the unit disc and
integral `1`. -/
theorem isMollifier_stdMollifier : IsMollifier stdMollifier where
  contDiff := contDiff_const.mul contDiff_stdBump
  nonneg z := mul_nonneg (inv_nonneg.2 integral_stdBump_pos.le) (Real.smoothTransition.nonneg _)
  radial z w h := by simp only [stdMollifier, stdBump, h]
  hasCompactSupport := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (1 / 2)) fun z hz =>
    stdMollifier_eq_zero (show 1 / 2 < ‖z‖ by simpa using hz).le
  tsupport_subset := by
    refine (closure_minimal (fun z hz => ?_) isClosed_closedBall).trans
      (closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1))
    by_contra h
    exact hz (stdMollifier_eq_zero (show 1 / 2 < ‖z‖ by simpa using h).le)
  integral_eq_one := by
    simp only [stdMollifier]
    rw [integral_const_mul, inv_mul_cancel₀ integral_stdBump_pos.ne']

/-! ### Continuity of the smoothed field in the centre -/

section Translate

variable {V : TopologicalSpace.Opens ℂ} {f : ℂ → ℝ} {ε : ℝ}

/-- The family `(z, w) ↦ f_ε(z - w)` is jointly smooth. -/
theorem contDiff_mollScale_sub (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry fun z w : ℂ => mollScale f ε (z - w)) := by
  show ContDiff ℝ (⊤ : ℕ∞) fun p : ℂ × ℂ => (ε ^ 2)⁻¹ * f ((p.1 - p.2) / (ε : ℂ))
  exact contDiff_const.mul (hf.comp ((contDiff_fst.sub contDiff_snd).div_const _))

theorem mollScale_eq_zero_of_le {ρ : ℝ} (hρ : ∀ u : ℂ, ρ ≤ ‖u‖ → f u = 0) (hε : 0 < ε) {v : ℂ}
    (hv : ε * ρ ≤ ‖v‖) : mollScale f ε v = 0 := by
  rw [mollScale, hρ, mul_zero]
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hε.le, le_div_iff₀ hε]
  linarith [mul_comm ρ ε]

/-- The pairing of a distribution with (the function of) a test function is its value. -/
theorem pairFun_testFunction (g : LQGMetric.DistOn V) (φ : LQGMetric.TestOn V) : pairFun g ⇑φ = g φ := by
  have h : ContDiff ℝ (⊤ : ℕ∞) ⇑φ ∧ HasCompactSupport ⇑φ ∧ tsupport ⇑φ ⊆ V :=
    ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
  unfold pairFun
  exact (dite_eq_left h).trans rfl

/-- The pairing of `g` with the measurable family of translates `f_ε(z - ·)` is measurable in `g`. -/
theorem measurable_pairFun (u : ℂ → ℝ) : Measurable fun g : LQGMetric.DistOn V => pairFun g u := by
  by_cases hu : ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ V
  · simp only [pairFun, dite_eq_left hu]
    exact LQGMetric.measurable_distOn_apply _
  · simp only [pairFun, dite_eq_right hu]
    exact measurable_const

/-- **Continuity of the smoothed field.** If `f` vanishes off `ball 0 ρ` and `closedBall z₀ (ερ + δ) ⊆ V`, then
`z ↦ ⟨g, f_ε(z - ·)⟩` is continuous at `z₀`: for `z ∈ closedBall z₀ δ` the translates are supported in the fixed
compact `closedBall z₀ (ερ + δ)`, and translation is continuous into the test functions supported there. -/
theorem continuousAt_pairFun_mollScale (g : LQGMetric.DistOn V) (hf : ContDiff ℝ (⊤ : ℕ∞) f) {ρ δ : ℝ}
    (hρ : ∀ u : ℂ, ρ ≤ ‖u‖ → f u = 0) (hε : 0 < ε) (hδ : 0 < δ) {z₀ : ℂ}
    (hV : closedBall z₀ (ε * ρ + δ) ⊆ V) :
    ContinuousAt (fun z => pairFun g fun w => mollScale f ε (z - w)) z₀ := by
  let X := closedBall z₀ δ
  have : CompactSpace X := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let K : TopologicalSpace.Compacts ℂ := ⟨closedBall z₀ (ε * ρ + δ), isCompact_closedBall _ _⟩
  let Ψ : X → ℂ → ℝ := fun x w => mollScale f ε ((x : ℂ) - w)
  have hs : ∀ x : X, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ x) := fun x =>
    (contDiff_mollScale_sub hf ε).comp (contDiff_const.prodMk contDiff_id)
  have hK : ∀ x : X, ∀ w ∉ (K : Set ℂ), Ψ x w = 0 := by
    intro x w hw
    have hw' : ε * ρ + δ < dist w z₀ := by simpa [K] using hw
    have hx : dist (x : ℂ) z₀ ≤ δ := mem_closedBall.1 x.2
    apply mollScale_eq_zero_of_le hρ hε
    have h1 := dist_triangle w (x : ℂ) z₀
    rw [dist_comm w (x : ℂ)] at h1
    rw [← dist_eq_norm]
    linarith
  have hD : ∀ i : ℕ, Continuous fun p : X × ℂ => iteratedFDeriv ℝ i (Ψ p.1) p.2 := fun i =>
    (LQGMetric.continuous_iteratedFDeriv_snd (contDiff_mollScale_sub hf ε) i).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hc := LQGMetric.continuous_testFamK K Ψ hs hK hD
  let T : X → LQGMetric.TestOn V := fun x =>
    TestFunction.ofSupportedIn (show (K : Set ℂ) ⊆ V from hV) (LQGMetric.testFamK K Ψ hs hK x)
  have hTc : Continuous T := (TestFunction.continuous_ofSupportedIn _).comp hc
  have heq : ∀ x : X, (pairFun g fun w => mollScale f ε ((x : ℂ) - w)) = g (T x) := by
    intro x
    exact pairFun_testFunction g (T x)
  have h2 : Continuous fun x : X => pairFun g fun w => mollScale f ε ((x : ℂ) - w) := by
    simp_rw [heq]
    exact (map_continuous g).comp hTc
  exact ((continuousOn_iff_continuous_domRestrict (f := fun z => pairFun g fun w => mollScale f ε (z - w))
    (s := X)).2 h2).continuousAt (closedBall_mem_nhds _ hδ)

/-- A bump function vanishes off a disc `ball 0 r` with `r < 1`. -/
theorem IsMollifier.exists_lt_one_eq_zero (hf : IsMollifier f) : ∃ r < 1, ∀ u : ℂ, r ≤ ‖u‖ → f u = 0 := by
  obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball (isClosed_tsupport f) hf.tsupport_subset
  refine ⟨r, hr, fun u hu => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := hsub h
  rw [mem_ball, dist_zero_right] at this
  linarith

/-- **Continuity of the smoothed field** at every centre `z₀` with `B_ε(z₀) ⊆ V`. -/
theorem continuousAt_pairFun_mollScale_of_ball (g : LQGMetric.DistOn V) (hf : IsMollifier f) (hε : 0 < ε)
    {z₀ : ℂ} (hz : ball z₀ ε ⊆ V) :
    ContinuousAt (fun z => pairFun g fun w => mollScale f ε (z - w)) z₀ := by
  obtain ⟨r, hr, hr0⟩ := hf.exists_lt_one_eq_zero
  have h1 : 0 < ε * (1 - r) := mul_pos hε (sub_pos.2 hr)
  refine continuousAt_pairFun_mollScale g hf.contDiff hr0 hε (div_pos h1 two_pos) ?_
  exact (closedBall_subset_ball (by linarith)).trans hz

end Translate

/-! ### Measurability of the smooth approximations in the field -/

section SmoothMeasurable

variable {V : TopologicalSpace.Opens ℂ} {f : ℂ → ℝ} {ε : ℝ}

theorem isOpen_setOf_closedBall_subset (V : TopologicalSpace.Opens ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    IsOpen {z : ℂ | closedBall z ε ⊆ V} := by
  refine Metric.isOpen_iff.2 fun z hz => ?_
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall z ε).exists_cthickening_subset_open V.isOpen hz
  rw [cthickening_closedBall hδ.le hε] at hsub
  refine ⟨δ, hδ, fun z' hz' => (closedBall_subset_closedBall' ?_).trans hsub⟩
  rw [mem_ball] at hz'
  linarith

theorem isClosed_setOf_ball_subset (V : Set ℂ) (ε : ℝ) : IsClosed {z : ℂ | ball z ε ⊆ V} := by
  have e : {z : ℂ | ball z ε ⊆ V} = ⋂ w ∈ Vᶜ, {z | ε ≤ dist z w} := by
    ext z
    simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff]
    constructor
    · intro h w hw
      by_contra hlt
      exact hw (h (mem_ball'.2 (not_le.1 hlt)))
    · intro h w hw
      by_contra hwV
      exact absurd (h w hwV) (not_le.2 (mem_ball'.1 hw))
  rw [e]
  exact isClosed_biInter fun w _ => isClosed_le continuous_const (continuous_id.dist continuous_const)

open Classical in
/-- The density `e^{h̃_ε(z)} 1_{B̄_ε(z) ⊆ V}` of the smooth approximation, as a real function of the field and the
centre. -/
def smoothDensity (γ : ℝ) (f : ℂ → ℝ) (V : TopologicalSpace.Opens ℂ) (ε : ℝ) (g : LQGMetric.DistOn V) (z : ℂ) :
    ℝ :=
  if closedBall z ε ⊆ V then Real.exp (smoothExponent γ f (pairFun g) ε z) else 0

theorem smoothDensity_nonneg (γ : ℝ) (f : ℂ → ℝ) (V : TopologicalSpace.Opens ℂ) (ε : ℝ) (g : LQGMetric.DistOn V)
    (z : ℂ) : 0 ≤ smoothDensity γ f V ε g z := by
  unfold smoothDensity
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem smoothApprox_eq_withDensity (γ : ℝ) (f : ℂ → ℝ) (ε : ℝ) (g : LQGMetric.DistOn V) :
    smoothApprox γ f V (pairFun g) ε =
      volume.withDensity fun z => ENNReal.ofReal (smoothDensity γ f V ε g z) := by
  unfold smoothApprox smoothDensity
  congr 1
  funext z
  split_ifs <;> simp

/-- **Joint measurability of the density** in the field and the centre (Carathéodory: continuous in the centre on the
open set of centres `z` with `B̄_ε(z) ⊆ V`, measurable in the field). -/
theorem measurable_smoothDensity (γ : ℝ) (hf : IsMollifier f) (hε : 0 < ε) :
    Measurable (Function.uncurry (smoothDensity γ f V ε)) := by
  set S : Set ℂ := {z | closedBall z ε ⊆ V}
  have hSm : MeasurableSet {p : LQGMetric.DistOn V × ℂ | p.2 ∈ S} :=
    measurable_snd (isOpen_setOf_closedBall_subset V hε.le).measurableSet
  let u : S → LQGMetric.DistOn V → ℝ := fun z g =>
    γ * pairFun g (fun w => mollScale f ε ((z : ℂ) - w)) + γ ^ 2 / 2 * (Real.log ε + mollConst f)
  have hu : Measurable (Function.uncurry u) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun g => ?_) (fun z => ?_)
    · have hcont : ContinuousOn (fun z : ℂ =>
          γ * pairFun g (fun w => mollScale f ε (z - w)) + γ ^ 2 / 2 * (Real.log ε + mollConst f)) S :=
        fun z hz => ((continuousAt_const.mul (continuousAt_pairFun_mollScale_of_ball g hf hε
          (ball_subset_closedBall.trans hz))).add continuousAt_const).continuousWithinAt
      exact continuousOn_iff_continuous_domRestrict.1 hcont
    · exact ((measurable_pairFun _).const_mul γ).add_const _
  have hmap : Measurable fun p : {p : LQGMetric.DistOn V × ℂ | p.2 ∈ S} => ((⟨p.1.2, p.2⟩ : S), p.1.1) :=
    (measurable_snd.comp measurable_subtype_coe).subtype_mk.prodMk (measurable_fst.comp measurable_subtype_coe)
  refine measurable_of_restrict_of_restrict_compl hSm ?_ ?_
  · have e : ({p : LQGMetric.DistOn V × ℂ | p.2 ∈ S}).domRestrict (Function.uncurry (smoothDensity γ f V ε)) =
        fun p => Real.exp (Function.uncurry u ((⟨p.1.2, p.2⟩ : S), p.1.1)) := by
      funext p
      show smoothDensity γ f V ε p.1.1 p.1.2 = _
      rw [smoothDensity, ite_eq_left (show closedBall (p : LQGMetric.DistOn V × ℂ).2 ε ⊆ V from p.2)]
      rfl
    rw [e]
    exact Real.measurable_exp.comp (hu.comp hmap)
  · have e : ({p : LQGMetric.DistOn V × ℂ | p.2 ∈ S}ᶜ).domRestrict (Function.uncurry (smoothDensity γ f V ε)) =
        fun _ => 0 := by
      funext p
      show smoothDensity γ f V ε p.1.1 p.1.2 = 0
      rw [smoothDensity, ite_eq_right (show ¬closedBall (p : LQGMetric.DistOn V × ℂ).2 ε ⊆ V from p.2)]
    rw [e]
    exact measurable_const

/-- **The smooth approximation is a measurable function of the field** (Giry σ-algebra on `Measure ℂ`). -/
theorem measurable_smoothApprox (γ : ℝ) (hf : IsMollifier f) (hε : 0 < ε) :
    Measurable fun g : LQGMetric.DistOn V => smoothApprox γ f V (pairFun g) ε := by
  simp_rw [smoothApprox_eq_withDensity]
  exact measurable_withDensity (ENNReal.measurable_ofReal.comp (measurable_smoothDensity γ hf hε))

theorem integral_withDensity_ofReal_eq {μ : Measure ℂ} {c : ℂ → ℝ} (hc : Measurable c) (hc0 : ∀ z, 0 ≤ c z)
    (h : ℂ → ℝ) : ∫ z, h z ∂(μ.withDensity fun z => ENNReal.ofReal (c z)) = ∫ z, c z * h z ∂μ := by
  rw [show (fun z => ENNReal.ofReal (c z)) = fun z => ((Real.toNNReal (c z) : ℝ≥0) : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul hc.real_toNNReal]
  congr 1
  funext z
  rw [NNReal.smul_def, Real.coe_toNNReal _ (hc0 z), smul_eq_mul]

/-- The integrals of a measurable function against the smooth approximations are measurable in the field. -/
theorem measurable_integral_smoothApprox (γ : ℝ) (hf : IsMollifier f) (hε : 0 < ε) {φ : ℂ → ℝ}
    (hφ : Measurable φ) :
    Measurable fun g : LQGMetric.DistOn V => ∫ z, φ z ∂smoothApprox γ f V (pairFun g) ε := by
  have hd := measurable_smoothDensity (V := V) γ hf hε
  have e : ∀ g : LQGMetric.DistOn V, ∫ z, φ z ∂smoothApprox γ f V (pairFun g) ε =
      ∫ z, smoothDensity γ f V ε g z * φ z := fun g => by
    rw [smoothApprox_eq_withDensity, integral_withDensity_ofReal_eq (c := smoothDensity γ f V ε g)
      (hd.comp measurable_prodMk_left) (smoothDensity_nonneg γ f V ε g) φ]
  simp_rw [e]
  exact (hd.mul (hφ.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

/-- The smooth approximations are finite on compact sets: the density vanishes off the closed set of centres `z` with
`B_ε(z) ⊆ V`, on which the smoothed field is continuous. -/
theorem smoothApprox_lt_top (γ : ℝ) (hf : IsMollifier f) (hε : 0 < ε) (g : LQGMetric.DistOn V) {K : Set ℂ}
    (hK : IsCompact K) : smoothApprox γ f V (pairFun g) ε K < ∞ := by
  set T : Set ℂ := {z | ball z ε ⊆ V}
  have hT : IsClosed T := isClosed_setOf_ball_subset V ε
  set F : ℂ → ℝ := fun z => Real.exp (smoothExponent γ f (pairFun g) ε z)
  have hFc : ContinuousOn F T := fun z hz =>
    (Real.continuous_exp.continuousAt.comp ((continuousAt_const.mul
      (continuousAt_pairFun_mollScale_of_ball g hf hε hz)).add continuousAt_const)).continuousWithinAt
  have hint : ∫⁻ z in T ∩ K, ENNReal.ofReal (F z) < ∞ :=
    ((hFc.mono inter_subset_left).integrableOn_compact (hK.inter_left hT)).lintegral_lt_top
  have hle : ∀ z, ENNReal.ofReal (smoothDensity γ f V ε g z) ≤ T.indicator (fun z => ENNReal.ofReal (F z)) z := by
    intro z
    unfold smoothDensity
    split_ifs with h
    · exact (indicator_of_mem (show z ∈ T from ball_subset_closedBall.trans h)
        (fun z => ENNReal.ofReal (F z))).symm.le
    · simp
  rw [smoothApprox_eq_withDensity, withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (smoothDensity γ f V ε g z)
      ≤ ∫⁻ z in K, T.indicator (fun z => ENNReal.ofReal (F z)) z := lintegral_mono hle
    _ = ∫⁻ z in T ∩ K, ENNReal.ofReal (F z) := by
      rw [lintegral_indicator hT.measurableSet, Measure.restrict_restrict hT.measurableSet]
    _ < ∞ := hint

end SmoothMeasurable

/-! ### A measurable choice of vague limits in the unit disc -/

section VagueDisc

open QuantumZipper.LQGMeas

open Classical in
/-- A chosen vague limit in the unit disc (`QuantumZipper.IsVagueLimitOn (ball 0 1)`), `0` if there is none. -/
def discVagueLimit (μs : ℕ → Measure ℂ) : Measure ℂ :=
  if h : ∃ ν, QuantumZipper.IsVagueLimitOn (ball 0 1) μs ν then h.choose else 0

theorem discVagueLimit_spec {μs : ℕ → Measure ℂ} (h : ∃ ν, QuantumZipper.IsVagueLimitOn (ball 0 1) μs ν) :
    QuantumZipper.IsVagueLimitOn (ball 0 1) μs (discVagueLimit μs) := by
  unfold discVagueLimit
  rw [dite_eq_left h]
  exact h.choose_spec

theorem discVagueLimit_of_not {μs : ℕ → Measure ℂ} (h : ¬∃ ν, QuantumZipper.IsVagueLimitOn (ball 0 1) μs ν) :
    discVagueLimit μs = 0 := by
  unfold discVagueLimit
  rw [dite_eq_right h]

/-- The chosen limit is the vague limit in the disc whenever one exists. -/
theorem discVagueLimit_eq {μs : ℕ → Measure ℂ} {ν : Measure ℂ}
    (h : QuantumZipper.IsVagueLimitOn (ball 0 1) μs ν) : discVagueLimit μs = ν :=
  QuantumZipper.isVagueLimitOn_unique isOpen_ball (discVagueLimit_spec ⟨ν, h⟩) h

/-- The continuous cutoffs `openBump (ball 0 1) j` are eventually `1` on every compact subset of the disc. -/
theorem exists_openBump_ball_eq_one {K : Set ℂ} (hK : IsCompact K) (hK1 : K ⊆ ball 0 1) :
    ∃ j : ℕ, ∀ z ∈ K, openBump (ball (0 : ℂ) 1) j z = 1 := by
  obtain ⟨r, hr, hKr⟩ := exists_lt_subset_ball hK.isClosed hK1
  obtain ⟨j, hj⟩ := exists_nat_gt (2 / (1 - r))
  have h1r : 0 < 1 - r := by linarith
  refine ⟨j, fun z hz => ?_⟩
  have hzr : ‖z‖ < r := by simpa using hKr hz
  have hd : 1 - r ≤ infDist z (ball (0 : ℂ) 1)ᶜ := by
    refine (le_infDist ⟨1, by simp⟩).2 fun y hy => ?_
    have hy1 : 1 ≤ ‖y‖ := by simpa using hy
    have := norm_sub_norm_le y z
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  rw [div_lt_iff₀ h1r] at hj
  have h2 : 2 ≤ (j : ℝ) * infDist z (ball (0 : ℂ) 1)ᶜ := by
    linarith [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α := ℝ) j)]
  rw [openBump, max_eq_right (by linarith), min_eq_left (by linarith)]

/-- **Existence of a vague limit in the disc from countably many tests.** For measures finite on compact sets and a
countable dense family `F` of test functions on `ℂ`, a vague limit in the unit disc exists if and only if the
integrals of `g · openBump (ball 0 1) j` converge for all `g ∈ F` and all `j`. -/
theorem exists_isVagueLimitOn_ball_iff {μs : ℕ → Measure ℂ} (hfin : ∀ k K, IsCompact K → μs k K < ∞)
    {F : Set (ℂ → ℝ)} (hF : VagueWholePlane.IsDenseTestFamilyC F) :
    (∃ ν, QuantumZipper.IsVagueLimitOn (ball 0 1) μs ν) ↔
      ∀ j : ℕ, ∀ g ∈ F, ∃ l, Tendsto (fun k => ∫ z, g z * openBump (ball (0 : ℂ) 1) j z ∂μs k) atTop (𝓝 l) := by
  constructor
  · rintro ⟨ν, hν⟩ j g hg
    exact ⟨_, hν.2.2 _ ((hF.1 g hg).1.mul (continuous_openBump _ j))
      (HasCompactSupport.mul_left (f := g) (hasCompactSupport_openBump isBounded_ball j))
      (tsupport_mul_subset_right.trans (tsupport_openBump_subset _ j))⟩
  · intro hconv
    refine QuantumZipper.VagueOpen.exists_isVagueLimitOn_of_tendsto_open isOpen_ball
      (fun K hK _ => Eventually.of_forall fun k => hfin k K hK) fun f hf hfc hfU => ?_
    obtain ⟨j, hj⟩ := exists_openBump_ball_eq_one hfc.isCompact hfU
    have hχm : Measurable (openBump (ball (0 : ℂ) 1) j) := (continuous_openBump _ j).measurable
    let ms : ℕ → Measure ℂ := fun k =>
      (μs k).withDensity fun z => ENNReal.ofReal (openBump (ball (0 : ℂ) 1) j z)
    have hms : ∀ k (h : ℂ → ℝ), ∫ z, h z ∂ms k = ∫ z, openBump (ball (0 : ℂ) 1) j z * h z ∂μs k :=
      fun k h => integral_withDensity_ofReal_eq hχm (openBump_nonneg _ j) h
    have hfin' : ∀ K, IsCompact K → ∀ᶠ k in atTop, ms k K < ∞ := fun K hK =>
      Eventually.of_forall fun k => by
        calc ms k K = ∫⁻ z in K, ENNReal.ofReal (openBump (ball (0 : ℂ) 1) j z) ∂μs k :=
              withDensity_apply _ hK.measurableSet
          _ ≤ ∫⁻ _ in K, 1 ∂μs k := lintegral_mono fun z => ENNReal.ofReal_le_one.2 (openBump_le_one _ j z)
          _ = μs k K := setLIntegral_one K
          _ < ∞ := hfin k K hK
    have hconv' : ∀ g ∈ F, ∃ l, Tendsto (fun k => ∫ z, g z ∂ms k) atTop (𝓝 l) := by
      intro g hg
      obtain ⟨l, hl⟩ := hconv j g hg
      refine ⟨l, hl.congr fun k => ?_⟩
      rw [hms]
      congr 1
      funext z
      ring
    obtain ⟨l, hl⟩ := VagueWholePlane.tendsto_of_denseTestFamilyC hfin' hF hconv' f ⟨hf, hfc⟩
    refine ⟨l, hl.congr fun k => ?_⟩
    rw [hms]
    congr 1
    funext z
    by_cases hz : z ∈ tsupport f
    · rw [hj z hz, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The event that a vague limit in the disc exists is measurable**, for measures finite on compact sets whose
integrals against continuous compactly supported functions are measurable. -/
theorem measurableSet_exists_isVagueLimitOn_ball {m : Ω → ℕ → Measure ℂ}
    (hfin : ∀ ω k K, IsCompact K → m ω k K < ∞)
    (hint : ∀ k (φ : ℂ → ℝ), Continuous φ → HasCompactSupport φ → Measurable fun ω => ∫ z, φ z ∂m ω k) :
    MeasurableSet {ω | ∃ ν, QuantumZipper.IsVagueLimitOn (ball 0 1) (m ω) ν} := by
  obtain ⟨F, hFc, hF⟩ := VagueWholePlane.exists_denseTestFamilyC
  have e : {ω | ∃ ν, QuantumZipper.IsVagueLimitOn (ball 0 1) (m ω) ν} =
      ⋂ j : ℕ, ⋂ g ∈ F, {ω | ∃ l, Tendsto (fun k => ∫ z, g z * openBump (ball (0 : ℂ) 1) j z ∂m ω k) atTop
        (𝓝 l)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    exact exists_isVagueLimitOn_ball_iff (hfin ω) hF
  rw [e]
  exact MeasurableSet.iInter fun j => MeasurableSet.biInter hFc fun g hg =>
    measurableSet_exists_tendsto fun k => hint k _ ((hF.1 g hg).1.mul (continuous_openBump _ j))
      (HasCompactSupport.mul_left (f := g) (hasCompactSupport_openBump isBounded_ball j))

/-- **A measurable choice of vague limits in the unit disc.** For measures finite on compact sets whose integrals
against continuous compactly supported functions are measurable, the chosen vague limit in the disc is measurable for
the Giry σ-algebra. -/
theorem measurable_discVagueLimit {m : Ω → ℕ → Measure ℂ} (hfin : ∀ ω k K, IsCompact K → m ω k K < ∞)
    (hint : ∀ k (φ : ℂ → ℝ), Continuous φ → HasCompactSupport φ → Measurable fun ω => ∫ z, φ z ∂m ω k) :
    Measurable fun ω => discVagueLimit (m ω) := by
  set E := {ω | ∃ ν, QuantumZipper.IsVagueLimitOn (ball 0 1) (m ω) ν}
  have hE : MeasurableSet E := measurableSet_exists_isVagueLimitOn_ball hfin hint
  let Vn : ℕ → Set ℂ := fun N => ball 0 (1 - 1 / ((N : ℝ) + 2))
  have hVsub : ∀ N : ℕ, closedBall (0 : ℂ) (1 - 1 / ((N : ℝ) + 2)) ⊆ ball 0 1 := by
    intro N
    have : 0 < 1 / ((N : ℝ) + 2) := by positivity
    exact closedBall_subset_ball (by linarith)
  have hO : ∀ O : Set ℂ, IsOpen O → O ⊆ ball 0 1 → Measurable fun ω => discVagueLimit (m ω) O := by
    intro O hO hO1
    have hOb : Bornology.IsBounded O := isBounded_ball.subset hO1
    have hOc : Oᶜ.Nonempty := ⟨1, fun h => by simpa using hO1 h⟩
    have e : (fun ω => discVagueLimit (m ω) O) = E.indicator fun ω =>
        ⨆ n : ℕ, ENNReal.ofReal (limUnder atTop fun k => ∫ z, openBump O n z ∂m ω k) := by
      funext ω
      by_cases hω : ω ∈ E
      · rw [indicator_of_mem hω]
        have hspec := discVagueLimit_spec hω
        rw [measure_open_eq_iSup _ hO hOc]
        congr 1
        funext n
        have hsupp : tsupport (openBump O n) ⊆ ball 0 1 := (tsupport_openBump_subset O n).trans hO1
        have hInt : Integrable (openBump O n) (discVagueLimit (m ω)) :=
          QuantumZipper.VagueOpen.integrable_of_testFun (continuous_openBump O n) (hasCompactSupport_openBump hOb n)
            (hspec.2.1 _ (hasCompactSupport_openBump hOb n).isCompact hsupp)
        rw [(hspec.2.2 _ (continuous_openBump O n) (hasCompactSupport_openBump hOb n) hsupp).limUnder_eq,
          ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun z => openBump_nonneg O n z)]
      · rw [indicator_of_notMem hω, discVagueLimit_of_not hω, Measure.coe_zero, Pi.zero_apply]
    rw [e]
    refine Measurable.indicator (Measurable.iSup fun n => ENNReal.measurable_ofReal.comp ?_) hE
    exact (StronglyMeasurable.limUnder fun k =>
      (hint k _ (continuous_openBump O n) (hasCompactSupport_openBump hOb n)).stronglyMeasurable).measurable
  refine measurable_measure_of_open (fun ω => discVagueLimit (m ω)) Vn (fun N => measurableSet_ball)
    (fun N N' h => ?_) (fun ω => ?_) (fun ω N => ?_) (fun W N hW => ?_)
  · show ball (0 : ℂ) (1 - 1 / ((N : ℝ) + 2)) ⊆ ball 0 (1 - 1 / ((N' : ℝ) + 2))
    refine ball_subset_ball ?_
    have h' : (N : ℝ) + 2 ≤ (N' : ℝ) + 2 := by
      have : (N : ℝ) ≤ N' := Nat.cast_le.2 h
      linarith
    have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (N : ℝ) + 2) h'
    linarith
  · have hcov : ball (0 : ℂ) 1 ⊆ ⋃ N, Vn N := by
      intro z hz
      rw [mem_ball, dist_zero_right] at hz
      have h1 : 0 < 1 - ‖z‖ := by linarith
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - ‖z‖))
      rw [div_lt_iff₀ h1] at hN
      refine mem_iUnion.2 ⟨N, ?_⟩
      show z ∈ ball (0 : ℂ) (1 - 1 / ((N : ℝ) + 2))
      rw [mem_ball, dist_zero_right]
      have h2 : 1 / ((N : ℝ) + 2) < 1 - ‖z‖ := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    refine measure_mono_null (compl_subset_compl.2 hcov) ?_
    by_cases hω : ω ∈ E
    · exact (discVagueLimit_spec hω).1
    · rw [discVagueLimit_of_not hω, Measure.coe_zero, Pi.zero_apply]
  · by_cases hω : ω ∈ E
    · exact ((measure_mono ball_subset_closedBall).trans_lt
        ((discVagueLimit_spec hω).2.1 _ (isCompact_closedBall _ _) (hVsub N))).ne
    · rw [discVagueLimit_of_not hω, Measure.coe_zero, Pi.zero_apply]
      exact ENNReal.zero_ne_top
  · exact hO _ (hW.inter isOpen_ball) (inter_subset_right.trans (ball_subset_closedBall.trans (hVsub N)))

end VagueDisc

/-! ### The measure map -/

/-- The smooth approximations `e^{γ g ∗ f_ε(z) + (γ²/2)(log ε + C)} dz` (Sheffield–Wang (2016), §3.2) on the unit disc,
`f = stdMollifier`, `ε = 2^{-k}`, of the field decoded from the assignment `a`. -/
def chartApprox (γ : ℝ) (a : 𝓓(unitDiscOpens, ℝ) → ℝ) (k : ℕ) : Measure ℂ :=
  smoothApprox γ stdMollifier (unitDiscOpens : Set ℂ) (pairFun (discDecode a)) (HarmonicBalls.dyadicScale k)

theorem chartApprox_lt_top (γ : ℝ) (a : 𝓓(unitDiscOpens, ℝ) → ℝ) (k : ℕ) {K : Set ℂ} (hK : IsCompact K) :
    chartApprox γ a k K < ∞ :=
  smoothApprox_lt_top (V := unitDiscOpens) (f := stdMollifier) (ε := HarmonicBalls.dyadicScale k) γ
    isMollifier_stdMollifier (HarmonicBalls.dyadicScale_pos k) (discDecode a) hK

theorem measurable_integral_chartApprox (γ : ℝ) (k : ℕ) {φ : ℂ → ℝ} (hφ : Measurable φ) :
    Measurable fun a : 𝓓(unitDiscOpens, ℝ) → ℝ => ∫ z, φ z ∂chartApprox γ a k := by
  have h : Measurable fun g : LQGMetric.DistOn unitDiscOpens =>
      ∫ z, φ z ∂smoothApprox γ stdMollifier (unitDiscOpens : Set ℂ) (pairFun g) (HarmonicBalls.dyadicScale k) :=
    measurable_integral_smoothApprox (V := unitDiscOpens) (f := stdMollifier) (ε := HarmonicBalls.dyadicScale k) γ
      isMollifier_stdMollifier (HarmonicBalls.dyadicScale_pos k) hφ
  exact h.comp measurable_discDecode

/-- **The measure map.** The vague limit in the unit disc of the smooth approximations of the decoded field along the
scales `2^{-k}` when it exists, `0` otherwise. -/
def chartMeasure (γ : ℝ) (a : 𝓓(unitDiscOpens, ℝ) → ℝ) : Measure ℂ :=
  discVagueLimit (chartApprox γ a)

/-- **The measure map is Borel**: measurable for the product σ-algebra on the assignments and the Giry σ-algebra on
`Measure ℂ`. -/
theorem measurable_chartMeasure (γ : ℝ) : Measurable (chartMeasure γ) := by
  have h : Measurable fun a : 𝓓(unitDiscOpens, ℝ) → ℝ => discVagueLimit (chartApprox γ a) :=
    measurable_discVagueLimit (m := chartApprox γ) (fun a k _ hK => chartApprox_lt_top γ a k hK)
      (fun k _ hφ _ => measurable_integral_chartApprox γ k hφ.measurable)
  exact h

theorem smoothApprox_unitDiscOpens (γ : ℝ) (f : ℂ → ℝ) (G : (ℂ → ℝ) → ℝ) (ε : ℝ) :
    smoothApprox γ f (unitDiscOpens : Set ℂ) G ε = smoothApprox γ f (ball 0 1) G ε :=
  rfl

/-- **The measure map on the pairings of a distribution.** If the smooth approximations of a distribution `g` on the
unit disc converge vaguely in the disc along the scales `2^{-k}` to `ν`, then `chartMeasure γ` sends the pairings of
`g` to `ν`. -/
theorem chartMeasure_eq_of_isVagueLimitOn (γ : ℝ) {g : LQGMetric.DistOn unitDiscOpens} {ν : Measure ℂ}
    (h : QuantumZipper.IsVagueLimitOn (ball 0 1)
      (fun k => smoothApprox γ stdMollifier (ball 0 1) (pairFun g) (HarmonicBalls.dyadicScale k)) ν) :
    chartMeasure γ ⇑g = ν := by
  have e : chartApprox γ ⇑g =
      fun k => smoothApprox γ stdMollifier (ball 0 1) (pairFun g) (HarmonicBalls.dyadicScale k) := by
    funext k
    rw [chartApprox, discDecode_coe, smoothApprox_unitDiscOpens]
  rw [chartMeasure, e]
  exact discVagueLimit_eq h

end LQGMeasureChart

end MatedCRT
