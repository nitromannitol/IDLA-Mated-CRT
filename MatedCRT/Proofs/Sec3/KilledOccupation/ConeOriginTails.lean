import Mathlib
import HarmonicBalls.Defs.GFF
import MatedCRT.Defs.Setting
import MatedCRT.Proofs.Sec3.KilledOccupation.ConeGFFTransfer
import MatedCRT.Proofs.Sec3.KilledOccupation.OriginTails

/-!
# Origin tail moment of the quantum cone, transferred from the law of its circle averages (ConeOriginTails)

Printed source: lem:occ-tails (appendix tex:296) for the cone field of eq:occ-field (tex:20-29). The Lean form
`ConeUnitDiskGFFLaw` (`ConeGFFTransfer.lean`) identifies the law of the circle averages of the cone on the unit disk
with the law of the circle averages of a whole-plane GFF. The origin functional
`∫_{B_a} (1 + log(1/|x|)) ε^{γ²/2} e^{γ h_ε(x)} dx` is not a measurable function of uncountably many circle averages.
It is approximated from below by functionals of countably many coordinates: infima of the density over a countable
dense set `D`, whose joint laws on the two sides agree. For continuous circle averages these approximants increase to
the functional (Lebesgue monotone convergence), so its `p`-th moment is bounded by the moment on the whole-plane side,
which is `origin_tail_moment`.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal NNReal
open Real

noncomputable section

namespace MatedCRT.KilledOccupation

/-- The regularized density `ε^{γ²/2} e^{γ v}` (`regDensity`, OriginTails.lean:46) at a circle average `v`. -/
def expDens (γ ε v : ℝ) : ℝ≥0∞ := ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * v))

lemma continuous_expDens (γ ε : ℝ) : Continuous (expDens γ ε) :=
  ENNReal.continuous_ofReal.comp (by fun_prop)

open Classical in
/-- The value at the circle `(ε, d)` of a family indexed by the unit-disk circles; `0` off the index. -/
def coordAt (ε : ℝ) (d : ℂ) (F : UnitDiskCircleIndex → ℝ) : ℝ :=
  if h : (ε, d) ∈ UnitDiskCircleIndex then F ⟨(ε, d), h⟩ else 0

lemma measurable_coordAt (ε : ℝ) (d : ℂ) :
    Measurable fun F : UnitDiskCircleIndex → ℝ => coordAt ε d F := by
  unfold coordAt
  split_ifs with h
  · exact measurable_pi_apply _
  · exact measurable_const

/-- For `0 < ε < 1/2` and `‖d‖ < 1/2`, `(ε, d)` is a circle of the unit disk. -/
lemma mem_index_of_norm_lt {ε : ℝ} {d : ℂ} (hε0 : 0 < ε) (hε : ε < 1 / 2) (hd : ‖d‖ < 1 / 2) :
    (ε, d) ∈ UnitDiskCircleIndex := by
  show 0 < ε ∧ closedBall d ε ⊆ ball (0 : ℂ) 1
  refine ⟨hε0, fun z hz => ?_⟩
  rw [mem_closedBall, dist_eq_norm] at hz
  rw [mem_ball_zero_iff]
  have h1 : ‖z‖ ≤ ‖z - d‖ + ‖d‖ := by simpa using norm_add_le (z - d) d
  linarith

/-- The circle averages of the cone, as a family on the unit-disk index. -/
def coneFamily {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω) : UnitDiskCircleIndex → ℝ :=
  fun q => S.hcirc ω q.1.1 q.1.2

/-- The circle averages `h_r(z)` of the field `h^ℂ - γ log|·|`, as a family on the unit-disk index. -/
def gffFamily (γ : ℝ) (hc : ℝ → ℂ → ℝ) : UnitDiskCircleIndex → ℝ :=
  fun q => HarmonicBalls.fieldCircleAverage γ hc q.1.1 q.1.2

lemma coordAt_coneFamily {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω) {ε : ℝ} {y : ℂ}
    (hε0 : 0 < ε) (hε : ε < 1 / 2) (hy : ‖y‖ < 1 / 2) :
    coordAt ε y (coneFamily S ω) = S.hcirc ω ε y := by
  simp [coordAt, coneFamily, mem_index_of_norm_lt hε0 hε hy]

lemma coordAt_gffFamily (γ : ℝ) (hc : ℝ → ℂ → ℝ) {ε : ℝ} {y : ℂ}
    (hε0 : 0 < ε) (hε : ε < 1 / 2) (hy : ‖y‖ < 1 / 2) :
    coordAt ε y (gffFamily γ hc) = HarmonicBalls.fieldCircleAverage γ hc ε y := by
  simp [coordAt, gffFamily, mem_index_of_norm_lt hε0 hε hy]

/-- A coordinate that agrees with a continuous function `f` on the small disk is continuous there. -/
lemma continuousAt_coordAt {ε : ℝ} {f : ℂ → ℝ} (hf : Continuous f) (F : UnitDiskCircleIndex → ℝ)
    (hF : ∀ y : ℂ, ‖y‖ < 1 / 2 → coordAt ε y F = f y) {x : ℂ} (hx : ‖x‖ < 1 / 2) :
    ContinuousAt (fun y => coordAt ε y F) x := by
  refine ContinuousAt.congr hf.continuousAt ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
  exact (hF y (mem_ball_zero_iff.1 hy)).symm

/-- Continuity in the centre of the circle average of `h^ℂ - γ log|·|` at a fixed radius, from Jensen's formula
`⨍_{∂B_ε(z)} log|·| = log ε + log⁺(|z|/ε)` (Mathlib). -/
lemma continuous_fieldCircleAverage (γ ε : ℝ) (hε : ε ≠ 0) (hc : ℝ → ℂ → ℝ)
    (hcont : Continuous fun y => hc ε y) :
    Continuous fun y => HarmonicBalls.fieldCircleAverage γ hc ε y := by
  have hJ : ∀ y : ℂ, Real.circleAverage (fun x => Real.log ‖x‖) y ε =
      Real.log ε + Real.posLog (ε⁻¹ * ‖y‖) := by
    intro y
    have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := y) (R := ε) hε
    simpa [sub_zero] using h
  unfold HarmonicBalls.fieldCircleAverage
  simp only [hJ]
  exact hcont.sub (continuous_const.mul (continuous_const.add
    (continuous_posLog.comp (continuous_const.mul continuous_norm))))

/-- Continuity of a circle-average process in the centre at a fixed positive radius. -/
lemma continuous_of_continuousOn_circle {f : ℝ → ℂ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℂ => f p.1 p.2) (Ioi 0 ×ˢ univ)) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun y => f ε y := by
  have h : ContinuousOn (fun y : ℂ => f ε y) univ :=
    hf.comp (continuousOn_const.prodMk continuousOn_id) (fun y _ => ⟨hε, mem_univ _⟩)
  exact continuousOn_univ.1 h

/-- Lower approximant of `x ↦ expDens(V x)`: the infimum over the points `d` of the countable set `D` with
`dist d x < δ n`, the value `⊤` off that ball. -/
def mGen (D : Set ℂ) (δ : ℕ → ℝ) (γ ε : ℝ) (V : ℂ → ℝ) (n : ℕ) (x : ℂ) : ℝ≥0∞ :=
  ⨅ d : D, if dist (d : ℂ) x < δ n then expDens γ ε (V (d : ℂ)) else ⊤

lemma mGen_mono (D : Set ℂ) {δ : ℕ → ℝ} (hδ : Antitone δ) (γ ε : ℝ) (V : ℂ → ℝ) (x : ℂ) :
    Monotone fun n => mGen D δ γ ε V n x := by
  intro n m hnm
  show mGen D δ γ ε V n x ≤ mGen D δ γ ε V m x
  have hm : δ m ≤ δ n := hδ hnm
  unfold mGen
  refine iInf_mono fun d => ?_
  by_cases h1 : dist (d : ℂ) x < δ n
  · by_cases h2 : dist (d : ℂ) x < δ m
    · simp [h1, h2]
    · simp [h1, h2]
  · by_cases h2 : dist (d : ℂ) x < δ m
    · exact absurd (lt_of_lt_of_le h2 hm) h1
    · simp [h1, h2]

lemma mGen_tendsto (D : Set ℂ) (hDd : Dense D) {δ : ℕ → ℝ} (hδpos : ∀ n, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (γ ε : ℝ) (V : ℂ → ℝ) {x : ℂ} (hV : ContinuousAt V x) :
    Tendsto (fun n => mGen D δ γ ε V n x) atTop (𝓝 (expDens γ ε (V x))) := by
  have hc : ContinuousAt (fun y => expDens γ ε (V y)) x :=
    (continuous_expDens γ ε).continuousAt.comp hV
  rw [tendsto_order]
  constructor
  · intro a' ha'
    obtain ⟨b, hab, hbE⟩ := exists_between ha'
    have hev : ∀ᶠ y in 𝓝 x, b < expDens γ ε (V y) := hc.eventually (lt_mem_nhds hbE)
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    filter_upwards [hδ0.eventually (gt_mem_nhds hρ)] with n hn
    refine lt_of_lt_of_le hab ?_
    unfold mGen
    refine le_iInf fun d => ?_
    by_cases h1 : dist (d : ℂ) x < δ n
    · simp only [h1]
      exact (hball (h1.trans hn)).le
    · simp only [h1]
      exact le_top
  · intro a' ha'
    obtain ⟨b, hbE, hba⟩ := exists_between ha'
    have hev : ∀ᶠ y in 𝓝 x, expDens γ ε (V y) < b := hc.eventually (gt_mem_nhds hbE)
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    filter_upwards [hδ0.eventually (gt_mem_nhds hρ)] with n hn
    obtain ⟨d, hdD, hd⟩ := hDd.exists_dist_lt x (hδpos n)
    have hdn : dist d x < δ n := by rw [dist_comm]; exact hd
    unfold mGen
    refine lt_of_le_of_lt (iInf_le _ ⟨d, hdD⟩) ?_
    show (if dist d x < δ n then expDens γ ε (V d) else ⊤) < a'
    simp only [hdn]
    exact lt_trans (hball (hdn.trans hn)) hba

lemma mGen_le (D : Set ℂ) (hDd : Dense D) {δ : ℕ → ℝ} (hδ : Antitone δ) (hδpos : ∀ n, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (γ ε : ℝ) (V : ℂ → ℝ) {x : ℂ} (hV : ContinuousAt V x) (n : ℕ) :
    mGen D δ γ ε V n x ≤ expDens γ ε (V x) :=
  (mGen_mono D hδ γ ε V x).ge_of_tendsto (mGen_tendsto D hDd hδpos hδ0 γ ε V hV) n

lemma mGen_iSup (D : Set ℂ) (hDd : Dense D) {δ : ℕ → ℝ} (hδ : Antitone δ) (hδpos : ∀ n, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (γ ε : ℝ) (V : ℂ → ℝ) {x : ℂ} (hV : ContinuousAt V x) :
    ⨆ n, mGen D δ γ ε V n x = expDens γ ε (V x) :=
  tendsto_nhds_unique (tendsto_atTop_iSup (mGen_mono D hδ γ ε V x))
    (mGen_tendsto D hDd hδpos hδ0 γ ε V hV)

lemma measurable_mGen (D : Set ℂ) [Countable D] (δ : ℕ → ℝ) (γ ε : ℝ) (n : ℕ) :
    Measurable fun p : (UnitDiskCircleIndex → ℝ) × ℂ =>
      mGen D δ γ ε (fun d => coordAt ε d p.1) n p.2 := by
  unfold mGen
  refine Measurable.iInf fun d => ?_
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt (measurable_const.dist measurable_snd) measurable_const
  · exact (continuous_expDens γ ε).measurable.comp ((measurable_coordAt ε d).comp measurable_fst)

/-- For a fixed family the approximant is a measurable function of the centre. -/
lemma measurable_mGen_fixed (D : Set ℂ) [Countable D] (δ : ℕ → ℝ) (γ ε : ℝ)
    (F : UnitDiskCircleIndex → ℝ) (n : ℕ) :
    Measurable fun x : ℂ => mGen D δ γ ε (fun d => coordAt ε d F) n x := by
  unfold mGen
  refine Measurable.iInf fun d => ?_
  exact Measurable.ite (measurableSet_lt (measurable_const.dist measurable_id) measurable_const)
    measurable_const measurable_const

/-- The approximant `∫_{B_a} w(x) m_n(x) dx` of the origin functional, `w(x) = 1 + log(1/|x|)`. -/
def Lapp (D : Set ℂ) (δ : ℕ → ℝ) (γ ε a : ℝ) (n : ℕ) (F : UnitDiskCircleIndex → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in ball (0 : ℂ) a,
    ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) * mGen D δ γ ε (fun d => coordAt ε d F) n x

lemma measurable_Lapp (D : Set ℂ) [Countable D] (δ : ℕ → ℝ) (γ ε a : ℝ) (n : ℕ) :
    Measurable (Lapp D δ γ ε a n) := by
  have hw : Measurable fun x : ℂ => ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.add (Real.measurable_log.comp
      (measurable_const.div measurable_norm)))
  have hj : Measurable fun p : (UnitDiskCircleIndex → ℝ) × ℂ =>
      ENNReal.ofReal (1 + Real.log (1 / ‖p.2‖)) * mGen D δ γ ε (fun d => coordAt ε d p.1) n p.2 :=
    (hw.comp measurable_snd).mul (measurable_mGen D δ γ ε n)
  exact hj.lintegral_prod_right'

lemma Lapp_mono (D : Set ℂ) {δ : ℕ → ℝ} (hδ : Antitone δ) (γ ε a : ℝ) (F : UnitDiskCircleIndex → ℝ) :
    Monotone fun n => Lapp D δ γ ε a n F := by
  intro n m hnm
  show Lapp D δ γ ε a n F ≤ Lapp D δ γ ε a m F
  unfold Lapp
  exact lintegral_mono fun x => mul_le_mul' le_rfl (mGen_mono D hδ γ ε _ x hnm)

/-- The approximants increase to the origin functional when the circle averages are continuous near the origin. -/
lemma Lapp_iSup (D : Set ℂ) [Countable D] (hDd : Dense D) {δ : ℕ → ℝ} (hδ : Antitone δ) (hδpos : ∀ n, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (γ ε a : ℝ) (F : UnitDiskCircleIndex → ℝ) (ha : a ≤ 1 / 2)
    (hF : ∀ x, ‖x‖ < 1 / 2 → ContinuousAt (fun y => coordAt ε y F) x) :
    ⨆ n, Lapp D δ γ ε a n F = ∫⁻ x in ball (0 : ℂ) a,
      ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) * expDens γ ε (coordAt ε x F) := by
  have hw : Measurable fun x : ℂ => ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.add (Real.measurable_log.comp
      (measurable_const.div measurable_norm)))
  have hmeas : ∀ n, Measurable fun x : ℂ =>
      ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) * mGen D δ γ ε (fun d => coordAt ε d F) n x := by
    intro n
    exact hw.mul (measurable_mGen_fixed D δ γ ε F n)
  have hmono : Monotone fun n (x : ℂ) =>
      ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) * mGen D δ γ ε (fun d => coordAt ε d F) n x :=
    fun n m hnm x => mul_le_mul' le_rfl (mGen_mono D hδ γ ε _ x hnm)
  unfold Lapp
  rw [← lintegral_iSup hmeas hmono]
  refine setLIntegral_congr_fun measurableSet_ball fun x hx => ?_
  have hxa : ‖x‖ < 1 / 2 := lt_of_lt_of_le (mem_ball_zero_iff.1 hx) ha
  rw [← ENNReal.mul_iSup, mGen_iSup D hDd hδ hδpos hδ0 γ ε _ (hF x hxa)]

/-- The approximants lie below the origin functional when the circle averages are continuous near the origin. -/
lemma Lapp_le (D : Set ℂ) (hDd : Dense D) {δ : ℕ → ℝ} (hδ : Antitone δ) (hδpos : ∀ n, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (γ ε a : ℝ) (F : UnitDiskCircleIndex → ℝ) (ha : a ≤ 1 / 2)
    (hF : ∀ x, ‖x‖ < 1 / 2 → ContinuousAt (fun y => coordAt ε y F) x) (n : ℕ) :
    Lapp D δ γ ε a n F ≤ ∫⁻ x in ball (0 : ℂ) a,
      ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) * expDens γ ε (coordAt ε x F) := by
  unfold Lapp
  refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
  have hxa : ‖x‖ < 1 / 2 := lt_of_lt_of_le (mem_ball_zero_iff.1 hx) ha
  exact mul_le_mul' le_rfl (mGen_le D hDd hδ hδpos hδ0 γ ε _ (hF x hxa) n)

/-- The approximation of `ENNReal` powers of a monotone supremum. -/
lemma rpow_iSup_of_monotone {f : ℕ → ℝ≥0∞} {p : ℝ} (hp : 0 < p) :
    (⨆ n, f n) ^ p = ⨆ n, f n ^ p :=
  Monotone.map_iSup_of_continuousAt (f := fun t : ℝ≥0∞ => t ^ p)
    (ENNReal.continuous_rpow_const.continuousAt) (fun a b h => ENNReal.rpow_le_rpow h hp.le)
    (by simp [ENNReal.zero_rpow_of_pos hp])

/-- The shrinking radii of the dyadic approximation. -/
def shrinkRad (n : ℕ) : ℝ := (1 / 8) * (1 / 2) ^ n

lemma shrinkRad_pos (n : ℕ) : 0 < shrinkRad n := by
  unfold shrinkRad
  positivity

lemma shrinkRad_anti : Antitone shrinkRad := fun m n hmn => by
  unfold shrinkRad
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn) (by norm_num)

lemma shrinkRad_tendsto : Tendsto shrinkRad atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (1 / 8 : ℝ)
  unfold shrinkRad
  simpa using h

/-- The weighted mass of the cone field in terms of its circle averages `hcirc`. -/
lemma weightedMass_cone (γ ε a : ℝ) (hcirc : ℝ → ℂ → ℝ) :
    weightedMass γ ε (fun r z => hcirc r z + γ * Real.circleAverage (fun x => Real.log ‖x‖) z r) (ball 0 a) =
      ∫⁻ x in ball (0 : ℂ) a, ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) * expDens γ ε (hcirc ε x) := by
  unfold weightedMass
  refine lintegral_congr fun x => ?_
  unfold regDensity expDens HarmonicBalls.fieldCircleAverage
  simp only [add_sub_cancel_right]

lemma weightedMass_gff (γ ε a : ℝ) (hc : ℝ → ℂ → ℝ) :
    weightedMass γ ε hc (ball 0 a) =
      ∫⁻ x in ball (0 : ℂ) a,
        ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) * expDens γ ε (HarmonicBalls.fieldCircleAverage γ hc ε x) := by
  rfl

/-- **Origin tail moment of the quantum cone** (lem:occ-tails, tex:296, for the cone field of eq:occ-field): the
`p`-th moment of the weighted mass of the cone's origin field is bounded as in `origin_tail_moment`, transferred from
the whole-plane GFF through the law `ConeUnitDiskGFFLaw`. -/
theorem coneOriginTailMoment_of_law (hlaw : ConeUnitDiskGFFLaw) (𝒮 : SpaceFillingSLEModel)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < min 1 (4 / γ ^ 2 - 1))
    (hκ : κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∃ C a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Ioo 0 a₀, ∀ ε ∈ Ioo 0 a₀,
      ∫⁻ ω, weightedMass γ ε (fun r z => S.hcirc ω r z + γ * Real.circleAverage (fun x => Real.log ‖x‖) z r)
        (ball 0 a) ^ p ∂S.P ≤ ENNReal.ofReal (C * a ^ κ * (1 + Real.log (1 / a)) ^ p) := by
  obtain ⟨Ω', _, P', hC', hc', hP', hGFF, hid⟩ := hlaw 𝒮 γ hγ0 hγ2 Ω S hS
  have := hP'
  obtain ⟨C, a₀, ha₀, hT⟩ := origin_tail_moment P' hC' hc' hGFF hγ0 hγ2 hp0 hp1 hκ
  have hid' : IdentDistrib (fun ω => coneFamily S ω) (fun ω' => gffFamily γ (hc' ω')) S.P P' := hid
  have hcone := hS.isQuantumCone.ae_continuousOn_circle
  refine ⟨C, min a₀ (1 / 8), lt_min ha₀ (by norm_num), fun a ha ε hε => ?_⟩
  obtain ⟨ha0, haL⟩ := ha
  obtain ⟨hε0, hεL⟩ := hε
  have haa : a < a₀ := lt_of_lt_of_le haL (min_le_left _ _)
  have ha8 : a ≤ 1 / 2 := by linarith [lt_of_lt_of_le haL (min_le_right _ _)]
  have hεa : ε < a₀ := lt_of_lt_of_le hεL (min_le_left _ _)
  have hε8 : ε < 1 / 2 := by linarith [lt_of_lt_of_le hεL (min_le_right _ _)]
  have hT' := hT a ⟨ha0, haa⟩ ε ⟨hε0, hεa⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable D := hDc.to_subtype
  -- on the cone side, the origin functional is the increasing limit of the approximants
  have hA : ∀ᵐ ω ∂S.P, weightedMass γ ε
      (fun r z => S.hcirc ω r z + γ * Real.circleAverage (fun x => Real.log ‖x‖) z r) (ball 0 a) =
      ⨆ n, Lapp D shrinkRad γ ε a n (coneFamily S ω) := by
    filter_upwards [hcone] with ω hω
    have hcω : Continuous fun y => S.hcirc ω ε y := continuous_of_continuousOn_circle hω hε0
    have hF : ∀ x, ‖x‖ < 1 / 2 → ContinuousAt (fun y => coordAt ε y (coneFamily S ω)) x :=
      fun x hx => continuousAt_coordAt hcω (coneFamily S ω)
        (fun y hy => coordAt_coneFamily S ω hε0 hε8 hy) hx
    rw [weightedMass_cone γ ε a (S.hcirc ω), Lapp_iSup D hDd shrinkRad_anti shrinkRad_pos shrinkRad_tendsto γ ε a
      (coneFamily S ω) ha8 hF]
    refine setLIntegral_congr_fun measurableSet_ball fun x hx => ?_
    have hxa : ‖x‖ < 1 / 2 := lt_of_lt_of_le (mem_ball_zero_iff.1 hx) ha8
    rw [coordAt_coneFamily S ω hε0 hε8 hxa]
  -- on the whole-plane side, the approximants lie below the origin functional
  have hB : ∀ᵐ ω' ∂P', ∀ n, Lapp D shrinkRad γ ε a n (gffFamily γ (hc' ω')) ≤
      weightedMass γ ε (hc' ω') (ball 0 a) := by
    filter_upwards [hGFF.ae_continuousOn_circle] with ω' hω' n
    have hcω : Continuous fun y => hc' ω' ε y := continuous_of_continuousOn_circle hω' hε0
    have hcf : Continuous fun y => HarmonicBalls.fieldCircleAverage γ (hc' ω') ε y :=
      continuous_fieldCircleAverage γ ε hε0.ne' (hc' ω') hcω
    have hF : ∀ x, ‖x‖ < 1 / 2 → ContinuousAt (fun y => coordAt ε y (gffFamily γ (hc' ω'))) x :=
      fun x hx => continuousAt_coordAt hcf (gffFamily γ (hc' ω'))
        (fun y hy => coordAt_gffFamily γ (hc' ω') hε0 hε8 hy) hx
    refine (Lapp_le D hDd shrinkRad_anti shrinkRad_pos shrinkRad_tendsto γ ε a _ ha8 hF n).trans
      (le_of_eq ?_)
    rw [weightedMass_gff]
    refine setLIntegral_congr_fun measurableSet_ball fun x hx => ?_
    have hxa : ‖x‖ < 1 / 2 := lt_of_lt_of_le (mem_ball_zero_iff.1 hx) ha8
    rw [coordAt_gffFamily γ (hc' ω') hε0 hε8 hxa]
  -- the two sides have the same law for each approximant
  have htr : ∀ n, ∫⁻ ω, (Lapp D shrinkRad γ ε a n (coneFamily S ω)) ^ p ∂S.P =
      ∫⁻ ω', (Lapp D shrinkRad γ ε a n (gffFamily γ (hc' ω'))) ^ p ∂P' := by
    intro n
    have hG : Measurable fun F : UnitDiskCircleIndex → ℝ => (Lapp D shrinkRad γ ε a n F) ^ p :=
      (measurable_Lapp D shrinkRad γ ε a n).pow_const p
    calc ∫⁻ ω, (Lapp D shrinkRad γ ε a n (coneFamily S ω)) ^ p ∂S.P
        = ∫⁻ y, (Lapp D shrinkRad γ ε a n y) ^ p ∂(S.P.map fun ω => coneFamily S ω) :=
          (lintegral_map' hG.aemeasurable hid'.aemeasurable_fst).symm
      _ = ∫⁻ y, (Lapp D shrinkRad γ ε a n y) ^ p ∂(P'.map fun ω' => gffFamily γ (hc' ω')) := by
          rw [hid'.map_eq]
      _ = ∫⁻ ω', (Lapp D shrinkRad γ ε a n (gffFamily γ (hc' ω'))) ^ p ∂P' :=
          lintegral_map' hG.aemeasurable hid'.aemeasurable_snd
  calc ∫⁻ ω, weightedMass γ ε
        (fun r z => S.hcirc ω r z + γ * Real.circleAverage (fun x => Real.log ‖x‖) z r) (ball 0 a) ^ p ∂S.P
      = ∫⁻ ω, (⨆ n, Lapp D shrinkRad γ ε a n (coneFamily S ω)) ^ p ∂S.P :=
        lintegral_congr_ae (hA.mono fun ω hω => by simp only [hω])
    _ = ∫⁻ ω, ⨆ n, (Lapp D shrinkRad γ ε a n (coneFamily S ω)) ^ p ∂S.P :=
        lintegral_congr fun ω => rpow_iSup_of_monotone hp0
    _ = ⨆ n, ∫⁻ ω, (Lapp D shrinkRad γ ε a n (coneFamily S ω)) ^ p ∂S.P :=
        lintegral_iSup' (fun n => ((measurable_Lapp D shrinkRad γ ε a n).pow_const p).comp_aemeasurable
          hid'.aemeasurable_fst) (ae_of_all _ fun ω n m hnm =>
            ENNReal.rpow_le_rpow (Lapp_mono D shrinkRad_anti γ ε a (coneFamily S ω) hnm) hp0.le)
    _ = ⨆ n, ∫⁻ ω', (Lapp D shrinkRad γ ε a n (gffFamily γ (hc' ω'))) ^ p ∂P' := by
        simp_rw [htr]
    _ ≤ ∫⁻ ω', weightedMass γ ε (hc' ω') (ball 0 a) ^ p ∂P' := by
        refine iSup_le fun n => lintegral_mono_ae ?_
        filter_upwards [hB] with ω' hω' using ENNReal.rpow_le_rpow (hω' n) hp0.le
    _ ≤ ENNReal.ofReal (C * a ^ κ * (1 + Real.log (1 / a)) ^ p) := hT'

end MatedCRT.KilledOccupation
