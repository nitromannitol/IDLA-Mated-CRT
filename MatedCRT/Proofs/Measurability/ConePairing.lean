import MatedCRT.Proofs.Measurability.CirclePairing
import MatedCRT.Defs.QuantumCone

/-!
# Circle averages of the quantum cone field are limits of pairings

For the circle average embedding of the `γ`-quantum cone (`IsQuantumCone`), almost surely `(h, φ_k) → h_r(z)` where
`φ_k = circBump k z r` and `|z| ≠ r` (`ae_tendsto_circBump_of_isQuantumCone`). The field is the sum of its lateral part,
whose law is that of the lateral part of a whole-plane GFF, and of its radial part `x ↦ h_{|x|}(0)`:

* for the whole-plane GFF, `(h, φ_k) → h_r(z)` a.s. (`ae_tendsto_circBump`), and the radial terms converge pathwise
  (`tendsto_integral_circBump_mul_radial`: `∫ φ_k(x) R(|x|) dx → ⨍_{∂B_r(z)} R(|·|)` for `R` continuous on `(0, ∞)`,
  `|z| ≠ r`), so the lateral observables converge a.s.;
* this is an event of the product σ-algebra of the lateral process, which is a random variable
  (`aemeasurable_lateralProcess`: a jointly measurable version of `s ↦ h_s(0)` from the a.s. continuity); by equality of
  the laws of the lateral parts it has probability one for the cone, and the radial terms converge pathwise again.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real ENNReal
open _root_.HarmonicBalls

namespace MatedCRT
namespace CirclePairing

open LQGMetric LQGMetric.CircleAvg

/-! ### Pathwise convergence of the pairings of continuous functions -/

lemma circleAverage_congr_sphere {f g : ℂ → ℝ} {c : ℂ} {R : ℝ} (h : EqOn f g (sphere c |R|)) :
    Real.circleAverage f c R = Real.circleAverage g c R := by
  simp only [Real.circleAverage_def]
  congr 1
  exact intervalIntegral.integral_congr fun θ _ => h (circleMap_mem_sphere' c R θ)

lemma abs_circleAverage_le {f : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hf : CircleIntegrable f c R)
    (h : ∀ x ∈ sphere c |R|, |f x| ≤ M) : |Real.circleAverage f c R| ≤ M := by
  have hc : ∀ v : ℝ, CircleIntegrable (fun _ : ℂ => v) c R := fun v =>
    circleIntegrable_of_continuous continuous_const c R
  rw [abs_le]
  constructor
  · calc -M = Real.circleAverage (fun _ => -M) c R := (Real.circleAverage_const _ c R).symm
      _ ≤ _ := Real.circleAverage_mono (hc _) hf fun x hx => (abs_le.1 (h x hx)).1
  · calc Real.circleAverage f c R ≤ Real.circleAverage (fun _ => M) c R :=
          Real.circleAverage_mono hf (hc _) fun x hx => (abs_le.1 (h x hx)).2
      _ = M := Real.circleAverage_const _ c R

lemma circBump_eq_zero_of_forall_le {k : ℕ} {z x : ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ c ∈ sphere z r, (2 : ℝ)⁻¹ ^ k ≤ dist x c) : circBump k z r x = 0 := by
  rw [circBump_apply]
  have hcont : Continuous fun c => bumpTest k c x := by
    have e : (fun c => bumpTest k c x) = fun c => bumpTest k 0 (x - c) := funext fun c => bumpTest_eq_sub k c x
    rw [e]
    exact (bumpTest k 0).continuous.comp (continuous_const.sub continuous_id)
  refine circleAverage_eq_of_eqOn_sphere (circleIntegrable_of_continuous hcont z r) fun c hc => ?_
  rw [abs_of_pos hr] at hc
  exact bumpTest_eq_zero_of_le k (h c hc)

/-- `∫ φ_k g → ⨍_{∂B_r(z)} g` for `g` continuous. -/
theorem tendsto_integral_circBump_mul {g : ℂ → ℝ} (hg : Continuous g) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Tendsto (fun k => ∫ x, circBump k z r x * g x) atTop (𝓝 (Real.circleAverage g z r)) := by
  have hpair : ∀ k, ∫ x, circBump k z r x * g x =
      Real.circleAverage (fun c => ∫ y, bumpTest k c y * g y) z r := by
    intro k
    have h := circleAverage_pairing (ofCont ⟨g, hg⟩) k z r
    simp only [ofCont_apply, ContinuousMap.coe_mk] at h
    exact h.symm
  have huc := (isCompact_closedBall z (r + 1)).uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := huc (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (lt_min hδ one_pos) (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N, fun k hk => ?_⟩
  have hkN : (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have hk1 : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hloc : ∀ c ∈ sphere z |r|, |(∫ y, bumpTest k c y * g y) - g c| ≤ ε / 2 := by
    intro c hc
    rw [abs_of_pos hr, mem_sphere] at hc
    have hi1 : Integrable fun y => bumpTest k c y * g y :=
      ((bumpTest k c).continuous.mul hg).integrable_of_hasCompactSupport
        (bumpTest k c).hasCompactSupport.mul_right
    have hi2 : Integrable fun y => bumpTest k c y * g c := (integrable_testC _).mul_const _
    have e : (∫ y, bumpTest k c y * g y) - g c = ∫ y, (bumpTest k c y * g y - bumpTest k c y * g c) := by
      rw [integral_sub hi1 hi2, integral_mul_const, integral_bumpTest', one_mul]
    rw [e, ← Real.norm_eq_abs]
    have hb : ∀ y, ‖bumpTest k c y * g y - bumpTest k c y * g c‖ ≤ bumpTest k c y * (ε / 2) := by
      intro y
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (bumpTest_nonneg k c y)]
      by_cases hy : dist y c < (2 : ℝ)⁻¹ ^ k
      · refine mul_le_mul_of_nonneg_left ?_ (bumpTest_nonneg k c y)
        have hyK : y ∈ closedBall z (r + 1) := by
          rw [mem_closedBall]
          linarith [dist_triangle y c z]
        have hcK : c ∈ closedBall z (r + 1) := by
          rw [mem_closedBall]
          linarith
        have := hδg y hyK c hcK (by linarith [min_le_left δ 1])
        rw [Real.norm_eq_abs, ← Real.dist_eq]
        exact this.le
      · rw [bumpTest_eq_zero_of_le k (not_lt.1 hy), zero_mul, zero_mul]
    refine (norm_integral_le_of_norm_le ((integrable_testC _).mul_const _) (Eventually.of_forall hb)).trans
      (le_of_eq ?_)
    rw [integral_mul_const, integral_bumpTest', one_mul]
  have hci : CircleIntegrable (fun c => ∫ y, bumpTest k c y * g y) z r := by
    have := circleIntegrable_pairing (ofCont ⟨g, hg⟩) k z r
    simpa only [ofCont_apply, ContinuousMap.coe_mk] using this
  have hgi := circleIntegrable_of_continuous hg z r
  rw [hpair, Real.dist_eq, ← Real.circleAverage_sub hci hgi]
  exact (abs_circleAverage_le (hci.sub hgi) fun c hc => hloc c hc).trans_lt (half_lt_self hε)

/-- **Pathwise convergence of the radial terms**: `∫ φ_k(x) R(|x|) dx → ⨍_{∂B_r(z)} R(|·|)` for `R` continuous on
`(0, ∞)`, when the circle `∂B_r(z)` avoids `0`. -/
theorem tendsto_integral_circBump_mul_radial {R : ℝ → ℝ} (hR : ContinuousOn R (Ioi 0)) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : ‖z‖ ≠ r) :
    Tendsto (fun k => ∫ x, circBump k z r x * R ‖x‖) atTop
      (𝓝 (Real.circleAverage (fun x => R ‖x‖) z r)) := by
  set m := |‖z‖ - r| / 2 with hm_def
  have hm : 0 < m := by
    have := abs_pos.2 (sub_ne_zero.2 hz)
    positivity
  set g : ℂ → ℝ := fun x => R (max ‖x‖ m) with hg_def
  have hg : Continuous g :=
    hR.comp_continuous (continuous_norm.max continuous_const) fun x => lt_of_lt_of_le hm (le_max_right _ _)
  have hsph : ∀ c ∈ sphere z r, 2 * m ≤ ‖c‖ := by
    intro c hc
    rw [mem_sphere, dist_eq_norm] at hc
    have h1 : |‖z‖ - r| ≤ ‖c‖ := abs_le'.2
      ⟨by linarith [norm_sub_norm_le z c, norm_sub_rev z c], by linarith [norm_sub_le c z]⟩
    linarith
  have hev : ∀ᶠ k in atTop, ∫ x, circBump k z r x * g x = ∫ x, circBump k z r x * R ‖x‖ := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hm (by norm_num : (2 : ℝ)⁻¹ < 1)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hkN : (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    congr 1
    funext x
    by_cases hx : m ≤ ‖x‖
    · simp only [g, max_eq_left hx]
    · rw [circBump_eq_zero_of_forall_le hr fun c hc => ?_, zero_mul, zero_mul]
      have h1 := hsph c hc
      have h2 : ‖c‖ - ‖x‖ ≤ dist x c := by
        rw [dist_comm, dist_eq_norm]
        exact norm_sub_norm_le c x
      linarith [not_le.1 hx]
  have hCA : Real.circleAverage g z r = Real.circleAverage (fun x => R ‖x‖) z r :=
    circleAverage_congr_sphere fun c hc => by
      rw [abs_of_pos hr] at hc
      simp only [g, max_eq_left (by linarith [hsph c hc] : m ≤ ‖c‖)]
  rw [← hCA]
  exact (tendsto_integral_circBump_mul hg hr z).congr' hev

/-! ### A measurable version of the lateral process -/

/-- The dyadic upper approximation `⌈s 2ⁿ⌉ / 2ⁿ` of `s`. -/
def dyadicCeil (n : ℕ) (s : ℝ) : ℝ := ⌈s * 2 ^ n⌉ / 2 ^ n

lemma tendsto_dyadicCeil (s : ℝ) : Tendsto (fun n => dyadicCeil n s) atTop (𝓝 s) := by
  have h2 : ∀ n : ℕ, (0 : ℝ) < 2 ^ n := fun n => by positivity
  have hlo : ∀ n, s ≤ dyadicCeil n s := fun n => by
    rw [dyadicCeil, le_div_iff₀ (h2 n)]
    exact Int.le_ceil _
  have hhi : ∀ n, dyadicCeil n s ≤ s + (2 : ℝ)⁻¹ ^ n := fun n => by
    rw [dyadicCeil, div_le_iff₀ (h2 n), add_mul, inv_pow, inv_mul_cancel₀ (h2 n).ne']
    exact (Int.ceil_lt_add_one _).le
  have hup : Tendsto (fun n : ℕ => s + (2 : ℝ)⁻¹ ^ n) atTop (𝓝 s) := by
    have := tendsto_const_nhds (x := s) |>.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num))
    rwa [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hlo hhi

variable {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- `h_s(0)` at the dyadic radius `⌈s 2ⁿ⌉ / 2ⁿ` (and `0` if that radius is not positive). -/
def radialApprox (hcirc : Ω → ℝ → ℂ → ℝ) (n : ℕ) (ω : Ω) (s : ℝ) : ℝ :=
  if 0 < ⌈s * 2 ^ n⌉ then hcirc ω (dyadicCeil n s) 0 else 0

lemma measurable_radialApprox (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) (n : ℕ) :
    Measurable (Function.uncurry (radialApprox hcirc n)) := by
  have hG : Measurable fun p : Ω × ℤ => if 0 < p.2 then hcirc p.1 ((p.2 : ℝ) / 2 ^ n) 0 else 0 := by
    refine measurable_from_prod_countable_left fun m => ?_
    by_cases hm : 0 < m
    · simp only [hm, ↓reduceIte]
      exact hmc _ _ (div_pos (Int.cast_pos.2 hm) (by positivity))
    · simp only [hm, ↓reduceIte]
      exact measurable_const
  exact hG.comp (measurable_fst.prodMk (Int.measurable_ceil.comp (measurable_snd.mul_const _)))

/-- A jointly measurable version of the radial process `s ↦ h_s(0)`. -/
def radialVersion (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (s : ℝ) : ℝ :=
  limsup (fun n => radialApprox hcirc n ω s) atTop

lemma measurable_radialVersion (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    Measurable (Function.uncurry (radialVersion hcirc)) :=
  Measurable.limsup fun n => measurable_radialApprox hmc n

omit [MeasurableSpace Ω] in
lemma radialVersion_eq {ω : Ω} (hc : ContinuousOn (fun s => hcirc ω s 0) (Ioi 0)) {s : ℝ} (hs : 0 < s) :
    radialVersion hcirc ω s = hcirc ω s 0 := by
  have hpos : ∀ n : ℕ, 0 < ⌈s * 2 ^ n⌉ := fun n => Int.ceil_pos.2 (by positivity)
  have ht : Tendsto (fun n => radialApprox hcirc n ω s) atTop (𝓝 (hcirc ω s 0)) := by
    have := ((hc.continuousAt (Ioi_mem_nhds hs)).tendsto).comp (tendsto_dyadicCeil s)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, radialApprox, hpos n, ↓reduceIte]
  exact ht.limsup_eq

lemma continuousOn_radial {f : ℝ → ℂ → ℝ} (h : ContinuousOn (fun p : ℝ × ℂ => f p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun s => f s 0) (Ioi 0) :=
  h.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hs => ⟨hs, mem_univ _⟩

/-- The lateral observables computed with the measurable radial version. -/
def lateralVersionEval (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) : GFFObservable → ℝ
  | .pairing φ => hC ω φ - ∫ x, φ x * radialVersion hcirc ω ‖x‖
  | .circle r z => hcirc ω r z - Real.circleAverage (fun x => radialVersion hcirc ω ‖x‖) z r

lemma measurable_lateralVersion (hmp : ∀ φ, IsTestFunction univ φ → Measurable fun ω => hC ω φ)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    Measurable fun ω (o : GFFObservable.Admissible) => lateralVersionEval hC hcirc ω o.1 := by
  have hrad := measurable_radialVersion hmc
  rw [measurable_pi_iff]
  rintro ⟨o, ho⟩
  cases o with
  | pairing φ =>
    have hf : StronglyMeasurable fun p : Ω × ℂ => φ p.2 * radialVersion hcirc p.1 ‖p.2‖ :=
      ((ho.1.continuous.measurable.comp measurable_snd).mul
        (hrad.comp (measurable_fst.prodMk measurable_snd.norm))).stronglyMeasurable
    exact (hmp φ ho).sub (hf.integral_prod_right' (ν := volume)).measurable
  | circle r z =>
    have e : (fun ω => Real.circleAverage (fun x => radialVersion hcirc ω ‖x‖) z r) = fun ω =>
        (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), radialVersion hcirc ω ‖circleMap z r θ‖ := funext fun ω => by
      rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity), smul_eq_mul]
    have hf : StronglyMeasurable fun p : Ω × ℝ => radialVersion hcirc p.1 ‖circleMap z r p.2‖ :=
      (hrad.comp (measurable_fst.prodMk ((continuous_circleMap z r).measurable.comp measurable_snd).norm))
        |>.stronglyMeasurable
    have hCA : Measurable fun ω => Real.circleAverage (fun x => radialVersion hcirc ω ‖x‖) z r := by
      rw [e]
      exact (hf.integral_prod_right' (ν := volume.restrict (Ioc 0 (2 * π)))).measurable.const_mul _
    exact (hmc r z ho).sub hCA

omit [MeasurableSpace Ω] in
lemma lateralVersion_eq {ω : Ω} (hc : ContinuousOn (fun s => hcirc ω s 0) (Ioi 0)) :
    (fun o : GFFObservable.Admissible => lateralVersionEval hC hcirc ω o.1) =
      lateralProcess (hC ω) (hcirc ω) := by
  funext ⟨o, ho⟩
  cases o with
  | pairing φ =>
    show hC ω φ - ∫ x, φ x * radialVersion hcirc ω ‖x‖ = hC ω φ - ∫ x, φ x * hcirc ω ‖x‖ 0
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with x hx
    have hx0 : x ≠ 0 := fun h => hx (by rw [h]; rfl)
    rw [radialVersion_eq hc (norm_pos_iff.2 hx0)]
  | circle r z =>
    show hcirc ω r z - Real.circleAverage (fun x => radialVersion hcirc ω ‖x‖) z r =
      hcirc ω r z - Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r
    have hr : 0 < r := ho
    rw [Real.circleAverage_congr_codiscreteWithin
      (eventuallyEq_codiscreteWithin_of_ne _ 0 fun y hy => radialVersion_eq hc (norm_pos_iff.2 hy)) hr.ne']

/-- **The lateral process is a random variable** (product σ-algebra), given measurable pairings and circle averages
and an a.s. continuous circle average process. -/
theorem aemeasurable_lateralProcess {P : Measure Ω}
    (hmp : ∀ φ, IsTestFunction univ φ → Measurable fun ω => hC ω φ)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) :
    AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
  ⟨_, measurable_lateralVersion hmp hmc, by
    filter_upwards [hcont] with ω hω
    exact (lateralVersion_eq (continuousOn_radial hω)).symm⟩

/-! ### Transfer to the quantum cone -/

lemma tendsto_iff_forall_nat {u : ℕ → ℝ} {a : ℝ} :
    Tendsto u atTop (𝓝 a) ↔ ∀ m : ℕ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → dist (u k) a < ((m : ℝ) + 1)⁻¹ := by
  constructor
  · intro h m
    exact Metric.tendsto_atTop.1 h _ (by positivity)
  · intro h
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := h m
    exact ⟨N, fun k hk => (hN k hk).trans (by rwa [one_div] at hm)⟩

/-- **Almost surely `(h, φ_k) → h_r(z)` for the quantum cone** (`φ_k = circBump k z r`, `r > 0`, `|z| ≠ r`). -/
theorem ae_tendsto_circBump_of_isQuantumCone {γ : ℝ} {P : Measure Ω} (hQ : IsQuantumCone γ P hC hcirc)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≠ r) :
    ∀ᵐ ω ∂P, Tendsto (fun k => hC ω (circBump k z r)) atTop (𝓝 (hcirc ω r z)) := by
  obtain ⟨Ω', _, P', hC', hcirc', hP', hG, hlaw⟩ := hQ.lateral_law
  let pk : ℕ → GFFObservable.Admissible := fun k => ⟨.pairing (circBump k z r), isTestFunction_circBump k z r⟩
  let oc : GFFObservable.Admissible := ⟨.circle r z, hr⟩
  let E : Set (GFFObservable.Admissible → ℝ) :=
    {f | ∀ m : ℕ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → dist (f (pk k)) (f oc) < ((m : ℝ) + 1)⁻¹}
  have hE : MeasurableSet E := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun m => Measurable.exists fun N => Measurable.forall fun k =>
      measurable_const.imp (measurableSet_setOfPred.1 ?_))
    exact measurableSet_lt ((measurable_pi_apply _).dist (measurable_pi_apply _)) measurable_const
  have hlat' := aemeasurable_lateralProcess (P := P') hG.measurable_pairing hG.measurable_circle
    hG.ae_continuousOn_circle
  have hlat := aemeasurable_lateralProcess (P := P) hQ.measurable_pairing hQ.measurable_circle
    hQ.ae_continuousOn_circle
  have hgff : ∀ᵐ ω' ∂P', lateralProcess (hC' ω') (hcirc' ω') ∈ E := by
    filter_upwards [ae_tendsto_circBump hG hr z, hG.ae_continuousOn_circle] with ω' h1 h2
    have h3 := h1.sub (tendsto_integral_circBump_mul_radial (continuousOn_radial h2) hr hz)
    exact tendsto_iff_forall_nat.1 h3
  have hcone : ∀ᵐ ω ∂P, lateralProcess (hC ω) (hcirc ω) ∈ E := by
    have h := (ae_map_iff hlat' hE).2 hgff
    rw [← hlaw] at h
    exact (ae_map_iff hlat hE).1 h
  filter_upwards [hcone, hQ.ae_continuousOn_circle] with ω h1 h2
  have h1' : Tendsto (fun k => hC ω (circBump k z r) - ∫ x, circBump k z r x * hcirc ω ‖x‖ 0) atTop
      (𝓝 (hcirc ω r z - Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r)) :=
    tendsto_iff_forall_nat.2 h1
  have h3 := h1'.add (tendsto_integral_circBump_mul_radial (continuousOn_radial h2) hr hz)
  simp only [sub_add_cancel] at h3
  exact h3

end CirclePairing
end MatedCRT
