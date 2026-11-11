import MatedCRT.LPStaging.Bonanno.CirclePairing
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
    Real.circleAverage f c R = Real.circleAverage g c R :=
  LatticeProb.CirclePairing.circleAverage_congr_sphere h

lemma abs_circleAverage_le {f : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hf : CircleIntegrable f c R)
    (h : ∀ x ∈ sphere c |R|, |f x| ≤ M) : |Real.circleAverage f c R| ≤ M :=
  LatticeProb.CirclePairing.abs_circleAverage_le hf h

lemma circBump_eq_zero_of_forall_le {k : ℕ} {z x : ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ c ∈ sphere z r, (2 : ℝ)⁻¹ ^ k ≤ dist x c) : circBump k z r x = 0 :=
  LatticeProb.CirclePairing.circBump_eq_zero_of_forall_le hr h

/-- `∫ φ_k g → ⨍_{∂B_r(z)} g` for `g` continuous. -/
theorem tendsto_integral_circBump_mul {g : ℂ → ℝ} (hg : Continuous g) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Tendsto (fun k => ∫ x, circBump k z r x * g x) atTop (𝓝 (Real.circleAverage g z r)) :=
  LatticeProb.CirclePairing.tendsto_integral_circBump_mul hg hr z

/-- **Pathwise convergence of the radial terms**: `∫ φ_k(x) R(|x|) dx → ⨍_{∂B_r(z)} R(|·|)` for `R` continuous on
`(0, ∞)`, when the circle `∂B_r(z)` avoids `0`. -/
theorem tendsto_integral_circBump_mul_radial {R : ℝ → ℝ} (hR : ContinuousOn R (Ioi 0)) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : ‖z‖ ≠ r) :
    Tendsto (fun k => ∫ x, circBump k z r x * R ‖x‖) atTop
      (𝓝 (Real.circleAverage (fun x => R ‖x‖) z r)) :=
  LatticeProb.CirclePairing.tendsto_integral_circBump_mul_radial hR hr hz

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
  LatticeProb.CirclePairing.continuousOn_radial h

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
    Tendsto u atTop (𝓝 a) ↔ ∀ m : ℕ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → dist (u k) a < ((m : ℝ) + 1)⁻¹ :=
  LatticeProb.CirclePairing.tendsto_iff_forall_nat

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
