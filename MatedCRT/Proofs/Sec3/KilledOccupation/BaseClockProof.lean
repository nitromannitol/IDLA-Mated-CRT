import Mathlib
import HarmonicBalls.Defs.Green
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Defs.LBM
import HarmonicBalls.Defs.LQG
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClock
import MatedCRT.Proofs.Sec3.KilledOccupation.Potential

/-!
# The base occupation identity from its literature inputs (Appendix B, step S1: lem:occ-base)

Source: `paper/appendix-occupation-C16.tex`, Lemma lem:occ-base (lines 140-151, eq:occ-base) and its proof
(lines 152-240). The conclusion is `BaseOccupationIdentity` (`BaseClock.lean`).
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

/-- Lebesgue measure on the time line `ℝ≥0` of the clocks: the image of Lebesgue measure on `[0, ∞)` under
`Real.toNNReal`. (Mathlib has no `MeasureSpace ℝ≥0`.) -/
noncomputable def lebNN : Measure ℝ≥0 := (volume.restrict (Ici (0 : ℝ))).map Real.toNNReal

/-- Integrals over `Icc 0 s` for `lebNN` are the real integrals over `Ioc 0 s`. -/
theorem lintegral_Icc_lebNN {s : ℝ≥0} {F : ℝ≥0 → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u in Icc (0 : ℝ≥0) s, F u ∂lebNN = ∫⁻ t in Ioc (0 : ℝ) (s : ℝ), F t.toNNReal := by
  have hset : (Real.toNNReal ⁻¹' Icc (0 : ℝ≥0) s) ∩ Ici (0 : ℝ) = Icc (0 : ℝ) s := by
    ext t
    constructor
    · rintro ⟨⟨_, h⟩, h0⟩
      exact ⟨h0, Real.toNNReal_le_iff_le_coe.mp h⟩
    · rintro ⟨h0, h⟩
      exact ⟨⟨zero_le, Real.toNNReal_le_iff_le_coe.mpr h⟩, h0⟩
  rw [lebNN, Measure.restrict_map measurable_real_toNNReal measurableSet_Icc,
    lintegral_map hF measurable_real_toNNReal, Measure.restrict_restrict
      (measurable_real_toNNReal measurableSet_Icc), hset,
    Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- The circle-average weight `ε^{γ²/2} e^{γ h_ε(x)}` at the scale `ε = dyadicScale k` (paper eq:occ-var,
tex:27-33): the density of the approximating measure `ν_ε` and of the approximating clock. -/
noncomputable def circleWeight {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (k : ℕ) (x : ℂ) : ℝ :=
  dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω (dyadicScale k) x)

/-- The approximating measure `ν_ε(dx) = ε^{γ²/2} e^{γ h_ε(x)} dx` (paper tex:~27-33, `ν_ε`). -/
noncomputable def circleMeasure {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (k : ℕ) : Measure ℂ :=
  volume.withDensity fun x => ENNReal.ofReal (circleWeight γ hcirc ω k x)

/-- The approximating clock `dA_ε(s) = ε^{γ²/2} e^{γ h_ε(B_s)} ds` of the path `b` (paper tex:~27-33, `A_ε`). -/
noncomputable def circleClock {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (k : ℕ)
    (b : ContinuousPath ℂ) : Measure ℝ≥0 :=
  lebNN.withDensity fun u => ENNReal.ofReal (circleWeight γ hcirc ω k (b u))

/-- Joint measurability of a path evaluated at a real time (`ContinuousEval` of the path space). -/
theorem measurable_path_eval_real :
    Measurable fun p : ContinuousPath ℂ × ℝ => p.1 (p.2.toNNReal) :=
  (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
    (measurable_fst.prodMk (measurable_snd.real_toNNReal))

/-- Measurability in the path of the killed occupation integral `∫_0^{τ} f(b_t) dt` (the inner integral of
eq:occ-baseapprox, tex:208-212), for measurable `f ≥ 0`: the integrand is jointly measurable in `(b, t)`. -/
theorem measurable_occ_inner {z : ℂ} {r : ℝ}
    (hτmeas : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun b : ContinuousPath ℂ =>
      ∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal, f (b t.toNNReal) := by
  set τ : ContinuousPath ℂ → ℝ≥0∞ := fun b => pathExitTime (ball z r) b with hτdef
  have hτ' : Measurable fun b : ContinuousPath ℂ => (τ b).toReal := hτmeas.ennreal_toReal
  have hH : Measurable fun p : ContinuousPath ℂ × ℝ =>
      (if p.2 ∈ Ioc (0 : ℝ) (τ p.1).toReal then f (p.1 p.2.toNNReal) else 0) := by
    have hS : MeasurableSet {p : ContinuousPath ℂ × ℝ | p.2 ∈ Ioc (0 : ℝ) (τ p.1).toReal} := by
      have : {p : ContinuousPath ℂ × ℝ | p.2 ∈ Ioc (0 : ℝ) (τ p.1).toReal}
          = {p | 0 < p.2} ∩ {p | p.2 ≤ (τ p.1).toReal} := by
        ext p; simp [mem_Ioc]
      rw [this]
      exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (hτ'.comp measurable_fst))
    exact Measurable.ite hS (hf.comp measurable_path_eval_real) measurable_const
  have heq : ∀ b, (∫⁻ t in Ioc (0 : ℝ) (τ b).toReal, f (b t.toNNReal))
      = ∫⁻ t, (if t ∈ Ioc (0 : ℝ) (τ b).toReal then f (b t.toNNReal) else 0) := by
    intro b
    rw [← lintegral_indicator measurableSet_Ioc]
    exact lintegral_congr fun t => by simp only [Set.indicator_apply]
  have hfun : (fun b : ContinuousPath ℂ => ∫⁻ t in Ioc (0 : ℝ) (τ b).toReal, f (b t.toNNReal))
      = fun b => ∫⁻ t, (if t ∈ Ioc (0 : ℝ) (τ b).toReal then f (b t.toNNReal) else 0) :=
    funext heq
  rw [hfun]
  exact hH.lintegral_prod_right'

/-- Step A, lintegral form of the ordinary Brownian Green identity (paper tex:48-52, applied at tex:208-212):
for a bounded measurable `f ≥ 0` on `ℂ`, the expected occupation of `f` by the planar Brownian motion from `y`
killed on exiting `ball z r` equals `∫_D 2 G_D(y,x) f(x) dx`. Input: the Prop `KilledBrownianOccupationOnBall`
(S0, MQ-li-8e); integrability of the exit time (tex:169-170) and of the Green function (tex:226-227). -/
theorem lintegral_brownian_occupation {z : ℂ} {r : ℝ} {y : ℂ} (hy : y ∈ ball z r)
    (hS0 : KilledBrownianOccupationOnBall z r)
    (hτ : Integrable (fun b : ContinuousPath ℂ => (pathExitTime (ball z r) b).toReal)
      (planarBrownianMotion y))
    (hτmeas : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b)
    (hGmeas : Measurable fun x => greenFunction (ball z r) y x)
    (hGint : IntegrableOn (fun x => greenFunction (ball z r) y x) (ball z r))
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) {M : ℝ≥0∞} (hM : M ≠ ⊤) (hfM : ∀ x, f x ≤ M) :
    ∫⁻ b, (∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal, f (b t.toNNReal))
        ∂(planarBrownianMotion y)
      = ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * f x := by
  set PB := planarBrownianMotion y with hPB
  set τ : ContinuousPath ℂ → ℝ≥0∞ := fun b => pathExitTime (ball z r) b with hτdef
  set g : ContinuousPath ℂ → ℝ≥0∞ := fun b => ∫⁻ t in Ioc (0 : ℝ) (τ b).toReal, f (b t.toNNReal) with hgdef
  have hG0 : ∀ x, 0 ≤ greenFunction (ball z r) y x := fun x => greenFunction_nonneg isBounded_ball y x
  have hτ' : Measurable fun b : ContinuousPath ℂ => (τ b).toReal := hτmeas.ennreal_toReal
  have hM' : M < ⊤ := hM.lt_top
  -- pointwise bound of the inner integral
  have hgle : ∀ b, g b ≤ M * ENNReal.ofReal (τ b).toReal := by
    intro b
    calc g b ≤ ∫⁻ t in Ioc (0 : ℝ) (τ b).toReal, M := lintegral_mono fun t => hfM _
      _ = M * ENNReal.ofReal (τ b).toReal := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  have hgtop : ∀ b, g b < ⊤ := fun b => (hgle b).trans_lt
    (ENNReal.mul_lt_top hM' ENNReal.ofReal_lt_top)
  -- joint measurability and measurability of the inner integral in the path
  have hgmeas : Measurable g := measurable_occ_inner hτmeas hf
  -- finiteness of both sides
  have hLfin : ∫⁻ b, g b ∂(planarBrownianMotion y) < ⊤ := by
    calc ∫⁻ b, g b ∂(planarBrownianMotion y)
        ≤ ∫⁻ b, M * ENNReal.ofReal (τ b).toReal ∂(planarBrownianMotion y) := lintegral_mono hgle
      _ = M * ∫⁻ b, ENNReal.ofReal (τ b).toReal ∂(planarBrownianMotion y) :=
          lintegral_const_mul' M _ hM
      _ < ⊤ := ENNReal.mul_lt_top hM' hτ.lintegral_lt_top
  have hGfin : ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) < ⊤ :=
    Integrable.lintegral_lt_top hGint
  have hRfin : ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * f x < ⊤ := by
    have h1 : ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) < ⊤ := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGfin
    calc ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * f x
        ≤ ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * M :=
          lintegral_mono fun x => mul_le_mul_of_nonneg_left (hfM x) zero_le
      _ = (∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x)) * M :=
          lintegral_mul_const' _ _ hM
      _ < ⊤ := ENNReal.mul_lt_top h1 hM'
  -- the Bochner form of the left side, pointwise in the path
  have hLeq : ∫ b, (g b).toReal ∂(planarBrownianMotion y) = (∫⁻ b, g b ∂(planarBrownianMotion y)).toReal :=
    integral_toReal hgmeas.aemeasurable (ae_of_all _ hgtop)
  have hinner : ∀ b, (g b).toReal = ∫ t in Ioc (0 : ℝ) (τ b).toReal, (f (b t.toNNReal)).toReal := by
    intro b
    have hmt : Measurable fun t : ℝ => f (b t.toNNReal) :=
      hf.comp (b.continuous.comp continuous_real_toNNReal).measurable
    exact (integral_toReal hmt.aemeasurable (ae_of_all _ fun t => (hfM _).trans_lt hM')).symm
  set f' : ℂ → ℝ := fun x => (f x).toReal with hf'def
  have hf'm : Measurable f' := hf.ennreal_toReal
  have hf'b : ∃ K : ℝ, ∀ x, |f' x| ≤ K :=
    ⟨M.toReal, fun x => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono hM (hfM x)⟩
  have hS0app := hS0 y hy f' hf'm hf'b
  have hLHSeq : (∫⁻ b, g b ∂(planarBrownianMotion y)).toReal
      = 2 * ∫ x in ball z r, greenFunction (ball z r) y x * f' x := by
    rw [← hLeq]
    simp_rw [hinner]
    exact hS0app
  have hRHSeq : (∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * f x).toReal
      = 2 * ∫ x in ball z r, greenFunction (ball z r) y x * f' x := by
    have hmeasR : Measurable fun x => ENNReal.ofReal (2 * greenFunction (ball z r) y x) * f x :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hGmeas)).mul hf
    rw [← integral_toReal hmeasR.aemeasurable
      (ae_of_all _ fun x => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((hfM x).trans_lt hM')),
      ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hf'def]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg zero_le_two (hG0 x))]
    ring
  exact (ENNReal.toReal_eq_toReal_iff' hLfin.ne hRfin.ne).1 (hLHSeq.trans hRHSeq.symm)

/-- Step A for measurable (not necessarily bounded) weights: the monotone truncations `min f N` and
`⨆_N min(a, N) = a` (`iSup_min_natCast`) reduce to `lintegral_brownian_occupation`. -/
theorem lintegral_brownian_occupation_all {z : ℂ} {r : ℝ} {y : ℂ} (hy : y ∈ ball z r)
    (hS0 : KilledBrownianOccupationOnBall z r)
    (hτ : Integrable (fun b : ContinuousPath ℂ => (pathExitTime (ball z r) b).toReal)
      (planarBrownianMotion y))
    (hτmeas : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b)
    (hGmeas : Measurable fun x => greenFunction (ball z r) y x)
    (hGint : IntegrableOn (fun x => greenFunction (ball z r) y x) (ball z r))
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ b, (∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal, f (b t.toNNReal))
        ∂(planarBrownianMotion y)
      = ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * f x := by
  have hfN : ∀ N : ℕ, Measurable fun x => min (f x) (N : ℝ≥0∞) :=
    fun N => hf.min measurable_const
  have hmonoN : ∀ x, Monotone fun N : ℕ => min (f x) (N : ℝ≥0∞) :=
    fun x N M h => min_le_min_left _ (Nat.cast_le.mpr h)
  have hI : ∀ b : ContinuousPath ℂ,
      (∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal, f (b t.toNNReal))
        = ∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal, ⨆ N : ℕ, min (f (b t.toNNReal)) (N : ℝ≥0∞) :=
    fun b => lintegral_congr fun t => (iSup_min_natCast _).symm
  have hmeasN : ∀ (b : ContinuousPath ℂ) (N : ℕ), Measurable fun t : ℝ => min (f (b t.toNNReal)) (N : ℝ≥0∞) :=
    fun b N => (hfN N).comp (b.continuous.comp continuous_real_toNNReal).measurable
  have hmonoI : Monotone fun N : ℕ => fun b : ContinuousPath ℂ =>
      ∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal, min (f (b t.toNNReal)) (N : ℝ≥0∞) :=
    fun N M h b => lintegral_mono fun t => min_le_min_left _ (Nat.cast_le.mpr h)
  have hbdd : ∀ N : ℕ, ∫⁻ b, (∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal,
      min (f (b t.toNNReal)) (N : ℝ≥0∞)) ∂(planarBrownianMotion y)
        = ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * min (f x) (N : ℝ≥0∞) :=
    fun N => lintegral_brownian_occupation hy hS0 hτ hτmeas hGmeas hGint (hfN N)
      (ENNReal.natCast_ne_top N) (fun x => min_le_right _ _)
  have hmeasR : ∀ N : ℕ, Measurable fun x => ENNReal.ofReal (2 * greenFunction (ball z r) y x) * min (f x) (N : ℝ≥0∞) :=
    fun N => (ENNReal.measurable_ofReal.comp (measurable_const.mul hGmeas)).mul (hfN N)
  have hmonoR : Monotone fun N : ℕ => fun x : ℂ =>
      ENNReal.ofReal (2 * greenFunction (ball z r) y x) * min (f x) (N : ℝ≥0∞) :=
    fun N M h x => mul_le_mul_of_nonneg_left (min_le_min_left _ (Nat.cast_le.mpr h)) zero_le
  have hRsup : ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * f x
      = ⨆ N : ℕ, ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * min (f x) (N : ℝ≥0∞) := by
    calc ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * f x
        = ∫⁻ x in ball z r, ⨆ N : ℕ, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * min (f x) (N : ℝ≥0∞) :=
          lintegral_congr fun x => by rw [← ENNReal.mul_iSup, iSup_min_natCast]
      _ = _ := lintegral_iSup hmeasR hmonoR
  calc ∫⁻ b, (∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal, f (b t.toNNReal)) ∂(planarBrownianMotion y)
      = ∫⁻ b, (⨆ N : ℕ, ∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal,
          min (f (b t.toNNReal)) (N : ℝ≥0∞)) ∂(planarBrownianMotion y) := by
        refine lintegral_congr fun b => ?_
        rw [hI b]
        exact lintegral_iSup (hmeasN b) (fun N M h t => min_le_min_left _ (Nat.cast_le.mpr h))
    _ = ⨆ N : ℕ, ∫⁻ b, (∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal,
          min (f (b t.toNNReal)) (N : ℝ≥0∞)) ∂(planarBrownianMotion y) :=
        lintegral_iSup (fun N => measurable_occ_inner hτmeas (hfN N)) hmonoI
    _ = ⨆ N : ℕ, ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * min (f x) (N : ℝ≥0∞) :=
        iSup_congr fun N => hbdd N
    _ = _ := hRsup.symm

/-- Step A (paper eq:occ-baseapprox, tex:208-212), for one approximant at scale `dyadicScale k`: the
Brownian expectation of the approximating clock `dA_ε` equals the Green pairing with `ν_ε`, for every
measurable weight `q` (the ordinary Brownian Green identity S0 applied to `q · ε^{γ²/2} e^{γ h_ε}`). -/
theorem circle_occupation_identity {Ω : Type*} {z : ℂ} {r : ℝ} {y : ℂ} (hy : y ∈ ball z r)
    (hS0 : KilledBrownianOccupationOnBall z r)
    (hτ : Integrable (fun b : ContinuousPath ℂ => (pathExitTime (ball z r) b).toReal)
      (planarBrownianMotion y))
    (hτmeas : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b)
    (hGmeas : Measurable fun x => greenFunction (ball z r) y x)
    (hGint : IntegrableOn (fun x => greenFunction (ball z r) y x) (ball z r))
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (k : ℕ)
    (hw : Measurable (circleWeight γ hcirc ω k)) {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    ∫⁻ b, (∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal,
        q (b u) ∂(circleClock γ hcirc ω k b)) ∂(planarBrownianMotion y)
      = ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * q x
          ∂(circleMeasure γ hcirc ω k) := by
  have hbm : ∀ b : ContinuousPath ℂ, Measurable fun t : ℝ≥0 => b t :=
    fun b => b.continuous.measurable
  have hwb : ∀ b : ContinuousPath ℂ,
      Measurable fun u : ℝ≥0 => ENNReal.ofReal (circleWeight γ hcirc ω k (b u)) :=
    fun b => ENNReal.measurable_ofReal.comp (hw.comp (hbm b))
  have hqb : ∀ b : ContinuousPath ℂ, Measurable fun u : ℝ≥0 => q (b u) :=
    fun b => hq.comp (hbm b)
  have hinner : ∀ b : ContinuousPath ℂ,
      (∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal, q (b u) ∂(circleClock γ hcirc ω k b))
        = ∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal,
            q (b t.toNNReal) * ENNReal.ofReal (circleWeight γ hcirc ω k (b t.toNNReal)) := by
    intro b
    unfold circleClock
    rw [setLIntegral_withDensity_eq_setLIntegral_mul lebNN (hwb b) (hqb b) measurableSet_Icc]
    simp only [Pi.mul_apply]
    rw [lintegral_Icc_lebNN (F := fun u => ENNReal.ofReal (circleWeight γ hcirc ω k (b u)) * q (b u))
      ((hwb b).mul (hqb b))]
    exact lintegral_congr fun t => mul_comm _ _
  have hRHS : ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * q x
        ∂(circleMeasure γ hcirc ω k)
      = ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x)
          * (q x * ENNReal.ofReal (circleWeight γ hcirc ω k x)) := by
    have hρ : Measurable fun x => ENNReal.ofReal (circleWeight γ hcirc ω k x) :=
      ENNReal.measurable_ofReal.comp hw
    have hg : Measurable fun x => ENNReal.ofReal (2 * greenFunction (ball z r) y x) * q x :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hGmeas)).mul hq
    unfold circleMeasure
    rw [setLIntegral_withDensity_eq_setLIntegral_mul volume hρ hg measurableSet_ball]
    exact lintegral_congr fun x => by simp only [Pi.mul_apply]; ring
  calc ∫⁻ b, (∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal,
        q (b u) ∂(circleClock γ hcirc ω k b)) ∂(planarBrownianMotion y)
      = ∫⁻ b, (∫⁻ t in Ioc (0 : ℝ) (pathExitTime (ball z r) b).toReal,
          q (b t.toNNReal) * ENNReal.ofReal (circleWeight γ hcirc ω k (b t.toNNReal)))
          ∂(planarBrownianMotion y) := lintegral_congr hinner
    _ = ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x)
          * (q x * ENNReal.ofReal (circleWeight γ hcirc ω k x)) :=
        lintegral_brownian_occupation_all hy hS0 hτ hτmeas hGmeas hGint
          (hq.mul (ENNReal.measurable_ofReal.comp hw))
    _ = _ := hRHS.symm

end MatedCRT.KilledOccupation
