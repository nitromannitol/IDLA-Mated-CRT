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


/-! ## Step B: the limit (paper tex:213-237)

`ediffE a b = |a - b|` on `ℝ≥0∞` (the `L¹` distance; `ℝ≥0∞` carries no `edist`). The approximating
circle clock and circle measure at scale `dyadicScale k` are `circleClock` and `circleMeasure`. -/

/-- The distance `|a - b| = (a - b) + (b - a)` on `ℝ≥0∞`, used for the `L¹(P)` convergences of Step B. -/
noncomputable def ediffE (a b : ℝ≥0∞) : ℝ≥0∞ := (a - b) + (b - a)

theorem ediffE_triangle (a b c : ℝ≥0∞) : ediffE a c ≤ ediffE a b + ediffE b c := by
  unfold ediffE
  have h1 : a - c ≤ (a - b) + (b - c) := by
    rw [tsub_le_iff_right]
    calc a ≤ (a - b) + b := le_tsub_add
      _ ≤ (a - b) + ((b - c) + c) := add_le_add le_rfl le_tsub_add
      _ = (a - b) + (b - c) + c := (add_assoc _ _ _).symm
  have h2 : c - a ≤ (c - b) + (b - a) := by
    rw [tsub_le_iff_right]
    calc c ≤ (c - b) + b := le_tsub_add
      _ ≤ (c - b) + ((b - a) + a) := add_le_add le_rfl le_tsub_add
      _ = (c - b) + (b - a) + a := (add_assoc _ _ _).symm
  calc (a - c) + (c - a) ≤ ((a - b) + (b - c)) + ((c - b) + (b - a)) := add_le_add h1 h2
    _ = ((a - b) + (b - a)) + ((b - c) + (c - b)) := by ring

theorem ediffE_le_add (a b : ℝ≥0∞) : ediffE a b ≤ a + b :=
  add_le_add tsub_le_self tsub_le_self

theorem le_add_ediffE (a b : ℝ≥0∞) : a ≤ b + ediffE a b :=
  calc a ≤ b + (a - b) := le_add_tsub
    _ ≤ b + ((a - b) + (b - a)) := add_le_add le_rfl le_self_add

theorem ediffE_sub_le (a b : ℝ≥0∞) : a - b ≤ ediffE a b :=
  le_self_add

theorem ediffE_eq_zero {a b : ℝ≥0∞} (h : ediffE a b = 0) : a = b := by
  unfold ediffE at h
  rw [add_eq_zero] at h
  exact le_antisymm (tsub_eq_zero_iff_le.mp h.1) (tsub_eq_zero_iff_le.mp h.2)

/-- Before the exit time the path lies in the open set (`pathExitTime`, HarmonicBalls `Defs/LBM.lean:126`). -/
theorem mem_of_lt_pathExitTime {U : Set ℂ} (b : ContinuousPath ℂ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < pathExitTime U b) : b t ∈ U := by
  by_contra h
  exact absurd ht (not_lt.mpr (sInf_le ⟨t, rfl, h⟩))

/-- Before `σ = (pathExitTime U b).toNNReal` (strictly) the path lies in `U`. -/
theorem mem_of_lt_exit_toNNReal {U : Set ℂ} (b : ContinuousPath ℂ) {u : ℝ≥0}
    (hu : u < (pathExitTime U b).toNNReal) : b u ∈ U := by
  apply mem_of_lt_pathExitTime b
  by_cases h : pathExitTime U b = ⊤
  · simp [h] at hu
  · rw [← ENNReal.coe_toNNReal h]
    exact ENNReal.coe_lt_coe.mpr hu

/-- Points are `lebNN`-null (the time line `ℝ≥0` carries no atoms). -/
theorem lebNN_singleton (s : ℝ≥0) : lebNN {s} = 0 := by
  have hm : MeasurableSet (Real.toNNReal ⁻¹' {s}) :=
    measurable_real_toNNReal (measurableSet_singleton s)
  rw [lebNN, Measure.map_apply measurable_real_toNNReal (measurableSet_singleton s),
    Measure.restrict_apply hm]
  refine measure_mono_null (t := {(s : ℝ)}) ?_ Real.volume_singleton
  intro t ht
  have h1 : t.toNNReal = s := ht.1
  have h2 : (0 : ℝ) ≤ t := ht.2
  rw [Set.mem_singleton_iff, ← Real.coe_toNNReal t h2, h1]

theorem lebNN_Icc (s : ℝ≥0) : lebNN (Icc (0 : ℝ≥0) s) = (s : ℝ≥0∞) := by
  have h := lintegral_Icc_lebNN (s := s) (F := fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero] at h
  rw [h, ENNReal.ofReal_coe_nnreal]

/-- The circle clock is the density `ε^{γ²/2} e^{γ h_ε(b_u)}` against the time line (paper tex:27-33). -/
theorem circleClock_eq_density {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (k : ℕ)
    (hw : Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (b : ContinuousPath ℂ) {q : ℂ → ℝ≥0∞} (hq : Measurable q) (s : ℝ≥0) :
    ∫⁻ u in Icc (0 : ℝ≥0) s, q (b u) ∂(circleClock γ hcirc ω k b)
      = ∫⁻ u in Icc (0 : ℝ≥0) s, ENNReal.ofReal (circleWeight γ hcirc ω k (b u)) * q (b u) ∂lebNN := by
  have hbm : Measurable (fun u : ℝ≥0 => b u) := b.continuous.measurable
  have hwω : Measurable fun u : ℝ≥0 => ENNReal.ofReal (circleWeight γ hcirc ω k (b u)) :=
    ENNReal.measurable_ofReal.comp ((hw.comp measurable_prodMk_left).comp hbm)
  have hqb : Measurable fun u : ℝ≥0 => q (b u) := hq.comp hbm
  unfold circleClock
  rw [setLIntegral_withDensity_eq_setLIntegral_mul lebNN hwω hqb measurableSet_Icc]
  rfl

instance lebNN_sFinite : SFinite lebNN := by
  unfold lebNN
  infer_instance

/-- Tonelli for the circle clock: the `P`-expectation of the clock integral `∫_{[0,s]} q(b_u) dA_ε(u)` is the
time integral of `q(b_u)` against the `P`-expectation of the weight (paper tex:208-212, the exchange of `E`
and the time integral). -/
theorem lintegral_circleClock_expect {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ)
    (hw : Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (b : ContinuousPath ℂ) {q : ℂ → ℝ≥0∞} (hq : Measurable q) (s : ℝ≥0) :
    ∫⁻ ω, (∫⁻ u in Icc (0 : ℝ≥0) s, q (b u) ∂(circleClock γ hcirc ω k b)) ∂P
      = ∫⁻ u in Icc (0 : ℝ≥0) s,
          (∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k (b u)) ∂P) * q (b u) ∂lebNN := by
  have hbm : Measurable (fun u : ℝ≥0 => b u) := b.continuous.measurable
  have hF : Measurable fun p : Ω × ℝ≥0 =>
      ENNReal.ofReal (circleWeight γ hcirc p.1 k (b p.2)) * q (b p.2) :=
    (ENNReal.measurable_ofReal.comp (hw.comp (measurable_fst.prodMk (hbm.comp measurable_snd)))).mul
      (hq.comp (hbm.comp measurable_snd))
  calc ∫⁻ ω, (∫⁻ u in Icc (0 : ℝ≥0) s, q (b u) ∂(circleClock γ hcirc ω k b)) ∂P
      = ∫⁻ ω, ∫⁻ u, ENNReal.ofReal (circleWeight γ hcirc ω k (b u)) * q (b u)
          ∂(lebNN.restrict (Icc (0 : ℝ≥0) s)) ∂P :=
        lintegral_congr fun ω => circleClock_eq_density γ hcirc ω k hw b hq s
    _ = ∫⁻ u, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k (b u)) * q (b u) ∂P
          ∂(lebNN.restrict (Icc (0 : ℝ≥0) s)) :=
        lintegral_lintegral_swap hF.aemeasurable
    _ = _ := lintegral_congr fun u => by
        have hm : Measurable fun ω : Ω => ENNReal.ofReal (circleWeight γ hcirc ω k (b u)) :=
          ENNReal.measurable_ofReal.comp (hw.comp (measurable_prodMk_right (y := b u)))
        rw [lintegral_mul_const _ hm]

/-- Measurability in the environment of the circle clock functional (Tonelli). -/
theorem measurable_circleClock_expect {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ)
    (hw : Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (b : ContinuousPath ℂ) {q : ℂ → ℝ≥0∞} (hq : Measurable q) (s : ℝ≥0) :
    Measurable fun ω => ∫⁻ u in Icc (0 : ℝ≥0) s, q (b u) ∂(circleClock γ hcirc ω k b) := by
  have hbm : Measurable (fun u : ℝ≥0 => b u) := b.continuous.measurable
  have hF : Measurable fun p : Ω × ℝ≥0 =>
      ENNReal.ofReal (circleWeight γ hcirc p.1 k (b p.2)) * q (b p.2) :=
    (ENNReal.measurable_ofReal.comp (hw.comp (measurable_fst.prodMk (hbm.comp measurable_snd)))).mul
      (hq.comp (hbm.comp measurable_snd))
  have heq : (fun ω => ∫⁻ u in Icc (0 : ℝ≥0) s, q (b u) ∂(circleClock γ hcirc ω k b))
      = fun ω => ∫⁻ u in Icc (0 : ℝ≥0) s,
          ENNReal.ofReal (circleWeight γ hcirc ω k (b u)) * q (b u) ∂lebNN :=
    funext fun ω => circleClock_eq_density γ hcirc ω k hw b hq s
  rw [heq]
  exact hF.lintegral_prod_right'

/-- The clock bound: `E_P ∫_{[0,σ]} q(b_u) dA_ε(u) ≤ ‖q‖_∞ σ(b)` once the weight has `P`-mean one on the
ball (eq:occ-var, tex:27-33), for `k` in the range where this holds. -/
theorem lintegral_circleClock_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {z : ℂ} {r : ℝ} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ)
    (hw : Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hVar : ∀ x ∈ ball z r, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) {M : ℝ≥0∞} (hM : ∀ x, q x ≤ M) (b : ContinuousPath ℂ) :
    ∫⁻ ω, (∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal, q (b u)
        ∂(circleClock γ hcirc ω k b)) ∂P
      ≤ M * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) := by
  set s := (pathExitTime (ball z r) b).toNNReal with hs
  have hae : ∀ᵐ u ∂lebNN, u ∈ Icc (0 : ℝ≥0) s →
      (∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k (b u)) ∂P) * q (b u) = q (b u) := by
    rw [ae_iff]
    refine measure_mono_null ?_ (lebNN_singleton s)
    intro u hu
    change ¬ (u ∈ Icc (0 : ℝ≥0) s → _) at hu
    rw [not_imp] at hu
    obtain ⟨hIcc, hne'⟩ := hu
    rw [Set.mem_singleton_iff]
    by_contra hne
    apply hne'
    rw [hVar (b u) (mem_of_lt_exit_toNNReal b (lt_of_le_of_ne hIcc.2 hne)), one_mul]
  rw [lintegral_circleClock_expect P γ hcirc k hw b hq s]
  calc ∫⁻ u in Icc (0 : ℝ≥0) s, (∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k (b u)) ∂P) * q (b u) ∂lebNN
      = ∫⁻ u in Icc (0 : ℝ≥0) s, q (b u) ∂lebNN :=
        lintegral_congr_ae ((ae_restrict_iff' measurableSet_Icc).mpr hae)
    _ ≤ ∫⁻ u in Icc (0 : ℝ≥0) s, M ∂lebNN := lintegral_mono fun u => hM (b u)
    _ = M * (s : ℝ≥0∞) := by rw [setLIntegral_const, lebNN_Icc]


/-! ### The approximating and the limit clock functionals on a path -/

/-- The approximating clock functional `∫_{[0,σ(b)]} q(b_u) dA_ε(b)(u)` (paper tex:208-212, LHS of
eq:occ-baseapprox), with `σ(b) = (pathExitTime (ball z r) b).toNNReal` (the exit time of `D = ball z r`). -/
noncomputable def approxClockFun {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ) (z : ℂ) (r : ℝ)
    (ω : Ω) (b : ContinuousPath ℂ) (q : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal, q (b u) ∂(circleClock γ hcirc ω k b)

/-- The limit clock functional `∫_{[0,σ(b)]} q(b_u) dA(ω, b)(u)` (paper tex:234-237). -/
noncomputable def limitClockFun {Ω : Type*} (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (z : ℂ) (r : ℝ)
    (ω : Ω) (b : ContinuousPath ℂ) (q : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal, q (b u) ∂(dA ω b)

/-- Measurability of `b ↦ ∫_{[0,σ(b)]} G(b, u) du` for a jointly measurable `G` and a measurable `σ`. -/
theorem measurable_lintegral_Icc_var {β : Type*} [MeasurableSpace β] {σ' : β → ℝ≥0}
    (hσ : Measurable σ') {G : β × ℝ≥0 → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun b => ∫⁻ u in Icc (0 : ℝ≥0) (σ' b), G (b, u) ∂lebNN := by
  have h1 : MeasurableSet {p : β × ℝ≥0 | (0 : ℝ≥0) ≤ p.2} :=
    measurableSet_le measurable_const measurable_snd
  have h2 : MeasurableSet {p : β × ℝ≥0 | p.2 ≤ σ' p.1} :=
    measurableSet_le measurable_snd (hσ.comp measurable_fst)
  have hset : MeasurableSet {p : β × ℝ≥0 | p.2 ∈ Icc (0 : ℝ≥0) (σ' p.1)} := h1.inter h2
  have heq : ∀ b : β, ∫⁻ u in Icc (0 : ℝ≥0) (σ' b), G (b, u) ∂lebNN
      = ∫⁻ u, {p : β × ℝ≥0 | p.2 ∈ Icc (0 : ℝ≥0) (σ' p.1)}.indicator G (b, u) ∂lebNN := by
    intro b
    rw [← lintegral_indicator measurableSet_Icc]
    rfl
  simp only [heq]
  exact (hG.indicator hset).lintegral_prod_right'

/-- Joint measurability of `(ω, b) ↦ ∫_{[0,σ(b)]} q(b_u) dA_ε(b)(u)`. -/
theorem measurable_approxClockFun {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (k : ℕ) (z : ℂ) (r : ℝ)
    (hw : Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) (hτmeas : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b) :
    Measurable fun p : Ω × ContinuousPath ℂ => approxClockFun γ hcirc k z r p.1 p.2 q := by
  have hσ : Measurable fun b : ContinuousPath ℂ => (pathExitTime (ball z r) b).toNNReal :=
    ENNReal.measurable_toNNReal.comp hτmeas
  have hev : Measurable fun x : ContinuousPath ℂ × ℝ≥0 => x.1 x.2 :=
    (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable
  have hG : Measurable fun x : (Ω × ContinuousPath ℂ) × ℝ≥0 =>
      ENNReal.ofReal (circleWeight γ hcirc x.1.1 k (x.1.2 x.2)) * q (x.1.2 x.2) := by
    have hpair : Measurable fun x : (Ω × ContinuousPath ℂ) × ℝ≥0 => (x.1.1, x.1.2 x.2) :=
      (measurable_fst.comp measurable_fst).prodMk
        (hev.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    have h1 : Measurable fun x : (Ω × ContinuousPath ℂ) × ℝ≥0 =>
        ENNReal.ofReal (circleWeight γ hcirc x.1.1 k (x.1.2 x.2)) :=
      ENNReal.measurable_ofReal.comp (hw.comp hpair)
    have h2 : Measurable fun x : (Ω × ContinuousPath ℂ) × ℝ≥0 => q (x.1.2 x.2) :=
      hq.comp (hev.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact h1.mul h2
  have heq : ∀ p : Ω × ContinuousPath ℂ, approxClockFun γ hcirc k z r p.1 p.2 q
      = ∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) p.2).toNNReal,
          ENNReal.ofReal (circleWeight γ hcirc p.1 k (p.2 u)) * q (p.2 u) ∂lebNN := fun p =>
    circleClock_eq_density γ hcirc p.1 k hw p.2 hq _
  have hfun : (fun p : Ω × ContinuousPath ℂ => approxClockFun γ hcirc k z r p.1 p.2 q)
      = fun p => ∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) p.2).toNNReal,
          ENNReal.ofReal (circleWeight γ hcirc p.1 k (p.2 u)) * q (p.2 u) ∂lebNN :=
    funext heq
  rw [hfun]
  exact measurable_lintegral_Icc_var (σ' := fun p : Ω × ContinuousPath ℂ =>
    (pathExitTime (ball z r) p.2).toNNReal) (hσ.comp measurable_snd) hG

/-- Measurability of the limit clock functional, for each environment, in the path. -/
theorem measurable_ediffE {α : Type*} [MeasurableSpace α] {f g : α → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => ediffE (f a) (g a) :=
  (hf.sub hg).add (hg.sub hf)

theorem ediffE_comm (a b : ℝ≥0∞) : ediffE a b = ediffE b a := add_comm _ _

/-- `L¹`-distance of two integrals is at most the integral of the distance (Tonelli-free form). -/
theorem ediffE_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ediffE (∫⁻ a, f a ∂μ) (∫⁻ a, g a ∂μ) ≤ ∫⁻ a, ediffE (f a) (g a) ∂μ := by
  have h1 : ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ ≤ ∫⁻ a, (f a - g a) ∂μ := by
    rw [tsub_le_iff_right]
    calc ∫⁻ a, f a ∂μ ≤ ∫⁻ a, ((f a - g a) + g a) ∂μ := lintegral_mono fun a => le_tsub_add
      _ = ∫⁻ a, (f a - g a) ∂μ + ∫⁻ a, g a ∂μ := lintegral_add_right _ hg
  have h2 : ∫⁻ a, g a ∂μ - ∫⁻ a, f a ∂μ ≤ ∫⁻ a, (g a - f a) ∂μ := by
    rw [tsub_le_iff_right]
    calc ∫⁻ a, g a ∂μ ≤ ∫⁻ a, ((g a - f a) + f a) ∂μ := lintegral_mono fun a => le_tsub_add
      _ = ∫⁻ a, (g a - f a) ∂μ + ∫⁻ a, f a ∂μ := lintegral_add_right _ hf
  unfold ediffE
  calc (∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ) + (∫⁻ a, g a ∂μ - ∫⁻ a, f a ∂μ)
      ≤ ∫⁻ a, (f a - g a) ∂μ + ∫⁻ a, (g a - f a) ∂μ := add_le_add h1 h2
    _ = ∫⁻ a, ((f a - g a) + (g a - f a)) ∂μ := (lintegral_add_left (hf.sub hg) _).symm

/-- The `ω`-gap `|Λ_k(ω, b; q) - Λ(ω, b; q)|` of the approximating and the limit clock at a path (ENNReal). -/
noncomputable def clockGap {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (z : ℂ) (r : ℝ) (k : ℕ) (q : ℂ → ℝ≥0∞)
    (ω : Ω) (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  ediffE (approxClockFun γ hcirc k z r ω b q) (limitClockFun dA z r ω b q)

/-- The `P`-mean of the clock gap at a path: `∫ |Λ_k(ω, b) - Λ(ω, b)| P(dω)`. -/
noncomputable def clockGapMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (z : ℂ) (r : ℝ) (k : ℕ)
    (q : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  ∫⁻ ω, clockGap γ hcirc dA z r k q ω b ∂P

theorem limit_le_approx_add_gap {a b : ℝ≥0∞} : a ≤ b + ediffE b a := by
  rw [ediffE_comm]
  exact le_add_ediffE a b

set_option maxHeartbeats 400000 in
/-- Step B (paper tex:213-237): the approximating clocks converge in `L¹(P ⊗ P_y)` to the limit clock,
for a bounded measurable weight `q` (for the continuous weights of the countable family of Step C).
Inputs: `hLpath` is the conditional GMC clock input (Berestycki 2017, Thm 1.1, p. 3, on the finite-energy
premise of tex:153-164, with the Dirichlet-clock transfer of tex:178-201), for `PB`-a.e. path;
`hVar` is eq:occ-var (tex:27-33); `hLjoint` is the joint measurability of the limit clock.
The domination over paths is the argument of tex:213-218: `E_P ∫_{[0,σ]} q(b_u) dA_ε(u) ≤ ‖q‖ σ(b)` and
`E_y σ < ∞`. -/
theorem approxClock_tendsto_L1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (PB : Measure (ContinuousPath ℂ)) [IsFiniteMeasure PB]
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (r : ℝ)
    (hw : ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hτmeas : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b)
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) {M : ℝ≥0∞} (hMtop : M ≠ ⊤) (hM : ∀ x, q x ≤ M)
    (hVar : ∀ᶠ k in atTop, ∀ x ∈ ball z r, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    (hLjoint : Measurable fun p : Ω × ContinuousPath ℂ => limitClockFun dA z r p.1 p.2 q)
    (hLpath : ∀ᵐ b ∂PB, Tendsto (fun k => clockGapMean P γ hcirc dA z r k q b) atTop (𝓝 0))
    (hσint : ∫⁻ b, ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) ∂PB ≠ ⊤) :
    Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂PB)
        (∫⁻ b, limitClockFun dA z r ω b q ∂PB) ∂P) atTop (𝓝 0) := by
  have hΛ : ∀ k, Measurable fun p : Ω × ContinuousPath ℂ => approxClockFun γ hcirc k z r p.1 p.2 q :=
    fun k => measurable_approxClockFun γ hcirc k z r (hw k) hq hτmeas
  have hpairL : ∀ ω : Ω, Measurable fun b : ContinuousPath ℂ => (ω, b) :=
    fun ω => (measurable_const (a := ω)).prodMk measurable_id
  have hpairR : ∀ b : ContinuousPath ℂ, Measurable fun ω : Ω => (ω, b) :=
    fun b => measurable_id.prodMk (measurable_const (a := b))
  have hΛω : ∀ (k : ℕ) (ω : Ω), Measurable fun b : ContinuousPath ℂ => approxClockFun γ hcirc k z r ω b q :=
    fun k ω => Measurable.comp (g := fun p : Ω × ContinuousPath ℂ => approxClockFun γ hcirc k z r p.1 p.2 q)
      (f := fun b : ContinuousPath ℂ => (ω, b)) (hΛ k) (hpairL ω)
  have hLω : ∀ ω : Ω, Measurable fun b : ContinuousPath ℂ => limitClockFun dA z r ω b q :=
    fun ω => Measurable.comp (g := fun p : Ω × ContinuousPath ℂ => limitClockFun dA z r p.1 p.2 q)
      (f := fun b : ContinuousPath ℂ => (ω, b)) hLjoint (hpairL ω)
  have hΛΩ : ∀ (k : ℕ) (b : ContinuousPath ℂ), Measurable fun ω : Ω => approxClockFun γ hcirc k z r ω b q :=
    fun k b => Measurable.comp (g := fun p : Ω × ContinuousPath ℂ => approxClockFun γ hcirc k z r p.1 p.2 q)
      (f := fun ω : Ω => (ω, b)) (hΛ k) (hpairR b)
  have hgap : ∀ k, Measurable fun p : Ω × ContinuousPath ℂ => clockGap γ hcirc dA z r k q p.1 p.2 := by
    intro k
    unfold clockGap
    exact measurable_ediffE (hΛ k) hLjoint
  have hgapM : ∀ k, Measurable fun b => clockGapMean P γ hcirc dA z r k q b := by
    intro k
    unfold clockGapMean
    exact (hgap k).lintegral_prod_left'
  -- reduction to the path-wise `L¹` gap by the `L¹` distance of integrals
  have hred : ∀ k, ∫⁻ ω, ediffE (∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂PB)
      (∫⁻ b, limitClockFun dA z r ω b q ∂PB) ∂P ≤ ∫⁻ b, clockGapMean P γ hcirc dA z r k q b ∂PB := by
    intro k
    calc ∫⁻ ω, ediffE (∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂PB)
          (∫⁻ b, limitClockFun dA z r ω b q ∂PB) ∂P
        ≤ ∫⁻ ω, ∫⁻ b, clockGap γ hcirc dA z r k q ω b ∂PB ∂P :=
          lintegral_mono fun ω => ediffE_lintegral_le PB (hΛω k ω) (hLω ω)
      _ = ∫⁻ b, clockGapMean P γ hcirc dA z r k q b ∂PB :=
          lintegral_lintegral_swap (hgap k).aemeasurable
  -- the path-wise `L¹(P)` bound of the limit clock, from the convergence `hLpath`
  have hLbd : ∀ᵐ b ∂PB, ∫⁻ ω, limitClockFun dA z r ω b q ∂P
      ≤ M * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) := by
    filter_upwards [hLpath] with b hb
    have hev : ∀ᶠ k in atTop, ∫⁻ ω, limitClockFun dA z r ω b q ∂P
        ≤ M * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) + clockGapMean P γ hcirc dA z r k q b := by
      filter_upwards [hVar] with k hk
      calc ∫⁻ ω, limitClockFun dA z r ω b q ∂P
          ≤ ∫⁻ ω, (approxClockFun γ hcirc k z r ω b q + clockGap γ hcirc dA z r k q ω b) ∂P :=
            lintegral_mono fun ω => limit_le_approx_add_gap
        _ = (∫⁻ ω, approxClockFun γ hcirc k z r ω b q ∂P) + clockGapMean P γ hcirc dA z r k q b :=
            lintegral_add_left (hΛΩ k b) _
        _ ≤ M * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞)
              + clockGapMean P γ hcirc dA z r k q b :=
            add_le_add (lintegral_circleClock_le P γ hcirc k (hw k) hk hq hM b) le_rfl
    have hlim : Tendsto (fun k => M * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞)
        + clockGapMean P γ hcirc dA z r k q b) atTop
        (𝓝 (M * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) + 0)) :=
      tendsto_const_nhds.add hb
    rw [add_zero] at hlim
    exact ge_of_tendsto hlim hev
  -- domination over paths
  have hbound : ∀ᶠ k in atTop, ∀ᵐ b ∂PB,
      clockGapMean P γ hcirc dA z r k q b ≤ (2 * M) * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) := by
    filter_upwards [hVar] with k hk
    filter_upwards [hLbd] with b hb
    calc clockGapMean P γ hcirc dA z r k q b
        = ∫⁻ ω, clockGap γ hcirc dA z r k q ω b ∂P := rfl
      _ ≤ ∫⁻ ω, (approxClockFun γ hcirc k z r ω b q + limitClockFun dA z r ω b q) ∂P :=
          lintegral_mono fun ω => ediffE_le_add _ _
      _ = (∫⁻ ω, approxClockFun γ hcirc k z r ω b q ∂P) + ∫⁻ ω, limitClockFun dA z r ω b q ∂P :=
          lintegral_add_left (hΛΩ k b) _
      _ ≤ M * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞)
            + M * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) :=
          add_le_add (lintegral_circleClock_le P γ hcirc k (hw k) hk hq hM b) hb
      _ = (2 * M) * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) := by ring
  have h2 : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hfin : ∫⁻ b, (2 * M) * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) ∂PB ≠ ⊤ := by
    rw [lintegral_const_mul' (2 * M) _ (ENNReal.mul_ne_top h2 hMtop)]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top h2 hMtop) hσint
  have hDCT : Tendsto (fun k => ∫⁻ b, clockGapMean P γ hcirc dA z r k q b ∂PB) atTop (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence (μ := PB) (l := atTop)
      (f := fun _ => (0 : ℝ≥0∞))
      (fun b => (2 * M) * ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞))
      (Eventually.of_forall hgapM) hbound hfin
      (by filter_upwards [hLpath] with b hb; exact hb)
    simpa only [lintegral_zero] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hDCT (fun k => zero_le)
    (fun k => hred k)

/-! ## Step B, the field side (paper tex:218-233): the GMC measures `ν_ε → ν` -/

theorem measurable_circleMeasure_lintegral {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ)
    (hw : Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    Measurable fun ω => ∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k) := by
  have hF : Measurable fun p : Ω × ℂ => ENNReal.ofReal (circleWeight γ hcirc p.1 k p.2) * ρ p.2 := by
    have h1 : Measurable fun p : Ω × ℂ => ENNReal.ofReal (circleWeight γ hcirc p.1 k p.2) :=
      ENNReal.measurable_ofReal.comp hw
    exact h1.mul (hρ.comp measurable_snd)
  have heq : ∀ ω : Ω, ∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)
      = ∫⁻ x, ENNReal.ofReal (circleWeight γ hcirc ω k x) * ρ x := by
    intro ω
    have hp : Measurable fun x : ℂ => (ω, x) := measurable_const.prodMk measurable_id
    have hwω : Measurable fun x : ℂ => ENNReal.ofReal (circleWeight γ hcirc ω k x) := by
      have h := ENNReal.measurable_ofReal.comp (hw.comp hp)
      exact h
    unfold circleMeasure
    rw [lintegral_withDensity_eq_lintegral_mul volume hwω hρ]
    rfl
  simp only [heq]
  exact hF.lintegral_prod_right'

theorem lintegral_eq_setLIntegral_of_zero {μ : Measure ℂ} {S : Set ℂ} (hS : MeasurableSet S)
    {ρ : ℂ → ℝ≥0∞} (hρS : ∀ x ∉ S, ρ x = 0) :
    ∫⁻ x, ρ x ∂μ = ∫⁻ x in S, ρ x ∂μ := by
  rw [← lintegral_indicator hS]
  congr 1
  funext x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hρS x hx]

/-- The circle measures integrate to Lebesgue measure on `S` once the weight has mean one there
(eq:occ-var, tex:27-33): `E_P ν_ε(ρ; S) = ∫_S ρ dx`. -/
theorem lintegral_circleMeasure_expect_set {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ)
    (hw : Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    {S : Set ℂ} (hS : MeasurableSet S)
    (hVarS : ∀ x ∈ S, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    ∫⁻ ω, (∫⁻ x in S, ρ x ∂(circleMeasure γ hcirc ω k)) ∂P = ∫⁻ x in S, ρ x := by
  have hwx : ∀ ω : Ω, Measurable fun x : ℂ => ENNReal.ofReal (circleWeight γ hcirc ω k x) := by
    intro ω
    have hp : Measurable fun x : ℂ => (ω, x) := measurable_const.prodMk measurable_id
    have h := ENNReal.measurable_ofReal.comp (hw.comp hp)
    exact h
  have hwm : ∀ x : ℂ, Measurable fun ω : Ω => ENNReal.ofReal (circleWeight γ hcirc ω k x) := by
    intro x
    have hp : Measurable fun ω : Ω => (ω, x) := measurable_id.prodMk measurable_const
    have h := ENNReal.measurable_ofReal.comp (hw.comp hp)
    exact h
  have hF : Measurable fun p : Ω × ℂ => ENNReal.ofReal (circleWeight γ hcirc p.1 k p.2) * ρ p.2 := by
    have h1 : Measurable fun p : Ω × ℂ => ENNReal.ofReal (circleWeight γ hcirc p.1 k p.2) :=
      ENNReal.measurable_ofReal.comp hw
    exact h1.mul (hρ.comp measurable_snd)
  have step : ∀ ω : Ω, ∫⁻ x in S, ρ x ∂(circleMeasure γ hcirc ω k)
      = ∫⁻ x, ENNReal.ofReal (circleWeight γ hcirc ω k x) * ρ x ∂(volume.restrict S) := by
    intro ω
    unfold circleMeasure
    rw [setLIntegral_withDensity_eq_setLIntegral_mul volume (hwx ω) hρ hS]
    rfl
  calc ∫⁻ ω, (∫⁻ x in S, ρ x ∂(circleMeasure γ hcirc ω k)) ∂P
      = ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (circleWeight γ hcirc ω k x) * ρ x ∂(volume.restrict S) ∂P :=
        lintegral_congr fun ω => step ω
    _ = ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) * ρ x ∂P ∂(volume.restrict S) :=
        lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ x in S, ρ x := by
        refine lintegral_congr_ae ((ae_restrict_iff' hS).mpr (Eventually.of_forall fun x hx => ?_))
        dsimp only
        rw [lintegral_mul_const _ (hwm x), hVarS x hx, one_mul]

/-- The bounded GMC expectation bound: for `ρ` bounded and vanishing off `S`, the `P`-mean of the limit
measure integral is at most the Lebesgue integral over `S`. The `L¹` convergence `hconv` of the GMC
measures on bounded weights is the input (Berestycki 2017, Thm 1.1, p. 3; tex:218-233). -/
theorem lintegral_nu_expect_le_bdd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ν : Ω → Measure ℂ) {S : Set ℂ} (hS : MeasurableSet S)
    (hw : ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hVar : ∀ᶠ k in atTop, ∀ x ∈ S, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (hρS : ∀ x ∉ S, ρ x = 0)
    (hconv : Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k))
      (∫⁻ x, ρ x ∂(ν ω)) ∂P) atTop (𝓝 0)) :
    ∫⁻ ω, (∫⁻ x, ρ x ∂(ν ω)) ∂P ≤ ∫⁻ x in S, ρ x := by
  have hbd : ∀ᶠ k in atTop, ∫⁻ ω, (∫⁻ x, ρ x ∂(ν ω)) ∂P
      ≤ (∫⁻ x in S, ρ x) + ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k))
          (∫⁻ x, ρ x ∂(ν ω)) ∂P := by
    filter_upwards [hVar] with k hk
    calc ∫⁻ ω, (∫⁻ x, ρ x ∂(ν ω)) ∂P
        ≤ ∫⁻ ω, ((∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k))
            + ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω))) ∂P :=
          lintegral_mono fun ω => limit_le_approx_add_gap
      _ = (∫⁻ ω, ∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k) ∂P)
            + ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P :=
          lintegral_add_left (measurable_circleMeasure_lintegral γ hcirc k (hw k) hρ) _
      _ = (∫⁻ x in S, ρ x) + ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k))
            (∫⁻ x, ρ x ∂(ν ω)) ∂P := by
          rw [lintegral_congr (fun ω => lintegral_eq_setLIntegral_of_zero hS hρS),
            lintegral_circleMeasure_expect_set P γ hcirc k (hw k) hS hk hρ]
  have hlim := (tendsto_const_nhds (x := ∫⁻ x in S, ρ x)).add hconv
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim hbd

/-- Monotone truncation of a weight: `min(g, N)`, with the bounded-case field bound
`E_P ∫_S min(g,N) dν ≤ ∫_S min(g,N) dx` of `lintegral_nu_expect_le_bdd`. -/
theorem lintegral_nu_expect_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ν : Ω → Measure ℂ) {S : Set ℂ} (hS : MeasurableSet S)
    (hw : ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hVar : ∀ᶠ k in atTop, ∀ x ∈ S, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    (hνmeas : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν ω))
    (hconv : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) → (∀ x ∉ S, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P)
        atTop (𝓝 0))
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) (hgS : ∀ x ∉ S, g x = 0) :
    ∫⁻ ω, (∫⁻ x, g x ∂(ν ω)) ∂P ≤ ∫⁻ x in S, g x := by
  have hmeasN : ∀ N : ℕ, Measurable fun x => min (g x) (N : ℝ≥0∞) := fun N => hg.min measurable_const
  have hbdd : ∀ N : ℕ, ∫⁻ ω, (∫⁻ x, min (g x) (N : ℝ≥0∞) ∂(ν ω)) ∂P
      ≤ ∫⁻ x in S, min (g x) (N : ℝ≥0∞) := fun N =>
    lintegral_nu_expect_le_bdd P γ hcirc ν hS hw hVar (hmeasN N)
      (fun x hx => by simp [hgS x hx])
      (hconv _ (hmeasN N) ⟨(N : ℝ≥0∞), ENNReal.natCast_ne_top N, fun x => min_le_right _ _⟩
        (fun x hx => by simp [hgS x hx]))
  have hmono : Monotone fun N : ℕ => fun x => min (g x) (N : ℝ≥0∞) := fun m n hmn x =>
    min_le_min_left _ (by exact_mod_cast hmn)
  have hsup : ∀ x, (⨆ N : ℕ, min (g x) (N : ℝ≥0∞)) = g x := fun x => iSup_min_natCast (g x)
  have hω : ∀ ω : Ω, ∫⁻ x, g x ∂(ν ω) = ⨆ N : ℕ, ∫⁻ x, min (g x) (N : ℝ≥0∞) ∂(ν ω) := fun ω => by
    rw [← lintegral_iSup (fun N => hmeasN N) hmono]
    exact lintegral_congr fun x => (hsup x).symm
  calc ∫⁻ ω, (∫⁻ x, g x ∂(ν ω)) ∂P
      = ∫⁻ ω, ⨆ N : ℕ, ∫⁻ x, min (g x) (N : ℝ≥0∞) ∂(ν ω) ∂P := lintegral_congr hω
    _ = ⨆ N : ℕ, ∫⁻ ω, (∫⁻ x, min (g x) (N : ℝ≥0∞) ∂(ν ω)) ∂P :=
        lintegral_iSup (fun N => hνmeas _ (hmeasN N))
          (fun m n hmn ω => lintegral_mono fun x => min_le_min_left _ (by exact_mod_cast hmn))
    _ ≤ ⨆ N : ℕ, ∫⁻ x in S, min (g x) (N : ℝ≥0∞) := iSup_mono hbdd
    _ = ∫⁻ x in S, g x := by
        rw [← lintegral_iSup (fun N => hmeasN N) hmono]
        exact lintegral_congr fun x => hsup x

/-- Truncated field weight `min(G', N) · q` (paper tex:221-225, the truncation of `G_D` at `M`). -/
noncomputable def truncWeight (G' q : ℂ → ℝ≥0∞) (N : ℕ) (x : ℂ) : ℝ≥0∞ :=
  min (G' x) (N : ℝ≥0∞) * q x

/-- Tail weight `(G' - N) · C`, the error of the truncation (paper tex:221-225). -/
noncomputable def tailWeight (G' : ℂ → ℝ≥0∞) (C : ℝ≥0∞) (N : ℕ) (x : ℂ) : ℝ≥0∞ :=
  (G' x - (N : ℝ≥0∞)) * C

theorem mul_le_truncWeight_add {a q C M : ℝ≥0∞} (hq : q ≤ C) :
    a * q ≤ min a M * q + (a - M) * C := by
  rcases le_total a M with h | h
  · simp [min_eq_left h, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]
    calc a * q ≤ ((a - M) + M) * q := by gcongr; exact le_tsub_add
      _ = (a - M) * q + M * q := add_mul _ _ _
      _ ≤ (a - M) * C + M * q := by gcongr
      _ = M * q + (a - M) * C := by ring

theorem ediffE_le_of_le_add {a a' t : ℝ≥0∞} (h1 : a' ≤ a) (h2 : a ≤ a' + t) : ediffE a a' ≤ t := by
  unfold ediffE
  rw [tsub_eq_zero_of_le h1, add_zero]
  exact tsub_le_iff_right.mpr (by rw [add_comm]; exact h2)

theorem tendsto_tsub_natCast_zero {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    Tendsto (fun N : ℕ => a - (N : ℝ≥0∞)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε _
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  have hm' : (n : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by exact_mod_cast hm
  rw [tsub_eq_zero_of_le (hn.le.trans hm')]
  exact zero_le

theorem measurable_circleMeasure_setLIntegral {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ)
    (hw : Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    {S : Set ℂ} (hS : MeasurableSet S) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    Measurable fun ω => ∫⁻ x in S, ρ x ∂(circleMeasure γ hcirc ω k) := by
  have h := measurable_circleMeasure_lintegral γ hcirc k hw (ρ := S.indicator ρ) (hρ.indicator hS)
  simp only [lintegral_indicator hS] at h
  exact h

theorem measurable_nu_setLIntegral {Ω : Type*} [MeasurableSpace Ω] (ν : Ω → Measure ℂ)
    (hνmeas : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν ω))
    {S : Set ℂ} (hS : MeasurableSet S) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    Measurable fun ω => ∫⁻ x in S, ρ x ∂(ν ω) := by
  have h := hνmeas (S.indicator ρ) (hρ.indicator hS)
  simp only [lintegral_indicator hS] at h
  exact h

/-- The sandwich of the truncation (paper tex:221-225): `min(G',N) q ≤ G' q ≤ min(G',N) q + (G'-N) C`
on `S`, integrated against any measure `μ`. -/
theorem truncWeight_sandwich (μ : Measure ℂ) {S : Set ℂ}
    {G' q : ℂ → ℝ≥0∞} (hG' : Measurable G') (hq : Measurable q) {C : ℝ≥0∞} (hqC : ∀ x, q x ≤ C)
    (N : ℕ) :
    ∫⁻ x in S, truncWeight G' q N x ∂μ ≤ ∫⁻ x in S, G' x * q x ∂μ ∧
      ∫⁻ x in S, G' x * q x ∂μ
        ≤ ∫⁻ x in S, truncWeight G' q N x ∂μ + ∫⁻ x in S, tailWeight G' C N x ∂μ := by
  have hT : Measurable (truncWeight G' q N) :=
    (hG'.min measurable_const).mul hq
  constructor
  · refine lintegral_mono fun x => ?_
    unfold truncWeight
    gcongr
    exact min_le_left _ _
  · calc ∫⁻ x in S, G' x * q x ∂μ
        ≤ ∫⁻ x in S, (truncWeight G' q N x + tailWeight G' C N x) ∂μ :=
          lintegral_mono fun x => by
            unfold truncWeight tailWeight
            exact mul_le_truncWeight_add (hqC x)
      _ = (∫⁻ x in S, truncWeight G' q N x ∂μ) + ∫⁻ x in S, tailWeight G' C N x ∂μ :=
          lintegral_add_left hT _

/-- Fixed truncation level `N` (paper tex:221-233): eventually in `k`, the `P`-mean `L¹` gap of the
weighted integrals `∫_S G' q dν_ε` is at most the gap of the truncated integrals plus `2 ∫_S (G'-N)C dx`.
The `E ν_ε = dx` identity is eq:occ-var (`hVar`); the truncated gap is `hconv` for bounded weights. -/
theorem radon_side_fixedN {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ν : Ω → Measure ℂ) {S : Set ℂ} (hS : MeasurableSet S)
    (hw : ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hVar : ∀ᶠ k in atTop, ∀ x ∈ S, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    (hνmeas : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν ω))
    (hconv : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) → (∀ x ∉ S, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P)
        atTop (𝓝 0))
    {G' q : ℂ → ℝ≥0∞} (hG' : Measurable G') (hq : Measurable q) {C : ℝ≥0∞} (hqC : ∀ x, q x ≤ C)
    (N : ℕ) :
    ∀ᶠ k in atTop, ∫⁻ ω, ediffE (∫⁻ x in S, G' x * q x ∂(circleMeasure γ hcirc ω k))
        (∫⁻ x in S, G' x * q x ∂(ν ω)) ∂P
      ≤ ∫⁻ ω, ediffE (∫⁻ x in S, truncWeight G' q N x ∂(circleMeasure γ hcirc ω k))
          (∫⁻ x in S, truncWeight G' q N x ∂(ν ω)) ∂P
        + ((∫⁻ x in S, tailWeight G' C N x) + ∫⁻ x in S, tailWeight G' C N x) := by
  have hT : Measurable (truncWeight G' q N) := (hG'.min measurable_const).mul hq
  have hTl : Measurable (tailWeight G' C N) := (hG'.sub measurable_const).mul measurable_const
  filter_upwards [hVar] with k hk
  -- the pieces at level `k` and on the limit measure
  have hsk := fun ω => truncWeight_sandwich (circleMeasure γ hcirc ω k) (S := S) hG' hq hqC N
  have hsν := fun ω => truncWeight_sandwich (ν ω) (S := S) hG' hq hqC N
  have hpt : ∀ ω, ediffE (∫⁻ x in S, G' x * q x ∂(circleMeasure γ hcirc ω k))
        (∫⁻ x in S, G' x * q x ∂(ν ω))
      ≤ (∫⁻ x in S, tailWeight G' C N x ∂(circleMeasure γ hcirc ω k))
        + (ediffE (∫⁻ x in S, truncWeight G' q N x ∂(circleMeasure γ hcirc ω k))
            (∫⁻ x in S, truncWeight G' q N x ∂(ν ω))
          + ∫⁻ x in S, tailWeight G' C N x ∂(ν ω)) := by
    intro ω
    have h1 : ediffE (∫⁻ x in S, G' x * q x ∂(circleMeasure γ hcirc ω k))
          (∫⁻ x in S, truncWeight G' q N x ∂(circleMeasure γ hcirc ω k))
        ≤ ∫⁻ x in S, tailWeight G' C N x ∂(circleMeasure γ hcirc ω k) :=
      ediffE_le_of_le_add (hsk ω).1 (hsk ω).2
    have h2 : ediffE (∫⁻ x in S, truncWeight G' q N x ∂(ν ω))
          (∫⁻ x in S, G' x * q x ∂(ν ω))
        ≤ ∫⁻ x in S, tailWeight G' C N x ∂(ν ω) := by
      rw [ediffE_comm]
      exact ediffE_le_of_le_add (hsν ω).1 (hsν ω).2
    calc ediffE (∫⁻ x in S, G' x * q x ∂(circleMeasure γ hcirc ω k))
          (∫⁻ x in S, G' x * q x ∂(ν ω))
        ≤ ediffE (∫⁻ x in S, G' x * q x ∂(circleMeasure γ hcirc ω k))
            (∫⁻ x in S, truncWeight G' q N x ∂(circleMeasure γ hcirc ω k))
          + ediffE (∫⁻ x in S, truncWeight G' q N x ∂(circleMeasure γ hcirc ω k))
            (∫⁻ x in S, G' x * q x ∂(ν ω)) := ediffE_triangle _ _ _
      _ ≤ _ := by
          refine add_le_add h1 (le_trans (ediffE_triangle _ (∫⁻ x in S, truncWeight G' q N x ∂(ν ω)) _) ?_)
          exact add_le_add le_rfl h2
  -- integrate in `ω`
  have hTK : Measurable fun ω => ∫⁻ x in S, tailWeight G' C N x ∂(circleMeasure γ hcirc ω k) :=
    measurable_circleMeasure_setLIntegral γ hcirc k (hw k) hS hTl
  have hTν : Measurable fun ω => ∫⁻ x in S, tailWeight G' C N x ∂(ν ω) :=
    measurable_nu_setLIntegral ν hνmeas hS hTl
  have hE : Measurable fun ω => ediffE (∫⁻ x in S, truncWeight G' q N x ∂(circleMeasure γ hcirc ω k))
      (∫⁻ x in S, truncWeight G' q N x ∂(ν ω)) :=
    measurable_ediffE (measurable_circleMeasure_setLIntegral γ hcirc k (hw k) hS hT)
      (measurable_nu_setLIntegral ν hνmeas hS hT)
  have hTKeq := lintegral_circleMeasure_expect_set P γ hcirc k (hw k) hS hk hTl
  have hTν' : ∫⁻ ω, (∫⁻ x in S, tailWeight G' C N x ∂(ν ω)) ∂P ≤ ∫⁻ x in S, tailWeight G' C N x := by
    have h := lintegral_nu_expect_le P γ hcirc ν hS hw hVar hνmeas hconv
      (g := S.indicator (tailWeight G' C N)) (hTl.indicator hS)
      (fun x hx => Set.indicator_of_notMem hx _)
    simp only [lintegral_indicator hS, Measure.restrict_restrict hS, Set.inter_self] at h
    exact h
  calc ∫⁻ ω, ediffE (∫⁻ x in S, G' x * q x ∂(circleMeasure γ hcirc ω k))
        (∫⁻ x in S, G' x * q x ∂(ν ω)) ∂P
      ≤ ∫⁻ ω, ((∫⁻ x in S, tailWeight G' C N x ∂(circleMeasure γ hcirc ω k))
          + (ediffE (∫⁻ x in S, truncWeight G' q N x ∂(circleMeasure γ hcirc ω k))
              (∫⁻ x in S, truncWeight G' q N x ∂(ν ω))
            + ∫⁻ x in S, tailWeight G' C N x ∂(ν ω))) ∂P := lintegral_mono hpt
    _ = (∫⁻ ω, (∫⁻ x in S, tailWeight G' C N x ∂(circleMeasure γ hcirc ω k)) ∂P)
          + ∫⁻ ω, ((ediffE (∫⁻ x in S, truncWeight G' q N x ∂(circleMeasure γ hcirc ω k))
              (∫⁻ x in S, truncWeight G' q N x ∂(ν ω)))
            + ∫⁻ x in S, tailWeight G' C N x ∂(ν ω)) ∂P := lintegral_add_left hTK _
    _ = (∫⁻ ω, (∫⁻ x in S, tailWeight G' C N x ∂(circleMeasure γ hcirc ω k)) ∂P)
          + ((∫⁻ ω, ediffE (∫⁻ x in S, truncWeight G' q N x ∂(circleMeasure γ hcirc ω k))
              (∫⁻ x in S, truncWeight G' q N x ∂(ν ω)) ∂P)
            + ∫⁻ ω, (∫⁻ x in S, tailWeight G' C N x ∂(ν ω)) ∂P) := by
        rw [lintegral_add_left hE]
    _ ≤ (∫⁻ x in S, tailWeight G' C N x) + ((∫⁻ ω, ediffE (∫⁻ x in S, truncWeight G' q N x ∂(circleMeasure γ hcirc ω k))
              (∫⁻ x in S, truncWeight G' q N x ∂(ν ω)) ∂P)
            + (∫⁻ x in S, tailWeight G' C N x)) := by
        rw [hTKeq]
        exact add_le_add le_rfl (add_le_add le_rfl hTν')
    _ = _ := by ring

/-- Step B, field side (paper tex:221-233): for a bounded weight `q` on `S` and the finite-mass weight
`G'` (here `G' = ofReal (2 G_D(y, ·))`), the `L¹(P)` gap of `∫_S G' q dν_ε` tends to `0`. The three inputs:
`hVar` (eq:occ-var), `hconv` (the GMC convergence of bounded weights, Berestycki 2017 Thm 1.1 p. 3), and
`hνmeas` (measurability of the GMC measure, a standard property of the random measure `ν`). -/
theorem radon_side_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ν : Ω → Measure ℂ) {S : Set ℂ} (hS : MeasurableSet S)
    (hw : ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hVar : ∀ᶠ k in atTop, ∀ x ∈ S, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    (hνmeas : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν ω))
    (hconv : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) → (∀ x ∉ S, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P)
        atTop (𝓝 0))
    {G' q : ℂ → ℝ≥0∞} (hG' : Measurable G') (hG'fin : ∀ x, G' x ≠ ⊤) (hGint : ∫⁻ x in S, G' x ≠ ⊤)
    (hq : Measurable q) {C : ℝ≥0∞} (hC : C ≠ ⊤) (hqC : ∀ x, q x ≤ C) :
    Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x in S, G' x * q x ∂(circleMeasure γ hcirc ω k))
      (∫⁻ x in S, G' x * q x ∂(ν ω)) ∂P) atTop (𝓝 0) := by
  have hTl : ∀ N : ℕ, Measurable (tailWeight G' C N) :=
    fun N => (hG'.sub measurable_const).mul measurable_const
  have hL : Tendsto (fun N : ℕ => ∫⁻ x in S, tailWeight G' C N x) atTop (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence (μ := volume.restrict S) (l := atTop)
      (f := fun _ => (0 : ℝ≥0∞)) (fun x => G' x * C)
      (Eventually.of_forall fun N => hTl N)
      (Eventually.of_forall fun N => Eventually.of_forall fun x => by
        unfold tailWeight
        gcongr
        exact tsub_le_self)
      (by rw [lintegral_mul_const' C G' hC]; exact ENNReal.mul_ne_top hGint hC)
      (Eventually.of_forall fun x => by
        have h := ENNReal.Tendsto.mul_const (tendsto_tsub_natCast_zero (hG'fin x)) (Or.inr hC)
        unfold tailWeight
        simpa only [zero_mul] using h)
    simpa only [lintegral_zero] using this
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hη : 0 < ε / 2 / 2 := ENNReal.half_pos hε2.ne'
  obtain ⟨N₀, hN₀⟩ := (ENNReal.tendsto_nhds_zero.1 hL (ε / 2 / 2) hη).exists
  have hT0 : Measurable (S.indicator (truncWeight G' q N₀)) :=
    ((hG'.min measurable_const).mul hq).indicator hS
  have hTb : ∀ x, S.indicator (truncWeight G' q N₀) x ≤ (N₀ : ℝ≥0∞) * C := fun x => by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      unfold truncWeight
      exact mul_le_mul' (min_le_right _ _) (hqC x)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hconvN := hconv _ hT0 ⟨(N₀ : ℝ≥0∞) * C, ENNReal.mul_ne_top (ENNReal.natCast_ne_top N₀) hC, hTb⟩
    (fun x hx => Set.indicator_of_notMem hx _)
  have hA := ENNReal.tendsto_nhds_zero.1 hconvN (ε / 2) hε2
  filter_upwards [hA, radon_side_fixedN P γ hcirc ν hS hw hVar hνmeas hconv hG' hq hqC N₀] with k hk1 hk2
  simp only [lintegral_indicator hS] at hk1
  calc _ ≤ _ := hk2
    _ ≤ ε / 2 + (ε / 2 / 2 + ε / 2 / 2) := add_le_add hk1 (add_le_add hN₀ hN₀)
    _ = ε := by rw [ENNReal.add_halves (ε / 2), ENNReal.add_halves ε]

/-- The Green weight `2 G_D(y, ·)` of the ordinary Brownian occupation kernel (paper tex:48-52), as `ℝ≥0∞`. -/
noncomputable def greenWeight (D : Set ℂ) (y x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * greenFunction D y x)

/-- The limit identity for one bounded measurable weight `q` (paper tex:208-237): for `P`-a.e. environment the
`PB`-integral of the limit clock functional equals the Green pairing with the GMC measure. Proof: `F_k = R_k`
for every `k` (Step A, `circle_occupation_identity`), so the `L¹(P)` gap of `F` and `R` is at most the sum of
the two gaps, which tend to `0` (`approxClock_tendsto_L1`, `radon_side_tendsto`); a `P`-null gap is zero. -/
theorem limitClock_eq_nu_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (r : ℝ) {y : ℂ} (hy : y ∈ ball z r)
    (hS0 : KilledBrownianOccupationOnBall z r)
    (hτ : Integrable (fun b : ContinuousPath ℂ => (pathExitTime (ball z r) b).toReal)
      (planarBrownianMotion y))
    (hτmeas : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b)
    (hGmeas : Measurable fun x => greenFunction (ball z r) y x)
    (hGint : IntegrableOn (fun x => greenFunction (ball z r) y x) (ball z r))
    (hw : ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hVar : ∀ᶠ k in atTop, ∀ x ∈ ball z r, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    (ν : Ω → Measure ℂ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (hνmeas : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν ω))
    (hconv : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) →
      (∀ x ∉ ball z r, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P)
        atTop (𝓝 0))
    (hLjoint : ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun p : Ω × ContinuousPath ℂ => limitClockFun dA z r p.1 p.2 q)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) {M : ℝ≥0∞} (hMtop : M ≠ ⊤) (hM : ∀ x, q x ≤ M)
    (hLpath : ∀ᵐ b ∂planarBrownianMotion y,
      Tendsto (fun k => clockGapMean P γ hcirc dA z r k q b) atTop (𝓝 0))
    (hσint : ∫⁻ b, ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) ∂planarBrownianMotion y ≠ ⊤) :
    ∀ᵐ ω ∂P, ∫⁻ b, limitClockFun dA z r ω b q ∂planarBrownianMotion y
      = ∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω) := by
  have hG'm : Measurable (greenWeight (ball z r) y) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hGmeas)
  have hG'fin : ∀ x, greenWeight (ball z r) y x ≠ ⊤ := fun x => ENNReal.ofReal_ne_top
  have hGint' : ∫⁻ x in ball z r, greenWeight (ball z r) y x ≠ ⊤ :=
    ((hGint.const_mul 2).lintegral_lt_top).ne
  have hwω : ∀ k (ω : Ω), Measurable fun x : ℂ => circleWeight γ hcirc ω k x := fun k ω => by
    have hp : Measurable fun x : ℂ => (ω, x) := measurable_const.prodMk measurable_id
    have h := (hw k).comp hp
    exact h
  -- Step A (paper tex:208-212): the identity for every environment and every scale
  have hA : ∀ k (ω : Ω), ∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂planarBrownianMotion y
      = ∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(circleMeasure γ hcirc ω k) := fun k ω =>
    circle_occupation_identity hy hS0 hτ hτmeas hGmeas hGint γ hcirc ω k (hwω k ω) hq
  have hFm : Measurable fun ω => ∫⁻ b, limitClockFun dA z r ω b q ∂planarBrownianMotion y :=
    (hLjoint q hq).lintegral_prod_right'
  have hRm : Measurable fun ω => ∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω) :=
    measurable_nu_setLIntegral ν hνmeas measurableSet_ball (hG'm.mul hq)
  have hFkm : ∀ k, Measurable fun ω => ∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂planarBrownianMotion y :=
    fun k => (measurable_approxClockFun γ hcirc k z r (hw k) hq hτmeas).lintegral_prod_right'
  have hLim := approxClock_tendsto_L1 P (planarBrownianMotion y) γ hcirc z r hw hτmeas dA hq hMtop hM
    hVar (hLjoint q hq) hLpath hσint
  have hRad := radon_side_tendsto P γ hcirc ν measurableSet_ball hw hVar hνmeas hconv hG'm hG'fin hGint'
    hq hMtop hM
  have hle : ∀ k, ∫⁻ ω, ediffE (∫⁻ b, limitClockFun dA z r ω b q ∂planarBrownianMotion y)
        (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω)) ∂P
      ≤ (∫⁻ ω, ediffE (∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂planarBrownianMotion y)
          (∫⁻ b, limitClockFun dA z r ω b q ∂planarBrownianMotion y) ∂P)
        + ∫⁻ ω, ediffE (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(circleMeasure γ hcirc ω k))
            (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω)) ∂P := by
    intro k
    calc ∫⁻ ω, ediffE (∫⁻ b, limitClockFun dA z r ω b q ∂planarBrownianMotion y)
          (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω)) ∂P
        ≤ ∫⁻ ω, (ediffE (∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂planarBrownianMotion y)
            (∫⁻ b, limitClockFun dA z r ω b q ∂planarBrownianMotion y)
          + ediffE (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(circleMeasure γ hcirc ω k))
            (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω))) ∂P := by
          refine lintegral_mono fun ω => ?_
          have htri : ediffE (∫⁻ b, limitClockFun dA z r ω b q ∂planarBrownianMotion y)
              (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω))
              ≤ ediffE (∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂planarBrownianMotion y)
                  (∫⁻ b, limitClockFun dA z r ω b q ∂planarBrownianMotion y)
                + ediffE (∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂planarBrownianMotion y)
                  (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω)) := by
            have h := ediffE_triangle (∫⁻ b, limitClockFun dA z r ω b q ∂planarBrownianMotion y)
              (∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂planarBrownianMotion y)
              (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω))
            rwa [ediffE_comm (∫⁻ b, limitClockFun dA z r ω b q ∂planarBrownianMotion y)
              (∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂planarBrownianMotion y)] at h
          have hk : ediffE (∫⁻ b, approxClockFun γ hcirc k z r ω b q ∂planarBrownianMotion y)
              (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω))
              = ediffE (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(circleMeasure γ hcirc ω k))
                (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω)) := by
            rw [hA k ω]
          rw [hk] at htri
          exact htri
      _ = _ := lintegral_add_left (measurable_ediffE (hFkm k) hFm) _
  have hsum := hLim.add hRad
  rw [add_zero] at hsum
  have hzero : ∫⁻ ω, ediffE (∫⁻ b, limitClockFun dA z r ω b q ∂planarBrownianMotion y)
      (∫⁻ x in ball z r, greenWeight (ball z r) y x * q x ∂(ν ω)) ∂P = 0 :=
    le_antisymm (ge_of_tendsto hsum (Eventually.of_forall hle)) zero_le
  filter_upwards [(lintegral_eq_zero_iff (measurable_ediffE hFm hRm)).1 hzero] with ω hω
  exact ediffE_eq_zero hω

/-! ## Step C: measure determination (paper tex:234-237), by a countable π-system -/

/-- The occupation kernel of the limit clock at a path: the image of `dA(ω, b)` restricted to `[0, σ(b)]`
under the path (paper tex:234-237). -/
noncomputable def occKernel {Ω : Type*} (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (z : ℂ) (r : ℝ)
    (ω : Ω) (b : ContinuousPath ℂ) : Measure ℂ :=
  ((dA ω b).restrict (Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal)).map (fun u => b u)

theorem occKernel_apply {Ω : Type*} (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (z : ℂ) (r : ℝ)
    (ω : Ω) (b : ContinuousPath ℂ) {s : Set ℂ} (hs : MeasurableSet s) :
    occKernel dA z r ω b s = limitClockFun dA z r ω b (s.indicator 1) := by
  have hb : Measurable fun u : ℝ≥0 => b u := b.continuous.measurable
  unfold occKernel limitClockFun
  rw [Measure.map_apply hb hs, ← lintegral_indicator_one (hb hs)]
  rfl

/-- The limit occupation measure of an environment: `μ_L(ω)(B) = ∫ dP_y(b) ∫_{[0,σ]} 1_B(b_u) dA(ω, b)(u)`
(the left side of tex:234-237). -/
noncomputable def occMeasure {Ω : Type*} (PB : Measure (ContinuousPath ℂ))
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (z : ℂ) (r : ℝ) (ω : Ω) : Measure ℂ :=
  PB.bind (occKernel dA z r ω)

/-- The weighted GMC measure of the Green weight on `D` (the right side of tex:234-237). -/
noncomputable def nuWeighted {Ω : Type*} (ν : Ω → Measure ℂ) (D : Set ℂ) (y : ℂ) (ω : Ω) : Measure ℂ :=
  ((ν ω).restrict D).withDensity (greenWeight D y)

theorem nuWeighted_apply {Ω : Type*} (ν : Ω → Measure ℂ) (D : Set ℂ) (y : ℂ)
    (ω : Ω) {s : Set ℂ} (hs : MeasurableSet s) :
    nuWeighted ν D y ω s = ∫⁻ x in D, greenWeight D y x * s.indicator 1 x ∂(ν ω) := by
  unfold nuWeighted
  rw [withDensity_apply _ hs]
  calc ∫⁻ a in s, greenWeight D y a ∂((ν ω).restrict D)
      = ∫⁻ x, s.indicator (greenWeight D y) x ∂((ν ω).restrict D) := (lintegral_indicator hs _).symm
    _ = ∫⁻ x in D, s.indicator (greenWeight D y) x ∂(ν ω) := rfl
    _ = ∫⁻ x in D, greenWeight D y x * s.indicator 1 x ∂(ν ω) :=
        lintegral_congr fun x => by
          by_cases hx : x ∈ s
          · simp [hx]
          · simp [hx]

/-- A countable π-system of sets generating the Borel σ-algebra of `ℂ`, containing `univ`: the finite
intersections of a countable basis (the Borel σ-algebra is second countable). -/
theorem exists_countable_pi_generator :
    ∃ C : Set (Set ℂ), C.Countable ∧ IsPiSystem C ∧ Set.univ ∈ C ∧
      (∀ s ∈ C, MeasurableSet s) ∧ (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom C := by
  obtain ⟨b, hbc, -, hbb⟩ := TopologicalSpace.exists_countable_basis ℂ
  have hb'c : (insert Set.univ b).Countable := hbc.insert _
  obtain ⟨e, he⟩ := hb'c.exists_eq_range ⟨Set.univ, Set.mem_insert _ _⟩
  have heOpen : ∀ i, IsOpen (e i) := fun i => by
    have hmem : e i ∈ insert Set.univ b := by rw [he]; exact ⟨i, rfl⟩
    rcases hmem with h | h
    · rw [h]; exact isOpen_univ
    · exact hbb.isOpen h
  have hCmem : ∀ i, e i ∈ Set.range fun F : Finset ℕ => ⋂ i ∈ F, e i := fun i =>
    ⟨{i}, by simp⟩
  refine ⟨Set.range fun F : Finset ℕ => ⋂ i ∈ F, e i, Set.countable_range _, ?_, ⟨∅, by simp⟩, ?_, ?_⟩
  · rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩ _
    exact ⟨F ∪ G, by ext x; simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union, or_imp, forall_and]⟩
  · rintro _ ⟨F, rfl⟩
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => (heOpen i).measurableSet
  · have hbC : b ⊆ Set.range fun F : Finset ℕ => ⋂ i ∈ F, e i := fun s hs => by
      have hs' : s ∈ insert Set.univ b := Set.mem_insert_of_mem _ hs
      rw [he] at hs'
      obtain ⟨i, rfl⟩ := hs'
      exact hCmem i
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le fun s hs => ?_)
    · have hb : (inferInstance : MeasurableSpace ℂ) = borel ℂ := BorelSpace.measurable_eq
      rw [hb]
      refine MeasurableSpace.generateFrom_le fun U hU => ?_
      obtain ⟨S, hSb, hUS⟩ := hbb.open_eq_sUnion hU
      rw [hUS]
      exact MeasurableSet.sUnion (hbc.mono hSb) fun s hs =>
        MeasurableSpace.measurableSet_generateFrom (hbC (hSb hs))
    · obtain ⟨F, rfl⟩ := hs
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => (heOpen i).measurableSet

theorem occMeasure_apply {Ω : Type*} (PB : Measure (ContinuousPath ℂ))
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (z : ℂ) (r : ℝ) (ω : Ω)
    (hf : AEMeasurable (occKernel dA z r ω) PB) {s : Set ℂ} (hs : MeasurableSet s) :
    occMeasure PB dA z r ω s = ∫⁻ b, occKernel dA z r ω b s ∂PB := by
  unfold occMeasure
  exact Measure.bind_apply hs hf

theorem indicator_one_measurable {s : Set ℂ} (hs : MeasurableSet s) :
    Measurable (s.indicator (1 : ℂ → ℝ≥0∞)) :=
  (measurable_const (a := (1 : ℝ≥0∞))).indicator hs

theorem indicator_one_le_one (s : Set ℂ) (x : ℂ) : s.indicator (1 : ℂ → ℝ≥0∞) x ≤ 1 := by
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx]

/-- The kernel `b ↦ occKernel ω b` is measurable as a `Measure`-valued map when the limit clock functional is
measurable in the path for indicator weights. -/
theorem occKernel_aemeasurable {Ω : Type*} (PB : Measure (ContinuousPath ℂ))
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (z : ℂ) (r : ℝ) (ω : Ω)
    (hk : ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b : ContinuousPath ℂ => ∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal,
        q (b u) ∂(dA ω b)) :
    AEMeasurable (occKernel dA z r ω) PB := by
  refine Measurable.aemeasurable (Measure.measurable_of_measurable_coe _ fun t ht => ?_)
  have hfun : (fun b : ContinuousPath ℂ => occKernel dA z r ω b t)
      = fun b => ∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal,
          (t.indicator (1 : ℂ → ℝ≥0∞)) (b u) ∂(dA ω b) :=
    funext fun b => occKernel_apply dA z r ω b ht
  rw [hfun]
  exact hk _ (indicator_one_measurable ht)

/-- Step C (paper tex:234-237): for `P`-a.e. environment the two sides `μ_L(ω)` and `μ_R(ω)` of the occupation
identity agree as measures on `ℂ`. Proof: a countable π-system generating the Borel sets
(`exists_countable_pi_generator`); on each of its members the identity of `limitClock_eq_nu_ae` holds a.s.
(countably many); both measures are finite a.s.; the π-λ uniqueness (`ext_of_generate_finite`) concludes. -/
theorem occMeasure_eq_nuWeighted_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (r : ℝ) {y : ℂ} (hy : y ∈ ball z r)
    (hS0 : KilledBrownianOccupationOnBall z r)
    (hτ : Integrable (fun b : ContinuousPath ℂ => (pathExitTime (ball z r) b).toReal)
      (planarBrownianMotion y))
    (hτmeas : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b)
    (hGmeas : Measurable fun x => greenFunction (ball z r) y x)
    (hGint : IntegrableOn (fun x => greenFunction (ball z r) y x) (ball z r))
    (hw : ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hVar : ∀ᶠ k in atTop, ∀ x ∈ ball z r, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    (ν : Ω → Measure ℂ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (hνmeas : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν ω))
    (hconv : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) →
      (∀ x ∉ ball z r, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P)
        atTop (𝓝 0))
    (hLjoint : ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun p : Ω × ContinuousPath ℂ => limitClockFun dA z r p.1 p.2 q)
    (hmeasKernel : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b : ContinuousPath ℂ => ∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal,
        q (b u) ∂(dA ω b))
    (hLpath : ∀ q : ℂ → ℝ≥0∞, Measurable q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∀ᵐ b ∂planarBrownianMotion y, Tendsto (fun k => clockGapMean P γ hcirc dA z r k q b) atTop (𝓝 0))
    (hσint : ∫⁻ b, ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) ∂planarBrownianMotion y ≠ ⊤) :
    ∀ᵐ ω ∂P, occMeasure (planarBrownianMotion y) dA z r ω = nuWeighted ν (ball z r) y ω := by
  obtain ⟨C, hCc, hCpi, hCuniv, hCmeas, hCgen⟩ := exists_countable_pi_generator
  have hgen : ∀ᵐ ω ∂P, ∀ s ∈ C, occMeasure (planarBrownianMotion y) dA z r ω s
      = nuWeighted ν (ball z r) y ω s := by
    refine (ae_ball_iff hCc).2 fun s hs => ?_
    have hsm := hCmeas s hs
    have hid := limitClock_eq_nu_ae P γ hcirc z r hy hS0 hτ hτmeas hGmeas hGint hw hVar ν dA hνmeas
      hconv hLjoint (indicator_one_measurable hsm) ENNReal.one_ne_top (indicator_one_le_one s)
      (hLpath _ (indicator_one_measurable hsm) ⟨1, ENNReal.one_ne_top, indicator_one_le_one s⟩) hσint
    filter_upwards [hid, hmeasKernel] with ω hω hk
    rw [occMeasure_apply _ dA z r ω (occKernel_aemeasurable _ dA z r ω hk) hsm,
      nuWeighted_apply ν (ball z r) y ω hsm, ← hω]
    exact lintegral_congr fun b => occKernel_apply dA z r ω b hsm
  have hfin : ∀ᵐ ω ∂P, ∫⁻ x in ball z r, greenWeight (ball z r) y x ∂(ν ω) ≠ ⊤ := by
    have hG'm : Measurable (greenWeight (ball z r) y) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul hGmeas)
    have hR := measurable_nu_setLIntegral ν hνmeas (S := ball z r) measurableSet_ball hG'm
    have hGfin : ∫⁻ x in ball z r, greenWeight (ball z r) y x ≠ ⊤ :=
      ((hGint.const_mul 2).lintegral_lt_top).ne
    have hint : ∫⁻ ω, (∫⁻ x in ball z r, greenWeight (ball z r) y x ∂(ν ω)) ∂P ≠ ⊤ := by
      have h := lintegral_nu_expect_le P γ hcirc ν measurableSet_ball hw hVar hνmeas hconv
        (g := (ball z r).indicator (greenWeight (ball z r) y)) (hG'm.indicator measurableSet_ball)
        (fun x hx => Set.indicator_of_notMem hx _)
      simp only [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
        Set.inter_self] at h
      exact ne_top_of_le_ne_top hGfin h
    filter_upwards [ae_lt_top hR hint] with ω hω
    exact hω.ne
  filter_upwards [hgen, hfin] with ω hω hfω
  have hu : nuWeighted ν (ball z r) y ω univ = ∫⁻ x in ball z r, greenWeight (ball z r) y x ∂(ν ω) := by
    rw [nuWeighted_apply ν (ball z r) y ω MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (occMeasure (planarBrownianMotion y) dA z r ω) :=
    ⟨by rw [hω univ hCuniv, hu]; exact lt_top_iff_ne_top.2 hfω⟩
  exact MeasureTheory.ext_of_generate_finite C hCgen hCpi (fun s hs => hω s hs) (hω univ hCuniv)

theorem lintegral_occMeasure_eq {Ω : Type*} (PB : Measure (ContinuousPath ℂ))
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (z : ℂ) (r : ℝ) (ω : Ω)
    (hκ : AEMeasurable (occKernel dA z r ω) PB) {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    ∫⁻ x, q x ∂(occMeasure PB dA z r ω) = ∫⁻ b, limitClockFun dA z r ω b q ∂PB := by
  unfold occMeasure
  rw [Measure.lintegral_bind hκ hq.aemeasurable]
  refine lintegral_congr fun b => ?_
  unfold occKernel limitClockFun
  rw [lintegral_map hq b.continuous.measurable]

theorem lintegral_nuWeighted_eq {Ω : Type*} (ν : Ω → Measure ℂ) (D : Set ℂ) (y : ℂ) (ω : Ω)
    (hG : Measurable (greenWeight D y)) {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    ∫⁻ x, q x ∂(nuWeighted ν D y ω) = ∫⁻ x in D, greenWeight D y x * q x ∂(ν ω) := by
  unfold nuWeighted
  rw [lintegral_withDensity_eq_lintegral_mul _ hG hq]
  rfl

/-- **Lemma lem:occ-base** (paper tex:140-151, eq:occ-base), as the quenched identity `BaseOccupationIdentity`
(BaseClock.lean), for the base clock `dA` and the GMC measure `ν` of the environment, with the Brownian
motion `planarBrownianMotion y` and `D = ball z r ⊆ ball 0 1`. The literature inputs are binders:
* `hLpath` : per-path conditional GMC convergence of the clocks (Berestycki 2017 Thm 1.1 p. 3 with the finite
  energy premise tex:153-164, and the Dirichlet-clock transfer tex:178-201, gap G1 (MQ-li-8a));
* `hconvB1` : `L¹(P)` convergence of the circle GMC measures on bounded weights supported in `B_1`
  (Berestycki 2017 Thm 1.1 p. 3; tex:218-233);
* `hVar` : eq:occ-var (tex:27-33); `hS0` : the ordinary Brownian occupation identity S0 (tex:48-52, MQ-li-8e);
* `hmeasKernel`, `hLjoint`, `hνmeas`, `hw`, `hσint`, `hτ`, `hτmeas`, `hGmeas`, `hGint`: measurability and
  integrability of the GMC objects and of the exit time. -/
theorem baseOccupationIdentity_of_GMC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (r : ℝ) {y : ℂ} (hy : y ∈ ball z r)
    (hDB : ball z r ⊆ ball 0 1)
    (hS0 : KilledBrownianOccupationOnBall z r)
    (hτ : Integrable (fun b : ContinuousPath ℂ => (pathExitTime (ball z r) b).toReal)
      (planarBrownianMotion y))
    (hτmeas : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b)
    (hGmeas : Measurable fun x => greenFunction (ball z r) y x)
    (hGint : IntegrableOn (fun x => greenFunction (ball z r) y x) (ball z r))
    (hw : ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hVar : ∀ᶠ k in atTop, ∀ x ∈ ball z r, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    (ν : Ω → Measure ℂ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (hνmeas : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν ω))
    (hconvB1 : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) →
      (∀ x ∉ ball 0 1, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P)
        atTop (𝓝 0))
    (hLjoint : ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun p : Ω × ContinuousPath ℂ => limitClockFun dA z r p.1 p.2 q)
    (hmeasKernel : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b : ContinuousPath ℂ => ∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal,
        q (b u) ∂(dA ω b))
    (hLpath : ∀ q : ℂ → ℝ≥0∞, Measurable q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∀ᵐ b ∂planarBrownianMotion y, Tendsto (fun k => clockGapMean P γ hcirc dA z r k q b) atTop (𝓝 0))
    (hσint : ∫⁻ b, ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) ∂planarBrownianMotion y ≠ ⊤) :
    BaseOccupationIdentity P (planarBrownianMotion y) (ball z r) (greenFunction (ball z r) y) ν dA
      (fun b => (pathExitTime (ball z r) b).toNNReal) := by
  have hconv : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) →
      (∀ x ∉ ball z r, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P)
        atTop (𝓝 0) :=
    fun ρ hρ hb hz => hconvB1 ρ hρ hb (fun x hx => hz x (fun h => hx (hDB h)))
  have hG'm : Measurable (greenWeight (ball z r) y) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hGmeas)
  unfold BaseOccupationIdentity
  filter_upwards [occMeasure_eq_nuWeighted_ae P γ hcirc z r hy hS0 hτ hτmeas hGmeas hGint hw hVar ν dA
    hνmeas hconv hLjoint hmeasKernel hLpath hσint, hmeasKernel] with ω hμ hk
  intro q hq _
  have hκ := occKernel_aemeasurable (planarBrownianMotion y) dA z r ω hk
  calc ∫⁻ b, (∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal, q (b u) ∂(dA ω b))
        ∂(planarBrownianMotion y)
      = ∫⁻ x, q x ∂(occMeasure (planarBrownianMotion y) dA z r ω) :=
        (lintegral_occMeasure_eq (planarBrownianMotion y) dA z r ω hκ hq).symm
    _ = ∫⁻ x, q x ∂(nuWeighted ν (ball z r) y ω) := by rw [hμ]
    _ = ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * q x ∂(ν ω) :=
        lintegral_nuWeighted_eq ν (ball z r) y ω hG'm hq

end MatedCRT.KilledOccupation

