import MatedCRT.Defs.QuantumCone
import MatedCRT.FirstPass.Frozen.S5S6S7
import MatedCRT.FirstPass.LPBridge.WholePlaneGFFLateral

/-!
# Mean-zero restriction of the cone field (`ConeMeanZeroRestrictionStep`)

Reduction of `ConeMeanZeroRestrictionStep` (`MatedCRT/Steps/Sec6/GoodAnnulusPrevalence.lean:59`) to
four inputs: the lateral laws of two whole-plane GFFs agree; the lateral part of a whole-plane GFF is
independent of its radial part; the radial path `q ↦ h_{e^{-q}}(0)` at rational times `q ≥ 0` of a
whole-plane GFF is a standard Brownian motion in law; and the radial pairings `∫ φ(x) h_{|x|}(0) dx` of
the quantum cone converge absolutely. The radial path enters only through the countable family of its
rational-time values: the radial functional `f ↦ ∫ φ(x) f(-log|x|) dx` is evaluated along rational
approximations of `max (-log |x|) 0` (Duplantier-Sheffield, Armitage-Gardiner terminology), so no
path-space measurability is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped NNReal NNRat

noncomputable section

namespace MatedCRT.ConeMeanZeroRestriction

/-- The index of `ConeMeanZeroRestrictionStep`: mean-zero test functions supported in the unit disc. -/
abbrev Mean0Test : Type := {φ : ℂ → ℝ // IsTestFunction (ball 0 1) φ ∧ ∫ x, φ x = 0}

/-- The radial path at rational times `q ≥ 0`: `q ↦ h_{e^{-q}}(0)`. -/
def radRat (hcirc : ℝ → ℂ → ℝ) (q : ℚ≥0) : ℝ := (radialProcess hcirc).1 (q : ℝ≥0)

/-- The time `max (-log |x|) 0` of `x` on the radial axis. -/
def radTime (x : ℂ) : ℝ := max (-Real.log ‖x‖) 0

/-- Rational approximations of `radTime x` from below, with mesh `1/(n+1)`. -/
def ratApprox (n : ℕ) (x : ℂ) : ℚ≥0 :=
  (⌊radTime x * ((n : ℝ) + 1)⌋₊ : ℚ≥0) / ((n : ℚ≥0) + 1)

/-- The value at `x` of a rational-time function `f`, read along `ratApprox · x`. -/
def limVal (f : ℚ≥0 → ℝ) (x : ℂ) : ℝ := limsup (fun n : ℕ => f (ratApprox n x)) atTop

/-- The radial functional `f ↦ ∫ φ(x) f(max (-log |x|) 0) dx` on rational-time paths. -/
def radialFunctional (φ : ℂ → ℝ) (f : ℚ≥0 → ℝ) : ℝ := ∫ x, φ x * limVal f x

/-- The drift removed from a rational-time path: `q ↦ f q - γ q`. -/
def driftRat (γ : ℝ) (f : ℚ≥0 → ℝ) : ℚ≥0 → ℝ := fun q => f q - γ * (q : ℝ)

/-- The lateral pairing `φ ↦ (h, φ) - ∫ φ(x) h_{|x|}(0) dx` of one sample (`lateralEval`, pairing case). -/
def lateralPair (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (φ : ℂ → ℝ) : ℝ :=
  hC φ - ∫ x, φ x * hcirc ‖x‖ 0

lemma ratApprox_coe (n : ℕ) (x : ℂ) :
    ((ratApprox n x : ℚ≥0) : ℝ) = (⌊radTime x * ((n : ℝ) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1) := by
  unfold ratApprox
  push_cast
  ring

lemma radTime_nonneg (x : ℂ) : 0 ≤ radTime x := le_max_right _ _

lemma tendsto_ratApprox (x : ℂ) :
    Tendsto (fun n : ℕ => ((ratApprox n x : ℚ≥0) : ℝ)) atTop (𝓝 (radTime x)) := by
  have hlow : ∀ n : ℕ, radTime x - 1 / ((n : ℝ) + 1) ≤ ((ratApprox n x : ℚ≥0) : ℝ) := by
    intro n
    rw [ratApprox_coe]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 := Nat.lt_floor_add_one (radTime x * ((n : ℝ) + 1))
    have key : radTime x * ((n : ℝ) + 1) - 1 ≤ (⌊radTime x * ((n : ℝ) + 1)⌋₊ : ℝ) := by
      linarith [h1]
    have e : radTime x - 1 / ((n : ℝ) + 1) = (radTime x * ((n : ℝ) + 1) - 1) / ((n : ℝ) + 1) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right key hpos.le
  have hup : ∀ n : ℕ, ((ratApprox n x : ℚ≥0) : ℝ) ≤ radTime x := by
    intro n
    rw [ratApprox_coe, div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    exact Nat.floor_le (mul_nonneg (radTime_nonneg x) (by positivity))
  have hlim : Tendsto (fun n : ℕ => radTime x - 1 / ((n : ℝ) + 1)) atTop (𝓝 (radTime x)) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (radTime x)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hup

lemma continuous_radialCircle {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) :
    Continuous (fun t : ℝ => hcirc (Real.exp (-t)) 0) := by
  have h1 : Continuous (fun t : ℝ => ((Real.exp (-t), (0 : ℂ)) : ℝ × ℂ)) := by fun_prop
  exact hc.comp_continuous h1 (fun t => ⟨Real.exp_pos _, mem_univ _⟩)

lemma limVal_eq_of_tendsto {f : ℚ≥0 → ℝ} {x : ℂ} {a : ℝ}
    (h : Tendsto (fun n : ℕ => f (ratApprox n x)) atTop (𝓝 a)) : limVal f x = a :=
  h.limsup_eq

lemma limVal_radRat {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (x : ℂ) :
    limVal (radRat hcirc) x = hcirc (Real.exp (-(radTime x))) 0 := by
  apply limVal_eq_of_tendsto
  have hT := ((continuous_radialCircle hc).tendsto (radTime x)).comp (tendsto_ratApprox x)
  refine hT.congr (fun n => ?_)
  simp [radRat, radialProcess]
  norm_cast

lemma limVal_driftRat {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (γ : ℝ) (x : ℂ) :
    limVal (driftRat γ (radRat hcirc)) x = limVal (radRat hcirc) x - γ * radTime x := by
  rw [limVal_radRat hc x]
  apply limVal_eq_of_tendsto
  have hT := ((continuous_radialCircle hc).tendsto (radTime x)).comp (tendsto_ratApprox x)
  have hD := hT.sub (((tendsto_ratApprox x).const_mul γ))
  refine hD.congr (fun n => ?_)
  simp [driftRat, radRat, radialProcess]
  norm_cast

lemma tsupport_ball_zero {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) 1) φ) {x : ℂ} (h1 : 1 ≤ ‖x‖) :
    φ x = 0 := by
  by_contra hne
  have := hφ.2.2 (subset_tsupport φ hne)
  simp [mem_ball, dist_zero_right] at this
  linarith

lemma limVal_radRat_mul_eq {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ))
    {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) 1) φ) {x : ℂ} (hx : x ≠ 0) :
    φ x * limVal (radRat hcirc) x = φ x * hcirc ‖x‖ 0 := by
  by_cases h1 : ‖x‖ < 1
  · have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hlog : Real.log ‖x‖ < 0 := Real.log_neg hpos h1
    have htime : radTime x = -Real.log ‖x‖ := by
      unfold radTime
      exact max_eq_left (by linarith)
    rw [limVal_radRat hc x, htime]
    congr 2
    simp [Real.exp_log hpos]
  · rw [tsupport_ball_zero hφ (not_lt.1 h1)]
    simp

lemma radialFunctional_eq_integral {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ))
    {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) 1) φ) :
    radialFunctional φ (radRat hcirc) = ∫ x, φ x * hcirc ‖x‖ 0 := by
  unfold radialFunctional
  apply integral_congr_ae
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (μ := (volume : Measure ℂ)) (0 : ℂ))] with x hx
  exact limVal_radRat_mul_eq hc hφ hx

lemma radTime_mul_eq_neg_log {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) 1) φ) (x : ℂ) :
    φ x * radTime x = -(φ x * Real.log ‖x‖) := by
  by_cases h1 : ‖x‖ < 1
  · by_cases hx : x = 0
    · simp [hx, radTime]
    · have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hlog : Real.log ‖x‖ < 0 := Real.log_neg hpos h1
      have htime : radTime x = -Real.log ‖x‖ := by
        unfold radTime
        exact max_eq_left (by linarith)
      rw [htime]; ring
  · rw [tsupport_ball_zero hφ (not_lt.1 h1)]
    simp

section Assembly

/-- The radial time is measurable in `x`. -/
lemma measurable_radTime : Measurable radTime := by
  unfold radTime
  fun_prop

lemma measurable_ratApprox_pair (n : ℕ) :
    Measurable (fun p : (ℚ≥0 → ℝ) × ℂ => p.1 (ratApprox n p.2)) := by
  have hk : Measurable (fun x : ℂ => ⌊radTime x * ((n : ℝ) + 1)⌋₊) :=
    Measurable.nat_floor ((measurable_radTime).mul_const _)
  have hG : Measurable (fun q : (ℚ≥0 → ℝ) × ℕ =>
      q.1 (((q.2 : ℕ) : ℚ≥0) / ((n : ℚ≥0) + 1))) :=
    measurable_from_prod_countable_left (fun j => measurable_pi_apply
      ((((j : ℕ) : ℚ≥0)) / ((n : ℚ≥0) + 1)))
  exact hG.comp (measurable_fst.prodMk (hk.comp measurable_snd))

lemma measurable_limVal_pair : Measurable (fun p : (ℚ≥0 → ℝ) × ℂ => limVal p.1 p.2) :=
  Measurable.limsup (fun n => measurable_ratApprox_pair n)

lemma measurable_radialFunctional {φ : ℂ → ℝ} (hφ : Measurable φ) :
    Measurable (radialFunctional φ) := by
  unfold radialFunctional
  have hf : StronglyMeasurable (fun p : (ℚ≥0 → ℝ) × ℂ => φ p.2 * limVal p.1 p.2) :=
    ((hφ.comp measurable_snd).mul measurable_limVal_pair).stronglyMeasurable
  exact (hf.integral_prod_right' (ν := volume)).measurable

/-- The radial path of a sample at rational times is measurable in the sample. -/
lemma measurable_radRat {Ω : Type*} [MeasurableSpace Ω] {hcirc : Ω → ℝ → ℂ → ℝ}
    (hm : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    Measurable (fun ω (q : ℚ≥0) => radRat (hcirc ω) q) := by
  apply Measurable.of_eval
  intro q
  exact hm _ _ (Real.exp_pos _)

end Assembly

section Identities

lemma measurable_test {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) 1) φ) : Measurable φ :=
  hφ.1.continuous.measurable

lemma test_univ {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) 1) φ) : IsTestFunction Set.univ φ :=
  ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩

/-- The radial pairing of a cone or whole-plane sample with the drift-removed rational path. -/
lemma radialFunctional_drift {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (γ : ℝ)
    {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) 1) φ)
    (hint : Integrable (fun x => φ x * hcirc ‖x‖ 0)) :
    radialFunctional φ (radRat hcirc) =
      radialFunctional φ (driftRat γ (radRat hcirc)) - γ * ∫ x, φ x * Real.log ‖x‖ := by
  have hA : Integrable (fun x => φ x * limVal (radRat hcirc) x) := by
    refine hint.congr ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (μ := (volume : Measure ℂ)) (0 : ℂ))]
      with x hx
    exact (limVal_radRat_mul_eq hc hφ hx).symm
  have hlog : Integrable (fun x => φ x * Real.log ‖x‖) := MatedCRT.WholePlaneGFFLateral.integrable_test_mul_log_norm (test_univ hφ)
  have hT : Integrable (fun x => φ x * radTime x) := by
    have e : (fun x => φ x * radTime x) = fun x => -(φ x * Real.log ‖x‖) :=
      funext (radTime_mul_eq_neg_log hφ)
    rw [e]
    exact hlog.neg
  have hB : Integrable (fun x => φ x * limVal (driftRat γ (radRat hcirc)) x) := by
    have e : (fun x => φ x * limVal (driftRat γ (radRat hcirc)) x) =
        fun x => φ x * limVal (radRat hcirc) x - γ * (φ x * radTime x) := by
      funext x
      rw [limVal_driftRat hc γ x]
      ring
    rw [e]
    exact hA.sub (hT.const_mul γ)
  have hpt : ∀ x, φ x * limVal (radRat hcirc) x =
      φ x * limVal (driftRat γ (radRat hcirc)) x + γ * (φ x * radTime x) := by
    intro x
    rw [limVal_driftRat hc γ x]
    ring
  have hm : ∫ x, φ x * radTime x = -∫ x, φ x * Real.log ‖x‖ := by
    rw [← integral_neg]
    exact integral_congr_ae (ae_of_all _ (radTime_mul_eq_neg_log hφ))
  unfold radialFunctional
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add hB (hT.const_mul γ), integral_const_mul, hm]
  ring

/-- Cone pairing: the pairing is its lateral part plus the drifted radial functional. -/
lemma cone_pairing_eq {hC : (ℂ → ℝ) → ℝ} {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (γ : ℝ)
    {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) 1) φ)
    (hint : Integrable (fun x => φ x * hcirc ‖x‖ 0)) :
    hC φ = lateralPair hC hcirc φ + radialFunctional φ (driftRat γ (radRat hcirc)) -
      γ * ∫ x, φ x * Real.log ‖x‖ := by
  unfold lateralPair
  rw [← radialFunctional_eq_integral hc hφ, radialFunctional_drift hc γ hφ hint]
  ring

/-- Whole-plane pairing: the pairing is its lateral part plus the radial functional. -/
lemma gff_pairing_eq {hC : (ℂ → ℝ) → ℝ} {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ))
    {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) 1) φ) :
    hC φ = lateralPair hC hcirc φ + radialFunctional φ (radRat hcirc) := by
  unfold lateralPair
  rw [radialFunctional_eq_integral hc hφ]
  ring

end Identities

section Readout

/-- The common read-out on `S`: lateral values, radial functional, deterministic drift. -/
def readOut (γ : ℝ) (S : Finset Mean0Test) : (S → ℝ) × (ℚ≥0 → ℝ) → (S → ℝ) :=
  fun p i => p.1 i + radialFunctional i.1.1 p.2 - γ * ∫ x, i.1.1 x * Real.log ‖x‖

lemma measurable_readOut (γ : ℝ) (S : Finset Mean0Test) : Measurable (readOut γ S) := by
  apply Measurable.of_eval
  intro i
  exact (((measurable_pi_apply i).comp measurable_fst).add
    ((measurable_radialFunctional (measurable_test i.1.2.1)).comp measurable_snd)).sub
    measurable_const

/-- Finite-dimensional marginals determine a probability law on `Mean0Test → ℝ`. -/
lemma eq_of_finset_marginals {μ ν : Measure (Mean0Test → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ S : Finset Mean0Test, μ.map (fun g (i : S) => g i) = ν.map (fun g (i : S) => g i)) :
    μ = ν := by
  have hμ : IsProjectiveLimit μ (fun S : Finset Mean0Test => μ.map (fun g (i : S) => g i)) :=
    fun S => rfl
  have hν : IsProjectiveLimit ν (fun S : Finset Mean0Test => μ.map (fun g (i : S) => g i)) :=
    fun S => (h S).symm
  exact IsProjectiveLimit.unique hμ hν

/-- Law of the read-out of an a.s. decomposition with independent lateral and radial parts. -/
lemma law_readOut_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] (γ : ℝ) (S : Finset Mean0Test)
    {L : Ω → (S → ℝ)} {B : Ω → (ℚ≥0 → ℝ)} {F : Ω → (S → ℝ)}
    (hF : ∀ᵐ ω ∂P, F ω = readOut γ S (L ω, B ω)) (hL : AEMeasurable L P) (hB : AEMeasurable B P)
    (hind : IndepFun L B P) :
    P.map F = ((P.map L).prod (P.map B)).map (readOut γ S) := by
  have hpair : AEMeasurable (fun ω => (L ω, B ω)) P := hL.prodMk hB
  have hiff := indepFun_iff_map_prod_eq_prod_map_map hL hB
  rw [Measure.map_congr hF, ← hiff.1 hind]
  exact (AEMeasurable.map_map_of_aemeasurable (measurable_readOut γ S).aemeasurable hpair).symm

end Readout

section Laws

lemma measurable_shift (γ : ℝ) :
    Measurable (fun w : MarkovProcess.ContinuousPath ℝ => fun t : ℝ≥0 => w t + γ * (t : ℝ)) := by
  apply Measurable.of_eval
  intro t
  exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t).add measurable_const

lemma measurable_shift' (γ : ℝ) :
    Measurable (fun w : MarkovProcess.ContinuousPath ℝ => fun t : ℝ≥0 => w t - γ * (t : ℝ)) := by
  apply Measurable.of_eval
  intro t
  exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t).sub measurable_const

/-- The drift-removed radial path of a cone sample at rational times is a Brownian motion in law. -/
lemma cone_radial_BM {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) :
    P.map (fun ω => driftRat γ (radRat (hcirc ω))) =
      (MarkovProcess.brownianMotion 0).map (fun (w : MarkovProcess.ContinuousPath ℝ) (q : ℚ≥0) => w (q : ℝ≥0)) := by
  obtain ⟨ν, ⟨hν, -⟩, hmap⟩ := hcone.radial_law
  have hrad : Measurable (fun ω => radialProcess (hcirc ω)) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro t
      exact hcone.measurable_circle _ _ (Real.exp_pos _)
    · apply Measurable.of_eval
      intro t
      exact hcone.measurable_circle _ _ (Real.exp_pos _)
  have hfst : P.map (fun ω => (radialProcess (hcirc ω)).1) =
      (MarkovProcess.brownianMotion 0).map (fun w (t : ℝ≥0) => w t + γ * (t : ℝ)) := by
    have h := congrArg (Measure.map Prod.fst) hmap
    rw [Measure.map_map measurable_fst hrad] at h
    have hmass : (ν.map (fun w (s : ℝ≥0) => w s - γ * (s : ℝ))) Set.univ = 1 := by
      rw [Measure.map_apply (measurable_shift' γ) MeasurableSet.univ, Set.preimage_univ,
        measure_univ]
    unfold quantumConeRadialLaw at h
    rw [Measure.map_fst_prod, hmass, one_smul] at h
    exact h
  have hψ : Measurable (fun r : ℝ≥0 → ℝ => fun q : ℚ≥0 => r (q : ℝ≥0) - γ * (q : ℝ)) := by
    apply Measurable.of_eval
    intro q
    exact (measurable_pi_apply _).sub measurable_const
  have hdrift : (fun ω => driftRat γ (radRat (hcirc ω))) =
      (fun r : ℝ≥0 → ℝ => fun q : ℚ≥0 => r (q : ℝ≥0) - γ * (q : ℝ)) ∘
        (fun ω => (radialProcess (hcirc ω)).1) := rfl
  rw [hdrift, ← Measure.map_map hψ (hrad.fst), hfst, Measure.map_map hψ (measurable_shift γ)]
  congr 1
  funext w q
  have hq : ((q : ℝ≥0) : ℝ) = (q : ℝ) := by norm_cast
  simp [hq]

lemma gff_isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) :
    IsProbabilityMeasure P := by
  have : Nonempty GFFObservable.Admissible := ⟨⟨GFFObservable.circle 1 0, zero_lt_one⟩⟩
  exact h.isGaussianProcess.isProbabilityMeasure

/-- The radial integrals of a sample are a.e. measurable (a.e. continuity of the circle averages). -/
lemma aemeasurable_radialIntegral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ}
    (hm : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) 1) φ) :
    AEMeasurable (fun ω => ∫ x, φ x * hcirc ω ‖x‖ 0) P := by
  have h1 : Measurable (fun ω => radialFunctional φ (radRat (hcirc ω))) :=
    (measurable_radialFunctional (measurable_test hφ)).comp (measurable_radRat hm)
  refine h1.aemeasurable.congr ?_
  filter_upwards [hc] with ω hω
  exact (radialFunctional_eq_integral hω hφ)

end Laws

section Inputs

/-- Pending External input (lateral law): finite-dimensional laws of the lateral pairings of two
whole-plane GFFs agree. Provable from `hN2` and the lateral covariance formula. -/
def LateralLawFinite : Prop :=
  ∀ (Ω₁ Ω₂ : Type) [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (hC₁ : Ω₁ → (ℂ → ℝ) → ℝ) (hcirc₁ : Ω₁ → ℝ → ℂ → ℝ) (hC₂ : Ω₂ → (ℂ → ℝ) → ℝ)
    (hcirc₂ : Ω₂ → ℝ → ℂ → ℝ), IsProbabilityMeasure P₁ → IsProbabilityMeasure P₂ →
    IsWholePlaneGFF P₁ hC₁ hcirc₁ → IsWholePlaneGFF P₂ hC₂ hcirc₂ → ∀ S : Finset Mean0Test,
      P₁.map (fun ω (i : S) => lateralPair (hC₁ ω) (hcirc₁ ω) i.1.1) =
        P₂.map (fun ω (i : S) => lateralPair (hC₂ ω) (hcirc₂ ω) i.1.1)

/-- Pending External input (measurability): the lateral process of a cone sample and of a
whole-plane GFF sample is a.e. measurable as a family indexed by admissible observables. -/
def LateralProcessAEMeasurable : Prop :=
  (∀ (γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P) ∧
  (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
      AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P)

/-- Pending External input (GFF independence): the lateral and radial parts of a whole-plane GFF are
independent (the whole-plane analogue of the independence in Definition 2.1; paper l.437-438, l.442). -/
def GFFRadialLateralIndep : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IndepFun (fun ω => radialProcess (hcirc ω)) (fun ω => lateralProcess (hC ω) (hcirc ω)) P

/-- Pending External input (GFF radial path): the whole-plane radial path `q ↦ h_{e^{-q}}(0)`, `q ∈ ℚ≥0`,
is a standard Brownian motion in law (Duplantier-Sheffield). -/
def GFFRadialBrownian : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    P.map (fun ω (q : ℚ≥0) => radRat (hcirc ω) q) =
      (MarkovProcess.brownianMotion 0).map (fun (w : MarkovProcess.ContinuousPath ℝ) (q : ℚ≥0) => w (q : ℝ≥0))

/-- Pending External input (cone radial integrability): the radial pairings `∫ φ(x) h_{|x|}(0) dx` of a
quantum cone converge absolutely almost surely (implicit in Definition 2.1 and eq:gff). -/
def ConeRadialAbsIntegrable : Prop :=
  ∀ (γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
    ∀ φ : ℂ → ℝ, IsTestFunction (ball (0 : ℂ) 1) φ →
      ∀ᵐ ω ∂P, Integrable (fun x => φ x * hcirc ω ‖x‖ 0)

end Inputs

section Main

/-- `ConeMeanZeroRestrictionStep` from the pending inputs `LateralLawFinite`, `LateralProcessAEMeasurable`,
`GFFRadialLateralIndep`, `GFFRadialBrownian`, `ConeRadialAbsIntegrable`. -/
theorem coneMeanZeroRestrictionStep_of_inputs (hLat : LateralLawFinite)
    (hMeas : LateralProcessAEMeasurable) (hInd : GFFRadialLateralIndep)
    (hBM : GFFRadialBrownian) (hAbs : ConeRadialAbsIntegrable) :
    MatedCRT.ConeMeanZeroRestrictionStep := by
  intro γ _ _ Ω _ P hC hcirc hP hcone Ω' _ P' hC' hcirc' hgff
  have hP' : IsProbabilityMeasure P' := gff_isProbabilityMeasure hgff
  have hrestr : ∀ S : Finset Mean0Test,
      Measurable (fun g : Mean0Test → ℝ => fun (i : S) => g i) :=
    fun S => Measurable.of_eval fun i => measurable_pi_apply _
  have hFc : Measurable (fun ω (φ : Mean0Test) => hC ω φ.1) :=
    Measurable.of_eval fun φ => hcone.measurable_pairing _ (test_univ φ.2.1)
  have hFg : Measurable (fun ω (φ : Mean0Test) => hC' ω φ.1 - γ * ∫ x, φ.1 x * Real.log ‖x‖) :=
    Measurable.of_eval fun φ => (hgff.measurable_pairing _ (test_univ φ.2.1)).sub measurable_const
  have hProj : ∀ S : Finset Mean0Test, Measurable (fun g : GFFObservable.Admissible → ℝ =>
      fun (i : S) => g ⟨GFFObservable.pairing i.1.1, test_univ i.1.2.1⟩) :=
    fun S => Measurable.of_eval fun i => measurable_pi_apply _
  -- lateral marginals: the cone's lateral law is that of some whole-plane GFF
  have hmarg : ∀ S : Finset Mean0Test,
      P.map (fun ω (i : S) => lateralPair (hC ω) (hcirc ω) i.1.1) =
        P'.map (fun ω (i : S) => lateralPair (hC' ω) (hcirc' ω) i.1.1) := by
    intro S
    obtain ⟨Ω'', _, P'', hC'', hcirc'', hP'', hgff'', heq⟩ := hcone.lateral_law
    calc P.map (fun ω (i : S) => lateralPair (hC ω) (hcirc ω) i.1.1)
        = (P.map (fun ω => lateralProcess (hC ω) (hcirc ω))).map
            (fun g (i : S) => g ⟨GFFObservable.pairing i.1.1, test_univ i.1.2.1⟩) :=
          (AEMeasurable.map_map_of_aemeasurable (hProj S).aemeasurable
            (hMeas.1 γ Ω P hC hcirc hP hcone)).symm
      _ = (P''.map (fun ω => lateralProcess (hC'' ω) (hcirc'' ω))).map
            (fun g (i : S) => g ⟨GFFObservable.pairing i.1.1, test_univ i.1.2.1⟩) := by
          rw [heq]
      _ = P''.map (fun ω (i : S) => lateralPair (hC'' ω) (hcirc'' ω) i.1.1) :=
          AEMeasurable.map_map_of_aemeasurable (hProj S).aemeasurable
            (hMeas.2 Ω'' P'' hC'' hcirc'' hP'' hgff'')
      _ = P'.map (fun ω (i : S) => lateralPair (hC' ω) (hcirc' ω) i.1.1) :=
          hLat Ω'' Ω' P'' P' hC'' hcirc'' hC' hcirc' hP'' hP' hgff'' hgff S
  refine eq_of_finset_marginals fun S => ?_
  rw [Measure.map_map (hrestr S) hFc, Measure.map_map (hrestr S) hFg]
  show P.map (fun ω (i : S) => hC ω i.1.1) =
    P'.map (fun ω (i : S) => hC' ω i.1.1 - γ * ∫ x, i.1.1 x * Real.log ‖x‖)
  -- cone side: read-out, measurability, independence
  have hLc : AEMeasurable (fun ω (i : S) => lateralPair (hC ω) (hcirc ω) i.1.1) P := by
    apply AEMeasurable.of_eval
    intro i
    exact (hcone.measurable_pairing _ (test_univ i.1.2.1)).aemeasurable.sub
      (aemeasurable_radialIntegral hcone.measurable_circle hcone.ae_continuousOn_circle i.1.2.1)
  have hBc : Measurable (fun ω (q : ℚ≥0) => driftRat γ (radRat (hcirc ω)) q) := by
    apply Measurable.of_eval
    intro q
    exact (hcone.measurable_circle _ _ (Real.exp_pos _)).sub measurable_const
  have hindC : IndepFun (fun ω (i : S) => lateralPair (hC ω) (hcirc ω) i.1.1)
      (fun ω (q : ℚ≥0) => driftRat γ (radRat (hcirc ω)) q) P := by
    have hg : Measurable (fun r : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
        fun q : ℚ≥0 => r.1 (q : ℝ≥0) - γ * (q : ℝ)) := by
      apply Measurable.of_eval
      intro q
      exact ((measurable_pi_apply _).comp measurable_fst).sub measurable_const
    exact (hcone.indep.comp hg (hProj S)).symm
  have hFc_ae : ∀ᵐ ω ∂P, (fun ω (i : S) => hC ω i.1.1) ω =
      readOut γ S ((fun ω (i : S) => lateralPair (hC ω) (hcirc ω) i.1.1) ω,
        (fun ω (q : ℚ≥0) => driftRat γ (radRat (hcirc ω)) q) ω) := by
    have hall : ∀ᵐ ω ∂P, ∀ i ∈ S, Integrable (fun x => i.1 x * hcirc ω ‖x‖ 0) := by
      refine (Filter.eventually_all_finset S).2 (fun i _ => ?_)
      exact hAbs γ Ω P hC hcirc hP hcone i.1 i.2.1
    filter_upwards [hcone.ae_continuousOn_circle, hall] with ω hωc hωi
    funext i
    dsimp only [readOut]
    exact cone_pairing_eq hωc γ i.1.2.1 (hωi i.1 i.2)
  -- GFF side
  have hLg : AEMeasurable (fun ω (i : S) => lateralPair (hC' ω) (hcirc' ω) i.1.1) P' := by
    apply AEMeasurable.of_eval
    intro i
    exact (hgff.measurable_pairing _ (test_univ i.1.2.1)).aemeasurable.sub
      (aemeasurable_radialIntegral hgff.measurable_circle hgff.ae_continuousOn_circle i.1.2.1)
  have hRg : Measurable (fun ω (q : ℚ≥0) => radRat (hcirc' ω) q) :=
    measurable_radRat hgff.measurable_circle
  have hindG : IndepFun (fun ω (i : S) => lateralPair (hC' ω) (hcirc' ω) i.1.1)
      (fun ω (q : ℚ≥0) => radRat (hcirc' ω) q) P' := by
    have hg : Measurable (fun r : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => fun q : ℚ≥0 => r.1 (q : ℝ≥0)) := by
      apply Measurable.of_eval
      intro q
      exact (measurable_pi_apply _).comp measurable_fst
    exact ((hInd Ω' P' hC' hcirc' hP' hgff).comp hg (hProj S)).symm
  have hFg_ae : ∀ᵐ ω ∂P', (fun ω (i : S) => hC' ω i.1.1 - γ * ∫ x, i.1.1 x * Real.log ‖x‖) ω =
      readOut γ S ((fun ω (i : S) => lateralPair (hC' ω) (hcirc' ω) i.1.1) ω,
        (fun ω (q : ℚ≥0) => radRat (hcirc' ω) q) ω) := by
    filter_upwards [hgff.ae_continuousOn_circle] with ω hωc
    funext i
    exact congrArg (fun x => x - γ * ∫ x_1, i.1.1 x_1 * Real.log ‖x_1‖)
      (gff_pairing_eq (hC := hC' ω) (hcirc := hcirc' ω) hωc i.1.2.1)
  -- assemble the laws
  rw [law_readOut_eq γ S hFc_ae hLc hBc.aemeasurable hindC,
    law_readOut_eq γ S hFg_ae hLg hRg.aemeasurable hindG, hmarg S,
    cone_radial_BM hcone, hBM Ω' P' hC' hcirc' hP' hgff]

end Main

end MatedCRT.ConeMeanZeroRestriction
