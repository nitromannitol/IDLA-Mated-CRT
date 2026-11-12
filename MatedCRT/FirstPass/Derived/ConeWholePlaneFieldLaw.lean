import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestrictionFinal
import MatedCRT.Proofs.Sec4.Prop42Closure.ConeWholePlaneSteps
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field

/-!
# The quantum cone and the whole-plane field agree in law on the unit disk (`ConeWholePlaneFieldLawStep`)

Discharges the Step Prop `ConeWholePlaneFieldLawStep` (`Proofs/Sec4/Prop42Closure/ConeWholePlaneSteps.lean:65`),
IDLA eq. (2.4): `h|_{B_1} =_d (h^ℂ - γ log|·|)|_{B_1}` as processes of pairings with test functions supported in
`B_1` and of circle averages of circles in `B_1`.

Route (Duplantier-Sheffield 2011, Prop. 3.1 and eq. (3.2)): both fields are the same measurable read-out of an
independent pair (lateral part, standard Brownian motion read at rational times). For the cone the Brownian
motion is the drift-removed radial path `q ↦ h_{e^{-q}}(0) - γ q`; for the whole-plane field it is the radial path
itself. The read-out is the lateral value plus the radial functional (`∫ φ(x) f(-log|x|) dx` for pairings, the
circle average of `x ↦ f(-log|x|)` for circle averages) minus the deterministic drift `γ ∫ φ log|·|`
(resp. `γ` times the circle average of `log|·|`). The circle average of the Brownian path along a circle is
a.s. circle integrable by Fubini and `E|B_t| ≤ (1 + t)/2`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped NNReal NNRat ENNReal

noncomputable section

namespace MatedCRT.ConeWholePlaneFieldLaw

open MatedCRT.ConeMeanZeroRestriction

/-- Standard Brownian motion read at the rational times `ℚ≥0`. -/
abbrev bmRat : Measure (ℚ≥0 → ℝ) :=
  (brownianMotion 0).map (fun (w : ContinuousPath ℝ) (q : ℚ≥0) => w (q : ℝ≥0))

lemma measurable_restrictRat :
    Measurable (fun (w : ContinuousPath ℝ) (q : ℚ≥0) => w (q : ℝ≥0)) :=
  Measurable.of_eval fun _ => ContinuousPath.measurable_coordinateProcess (alpha := ℝ) _

section CircleIntegrability

/-- A continuous path read along rational approximations of `radTime x` is its value at `radTime x`. -/
lemma limVal_restrict (w : ContinuousPath ℝ) (x : ℂ) :
    limVal (fun q : ℚ≥0 => w (q : ℝ≥0)) x = w (radTime x).toNNReal := by
  apply limVal_eq_of_tendsto
  have h1 : Tendsto (fun n : ℕ => ((ratApprox n x : ℚ≥0) : ℝ≥0)) atTop (𝓝 (radTime x).toNNReal) := by
    rw [← NNReal.tendsto_coe, Real.coe_toNNReal _ (radTime_nonneg x)]
    refine (tendsto_ratApprox x).congr fun n => ?_
    norm_cast
  exact (w.continuous.tendsto _).comp h1

lemma lintegral_enorm_limVal_le (x : ℂ) :
    ∫⁻ f, ‖limVal f x‖ₑ ∂bmRat ≤ ENNReal.ofReal ((1 + radTime x) / 2) := by
  have hf : Measurable (fun f : ℚ≥0 → ℝ => ‖limVal f x‖ₑ) :=
    (measurable_limVal_pair.comp (measurable_id.prodMk measurable_const)).enorm
  rw [lintegral_map hf measurable_restrictRat]
  simp_rw [limVal_restrict]
  have := lintegral_enorm_brownian_add_le 0 (radTime x).toNNReal
  simpa [Real.coe_toNNReal _ (radTime_nonneg x)] using this

lemma radTime_le_abs_log (x : ℂ) : radTime x ≤ |Real.log ‖x‖| := by
  unfold radTime
  refine max_le ?_ (abs_nonneg _)
  rw [← abs_neg]
  exact le_abs_self _

lemma measurable_limVal_circle (z : ℂ) (r : ℝ) :
    Measurable (fun p : (ℚ≥0 → ℝ) × ℝ => limVal p.1 (circleMap z r p.2)) := by
  have h2 : Measurable (fun θ : ℝ => circleMap z r θ) := (continuous_circleMap z r).measurable
  have h1 : Measurable (fun p : (ℚ≥0 → ℝ) × ℝ => ((p.1, circleMap z r p.2) : (ℚ≥0 → ℝ) × ℂ)) :=
    measurable_fst.prodMk (h2.comp measurable_snd)
  have h3 := (measurable_limVal_pair).comp h1
  exact h3

lemma lintegral_circle_limVal_ne_top (z : ℂ) (r : ℝ) :
    ∫⁻ f, (∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖limVal f (circleMap z r θ)‖ₑ) ∂bmRat ≠ ∞ := by
  have hmeas : Measurable (fun p : (ℚ≥0 → ℝ) × ℝ => ‖limVal p.1 (circleMap z r p.2)‖ₑ) :=
    (measurable_limVal_circle z r).enorm
  have hint : Integrable (fun θ : ℝ => 1 + |Real.log ‖circleMap z r θ‖|)
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (integrable_const (1 : ℝ)).add (integrable_abs_log_circleMap z r)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine ne_of_lt (lt_of_le_of_lt ?_ hint.lintegral_lt_top)
  refine lintegral_mono fun θ => ?_
  refine (lintegral_enorm_limVal_le _).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 := radTime_le_abs_log (circleMap z r θ)
  have h0 := abs_nonneg (Real.log ‖circleMap z r θ‖)
  linarith

/-- Almost every Brownian path (read at rationals) is integrable along every circle. -/
lemma ae_circleIntegrable_limVal (z : ℂ) (r : ℝ) :
    ∀ᵐ f ∂bmRat, CircleIntegrable (fun x => limVal f x) z r := by
  have hm2 : Measurable (fun f : ℚ≥0 → ℝ =>
      ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖limVal f (circleMap z r θ)‖ₑ) :=
    (measurable_limVal_circle z r).enorm.lintegral_prod_right'
  filter_upwards [ae_lt_top hm2 (lintegral_circle_limVal_ne_top z r)] with f hf
  have hmf : Measurable (fun θ : ℝ => limVal f (circleMap z r θ)) := by
    have h3 := (measurable_limVal_circle z r).comp
      (measurable_const.prodMk measurable_id : Measurable (fun θ : ℝ => ((f, θ) : (ℚ≥0 → ℝ) × ℝ)))
    exact h3
  have hI : IntegrableOn (fun θ : ℝ => limVal f (circleMap z r θ)) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    ⟨hmf.aestronglyMeasurable, by rw [HasFiniteIntegral]; exact hf⟩
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])).2 hI

/-- Transfer along a map with Brownian law. -/
lemma ae_circleIntegrable_of_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → ℚ≥0 → ℝ}
    (hB : AEMeasurable B P) (hlaw : P.map B = bmRat) (z : ℂ) (r : ℝ) :
    ∀ᵐ ω ∂P, CircleIntegrable (fun x => limVal (B ω) x) z r := by
  refine ae_of_ae_map (p := fun f => CircleIntegrable (fun x => limVal f x) z r) hB ?_
  rw [hlaw]
  exact ae_circleIntegrable_limVal z r

end CircleIntegrability

section CircleIdentities

lemma radTime_eq_neg_log {x : ℂ} (hx : ‖x‖ < 1) : radTime x = -Real.log ‖x‖ := by
  unfold radTime
  by_cases h0 : x = 0
  · simp [h0]
  · have : Real.log ‖x‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hx.le
    exact max_eq_left (by linarith)

lemma exp_neg_radTime {x : ℂ} (hx : ‖x‖ < 1) (h0 : x ≠ 0) : Real.exp (-(radTime x)) = ‖x‖ := by
  rw [radTime_eq_neg_log hx, neg_neg, Real.exp_log (norm_pos_iff.2 h0)]

/-- The circle average of two functions which agree off the origin on a circle agree. -/
lemma circleAverage_congr_ne_zero {f g : ℂ → ℝ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ x ∈ sphere z r, x ≠ 0 → f x = g x) :
    Real.circleAverage f z r = Real.circleAverage g z r := by
  unfold Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hne := circleMap_ne_zero_ae (z := z) hr
  rw [uIoc_of_le (by positivity)]
  filter_upwards [ae_restrict_iff' measurableSet_Ioc |>.1 hne] with θ hθ hmem
  exact h _ (circleMap_mem_sphere z hr.le θ) (hθ hmem)

lemma circleIntegrable_log_norm (z : ℂ) (r : ℝ) :
    CircleIntegrable (fun x : ℂ => Real.log ‖x‖) z r := by
  simpa using circleIntegrable_log_norm_sub_const (a := (0 : ℂ)) (c := z) r

/-- Circle average of the radial part of a cone sample, in terms of the drift-removed rational path. -/
lemma circleAverage_cone {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (γ : ℝ) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall z r ⊆ ball 0 1)
    (hB : CircleIntegrable (fun x => limVal (driftRat γ (radRat hcirc)) x) z r) :
    Real.circleAverage (fun x => hcirc ‖x‖ 0) z r =
      Real.circleAverage (fun x => limVal (driftRat γ (radRat hcirc)) x) z r -
        γ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r := by
  have hlog := circleIntegrable_log_norm z r
  have hpt : ∀ x ∈ sphere z r, x ≠ 0 →
      hcirc ‖x‖ 0 = limVal (driftRat γ (radRat hcirc)) x - γ * Real.log ‖x‖ := by
    intro x hx hx0
    have hx1 : ‖x‖ < 1 := by
      have := hsub (sphere_subset_closedBall hx)
      simpa using this
    rw [limVal_driftRat hc γ x, limVal_radRat hc x, exp_neg_radTime hx1 hx0, radTime_eq_neg_log hx1]
    ring
  have hlog' : CircleIntegrable (fun x : ℂ => γ * Real.log ‖x‖) z r := by
    exact hlog.const_smul (a := γ)
  have hsm : Real.circleAverage (fun x : ℂ => γ * Real.log ‖x‖) z r =
      γ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r := by
    simpa [smul_eq_mul] using Real.circleAverage_fun_smul (a := γ) (f := fun x : ℂ => Real.log ‖x‖) (c := z) (R := r)
  rw [circleAverage_congr_ne_zero hr hpt, Real.circleAverage_fun_sub hB hlog', hsm]

/-- Circle average of the radial part of a whole-plane sample, in terms of its rational path. -/
lemma circleAverage_plane {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall z r ⊆ ball 0 1) :
    Real.circleAverage (fun x => hcirc ‖x‖ 0) z r =
      Real.circleAverage (fun x => limVal (radRat hcirc) x) z r := by
  refine circleAverage_congr_ne_zero hr fun x hx hx0 => ?_
  have hx1 : ‖x‖ < 1 := by
    have := hsub (sphere_subset_closedBall hx)
    simpa using this
  rw [limVal_radRat hc x, exp_neg_radTime hx1 hx0]

end CircleIdentities

section Readout

/-- The index set of the compared observables: pairings and circle averages of the restriction to `B_1`. -/
abbrev Idx : Type := TestB1 ⊕ CircleB1

/-- An index as an admissible observable of the whole-plane model. -/
def toAdm : Idx → GFFObservable.Admissible
  | Sum.inl φ => ⟨GFFObservable.pairing φ.1, test_univ φ.2⟩
  | Sum.inr c => ⟨GFFObservable.circle c.1.1 c.1.2, c.2.1⟩

/-- The observables of the cone field restricted to `B_1`. -/
def obsCone {Ω : Type} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) : Idx → ℝ :=
  Sum.elim (fun φ => hC ω φ.1) (fun c => hcirc ω c.1.1 c.1.2)

/-- The observables of `h^ℂ - γ log|·|` restricted to `B_1`. -/
def obsPlane {Ω : Type} (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) : Idx → ℝ :=
  Sum.elim (fun φ => fieldPairing γ (hC ω) φ.1)
    (fun c => fieldCircleAverage γ (hcirc ω) c.1.1 c.1.2)

/-- The lateral value of an observable. -/
def latObs (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) : Idx → ℝ :=
  fun i => lateralProcess hC hcirc (toAdm i)

/-- The radial part of the read-out: the radial functional of a rational-time path minus the deterministic drift. -/
def radOf (γ : ℝ) (f : ℚ≥0 → ℝ) : Idx → ℝ :=
  Sum.elim (fun φ => radialFunctional φ.1 f - γ * ∫ x, φ.1 x * Real.log ‖x‖)
    (fun c => Real.circleAverage (fun x => limVal f x) c.1.2 c.1.1 -
      γ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) c.1.2 c.1.1)

/-- The common read-out on a finite set of observables. -/
def readOut (γ : ℝ) (S : Finset Idx) : (S → ℝ) × (ℚ≥0 → ℝ) → (S → ℝ) :=
  fun p i => p.1 i + radOf γ p.2 i.1

lemma measurable_circleAverage_limVal (z : ℂ) (r : ℝ) :
    Measurable (fun f : ℚ≥0 → ℝ => Real.circleAverage (fun x => limVal f x) z r) := by
  unfold Real.circleAverage
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by linarith [Real.pi_pos])]
  have hf : StronglyMeasurable (fun p : (ℚ≥0 → ℝ) × ℝ => limVal p.1 (circleMap z r p.2)) :=
    (measurable_limVal_circle z r).stronglyMeasurable
  exact (hf.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Ioc 0 (2 * Real.pi)))).measurable.const_smul ((2 * Real.pi)⁻¹ : ℝ)

lemma measurable_radOf (γ : ℝ) (j : Idx) : Measurable (fun f : ℚ≥0 → ℝ => radOf γ f j) := by
  rcases j with φ | c
  · exact (measurable_radialFunctional (measurable_test φ.2)).sub measurable_const
  · exact (measurable_circleAverage_limVal _ _).sub measurable_const

lemma measurable_readOut (γ : ℝ) (S : Finset Idx) : Measurable (readOut γ S) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp measurable_fst).add
    ((measurable_radOf γ i.1).comp measurable_snd)

/-- Finite-dimensional marginals determine a finite law on `ι → ℝ`. -/
lemma eq_of_finset_marginals {ι : Type} {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ S : Finset ι, μ.map (fun g (i : S) => g i) = ν.map (fun g (i : S) => g i)) :
    μ = ν := by
  have hμ : IsProjectiveLimit μ (fun S : Finset ι => μ.map (fun g (i : S) => g i)) :=
    fun S => rfl
  have hν : IsProjectiveLimit ν (fun S : Finset ι => μ.map (fun g (i : S) => g i)) :=
    fun S => (h S).symm
  exact IsProjectiveLimit.unique hμ hν

/-- Law of the read-out of an a.s. decomposition with independent lateral and radial parts. -/
lemma law_readOut_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] (γ : ℝ)
    (S : Finset Idx) {L : Ω → (S → ℝ)} {B : Ω → (ℚ≥0 → ℝ)} {F : Ω → (S → ℝ)}
    (hF : ∀ᵐ ω ∂P, F ω = readOut γ S (L ω, B ω)) (hL : AEMeasurable L P) (hB : AEMeasurable B P)
    (hind : IndepFun L B P) :
    P.map F = ((P.map L).prod (P.map B)).map (readOut γ S) := by
  have hpair : AEMeasurable (fun ω => (L ω, B ω)) P := hL.prodMk hB
  have hiff := indepFun_iff_map_prod_eq_prod_map_map hL hB
  rw [Measure.map_congr hF, ← hiff.1 hind]
  exact (AEMeasurable.map_map_of_aemeasurable (measurable_readOut γ S).aemeasurable hpair).symm

end Readout

section Main

lemma measurable_proj (S : Finset Idx) :
    Measurable (fun g : GFFObservable.Admissible → ℝ => fun i : S => g (toAdm i.1)) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- **`ConeWholePlaneFieldLawStep`.** The pairings with test functions and the circle averages in `B_1` of the
quantum cone have the law of those of `h^ℂ - γ log|·|` (IDLA eq. (2.4)). -/
theorem coneWholePlaneFieldLawStep_holds : MatedCRT.ConeWholePlaneFieldLawStep := by
  intro γ _ _ Ω _ P hC hcirc μ hcone Ω' _ P' hC' hcirc' hP' hgff
  obtain ⟨hP, hQ, -⟩ := hcone
  -- measurability of the observables
  have hOc : Measurable (obsCone hC hcirc) := by
    refine Measurable.of_eval fun i => ?_
    rcases i with φ | c
    · exact hQ.measurable_pairing _ (test_univ φ.2)
    · exact hQ.measurable_circle _ _ c.2.1
  have hOg : Measurable (obsPlane γ hC' hcirc') := by
    refine Measurable.of_eval fun i => ?_
    rcases i with φ | c
    · exact (hgff.measurable_pairing _ (test_univ φ.2)).sub measurable_const
    · exact (hgff.measurable_circle _ _ c.2.1).sub measurable_const
  -- ingredients
  have hLatC : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    lateralProcessAEMeasurable_holds.1 γ Ω P hC hcirc hP hQ
  have hLatG : AEMeasurable (fun ω => lateralProcess (hC' ω) (hcirc' ω)) P' :=
    lateralProcessAEMeasurable_holds.2 Ω' P' hC' hcirc' hP' hgff
  have hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)) := by
    obtain ⟨Ω'', _, P'', hC'', hcirc'', hP'', hgff'', heq⟩ := hQ.lateral_law
    exact heq.trans (MatedCRT.Sec1.IsWholePlaneGFF.lateral_law_eq hgff'' hgff)
  have hBc : Measurable (fun ω => driftRat γ (radRat (hcirc ω))) := by
    refine Measurable.of_eval fun q => ?_
    exact (hQ.measurable_circle _ _ (Real.exp_pos _)).sub measurable_const
  have hBg : Measurable (fun ω => radRat (hcirc' ω)) := measurable_radRat hgff.measurable_circle
  have hBlawC : P.map (fun ω => driftRat γ (radRat (hcirc ω))) = bmRat := by
    have := hP
    exact cone_radial_BM hQ
  have hBlawG : P'.map (fun ω => radRat (hcirc' ω)) = bmRat := gffRadialBrownian_holds Ω' P' hC' hcirc' hP' hgff
  -- almost sure decompositions
  have hallC : ∀ i : Idx, ∀ᵐ ω ∂P, obsCone hC hcirc ω i =
      latObs (hC ω) (hcirc ω) i + radOf γ (driftRat γ (radRat (hcirc ω))) i := by
    intro i
    rcases i with φ | c
    · filter_upwards [hQ.ae_continuousOn_circle,
        coneRadialAbsIntegrable_holds γ Ω P hC hcirc hP hQ φ.1 φ.2] with ω hωc hωi
      have h := cone_pairing_eq (hC := hC ω) hωc γ φ.2 hωi
      unfold lateralPair at h
      simp only [obsCone, latObs, radOf, toAdm, lateralProcess, lateralEval, Sum.elim_inl]
      linarith
    · filter_upwards [hQ.ae_continuousOn_circle,
        ae_circleIntegrable_of_law hBc.aemeasurable hBlawC c.1.2 c.1.1] with ω hωc hωB
      have h := circleAverage_cone hωc γ c.2.1 c.2.2 hωB
      simp only [obsCone, latObs, radOf, toAdm, lateralProcess, lateralEval, Sum.elim_inr]
      linarith
  have hallG : ∀ i : Idx, ∀ᵐ ω ∂P', obsPlane γ hC' hcirc' ω i =
      latObs (hC' ω) (hcirc' ω) i + radOf γ (radRat (hcirc' ω)) i := by
    intro i
    rcases i with φ | c
    · filter_upwards [hgff.ae_continuousOn_circle] with ω hωc
      have h := gff_pairing_eq (hC := hC' ω) (hcirc := hcirc' ω) hωc φ.2
      unfold lateralPair at h
      simp only [obsPlane, fieldPairing, latObs, radOf, toAdm, lateralProcess, lateralEval, Sum.elim_inl]
      linarith
    · filter_upwards [hgff.ae_continuousOn_circle] with ω hωc
      have h := circleAverage_plane hωc c.2.1 c.2.2
      simp only [obsPlane, fieldCircleAverage, latObs, radOf, toAdm, lateralProcess, lateralEval, Sum.elim_inr]
      linarith
  -- finite-dimensional marginals
  have key : P.map (obsCone hC hcirc) = P'.map (obsPlane γ hC' hcirc') := by
    have := hP
    have := hP'
    refine eq_of_finset_marginals fun S => ?_
    have hrestr : Measurable (fun g : Idx → ℝ => fun i : S => g i) :=
      Measurable.of_eval fun _ => measurable_pi_apply _
    rw [Measure.map_map hrestr hOc, Measure.map_map hrestr hOg]
    have hLc : AEMeasurable (fun ω (i : S) => latObs (hC ω) (hcirc ω) i.1) P :=
      (measurable_proj S).comp_aemeasurable hLatC
    have hLg : AEMeasurable (fun ω (i : S) => latObs (hC' ω) (hcirc' ω) i.1) P' :=
      (measurable_proj S).comp_aemeasurable hLatG
    have hindC : IndepFun (fun ω (i : S) => latObs (hC ω) (hcirc ω) i.1)
        (fun ω => driftRat γ (radRat (hcirc ω))) P := by
      have hg : Measurable (fun r : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
          fun q : ℚ≥0 => r.1 (q : ℝ≥0) - γ * (q : ℝ)) :=
        Measurable.of_eval fun q => ((measurable_pi_apply _).comp measurable_fst).sub measurable_const
      exact (hQ.indep.comp hg (measurable_proj S)).symm
    have hindG : IndepFun (fun ω (i : S) => latObs (hC' ω) (hcirc' ω) i.1)
        (fun ω => radRat (hcirc' ω)) P' := by
      have hg : Measurable (fun r : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => fun q : ℚ≥0 => r.1 (q : ℝ≥0)) :=
        Measurable.of_eval fun q => (measurable_pi_apply _).comp measurable_fst
      exact ((gffRadialLateralIndep_holds Ω' P' hC' hcirc' hP' hgff).comp hg (measurable_proj S)).symm
    have hFc : ∀ᵐ ω ∂P, (fun i : S => obsCone hC hcirc ω i.1) =
        readOut γ S ((fun i : S => latObs (hC ω) (hcirc ω) i.1), driftRat γ (radRat (hcirc ω))) := by
      filter_upwards [(Filter.eventually_all_finset S).2 fun i _ => hallC i] with ω hω
      funext i
      exact hω i.1 i.2
    have hFg : ∀ᵐ ω ∂P', (fun i : S => obsPlane γ hC' hcirc' ω i.1) =
        readOut γ S ((fun i : S => latObs (hC' ω) (hcirc' ω) i.1), radRat (hcirc' ω)) := by
      filter_upwards [(Filter.eventually_all_finset S).2 fun i _ => hallG i] with ω hω
      funext i
      exact hω i.1 i.2
    have hlatS : P.map (fun ω (i : S) => latObs (hC ω) (hcirc ω) i.1) =
        P'.map (fun ω (i : S) => latObs (hC' ω) (hcirc' ω) i.1) := by
      have e1 := AEMeasurable.map_map_of_aemeasurable (measurable_proj S).aemeasurable hLatC
      have e2 := AEMeasurable.map_map_of_aemeasurable (measurable_proj S).aemeasurable hLatG
      calc P.map (fun ω (i : S) => latObs (hC ω) (hcirc ω) i.1)
          = (P.map (fun ω => lateralProcess (hC ω) (hcirc ω))).map (fun g i => g (toAdm i.1)) := e1.symm
        _ = (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω))).map (fun g i => g (toAdm i.1)) := by
            rw [hlat]
        _ = P'.map (fun ω (i : S) => latObs (hC' ω) (hcirc' ω) i.1) := e2
    show P.map (fun ω (i : S) => obsCone hC hcirc ω i.1) = P'.map (fun ω (i : S) => obsPlane γ hC' hcirc' ω i.1)
    rw [law_readOut_eq γ S hFc hLc hBc.aemeasurable hindC,
      law_readOut_eq γ S hFg hLg hBg.aemeasurable hindG, hlatS, hBlawC, hBlawG]
  -- transport to the product of the two function spaces
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Idx => ℝ)
  have hcE : coneFieldOnB1 hC hcirc = fun ω => e (obsCone hC hcirc ω) := rfl
  have hgE : wholePlaneFieldOnB1 γ hC' hcirc' = fun ω => e (obsPlane γ hC' hcirc' ω) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hcE]; exact (e.measurable.comp hOc).aemeasurable
  · rw [hgE]; exact (e.measurable.comp hOg).aemeasurable
  · rw [hcE, hgE]
    have h1 : (fun ω => e (obsCone hC hcirc ω)) = e ∘ obsCone hC hcirc := rfl
    have h2 : (fun ω => e (obsPlane γ hC' hcirc' ω)) = e ∘ obsPlane γ hC' hcirc' := rfl
    rw [h1, h2, ← Measure.map_map e.measurable hOc, ← Measure.map_map e.measurable hOg, key]

end Main

end MatedCRT.ConeWholePlaneFieldLaw
