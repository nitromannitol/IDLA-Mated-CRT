import MatedCRT.Proofs.Sec1.EnvironmentScaling.FieldAssembly
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Radial law of the represented cone

The valid environment contains a distribution-valued cone from Leonardo
Bonanno's post-last-zero construction.  Its recovered circles have the
weak-limit radial law already required by the environment.  This does not
identify those circles with the explicit radial formula: that is a separate
circle-average calculation, and no equivalence of conditioning conventions is
assumed here.  Compare env-steps.tex:217–250.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
open HarmonicBalls

namespace MatedCRT.Sec1

/-- A quotient of functions vanishing at the origin has the quotient of
their nonzero first derivatives as its right-hand limit. -/
theorem tendsto_div_of_hasDerivAt_zero {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hb : b ≠ 0) :
    Tendsto (fun x => f x / g x) (𝓝[>] 0) (𝓝 (a / b)) := by
  have hf' := hf.tendsto_slope_zero_right
  have hg' := hg.tendsto_slope_zero_right
  simp only [zero_add, hf0, hg0, sub_zero, smul_eq_mul] at hf' hg'
  have h := hf'.div hg' hb
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := ne_of_gt hx
  dsimp
  field_simp

/-- The analytic entrance-density limit for the killed drifted Brownian
transition formula.  The hypothesis on `g` is the derivative identity for
the centered Gaussian density of variance `t`. -/
theorem tendsto_conditioned_entrance_density
    (g : ℝ → ℝ) (d t y : ℝ) (hd : d ≠ 0) (ht : t ≠ 0)
    (hg : HasDerivAt g (-(y / t) * g y) y) :
    Tendsto (fun x =>
      (Real.exp (d * (y - x) - d ^ 2 * t / 2) * (g (y - x) - g (y + x))) *
        (1 - Real.exp (-2 * d * y)) / (1 - Real.exp (-2 * d * x)))
      (𝓝[>] 0)
      (𝓝 ((y / (d * t)) * g y * Real.exp (d * y - d ^ 2 * t / 2) *
        (1 - Real.exp (-2 * d * y)))) := by
  have hminus : HasDerivAt (fun x => g (y - x)) (y / t * g y) 0 := by
    have hg' : HasDerivAt g (-(y / t) * g y) (y - 0) := by simpa using hg
    convert hg'.comp 0 ((hasDerivAt_const 0 y).sub (hasDerivAt_id 0)) using 1
    all_goals first | rfl | simp
  have hplus : HasDerivAt (fun x => g (y + x)) (-(y / t) * g y) 0 := by
    have hg' : HasDerivAt g (-(y / t) * g y) (y + 0) := by simpa using hg
    convert hg'.comp 0 ((hasDerivAt_const 0 y).add (hasDerivAt_id 0)) using 1
    all_goals first | rfl | simp
  have hnum : HasDerivAt (fun x => g (y - x) - g (y + x))
      (2 * (y / t * g y)) 0 := by
    convert hminus.sub hplus using 1; ring
  have hden : HasDerivAt (fun x => 1 - Real.exp (-2 * d * x)) (2 * d) 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).sub
      (((hasDerivAt_const 0 (-2 * d)).mul (hasDerivAt_id 0)).exp) using 1 <;>
      simp [← Pi.sub_def]
  have hq := tendsto_div_of_hasDerivAt_zero hnum hden (by simp) (by simp) (by
    exact mul_ne_zero (by norm_num) hd)
  have he : Tendsto (fun x : ℝ => Real.exp (d * (y - x) - d ^ 2 * t / 2))
      (𝓝[>] 0) (𝓝 (Real.exp (d * y - d ^ 2 * t / 2))) := by
    have hc : Continuous (fun x : ℝ => Real.exp (d * (y - x) - d ^ 2 * t / 2)) := by
      fun_prop
    simpa using (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto _ (𝓝[>] (0 : ℝ)) _)
  have h := (he.mul hq).mul_const (1 - Real.exp (-2 * d * y))
  convert h using 1
  · ext x
    ring
  · congr 1
    field_simp

/-- Mathlib's centered Gaussian density has the logarithmic derivative
needed for the entrance-law calculation. -/
theorem hasDerivAt_gaussianPDFReal_zero (t : ℝ≥0) (ht : t ≠ 0) (y : ℝ) :
    HasDerivAt (gaussianPDFReal 0 t) (-(y / (t : ℝ)) * gaussianPDFReal 0 t y) y := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have h := ((((hasDerivAt_id y).pow 2).neg.div_const (2 * (t : ℝ))).exp).const_mul
    (Real.sqrt (2 * Real.pi * t))⁻¹
  convert h using 1
  · ext x
    simp [gaussianPDFReal]
  · simp only [gaussianPDFReal, sub_zero, Pi.neg_apply, Pi.pow_apply, id_eq]
    field_simp
    ring

/-- The entrance density in the canonical-cone calculation is the
right-hand limit of the displayed conditioned transition density.  This is
an analytic limit; it does not assert that either expression is a law. -/
theorem tendsto_gaussian_conditioned_entrance_density
    (d y : ℝ) (t : ℝ≥0) (hd : d ≠ 0) (ht : t ≠ 0) :
    Tendsto (fun x =>
      (Real.exp (d * (y - x) - d ^ 2 * (t : ℝ) / 2) *
        (gaussianPDFReal 0 t (y - x) - gaussianPDFReal 0 t (y + x))) *
        (1 - Real.exp (-2 * d * y)) / (1 - Real.exp (-2 * d * x)))
      (𝓝[>] 0)
      (𝓝 ((y / (d * (t : ℝ))) * gaussianPDFReal 0 t y *
        Real.exp (d * y - d ^ 2 * (t : ℝ) / 2) * (1 - Real.exp (-2 * d * y)))) :=
  tendsto_conditioned_entrance_density (gaussianPDFReal 0 t) d t y hd
    (by exact_mod_cast ht) (hasDerivAt_gaussianPDFReal_zero t ht y)


/-- The explicit cone representative from the mating-of-trees witness has
both the field law and the weak-limit radial law of the valid environment.
The radial process here is recovered from the distribution; equality with the
post-last-zero formula is a separate assertion. -/
theorem exists_reference_cone_field_and_recovered_radial_law
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hHm : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∃ (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ)
      (ν : Measure (MarkovProcess.ContinuousPath ℝ)),
      LQGMetric.IsWholePlaneGFF X S.P ∧ IsBrownianReal B S.P ∧ IsBrownianReal B' S.P ∧
      IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) S.P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) S.P ∧
      IsBMConditionedPositive (lqgQ γ - γ) ν ∧
      let H' : Ω → LQGMetric.DistC := fun ω =>
        MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))
      (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H' ω φ) ∧
      AEMeasurable H' S.P ∧ S.P.map H = S.P.map H' ∧
      S.P.map (fun ω => radialProcess (distributionCircleVersion (H' ω))) =
        quantumConeRadialLaw γ ν := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hc, ha⟩ := hS.matingOfTrees
  let H' : Ω → LQGMetric.DistC := fun ω =>
    MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))
  have href : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H' ω φ := by
    filter_upwards [ha] with ω hω
    exact hω.2
  have heq : H =ᵐ[S.P] H' := by
    filter_upwards [hrep, href] with ω hω hω'
    ext φ
    exact (hω φ).symm.trans (hω' φ)
  have hcircle := ae_distributionCircleVersion_eq hS href
  have hradial : (fun ω => radialProcess (distributionCircleVersion (H' ω))) =ᵐ[S.P]
      (fun ω => radialProcess (S.hcirc ω)) := by
    filter_upwards [hcircle] with ω hω
    apply Prod.ext <;> funext t <;>
      exact hω _ (Real.exp_pos _) 0
  obtain ⟨ν, hν, hνlaw⟩ := hS.isQuantumCone.radial_law
  refine ⟨X, B, B', ν, hc.gff, hc.bm_B, hc.bm_B', hc.indep_cone.1,
    hc.indep_cone.2, hν, href, hHm.aemeasurable.congr heq, Measure.map_congr heq, ?_⟩
  rw [Measure.map_congr hradial, hνlaw]

/-- Adding a positive linear drift to a sublinear path makes it tend to
positive infinity. -/
theorem tendsto_add_pos_drift_of_sublinear (f : ℝ → ℝ) (d : ℝ) (hd : 0 < d)
    (hf : Tendsto (fun t => f t / t) atTop (𝓝 0)) :
    Tendsto (fun t => f t + d * t) atTop atTop := by
  have hsmall : ∀ᶠ t : ℝ in atTop, -(d / 2) < f t / t :=
    hf.eventually (lt_mem_nhds (by linarith))
  have hlower : (fun t : ℝ => (d / 2) * t) ≤ᶠ[atTop] fun t => f t + d * t := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    have htpos : 0 < t := by linarith
    have hbound := (lt_div_iff₀ htpos).mp ht
    nlinarith
  exact tendsto_atTop_mono' atTop hlower
    ((tendsto_const_mul_atTop_of_pos (by linarith : 0 < d / 2)).2 tendsto_id)

/-- A continuous path starting at zero and tending to positive infinity
attains zero at its last zero and is strictly positive thereafter. -/
theorem lastZeroR_eq_zero_and_pos {c : ℝ → ℝ} (hc : Continuous c) (hc0 : c 0 = 0)
    (htend : Tendsto c atTop atTop) :
    let ℓ := MatedCRTHarmonic.MatedCRT.lastZeroR c
    0 ≤ ℓ ∧ c ℓ = 0 ∧ ∀ t, ℓ < t → 0 < c t := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 (htend.eventually_gt_atTop 0)
  let Z : Set ℝ := {s | 0 ≤ s ∧ c s = 0}
  have hZne : Z.Nonempty := ⟨0, le_rfl, hc0⟩
  have hZclosed : IsClosed Z := isClosed_Ici.inter (isClosed_eq hc continuous_const)
  have hZbdd : BddAbove Z := by
    refine ⟨R, ?_⟩
    intro s hs
    by_contra h
    have := hR s (le_of_lt (lt_of_not_ge h))
    exact (ne_of_gt this) hs.2
  have hlast : sSup Z ∈ Z := hZclosed.csSup_mem hZne hZbdd
  refine ⟨hlast.1, hlast.2, ?_⟩
  intro t ht
  change sSup Z < t at ht
  by_contra hneg
  let u := max t R + 1
  have htu : t ≤ u := by dsimp [u]; linarith [le_max_left t R]
  have hRu : R ≤ u := by dsimp [u]; linarith [le_max_right t R]
  have hcu : 0 < c u := hR u hRu
  obtain ⟨v, hv, hcv⟩ := intermediate_value_Icc htu hc.continuousOn
    ⟨le_of_not_gt hneg, le_of_lt hcu⟩
  have hvZ : v ∈ Z := ⟨le_trans hlast.1 (le_trans (le_of_lt ht) hv.1), hcv⟩
  have hvle : v ≤ sSup Z := le_csSup hZbdd hvZ
  linarith [hv.1]

/-- The two radial branches of the reference cone.  The outer branch is
obtained from the drifted Brownian path after its last zero. -/
def referenceConeRadialPair (γ : ℝ) (b b' : ℝ≥0 → ℝ) :
    (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  let c : ℝ → ℝ := fun u => b' u.toNNReal +
    (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) * u
  let ℓ := MatedCRTHarmonic.MatedCRT.lastZeroR c
  (fun t => b t + γ * t, fun t => c (ℓ + t) - MatedCRTHarmonic.MatedCRT.lqgQ γ * t)

/-- At positive times the inner branch is exactly the corresponding branch
of Bonanno's radial process. -/
theorem referenceConeRadialPair_inner (γ : ℝ) (b b' : ℝ≥0 → ℝ) (t : ℝ≥0) :
    (referenceConeRadialPair γ b b').1 t =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ b b' t := by
  simp [referenceConeRadialPair, MatedCRTHarmonic.MatedCRT.coneRadial]

/-- At positive times the outer branch is the post-last-zero branch of
Bonanno's radial process. -/
theorem referenceConeRadialPair_outer (γ : ℝ) (b b' : ℝ≥0 → ℝ)
    (t : ℝ≥0) (ht : 0 < t) :
    (referenceConeRadialPair γ b b').2 t =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ b b' (-(t : ℝ)) := by
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  simp [referenceConeRadialPair, MatedCRTHarmonic.MatedCRT.coneRadial,
    not_le.mpr (neg_neg_of_pos ht'), sub_eq_add_neg]

/-- The remaining circle-average calculation for a reference cone.  Its
hypothesis is a simultaneous representation by that cone, and its conclusion
identifies the recovered circle process with the actual post-last-zero
formula.  This is an internal proof obligation, not a DMS hypothesis. -/
def ReferenceConeRadialCircleStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
    S.IsValid 𝒮 γ → ∀ (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ),
    LQGMetric.IsWholePlaneGFF X S.P → IsBrownianReal B S.P → IsBrownianReal B' S.P →
    IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) S.P →
    IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) S.P →
    (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ =
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) φ) →
    ∀ᵐ ω ∂S.P, radialProcess (distributionCircleVersion
      (MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) =
      referenceConeRadialPair γ (fun t => B t ω) (fun t => B' t ω)

/-- Once the reference circles are calculated, the reference post-last-zero
radial pair has the weak-limit conditioned law from the environment. -/
theorem exists_reference_cone_postLastZero_radial_law
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel}
    (hcircle : ReferenceConeRadialCircleStep 𝒮)
    {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hHm : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∃ (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ)
      (ν : Measure (MarkovProcess.ContinuousPath ℝ)),
      LQGMetric.IsWholePlaneGFF X S.P ∧ IsBrownianReal B S.P ∧ IsBrownianReal B' S.P ∧
      IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) S.P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) S.P ∧
      IsBMConditionedPositive (lqgQ γ - γ) ν ∧
      S.P.map (fun ω => referenceConeRadialPair γ (fun t => B t ω) (fun t => B' t ω)) =
        quantumConeRadialLaw γ ν := by
  obtain ⟨X, B, B', ν, hX, hB, hB', hi, hi', hν, href, _, _, hlaw⟩ :=
    exists_reference_cone_field_and_recovered_radial_law hS hHm hrep
  refine ⟨X, B, B', ν, hX, hB, hB', hi, hi', hν, ?_⟩
  have heq := hcircle γ Ω S hS X B B' hX hB hB' hi hi' href
  rw [← Measure.map_congr heq, hlaw]

/-- The drift-corrected post-last-zero path associated with the outer
branch of the reference cone. -/
def referenceConeConditionedPath (γ : ℝ) (B' : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  let d := MatedCRTHarmonic.MatedCRT.lqgQ γ - γ
  let c : ℝ → ℝ := fun u => B' u.toNNReal + d * u
  let ℓ := MatedCRTHarmonic.MatedCRT.lastZeroR c
  fun t => c (ℓ + t) - d * t

/-- If the drifted reference path tends to positive infinity, its
post-last-zero segment starts at zero and is strictly positive at every
positive time.  The drift is subtracted in `referenceConeConditionedPath`. -/
theorem referenceConeConditionedPath_start_and_pos (γ : ℝ) (b : ℝ≥0 → ℝ)
    (hb : Continuous b) (hb0 : b 0 = 0)
    (htend : Tendsto (fun u : ℝ => b u.toNNReal +
      (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) * u) atTop atTop) :
    referenceConeConditionedPath γ b 0 = 0 ∧
      ∀ t : ℝ≥0, 0 < t → 0 < referenceConeConditionedPath γ b t +
        (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) * t := by
  let c : ℝ → ℝ := fun u => b u.toNNReal +
    (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) * u
  have hc : Continuous c := (hb.comp continuous_real_toNNReal).add (by fun_prop)
  have hc0 : c 0 = 0 := by simp [c, hb0]
  have hlast := lastZeroR_eq_zero_and_pos hc hc0 htend
  constructor
  · simpa [referenceConeConditionedPath, c] using hlast.2.1
  · intro t ht
    have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
    have hp := hlast.2.2 (MatedCRTHarmonic.MatedCRT.lastZeroR c + t) (by linarith)
    simpa [referenceConeConditionedPath, c] using hp

/-- Under the same pathwise hypotheses, the outer radial branch agrees with
the reference cone's radial function also at time zero. -/
theorem referenceConeRadialPair_outer_all (γ : ℝ) (b b' : ℝ≥0 → ℝ)
    (hb0 : b 0 = 0) (hb' : Continuous b') (hb'0 : b' 0 = 0)
    (htend : Tendsto (fun u : ℝ => b' u.toNNReal +
      (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) * u) atTop atTop)
    (t : ℝ≥0) :
    (referenceConeRadialPair γ b b').2 t =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ b b' (-(t : ℝ)) := by
  have ht0 : 0 ≤ t := bot_le
  obtain rfl | ht := eq_or_lt_of_le ht0
  · have hstart := (referenceConeConditionedPath_start_and_pos γ b' hb' hb'0 htend).1
    simpa [referenceConeRadialPair, referenceConeConditionedPath,
      MatedCRTHarmonic.MatedCRT.coneRadial, hb0] using hstart
  · exact referenceConeRadialPair_outer γ b b' t ht

/-- Removing the outer radial drift gives the drift-corrected path after the
last zero. This identity also covers time zero. -/
theorem referenceConeRadialPair_outer_centered (γ : ℝ) (B B' : ℝ≥0 → ℝ) :
    (fun t : ℝ≥0 => (referenceConeRadialPair γ B B').2 t + γ * t) =
      referenceConeConditionedPath γ B' := by
  funext t
  simp only [referenceConeRadialPair, referenceConeConditionedPath]
  ring

/-- Centering the outer coordinate of the cone radial law recovers the
conditioned Brownian law as a law on coordinate paths. -/
theorem map_quantumConeRadialLaw_outer_centered (γ : ℝ)
    (ν : Measure (MarkovProcess.ContinuousPath ℝ)) [IsProbabilityMeasure ν] :
    (quantumConeRadialLaw γ ν).map
      (fun p (t : ℝ≥0) => p.2 t + γ * t) =
      ν.map (fun w (t : ℝ≥0) => w t) := by
  let f : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun x t => x t + γ * t
  let g : MarkovProcess.ContinuousPath ℝ → (ℝ≥0 → ℝ) := fun w t => w t - γ * t
  have hf : Measurable f := Measurable.of_eval fun t => (measurable_pi_apply t).add measurable_const
  have hg : Measurable g := Measurable.of_eval fun t =>
    (MarkovProcess.ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t).sub measurable_const
  have hm : Measurable (fun w : MarkovProcess.ContinuousPath ℝ =>
      fun t : ℝ≥0 => w t + γ * t) := Measurable.of_eval fun t =>
    (MarkovProcess.ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t).add measurable_const
  change (quantumConeRadialLaw γ ν).map (f ∘ Prod.snd) = _
  rw [← Measure.map_map hf measurable_snd]
  unfold quantumConeRadialLaw
  rw [Measure.map_snd_prod, Measure.map_apply hm MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, one_smul]
  change (ν.map g).map f = _
  rw [Measure.map_map hf hg]
  congr 1
  funext w t
  simp only [Function.comp_apply, f, g]
  ring

/-- Given the simultaneous circle identity, the post-last-zero path from
any represented reference cone has the weak-limit conditioned law supplied
by the valid environment. The equality is on coordinate paths. -/
theorem referenceConeConditionedPath_law
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hcircle : ReferenceConeRadialCircleStep 𝒮)
    (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ)
    (hX : LQGMetric.IsWholePlaneGFF X S.P) (hB : IsBrownianReal B S.P)
    (hB' : IsBrownianReal B' S.P)
    (hi : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) S.P)
    (hi' : IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) S.P)
    (href : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ =
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) φ) :
    ∃ ν : Measure (MarkovProcess.ContinuousPath ℝ),
      IsBMConditionedPositive (lqgQ γ - γ) ν ∧
      S.P.map (fun ω => referenceConeConditionedPath γ (fun t => B' t ω)) =
        ν.map (fun w (t : ℝ≥0) => w t) := by
  obtain ⟨ν, hν, hlaw⟩ := hS.isQuantumCone.radial_law
  refine ⟨ν, hν, ?_⟩
  let : IsProbabilityMeasure ν := hν.1
  have hc := hcircle γ Ω S hS X B B' hX hB hB' hi hi' href
  have hrec := ae_distributionCircleVersion_eq hS href
  have heq : (fun ω => referenceConeRadialPair γ (fun t => B t ω) (fun t => B' t ω)) =ᵐ[S.P]
      (fun ω => radialProcess (S.hcirc ω)) := by
    filter_upwards [hc, hrec] with ω hcω hrω
    rw [← hcω]
    apply Prod.ext <;> funext t <;> exact hrω _ (Real.exp_pos _) 0
  let f : ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) → (ℝ≥0 → ℝ) :=
    fun p t => p.2 t + γ * t
  have hf : Measurable f := Measurable.of_eval fun t =>
    ((measurable_pi_apply t).comp measurable_snd).add measurable_const
  have hmaps : (fun ω => referenceConeConditionedPath γ (fun t => B' t ω)) =ᵐ[S.P]
      (fun ω => f (radialProcess (S.hcirc ω))) := by
    filter_upwards [heq] with ω hω
    rw [← hω]
    exact (referenceConeRadialPair_outer_centered γ _ _).symm
  rw [Measure.map_congr hmaps]
  change S.P.map (f ∘ fun ω => radialProcess (S.hcirc ω)) = _
  rw [← Measure.map_map hf (IsQuantumCone.measurable_radialProcess hS.isQuantumCone), hlaw]
  exact map_quantumConeRadialLaw_outer_centered γ ν

/-- A measure on continuous paths is determined by its coordinate-path law.
The coordinate product has its product sigma algebra; no measurable range
assertion for the inclusion of continuous paths is needed. -/
theorem continuousPath_measure_ext_of_coordinate_law
    {μ ν : Measure (MarkovProcess.ContinuousPath ℝ)}
    (h : μ.map (fun w (t : ℝ≥0) => w t) = ν.map (fun w (t : ℝ≥0) => w t)) :
    μ = ν := by
  let e : MarkovProcess.ContinuousPath ℝ → (ℝ≥0 → ℝ) := fun w t => w t
  have he : Measurable e := Measurable.of_eval fun t =>
    MarkovProcess.ContinuousPath.measurable_coordinateProcess t
  have hcomap : (inferInstance : MeasurableSpace (MarkovProcess.ContinuousPath ℝ)) ≤
      (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)).comap e := by
    change (ContinuousMap.measurableSpace : MeasurableSpace C(ℝ≥0, ℝ)) ≤ _
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    refine iSup_le fun t => ?_
    apply measurable_iff_comap_le.mp
    exact (measurable_pi_apply t).comp (comap_measurable e)
  apply Measure.ext
  intro A hA
  obtain ⟨C, hC, hpre⟩ := MeasurableSpace.measurableSet_comap.mp (hcomap A hA)
  have hCeq := congrArg (fun m : Measure (ℝ≥0 → ℝ) => m C) h
  rw [Measure.map_apply he hC, Measure.map_apply he hC, hpre] at hCeq
  exact hCeq

/-- A measurable coordinate process with almost surely continuous paths has
a measurable continuous-path version. -/
theorem exists_measurable_continuousPath_version
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (Z : Ω → (ℝ≥0 → ℝ))
    (hZ : Measurable Z) (hc : ∀ᵐ ω ∂P, Continuous (Z ω)) :
    ∃ Y : Ω → MarkovProcess.ContinuousPath ℝ,
      Measurable Y ∧ ∀ᵐ ω ∂P, (fun t => Y ω t) = Z ω := by
  classical
  have hnull : P {ω | ¬ Continuous (Z ω)} = 0 := ae_iff.mp hc
  obtain ⟨N, hsub, hN, hNzero⟩ := exists_measurable_superset_of_null hnull
  let Y : Ω → MarkovProcess.ContinuousPath ℝ := fun ω =>
    if hω : ω ∈ N then 0 else ⟨Z ω, by
      by_contra h
      exact hω (hsub h)⟩
  have hm : Measurable Y := ContinuousMap.measurable_iff_eval.mpr fun t => by
    have heq : (fun ω => Y ω t) = fun ω => if ω ∈ N then 0 else Z ω t := by
      funext ω
      by_cases hω : ω ∈ N <;> simp [Y, hω]
    rw [heq]
    exact measurable_const.ite hN ((measurable_pi_apply t).comp hZ)
  refine ⟨Y, hm, ?_⟩
  have hgood : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.mpr (by simpa using hNzero)
  filter_upwards [hgood] with ω hω
  simp [Y, hω]

/-- The post-last-zero path is continuous whenever the underlying Brownian
path is continuous. -/
theorem continuous_referenceConeConditionedPath (γ : ℝ) (B' : ℝ≥0 → ℝ)
    (hB' : Continuous B') : Continuous (referenceConeConditionedPath γ B') := by
  unfold referenceConeConditionedPath
  dsimp only
  fun_prop

/-- A measurable continuous-path version of the post-last-zero process has
the weak-limit law itself, provided the reference circles are identified. -/
theorem referenceConeConditionedContinuousPath_law
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hcircle : ReferenceConeRadialCircleStep 𝒮)
    (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ)
    (hX : LQGMetric.IsWholePlaneGFF X S.P) (hB : IsBrownianReal B S.P)
    (hB' : IsBrownianReal B' S.P)
    (hi : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) S.P)
    (hi' : IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) S.P)
    (href : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ =
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) φ)
    (Y : Ω → MarkovProcess.ContinuousPath ℝ) (hY : AEMeasurable Y S.P)
    (hYeq : ∀ᵐ ω ∂S.P, (fun t => Y ω t) =
      referenceConeConditionedPath γ (fun t => B' t ω)) :
    IsBMConditionedPositive (lqgQ γ - γ) (S.P.map Y) := by
  obtain ⟨ν, hν, hlaw⟩ :=
    referenceConeConditionedPath_law hS hcircle X B B' hX hB hB' hi hi' href
  have he : Measurable (fun w : MarkovProcess.ContinuousPath ℝ => fun t : ℝ≥0 => w t) :=
    Measurable.of_eval fun t => MarkovProcess.ContinuousPath.measurable_coordinateProcess t
  have hmap : (S.P.map Y).map (fun w (t : ℝ≥0) => w t) =
      ν.map (fun w (t : ℝ≥0) => w t) := by
    rw [AEMeasurable.map_map_of_aemeasurable he.aemeasurable hY]
    exact (Measure.map_congr hYeq).trans hlaw
  have h := continuousPath_measure_ext_of_coordinate_law hmap
  rw [h]
  exact hν

/-- The represented post-last-zero process admits a measurable continuous
version with the weak-limit conditioned law, once the circles are identified. -/
theorem exists_referenceConeConditionedContinuousPath
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hcircle : ReferenceConeRadialCircleStep 𝒮)
    (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ)
    (hX : LQGMetric.IsWholePlaneGFF X S.P) (hB : IsBrownianReal B S.P)
    (hB' : IsBrownianReal B' S.P)
    (hi : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) S.P)
    (hi' : IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) S.P)
    (href : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ =
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) φ) :
    ∃ Y : Ω → MarkovProcess.ContinuousPath ℝ,
      Measurable Y ∧
      (∀ᵐ ω ∂S.P, (fun t => Y ω t) = referenceConeConditionedPath γ (fun t => B' t ω)) ∧
      IsBMConditionedPositive (lqgQ γ - γ) (S.P.map Y) := by
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω t => S.hcirc ω (Real.exp t) 0 + γ * t
  have hZ : Measurable Z := Measurable.of_eval fun t =>
    (hS.isQuantumCone.measurable_circle _ _ (Real.exp_pos _)).add measurable_const
  have hc := hcircle γ Ω S hS X B B' hX hB hB' hi hi' href
  have hrec := ae_distributionCircleVersion_eq hS href
  have heq : ∀ᵐ ω ∂S.P, Z ω = referenceConeConditionedPath γ (fun t => B' t ω) := by
    filter_upwards [hc, hrec] with ω hcω hrecω
    have he : radialProcess (S.hcirc ω) =
        referenceConeRadialPair γ (fun t => B t ω) (fun t => B' t ω) := by
      rw [← hcω]
      apply Prod.ext <;> funext t <;> exact (hrecω _ (Real.exp_pos _) 0).symm
    have ht := congrArg Prod.snd he
    change (fun t : ℝ≥0 => S.hcirc ω (Real.exp t) 0) = _ at ht
    change (fun t : ℝ≥0 => S.hcirc ω (Real.exp t) 0 + γ * t) = _
    funext t
    rw [congrFun ht t]
    exact congrFun (referenceConeRadialPair_outer_centered γ _ _) t
  have hcont : ∀ᵐ ω ∂S.P, Continuous (Z ω) := by
    filter_upwards [heq, hB'.cont] with ω heqω hcω
    rw [heqω]
    exact continuous_referenceConeConditionedPath γ _ hcω
  obtain ⟨Y, hY, hYZ⟩ := exists_measurable_continuousPath_version Z hZ hcont
  have hYeq : ∀ᵐ ω ∂S.P, (fun t => Y ω t) =
      referenceConeConditionedPath γ (fun t => B' t ω) := by
    filter_upwards [hYZ, heq] with ω hYZω heqω
    exact hYZω.trans heqω
  exact ⟨Y, hY, hYeq,
    referenceConeConditionedContinuousPath_law hS hcircle X B B' hX hB hB' hi hi' href
      Y hY.aemeasurable hYeq⟩

/-- Equality of the radial pairs identifies every logarithmic circle with the
reference radial formula, including the shared time zero. -/
theorem referenceConeRadial_eq_of_pair (γ : ℝ) (a : ℝ → ℂ → ℝ)
    (B B' : ℝ≥0 → ℝ)
    (hp : radialProcess a = referenceConeRadialPair γ B B') :
    ∀ s : ℝ, a (Real.exp s) 0 =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ B B' (-s) := by
  intro s
  by_cases hs : 0 < s
  · let t : ℝ≥0 := ⟨s, hs.le⟩
    have ht : 0 < t := hs
    have h := congrFun (congrArg Prod.snd hp) t
    change a (Real.exp s) 0 = (referenceConeRadialPair γ B B').2 t at h
    rw [referenceConeRadialPair_outer γ B B' t ht] at h
    exact h
  · by_cases hz : s = 0
    · subst s
      have h := congrFun (congrArg Prod.fst hp) 0
      rw [referenceConeRadialPair_inner] at h
      simpa [radialProcess] using h
    · have hs' : 0 < -s := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hs) hz)
      let t : ℝ≥0 := ⟨-s, hs'.le⟩
      have h := congrFun (congrArg Prod.fst hp) t
      rw [referenceConeRadialPair_inner] at h
      change a (Real.exp (-(-s))) 0 =
        MatedCRTHarmonic.MatedCRT.coneRadial γ γ B B' (-s) at h
      simpa only [neg_neg] using h

/-- Changing from logarithmic radius to radius preserves the largest level,
provided the logarithmic level set is nonempty and bounded above. -/
theorem exp_sSup_level_eq_sSup_positive_level (f : ℝ → ℝ) (c : ℝ)
    (hne : {s : ℝ | f s = c}.Nonempty) (hbounded : BddAbove {s : ℝ | f s = c}) :
    Real.exp (sSup {s : ℝ | f s = c}) =
      sSup {r : ℝ | 0 < r ∧ f (Real.log r) = c} := by
  have himage : Real.exp '' {s : ℝ | f s = c} =
      {r : ℝ | 0 < r ∧ f (Real.log r) = c} := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      change f s = c at hs
      exact ⟨Real.exp_pos s, by simpa only [Real.log_exp] using hs⟩
    · rintro ⟨hr, hf⟩
      exact ⟨Real.log r, hf, Real.exp_log hr⟩
  rw [Monotone.map_csSup_of_continuousAt Real.continuous_exp.continuousAt
    Real.exp_monotone hne hbounded, himage]

/-- If the circles agree with the reference radial process and its logarithmic
level set is nonempty and bounded, the two embedding-radius formulas agree. -/
theorem referenceConeEmbeddingRadius_eq_coneScaleRadius
    (γ b : ℝ) (a : ℝ → ℂ → ℝ) (B B' : ℝ≥0 → ℝ)
    (hcircle : ∀ s : ℝ, a (Real.exp s) 0 =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ B B' (-s))
    (hne : {s : ℝ | MatedCRTHarmonic.MatedCRT.coneLogRadial γ γ B B' s =
      γ⁻¹ * Real.log b}.Nonempty)
    (hbounded : BddAbove {s : ℝ | MatedCRTHarmonic.MatedCRT.coneLogRadial γ γ B B' s =
      γ⁻¹ * Real.log b}) :
    Proposed.dmsConeEmbeddingRadius γ γ (-Real.log b) B B' = coneScaleRadius γ a b := by
  rw [Proposed.dmsConeEmbeddingRadius_neg_log]
  unfold MatedCRTHarmonic.MatedCRT.coneScale coneScaleRadius
  rw [exp_sSup_level_eq_sSup_positive_level _ _ hne hbounded]
  congr 1
  ext r
  constructor <;> rintro ⟨hr, hlevel⟩ <;> refine ⟨hr, ?_⟩
  · have hc := hcircle (Real.log r)
    rw [Real.exp_log hr] at hc
    unfold MatedCRTHarmonic.MatedCRT.coneLogRadial at hlevel
    change a r 0 + MatedCRTHarmonic.MatedCRT.lqgQ γ * Real.log r = γ⁻¹ * Real.log b
    rw [hc]
    exact hlevel
  · have hc := hcircle (Real.log r)
    rw [Real.exp_log hr] at hc
    unfold MatedCRTHarmonic.MatedCRT.coneLogRadial
    change a r 0 + MatedCRTHarmonic.MatedCRT.lqgQ γ * Real.log r = γ⁻¹ * Real.log b at hlevel
    rw [← hc]
    exact hlevel

/-- Recovery of the explicit reference embedding radius from the represented
field.  This is the remaining internal radius calculation, not a field-law
or scaling-law assumption. -/
def ReferenceConeEmbeddingRadiusStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (b : ℝ), 0 < b →
    ∀ (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ),
    LQGMetric.IsWholePlaneGFF X S.P → IsBrownianReal B S.P → IsBrownianReal B' S.P →
    IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) S.P →
    IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) S.P →
    (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ =
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) φ) →
    ∀ᵐ ω ∂S.P, Proposed.dmsConeEmbeddingRadius γ γ (-Real.log b)
      (fun t => B t ω) (fun t => B' t ω) =
      distributionEmbeddingRadius γ b (MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))

/-- Nonemptiness and upper boundedness of each reference logarithmic level
set, the path-growth assertion used in env-steps.tex:280–286. -/
def ReferenceConeLogLevelSetStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (b : ℝ), 0 < b →
    ∀ (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ),
    LQGMetric.IsWholePlaneGFF X S.P → IsBrownianReal B S.P → IsBrownianReal B' S.P →
    IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) S.P →
    IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) S.P →
    (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ =
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) φ) →
    ∀ᵐ ω ∂S.P,
      let L : Set ℝ := {s | MatedCRTHarmonic.MatedCRT.coneLogRadial γ γ
        (fun t => B t ω) (fun t => B' t ω) s = γ⁻¹ * Real.log b}
      L.Nonempty ∧ BddAbove L

/-- A positive cone scale radius forces the corresponding logarithmic level
set to be nonempty and bounded above. -/
theorem referenceConeLogLevelSet_of_radius_pos
    (γ b : ℝ) (a : ℝ → ℂ → ℝ) (B B' : ℝ≥0 → ℝ)
    (hcircle : ∀ s : ℝ, a (Real.exp s) 0 =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ B B' (-s))
    (hpos : 0 < coneScaleRadius γ a b) :
    let L := {s : ℝ | MatedCRTHarmonic.MatedCRT.coneLogRadial γ γ B B' s =
      γ⁻¹ * Real.log b}
    L.Nonempty ∧ BddAbove L := by
  let A : Set ℝ := {r | 0 < r ∧ a r 0 + lqgQ γ * Real.log r = γ⁻¹ * Real.log b}
  have hp : 0 < sSup A := hpos
  have hne : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty] at hp
    exact lt_irrefl _ hp
  have hbdd : BddAbove A := by
    by_contra h
    rw [Real.sSup_of_not_bddAbove h] at hp
    exact lt_irrefl _ hp
  have hmem : ∀ s : ℝ, Real.exp s ∈ A ↔
      MatedCRTHarmonic.MatedCRT.coneLogRadial γ γ B B' s = γ⁻¹ * Real.log b := by
    intro s
    change (0 < Real.exp s ∧ a (Real.exp s) 0 + lqgQ γ * Real.log (Real.exp s) =
      γ⁻¹ * Real.log b) ↔ _
    rw [Real.log_exp, hcircle s]
    simp only [Real.exp_pos, true_and, MatedCRTHarmonic.MatedCRT.coneLogRadial]
    rfl
  constructor
  · obtain ⟨r, hr⟩ := hne
    refine ⟨Real.log r, ?_⟩
    apply (hmem _).mp
    simpa only [Real.exp_log hr.1] using hr
  · obtain ⟨M, hM⟩ := hbdd
    refine ⟨Real.log M, ?_⟩
    intro s hs
    have hsM : Real.exp s ≤ M := hM ((hmem s).mpr hs)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos s) hsM

/-- Radius positivity from the existing cone scaling input supplies the
reference logarithmic level bounds once the circles have been identified. -/
theorem referenceConeLogLevelSetStep_of_radial
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hcircle : ReferenceConeRadialCircleStep 𝒮) : ReferenceConeLogLevelSetStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb X B B' hX hB hB' hi hi' href
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hc := hcircle γ Ω S hS X B B' hX hB hB' hi hi' href
  have hrecovered := ae_distributionCircleVersion_eq hS href
  have hpos := ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone hb
  filter_upwards [hc, hrecovered, hpos] with ω hcω hrecoveredω hposω
  apply referenceConeLogLevelSet_of_radius_pos γ b (S.hcirc ω)
    (fun t => B t ω) (fun t => B' t ω) ?_ hposω
  intro s
  rw [← hrecoveredω (Real.exp s) (Real.exp_pos s) 0]
  exact referenceConeRadial_eq_of_pair γ _ _ _ hcω s

/-- The simultaneous radial-circle identity and the logarithmic level-set
bounds give reference-radius recovery. -/
theorem referenceConeEmbeddingRadiusStep_of_radial_and_levels
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hcircle : ReferenceConeRadialCircleStep 𝒮)
    (hlevels : ReferenceConeLogLevelSetStep 𝒮) : ReferenceConeEmbeddingRadiusStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb X B B' hX hB hB' hi hi' href
  have hc := hcircle γ Ω S hS X B B' hX hB hB' hi hi' href
  have hl := hlevels γ hγ hγ2 Ω S hS b hb X B B' hX hB hB' hi hi' href
  have hr := ae_distributionEmbeddingRadius_eq hscale hγ hγ2 hb hS href
  have hrecovered := ae_distributionCircleVersion_eq hS href
  filter_upwards [hc, hl, hr, hrecovered] with ω hcω hlω hrω hrecoveredω
  rw [hrω]
  have heq : coneScaleRadius γ
      (distributionCircleVersion (MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) b =
      coneScaleRadius γ (S.hcirc ω) b := by
    unfold coneScaleRadius
    congr 1
    ext r
    by_cases hr : 0 < r
    · simp only [Set.mem_ofPred_eq, hr, true_and, hrecoveredω r hr 0]
    · simp only [Set.mem_ofPred_eq, hr, false_and]
  rw [← heq]
  exact referenceConeEmbeddingRadius_eq_coneScaleRadius γ b
    (distributionCircleVersion (MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))))
    (fun t => B t ω) (fun t => B' t ω)
    (referenceConeRadial_eq_of_pair γ _ _ _ hcω) hlω.1 hlω.2

/-- The mating-of-trees witness and reference-radius recovery give the
canonical joint law.  The reference field is only almost-everywhere measurable;
the common representation event suffices to compare the joint maps. -/
theorem canonicalConeDistributionRadiusLawStep_of_reference_radius
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hradius : ReferenceConeEmbeddingRadiusStep 𝒮) :
    CanonicalConeDistributionRadiusLawStep 𝒮 := by
  intro γ hγ hγ2 Ω mΩ S hS b hb H R hHm _ hrep hR
  obtain ⟨X, B, B', ν, hX, hB, hB', hi, hi', hν, href, hHref, hlaw, hradial⟩ :=
    exists_reference_cone_field_and_recovered_radial_law hS hHm hrep
  let H' : Ω → LQGMetric.DistC := fun ω =>
    MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))
  let R' : Ω → ℝ := fun ω => Proposed.dmsConeEmbeddingRadius γ γ (-Real.log b)
    (fun t => B t ω) (fun t => B' t ω)
  have hR' : ∀ᵐ ω ∂S.P, R' ω = distributionEmbeddingRadius γ b (H' ω) :=
    hradius γ hγ hγ2 Ω S hS b hb X B B' hX hB hB' hi hi' href
  have hH : H =ᵐ[S.P] H' := by
    filter_upwards [hrep, href] with ω hω hω'
    ext φ
    exact (hω φ).symm.trans (hω' φ)
  have hrH := ae_distributionEmbeddingRadius_eq hscale hγ hγ2 hb hS href
  have hjoint : (fun ω => (H ω, R ω)) =ᵐ[S.P] (fun ω => (H' ω, R' ω)) := by
    filter_upwards [hH, hR, hR', hrH] with ω hfield hRω hRω' hrω
    exact Prod.ext hfield (hRω.trans (hrω.symm.trans hRω'.symm))
  have hRrev : (fun ω => distributionEmbeddingRadius γ b (H' ω)) =ᵐ[S.P] R' := by
    filter_upwards [hR'] with ω hω
    exact hω.symm
  have hRmeas : AEMeasurable R' S.P :=
    ((measurable_distributionEmbeddingRadius γ b).comp_aemeasurable hHref).congr hRrev
  exact ⟨Ω, mΩ, S.P, X, B, B', hS.isProbabilityMeasure, hX, hB, hB', hi, hi',
    hHref.prodMk hRmeas, Measure.map_congr hjoint⟩

/-- The canonical joint law follows from the reference radial-circle identity
and the nonempty, bounded logarithmic level sets. -/
theorem canonicalConeDistributionRadiusLawStep_of_reference_radial
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hcircle : ReferenceConeRadialCircleStep 𝒮)
    (hlevels : ReferenceConeLogLevelSetStep 𝒮) :
    CanonicalConeDistributionRadiusLawStep 𝒮 :=
  canonicalConeDistributionRadiusLawStep_of_reference_radius 𝒮 hscale
    (referenceConeEmbeddingRadiusStep_of_radial_and_levels 𝒮 hscale hcircle hlevels)

/-- The radial-circle identity suffices for the canonical joint law, given
the existing cone scaling input. -/
theorem canonicalConeDistributionRadiusLawStep_of_reference_circle
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hcircle : ReferenceConeRadialCircleStep 𝒮) :
    CanonicalConeDistributionRadiusLawStep 𝒮 :=
  canonicalConeDistributionRadiusLawStep_of_reference_radial 𝒮 hscale hcircle
    (referenceConeLogLevelSetStep_of_radial 𝒮 hscale hcircle)

end MatedCRT.Sec1
