import MatedCRT.Proofs.Sec1.EnvironmentScaling.FieldAssembly
import MatedCRT.Proposed.DuplantierMillerSheffieldCone2014
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

/-! ### Standalone post-last-zero path: rational-level description of the last zero -/

/-- A continuous path tending to `+∞` has a zero at or after any point where it is `≤ 0`
(intermediate value theorem). -/
theorem exists_zero_ge_of_nonpos {c : ℝ → ℝ} (hc : Continuous c)
    (htend : Tendsto c atTop atTop) {u : ℝ} (hu : c u ≤ 0) :
    ∃ v, u ≤ v ∧ c v = 0 := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (htend.eventually_ge_atTop 1)
  have hx : 0 ≤ c (max u T) := by linarith [hT (max u T) (le_max_right u T)]
  obtain ⟨v, hv, hcv⟩ := intermediate_value_Icc (le_max_left u T) hc.continuousOn ⟨hu, hx⟩
  exact ⟨v, hv.1, hcv⟩

/-- For a path tending to `+∞`, a nonpositive value at some `u ≥ q` is equivalent to: for every
`k`, a rational `a > q` with value below `1/(k+1)`. -/
theorem exists_nonpos_iff_rat {c : ℝ → ℝ} (hc : Continuous c)
    (htend : Tendsto c atTop atTop) (q : ℝ) :
    (∃ u, q ≤ u ∧ c u ≤ 0) ↔
      ∀ k : ℕ, ∃ a : ℚ, q < (a : ℝ) ∧ c (a : ℝ) < 1 / ((k : ℝ) + 1) := by
  constructor
  · rintro ⟨u, hqu, hu⟩ k
    have hlt : c u < 1 / ((k : ℝ) + 1) := lt_of_le_of_lt hu (by positivity)
    have hev : ∀ᶠ x in 𝓝 u, c x < 1 / ((k : ℝ) + 1) :=
      hc.continuousAt.eventually_lt continuousAt_const hlt
    obtain ⟨v, hv, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (nhdsWithin_le_nhds hev)
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (Set.mem_Ioi.1 hv)
    exact ⟨a, lt_of_le_of_lt hqu ha1, hsub ⟨ha1, ha2⟩⟩
  · intro H
    obtain ⟨T, hT⟩ := eventually_atTop.1 (htend.eventually_ge_atTop 1)
    have hqM : q ≤ max T q := le_max_right T q
    obtain ⟨u, hu, hmin⟩ := (isCompact_Icc : IsCompact (Set.Icc q (max T q))).exists_isMinOn
      ⟨q, ⟨le_refl q, hqM⟩⟩ hc.continuousOn
    refine ⟨u, hu.1, ?_⟩
    by_contra hpos
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (not_le.mp hpos)
    obtain ⟨a, ha1, ha2⟩ := H k
    have ha_le : (a : ℝ) ≤ max T q := by
      by_contra hcon
      have hcon' : max T q < (a : ℝ) := not_le.mp hcon
      have h1 : 1 ≤ c (a : ℝ) := hT (a : ℝ) (le_trans (le_max_left T q) (le_of_lt hcon'))
      have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      linarith
    have hle : c u ≤ c (a : ℝ) := isMinOn_iff.1 hmin (a : ℝ) ⟨le_of_lt ha1, ha_le⟩
    linarith

open scoped Classical in
/-- For a path tending to `+∞`, the last zero `lastZeroR c` is the supremum of the rational levels
`q ≥ 0` at which `c` is nonpositive somewhere at or after `q`; the supremum over an empty family is
`0`, matching Lean's convention in `lastZeroR`. -/
theorem lastZeroR_eq_iSup_rat {c : ℝ → ℝ} (hc : Continuous c)
    (htend : Tendsto c atTop atTop) :
    (⨆ q : ℚ, if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0 then (q : ℝ) else 0) =
      MatedCRTHarmonic.MatedCRT.lastZeroR c := by
  unfold MatedCRTHarmonic.MatedCRT.lastZeroR
  obtain ⟨R, hR⟩ := eventually_atTop.1 (htend.eventually_gt_atTop 0)
  have hZbdd : BddAbove {s : ℝ | 0 ≤ s ∧ c s = 0} := by
    refine ⟨R, fun s hs => ?_⟩
    by_contra h
    have h1 : 0 < c s := hR s (le_of_lt (not_le.mp h))
    linarith [hs.2]
  have hZcl : IsClosed {s : ℝ | 0 ≤ s ∧ c s = 0} :=
    (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).inter (isClosed_eq hc continuous_const)
  by_cases hZne : ({s : ℝ | 0 ≤ s ∧ c s = 0} : Set ℝ).Nonempty
  · have hs : sSup {s : ℝ | 0 ≤ s ∧ c s = 0} ∈ {s : ℝ | 0 ≤ s ∧ c s = 0} :=
      hZcl.csSup_mem hZne hZbdd
    have hsnn : 0 ≤ sSup {s : ℝ | 0 ≤ s ∧ c s = 0} := hs.1
    have hsz : c (sSup {s : ℝ | 0 ≤ s ∧ c s = 0}) = 0 := hs.2
    have hA : ∀ q : ℚ, (0 : ℝ) ≤ (q : ℝ) →
        ((∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0) ↔ (q : ℝ) ≤ sSup {s : ℝ | 0 ≤ s ∧ c s = 0}) := by
      intro q hq
      constructor
      · rintro ⟨u, hqu, hu⟩
        obtain ⟨v, huv, hv⟩ := exists_zero_ge_of_nonpos hc htend hu
        have hvZ : v ∈ {s : ℝ | 0 ≤ s ∧ c s = 0} := ⟨le_trans hq (le_trans hqu huv), hv⟩
        exact le_trans (le_trans hqu huv) (le_csSup hZbdd hvZ)
      · intro hqs
        exact ⟨sSup {s : ℝ | 0 ≤ s ∧ c s = 0}, hqs, le_of_eq hsz⟩
    have hterm_le : ∀ q : ℚ, (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
        then (q : ℝ) else 0) ≤ sSup {s : ℝ | 0 ≤ s ∧ c s = 0} := by
      intro q
      split_ifs with h
      · exact (hA q h.1).1 h.2
      · exact hsnn
    have hterm_nonneg : ∀ q : ℚ, (0 : ℝ) ≤ (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
        then (q : ℝ) else 0) := by
      intro q
      split_ifs with h
      · exact h.1
      · exact le_rfl
    have hbdd : BddAbove (Set.range fun q : ℚ => (if (0 : ℝ) ≤ (q : ℝ) ∧
        ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0 then (q : ℝ) else 0)) :=
      ⟨sSup {s : ℝ | 0 ≤ s ∧ c s = 0}, by rintro _ ⟨q, rfl⟩; exact hterm_le q⟩
    apply le_antisymm
    · exact ciSup_le hterm_le
    · by_contra hlt
      have hlt' : (⨆ q : ℚ, if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
          then (q : ℝ) else 0) < sSup {s : ℝ | 0 ≤ s ∧ c s = 0} := not_le.mp hlt
      have hM0 : (0 : ℝ) ≤ ⨆ q : ℚ, (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
          then (q : ℝ) else 0) := le_trans (hterm_nonneg 0) (le_ciSup hbdd 0)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt'
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_trans hM0 (le_of_lt hq1)
      have hqterm : (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
          then (q : ℝ) else 0) = (q : ℝ) := by
        split_ifs with h
        · rfl
        · exact absurd ⟨hq0, (hA q hq0).2 (le_of_lt hq2)⟩ h
      have hle : (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
          then (q : ℝ) else 0) ≤ ⨆ q : ℚ, (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
          then (q : ℝ) else 0) := le_ciSup hbdd q
      linarith
  · have hZempty : ({s : ℝ | 0 ≤ s ∧ c s = 0} : Set ℝ) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hZne
    have hzero : ∀ q : ℚ, (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
        then (q : ℝ) else 0) = 0 := by
      intro q
      split_ifs with h
      · obtain ⟨hq0, u, hqu, hu⟩ := h
        obtain ⟨v, huv, hv⟩ := exists_zero_ge_of_nonpos hc htend hu
        have hvZ : v ∈ ({s : ℝ | 0 ≤ s ∧ c s = 0} : Set ℝ) :=
          ⟨le_trans hq0 (le_trans hqu huv), hv⟩
        rw [hZempty] at hvZ
        simp at hvZ
      · rfl
    simp only [hzero, ciSup_const, hZempty, Real.sSup_empty]

/-! ### Measurable post-last-zero level on path space -/

/-- The drifted coordinate `u ↦ w(u⁺) + d u` of a path, the path `c` of
`referenceConeConditionedPath` with `d = lqgQ γ - γ`. -/
def driftedCoord (d : ℝ) (w : MarkovProcess.ContinuousPath ℝ) (u : ℝ) : ℝ :=
  w u.toNNReal + d * u

theorem driftedCoord_continuous (d : ℝ) (w : MarkovProcess.ContinuousPath ℝ) :
    Continuous (driftedCoord d w) :=
  ((w.continuous).comp continuous_real_toNNReal).add (continuous_const.mul continuous_id)

/-- Coordinate events of rational witnesses above a real level `q`: for every `k`, some rational
`a > q` has drifted value below `1/(k+1)`. A countable intersection of countable unions of
coordinate events. -/
def driftedBelowRat (d q : ℝ) : Set (MarkovProcess.ContinuousPath ℝ) :=
  ⋂ k : ℕ, ⋃ (a : ℚ) (_ : q < (a : ℝ)), {w | driftedCoord d w (a : ℝ) < 1 / ((k : ℝ) + 1)}

theorem measurableSet_driftedBelowRat (d q : ℝ) : MeasurableSet (driftedBelowRat d q) := by
  unfold driftedBelowRat
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun a => ?_
  refine MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_lt
    ((MarkovProcess.ContinuousPath.measurable_coordinateProcess _).add_const _) measurable_const

/-- The rational level set: a rational level `q ≥ 0` with a witness in `driftedBelowRat`. -/
def ratLevelSet (d q : ℝ) : Set (MarkovProcess.ContinuousPath ℝ) :=
  {w | 0 ≤ q ∧ w ∈ driftedBelowRat d q}

theorem measurableSet_ratLevelSet (d q : ℝ) : MeasurableSet (ratLevelSet d q) := by
  by_cases h : (0 : ℝ) ≤ q
  · have hset : ratLevelSet d q = driftedBelowRat d q := by
      ext w
      simp [ratLevelSet, h]
    rw [hset]
    exact measurableSet_driftedBelowRat d q
  · have hset : ratLevelSet d q = ∅ := by
      ext w
      simp [ratLevelSet, h]
    rw [hset]
    exact MeasurableSet.empty

/-- The post-last-zero level of a path: a countable supremum of coordinate-measurable rational
levels. On drifting paths it is the last zero `lastZeroR` (see `postLastZeroLevel_eq_lastZeroR`). -/
def postLastZeroLevel (d : ℝ) (w : MarkovProcess.ContinuousPath ℝ) : ℝ :=
  ⨆ q : ℚ, (ratLevelSet d (q : ℝ)).indicator (fun _ => (q : ℝ)) w

theorem measurable_postLastZeroLevel (d : ℝ) : Measurable (postLastZeroLevel d) := by
  unfold postLastZeroLevel
  exact Measurable.iSup fun q =>
    measurable_const.indicator (measurableSet_ratLevelSet d (q : ℝ))

theorem mem_driftedBelowRat_iff {d q : ℝ} {w : MarkovProcess.ContinuousPath ℝ}
    (htend : Tendsto (driftedCoord d w) atTop atTop) :
    w ∈ driftedBelowRat d q ↔ ∃ u, q ≤ u ∧ driftedCoord d w u ≤ 0 := by
  rw [exists_nonpos_iff_rat (driftedCoord_continuous d w) htend q]
  simp only [driftedBelowRat, Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]

open scoped Classical in
/-- On a path whose drifted coordinate tends to `+∞`, the countable-supremum level is the last zero
`lastZeroR` of the drifted path. -/
theorem postLastZeroLevel_eq_lastZeroR {d : ℝ} (w : MarkovProcess.ContinuousPath ℝ)
    (htend : Tendsto (driftedCoord d w) atTop atTop) :
    postLastZeroLevel d w = MatedCRTHarmonic.MatedCRT.lastZeroR (driftedCoord d w) := by
  rw [← lastZeroR_eq_iSup_rat (driftedCoord_continuous d w) htend]
  unfold postLastZeroLevel
  refine iSup_congr fun q => ?_
  simp only [Set.indicator_apply, ratLevelSet, Set.mem_ofPred_eq, mem_driftedBelowRat_iff htend]

/-- A standalone Brownian motion with almost surely sublinear growth has a measurable
continuous-path version of the explicit post-last-zero reference process:
`F ω t = referenceConeConditionedPath γ (B · ω) t` almost surely. Only this identity is proved;
the identification of the law of `F` with the conditioned Brownian law `IsBMConditionedPositive`
is a separate premise (DMS Remark 4.4, staged in `MatedCRT/Proposed`). -/
theorem exists_measurable_referenceConeConditionedPath
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} (hd : 0 < MatedCRTHarmonic.MatedCRT.lqgQ γ - γ)
    (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (hsub : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => B t.toNNReal ω / t) atTop (𝓝 0)) :
    ∃ F : Ω → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t := by
  set d := MatedCRTHarmonic.MatedCRT.lqgQ γ - γ with hdd
  have hZB : Measurable (fun ω (t : ℝ≥0) => B t ω) := measurable_pi_iff.mpr fun t => hBm t
  obtain ⟨Y, hY, hYB⟩ := exists_measurable_continuousPath_version (fun ω t => B t ω) hZB hcont
  let L : Ω → ℝ := fun ω => postLastZeroLevel d (Y ω)
  have hLm : Measurable L := (measurable_postLastZeroLevel d).comp hY
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω t => Y ω ((L ω + (t : ℝ)).toNNReal) + d * L ω
  have hZ : Measurable Z := by
    refine measurable_pi_iff.mpr fun t => ?_
    have hT : Measurable fun w : MarkovProcess.ContinuousPath ℝ =>
        (postLastZeroLevel d w + (t : ℝ)).toNNReal :=
      ((measurable_postLastZeroLevel d).add_const _).real_toNNReal
    have hev : Measurable fun ω => Y ω ((L ω + (t : ℝ)).toNNReal) :=
      (MarkovProcess.ContinuousPath.measurable_eval_of_measurable _ hT).comp hY
    exact hev.add (hLm.const_mul d)
  have hZc : ∀ ω, Continuous (Z ω) := fun ω => by
    have hcomp : Continuous fun t : ℝ≥0 => (L ω + (t : ℝ)).toNNReal :=
      continuous_real_toNNReal.comp (continuous_const.add NNReal.continuous_coe)
    exact (((Y ω).continuous).comp hcomp).add continuous_const
  obtain ⟨F, hF, hFZ⟩ := exists_measurable_continuousPath_version Z hZ (ae_of_all P hZc)
  refine ⟨F, hF, ?_⟩
  filter_upwards [hFZ, hYB, hsub] with ω hFω hYω hsubω
  have hpt : ∀ x : ℝ≥0, Y ω x = B x ω := fun x => congrFun hYω x
  have hfun : driftedCoord d (Y ω) = fun u : ℝ => B u.toNNReal ω + d * u := by
    funext u
    simp only [driftedCoord, hpt]
  have htendY : Tendsto (driftedCoord d (Y ω)) atTop atTop := by
    rw [hfun]
    exact tendsto_add_pos_drift_of_sublinear (fun t => B t.toNNReal ω) d hd hsubω
  have hLω : L ω = MatedCRTHarmonic.MatedCRT.lastZeroR (fun u : ℝ => B u.toNNReal ω + d * u) := by
    show postLastZeroLevel d (Y ω) = _
    rw [postLastZeroLevel_eq_lastZeroR (Y ω) htendY, hfun]
  intro t
  have hF_t : F ω t = Y ω ((L ω + (t : ℝ)).toNNReal) + d * L ω := congrFun hFω t
  rw [hF_t]
  simp only [referenceConeConditionedPath, ← hdd, hpt]
  rw [hLω]
  ring

/-- Conditional identification of the standalone post-last-zero reference process. Given the
staged, cited DMS Remark 4.4 input `hR` (`MatedCRT.Proposed.DMS14Remark44PostLastZeroLaw`), a
Brownian motion with measurable coordinates (`hBm`) and almost surely sublinear growth (`hsub`,
a named premise, not derived here) has a measurable continuous-path version of the explicit
reference process whose law is the weak-limit conditioned law. The law identity is the premise
`hR`; the path identity is proved. -/
theorem exists_referenceConeConditionedPath_law_of_remark44
    (hR : MatedCRT.Proposed.DMS14Remark44PostLastZeroLaw)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hsub : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => B t.toNNReal ω / t) atTop (𝓝 0)) :
    ∃ F : Ω → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P.map F) := by
  have hd : 0 < MatedCRTHarmonic.MatedCRT.lqgQ γ - γ :=
    MatedCRT.Proposed.lqgQ_sub_pos_of_lt_two hγ0 hγ2
  obtain ⟨F, hF, hFid⟩ :=
    exists_measurable_referenceConeConditionedPath hd B hBm hB.cont hsub
  exact ⟨F, hF, hFid, hR γ hγ0 hγ2 Ω P B F hB hF hFid⟩

end MatedCRT.Sec1