import MatedCRT.Proofs.Field.WholePlaneLateralCov
import MatedCRT.Proofs.Field.WholePlaneRadialLaw
import MatedCRT.Defs.QuantumCone

/-!
# The centred radial process of a quantum cone (eq:gff, cone side)

For a cone field `h = (hC, hcirc)` (`IsQuantumCone γ P hC hcirc`, Definition 2.1) the radial process
`t ↦ h_{e^{-t}}(0)` has the law `B_t + γ t` of its first component (`radial_law`, `map_fst_quantumConeRadialLaw`).
The centred radial process `coneRadW γ hcirc u = h_{e^{-max u 0}}(0) - γ max u 0` has, on `ℝ≥0 → ℝ`, the law of a
standard Brownian motion (`cone_radial_path_law`). Hence it is a centred Gaussian process with covariance
`min(max u 0, max v 0)` and satisfies `IsRadialLevelData` (`coneRadW_radialData`).
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Topology Set Real Metric HarmonicBalls MarkovProcess
open scoped NNReal

/-- The centred radial process of a cone sample on `ℝ≥0`: `t ↦ h_{e^{-t}}(0) - γ t`. -/
noncomputable def conePath (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) : ℝ≥0 → ℝ :=
  fun t => hcirc (Real.exp (-(t : ℝ))) 0 - γ * (t : ℝ)

/-- The centred radial process of a cone sample on `ℝ`: `u ↦ h_{e^{-max u 0}}(0) - γ max u 0`. -/
noncomputable def coneRadW (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (u : ℝ) : ℝ :=
  hcirc (Real.exp (-(max u 0))) 0 - γ * max u 0

lemma measurable_path_coord : Measurable fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t :=
  Measurable.of_eval fun t => ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t

lemma coneRadW_eq_conePath (u : ℝ) (hc : ℝ → ℂ → ℝ) (γ : ℝ) :
    coneRadW γ hc u = conePath γ hc (Real.toNNReal u) := by
  simp only [coneRadW, conePath, Real.coe_toNNReal']

section Cone

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {γ : ℝ}

omit [IsProbabilityMeasure P] in
/-- **The centred radial process of a cone is a Brownian motion in law** (first component of Definition 2.1). -/
theorem cone_radial_path_law (hcone : IsQuantumCone γ P hC hcirc)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    P.map (fun ω => fun t : ℝ≥0 => conePath γ (hcirc ω) t) =
      (brownianMotion 0).map (fun w (t : ℝ≥0) => w t) := by
  obtain ⟨ν, hν, hmap⟩ := hcone.radial_law
  have : IsProbabilityMeasure ν := hν.1
  have hcoord1 : ∀ t : ℝ≥0, Measurable fun ω => hcirc ω (Real.exp (-(t : ℝ))) 0 :=
    fun t => hmc _ _ (Real.exp_pos _)
  have hcoord2 : ∀ s : ℝ≥0, Measurable fun ω => hcirc ω (Real.exp (s : ℝ)) 0 :=
    fun s => hmc _ _ (Real.exp_pos _)
  have hR : Measurable fun ω => radialProcess (hcirc ω) :=
    Measurable.prodMk (Measurable.of_eval hcoord1) (Measurable.of_eval hcoord2)
  have hF : P.map (fun ω => fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0) =
      (brownianMotion 0).map (fun w (t : ℝ≥0) => w t + γ * t) := by
    have e : (fun ω => fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0) =
        Prod.fst ∘ (fun ω => radialProcess (hcirc ω)) := rfl
    rw [e, ← Measure.map_map measurable_fst hR, hmap, map_fst_quantumConeRadialLaw]
  have hFm : Measurable fun ω => fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0 :=
    Measurable.of_eval hcoord1
  have hshift : Measurable fun (x : ℝ≥0 → ℝ) (t : ℝ≥0) => x t - γ * t :=
    Measurable.of_eval fun t => (measurable_pi_apply t).sub measurable_const
  have hbr : Measurable fun w : ContinuousPath ℝ => fun t : ℝ≥0 => w t + γ * t :=
    Measurable.of_eval fun t => (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t).add
      measurable_const
  have hP : (fun ω => fun t : ℝ≥0 => conePath γ (hcirc ω) t) =
      (fun x : ℝ≥0 → ℝ => fun t : ℝ≥0 => x t - γ * t) ∘
        (fun ω => fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0) :=
    rfl
  rw [hP, ← Measure.map_map hshift hFm, hF, Measure.map_map hshift hbr]
  congr 1
  funext w t
  simp only [Function.comp_apply]
  ring

/-- The path map of a cone sample is measurable. -/
lemma measurable_conePath (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    Measurable fun ω => fun t : ℝ≥0 => conePath γ (hcirc ω) t :=
  Measurable.of_eval fun t => (hmc (Real.exp (-(t : ℝ))) 0 (Real.exp_pos _)).sub measurable_const

omit [IsProbabilityMeasure P] in
/-- A random variable whose law is that of a Gaussian one is Gaussian (law transfer). -/
lemma hasGaussianLaw_of_map_eq {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [BorelSpace E] {X : Ω → E} {Y : Ω' → E}
    (hXm : AEMeasurable X P) (h : P.map X = Q.map Y) (hY : HasGaussianLaw Y Q) : HasGaussianLaw X P := by
  have : IsGaussian (P.map X) := by
    rw [h]
    exact hY.isGaussian_map
  exact IsGaussian.hasGaussianLaw hXm

omit [IsProbabilityMeasure P] in
/-- The centred radial process of a cone is a centred Gaussian process. -/
theorem coneRadW_gaussian (hcone : IsQuantumCone γ P hC hcirc)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    IsGaussianProcess (fun (u : ℝ) (ω : Ω) => coneRadW γ (hcirc ω) u) P := by
  have hΦ := cone_radial_path_law hcone hmc
  have hΦm := measurable_conePath (γ := γ) hmc
  refine ⟨fun I => ?_⟩
  let G : (ℝ≥0 → ℝ) → (I → ℝ) := fun p i => p (Real.toNNReal (i : ℝ))
  have hG : Measurable G := Measurable.of_eval fun i => measurable_pi_apply _
  have hfun : (fun ω (i : I) => coneRadW γ (hcirc ω) (i : ℝ)) =
      G ∘ (fun ω => fun t : ℝ≥0 => conePath γ (hcirc ω) t) := by
    funext ω i
    simp only [Function.comp_apply, G, coneRadW_eq_conePath]
  have hlaw : P.map (fun ω (i : I) => coneRadW γ (hcirc ω) (i : ℝ)) =
      (brownianMotion 0).map (fun w (i : I) => w (Real.toNNReal (i : ℝ))) := by
    rw [hfun, ← Measure.map_map hG hΦm, hΦ, Measure.map_map hG measurable_path_coord]
    rfl
  have hBG : HasGaussianLaw (fun (w : ContinuousPath ℝ) (i : I) => w (Real.toNNReal (i : ℝ)))
      (brownianMotion 0) :=
    (IsGaussianProcess.comp_right brownian_isGaussianProcess
      (fun i : ℝ => Real.toNNReal i)).hasGaussianLaw I
  exact hasGaussianLaw_of_map_eq (hG.comp hΦm).aemeasurable hlaw hBG

omit [IsProbabilityMeasure P] in
/-- The covariance of the centred radial process: `Cov(W_u, W_v) = min(max u 0, max v 0)`. -/
theorem coneRadW_cov (hcone : IsQuantumCone γ P hC hcirc)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) (u v : ℝ) :
    covariance (fun ω => coneRadW γ (hcirc ω) u) (fun ω => coneRadW γ (hcirc ω) v) P =
      min (max u 0) (max v 0) := by
  have hΦ := cone_radial_path_law hcone hmc
  have hΦm := measurable_conePath (γ := γ) hmc
  have hXm : AEStronglyMeasurable (fun p : ℝ≥0 → ℝ => p (Real.toNNReal u))
      (P.map fun ω => fun t : ℝ≥0 => conePath γ (hcirc ω) t) :=
    (measurable_pi_apply (Real.toNNReal u)).aestronglyMeasurable
  have hYm : AEStronglyMeasurable (fun p : ℝ≥0 → ℝ => p (Real.toNNReal v))
      (P.map fun ω => fun t : ℝ≥0 => conePath γ (hcirc ω) t) :=
    (measurable_pi_apply (Real.toNNReal v)).aestronglyMeasurable
  have h1 := covariance_map hXm hYm hΦm.aemeasurable
  have hX : ((fun p : ℝ≥0 → ℝ => p (Real.toNNReal u)) ∘ fun ω => fun t : ℝ≥0 => conePath γ (hcirc ω) t) =
      fun ω => coneRadW γ (hcirc ω) u := by
    funext ω
    simp only [Function.comp_apply, coneRadW_eq_conePath]
  have hY : ((fun p : ℝ≥0 → ℝ => p (Real.toNNReal v)) ∘ fun ω => fun t : ℝ≥0 => conePath γ (hcirc ω) t) =
      fun ω => coneRadW γ (hcirc ω) v := by
    funext ω
    simp only [Function.comp_apply, coneRadW_eq_conePath]
  rw [hX, hY] at h1
  rw [← h1, hΦ]
  have hXb : AEStronglyMeasurable (fun p : ℝ≥0 → ℝ => p (Real.toNNReal u))
      ((brownianMotion 0).map (fun w (t : ℝ≥0) => w t)) :=
    (measurable_pi_apply (Real.toNNReal u)).aestronglyMeasurable
  have hYb : AEStronglyMeasurable (fun p : ℝ≥0 → ℝ => p (Real.toNNReal v))
      ((brownianMotion 0).map (fun w (t : ℝ≥0) => w t)) :=
    (measurable_pi_apply (Real.toNNReal v)).aestronglyMeasurable
  rw [covariance_map hXb hYb measurable_path_coord.aemeasurable]
  show covariance (fun w : ContinuousPath ℝ => w (Real.toNNReal u))
    (fun w : ContinuousPath ℝ => w (Real.toNNReal v)) (brownianMotion 0) = _
  rw [brownian_covariance]
  simp only [Real.coe_toNNReal']

omit [IsProbabilityMeasure P] in
/-- The centred radial process of a cone has mean zero. -/
theorem coneRadW_mean (hcone : IsQuantumCone γ P hC hcirc)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) (u : ℝ) :
    ∫ ω, coneRadW γ (hcirc ω) u ∂P = 0 := by
  have hΦ := cone_radial_path_law hcone hmc
  have hΦm := measurable_conePath (γ := γ) hmc
  have hev : Measurable fun p : ℝ≥0 → ℝ => p (Real.toNNReal u) := measurable_pi_apply _
  have h1 : ∫ ω, coneRadW γ (hcirc ω) u ∂P =
      ∫ p : ℝ≥0 → ℝ, p (Real.toNNReal u) ∂(P.map fun ω => fun t : ℝ≥0 => conePath γ (hcirc ω) t) := by
    rw [integral_map hΦm.aemeasurable hev.aestronglyMeasurable]
    simp only [coneRadW_eq_conePath]
  rw [h1, hΦ, integral_map measurable_path_coord.aemeasurable hev.aestronglyMeasurable]
  have hmap : ∫ x : ℝ, x ∂((brownianMotion 0).map (fun w : ContinuousPath ℝ => w (Real.toNNReal u)))
      = ∫ w : ContinuousPath ℝ, w (Real.toNNReal u) ∂(brownianMotion 0) :=
    integral_map (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) (Real.toNNReal u)).aemeasurable
      aestronglyMeasurable_id
  show ∫ w : ContinuousPath ℝ, w (Real.toNNReal u) ∂(brownianMotion 0) = 0
  rw [← hmap, brownianMotion_map_eval, integral_id_gaussianReal]

omit [IsProbabilityMeasure P] in
/-- **The centred radial process of a cone is a radial process** (`IsRadialLevelData`) with the Gaussian space
spanned by its values. -/
theorem coneRadW_radialData (hcone : IsQuantumCone γ P hC hcirc)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    IsRadialLevelData P (fun u ω => coneRadW γ (hcirc ω) u)
      (Submodule.span ℝ (Set.range fun u : ℝ => fun ω => coneRadW γ (hcirc ω) u)) where
  meas := fun u => (hmc _ _ (Real.exp_pos _)).sub measurable_const
  mem := fun u => Submodule.subset_span ⟨u, rfl⟩
  const_nonpos := fun u hu => by
    funext ω
    simp only [coneRadW, max_eq_right hu, max_self]
  cont := by
    filter_upwards [hcone.ae_continuousOn_circle] with ω hω
    have hcont : Continuous fun u : ℝ => (Real.exp (-(max u 0)), (0 : ℂ)) :=
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_id.max continuous_const))).prodMk
        continuous_const
    have hmaps : ∀ u : ℝ, (Real.exp (-(max u 0)), (0 : ℂ)) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ) :=
      fun u => ⟨Real.exp_pos _, trivial⟩
    have h := hω.comp_continuous hcont hmaps
    have h2 : Continuous fun u : ℝ => hcirc ω (Real.exp (-(max u 0))) 0 - γ * max u 0 :=
      h.sub (continuous_const.mul (continuous_id.max continuous_const))
    exact h2
  cov := fun u v hu hv => by
    rw [coneRadW_cov hcone hmc u v, max_eq_left hu, max_eq_left hv]

end Cone

end MatedCRT.Field
