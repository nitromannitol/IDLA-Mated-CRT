import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ContinuumModulus
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RetractionEstimate
import MatedCRT.Draft.Section3DirichletCorrected
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.FiniteDomainComplete
import MatedCRT.Steps.Sec2.ExpectedExitTimeExplicitBound

/-! Continuum Dirichlet data on a closed disk, corrected paper lines 1394–1412. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set _root_.HarmonicBalls MarkovProcess InnerProductSpace
open scoped ENNReal NNReal

/-- The projected boundary candidate solves the continuum Dirichlet problem
and is Hölder continuous up to the boundary, under volume growth. -/
theorem dirichletLimit_projected_ae_properties
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) (hψb : ∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M)
    (hψh : IsHolderContinuousOn ψ (ball z r))
    (hφ : IsHolderContinuousOn φ (closedBall z r)) :
    ∀ᵐ ω ∂S.P,
      ContinuousOn (dirichletLimit S r z ψ (fun x => φ (ballRetraction z r x)) ω) (closedBall z r) ∧
      HasLaplacian (dirichletLimit S r z ψ (fun x => φ (ballRetraction z r x)) ω)
        ((S.μ ω).withDensity fun x => ENNReal.ofReal (S.c₀ * ψ x))
        ((S.μ ω).withDensity fun x => ENNReal.ofReal (-(S.c₀ * ψ x))) (ball z r) ∧
      (∀ x ∈ sphere z r, dirichletLimit S r z ψ (fun x => φ (ballRetraction z r x)) ω x = φ x) ∧
      IsHolderContinuousOn (dirichletLimit S r z ψ (fun x => φ (ballRetraction z r x)) ω) (closedBall z r) := by
  let φ' := fun x => φ (ballRetraction z r x)
  have hφ' : ∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ' (closedBall z (r + s)) :=
    ⟨1, by norm_num, holder_ballRetraction hr (by linarith) z hφ⟩
  obtain ⟨M, hM⟩ := hψb
  obtain ⟨Cψ, χψ, hχψ, -, hHψ⟩ := hψh
  have hψc : ContinuousOn ψ (ball z r) := hHψ.continuousOn hχψ
  obtain ⟨s, hs, Cφ, χφ, hχφ, hχφ1, hHφ⟩ := hφ'
  have hφc : ContinuousOn φ' (closedBall z r) :=
    (hHφ.continuousOn hχφ).mono (closedBall_subset_closedBall (by linarith))
  have hφs : ContinuousOn φ' (sphere z r) := hφc.mono sphere_subset_closedBall
  have hrepr := dirichletLimit_ae_poisson_sub_green 𝒮 hγ hγ2 S hS hr ψ φ' hφc
  obtain ⟨-, -, hu⟩ := brownianDirichletDisc hr ⟨s, hs, Cφ, χφ, hχφ, hχφ1, hHφ⟩
  have hPEh : IsHolderContinuousOn (discPoissonExtension φ' z r) (closedBall z r) := by
    convert hu using 1
    funext x
    exact (brownianExitCandidate_eq_discPoissonExtension hr hφc x).symm
  have hPEc : ContinuousOn (discPoissonExtension φ' z r) (closedBall z r) :=
    continuousOn_discPoissonExtension hr hφs
  filter_upwards [hrepr, hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 hρ1, hS.isLQGMeasure]
    with ω hid hV hμ
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  obtain ⟨βm, βp, hVω⟩ := hV
  change ContinuousOn (dirichletLimit S r z ψ φ' ω) _ ∧ _
  rw [hid]
  have hG := greenPart_integrable_holder hVω hr hball hψc hM
  obtain ⟨CG, tG, htG, -, hHG⟩ := hG.2
  refine ⟨hPEc.sub (continuousOn_const.mul (hHG.continuousOn htG)), ?_, ?_,
    hPEh.sub_const_mul isBounded_closedBall hG.2 S.c₀⟩
  · have h1 := hasLaplacian_zero_of_harmonicOnNhd isOpen_ball
      (harmonicOnNhd_discPoissonExtension (hφs.circleIntegrable hr.le))
    have h2 := greenPart_hasLaplacian hVω hr hball hψc hM S.c₀_nonneg
    have h3 := hasLaplacian_add h1 h2
    rw [zero_add, zero_add] at h3
    have hfun : (fun x => discPoissonExtension φ' z r x -
        S.c₀ * ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂S.μ ω) =
        fun x => discPoissonExtension φ' z r x +
          -(S.c₀ * ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂S.μ ω) :=
      funext fun x => sub_eq_add_neg _ _
    rw [hfun]
    exact h3
  · intro x hx
    have hxn := notMem_ball_of_mem_sphere hx
    simp only [discPoissonExtension_of_notMem hxn, greenPart_eq_zero_of_notMem hxn, mul_zero, sub_zero]
    exact congrArg φ (ballRetraction_of_mem z hr (sphere_subset_closedBall hx))

/-- The discrete equations and regularity assumptions for the corrected
Dirichlet problem. -/
def ProjectedDirichletData {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (r : ℝ) (z : ℂ) (ψ φ : ℂ → ℝ) (F : ℝ → Ω → ℤ → ℝ) : Prop :=
  (∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M) ∧
  IsHolderContinuousOn ψ (ball z r) ∧ IsHolderContinuousOn φ (closedBall z r) ∧
  (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
    (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
      matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
    ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
      F ε ω b = S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) b)))

/-- Corrected Lemma 3.5, Steps 1–2, paper lines 1532–1574: local uniform
convergence to the projected continuum candidate. This remains open. -/
def ProjectedDirichletInteriorStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ φ : ℂ → ℝ) (F : ℝ → Ω → ℤ → ℝ), ProjectedDirichletData S r z ψ φ F →
  ∀ r' : ℝ, 0 < r' → r' < r →
  TendstoUniformlyOnInProbability S.P (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω))
    (dirichletLimit S r z ψ (fun x => φ (ballRetraction z r x))) (closedBall z r')

/-- Corrected Lemma 3.5, Step 3, paper lines 1575–1595: the boundary-layer
barrier for projected Dirichlet data. This remains open. -/
def ProjectedDirichletBoundaryStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ φ : ℂ → ℝ) (F : ℝ → Ω → ℤ → ℝ), ProjectedDirichletData S r z ψ φ F →
  ∀ δ : ℝ, 0 < δ → ∀ e : ℝ≥0∞, 0 < e → ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
  ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    S.P {ω | ∃ x ∈ closedBall z r \ closedBall z r',
      δ < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        dirichletLimit S r z ψ (fun y => φ (ballRetraction z r y)) ω x|} ≤ e

/-- Corrected Lemma 3.5, Step 1, paper lines 1532–1545: pointwise convergence
for projected Dirichlet data. This remains open. -/
def ProjectedDirichletPointwiseStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ φ : ℂ → ℝ) (F : ℝ → Ω → ℤ → ℝ), ProjectedDirichletData S r z ψ φ F →
  ∀ y ∈ ball z r, TendstoInProbability S.P
    (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω) y)
    (fun ω => dirichletLimit S r z ψ (fun x => φ (ballRetraction z r x)) ω y)

/-- Volume growth gives a probability modulus for the projected continuum
candidate, independently of the discrete harmonic convergence statement. -/
theorem projectedDirichletLimit_modulus_of_volumeGrowth
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) (hψb : ∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M)
    (hψh : IsHolderContinuousOn ψ (ball z r)) (hφ : IsHolderContinuousOn φ (closedBall z r))
    {r' : ℝ} (hr'r : r' < r) {t : ℝ} (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ S.P {ω | ∃ x ∈ closedBall z r', ∃ y ∈ closedBall z r', dist x y < δ ∧
      t < |dirichletLimit S r z ψ (fun x => φ (ballRetraction z r x)) ω x -
        dirichletLimit S r z ψ (fun x => φ (ballRetraction z r x)) ω y|} ≤ e := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  let φ' := fun x => φ (ballRetraction z r x)
  obtain ⟨M, hM⟩ := hψb
  obtain ⟨Cψ, χψ, hχψ, -, hHψ⟩ := hψh
  have hψc : ContinuousOn ψ (ball z r) := hHψ.continuousOn hχψ
  obtain ⟨Cφ, χφ, hχφ, -, hHφ⟩ := holder_ballRetraction hr (by linarith : 0 ≤ r) z hφ
  have hφc : ContinuousOn φ' (closedBall z r) := hHφ.continuousOn hχφ
  have hrepr := dirichletLimit_ae_poisson_sub_green 𝒮 hγ hγ2 S hS hr ψ φ' hφc
  apply pointwiseMeasurable_modulus_small_in_probability S.P (closedBall z r')
    (isCompact_closedBall z r') (dirichletLimit S r z ψ φ') ?_ ?_ ht he
  · intro x hx
    have hx' : x ∈ closedBall z r := closedBall_subset_closedBall hr'r.le hx
    have hpot := hS.aemeasurable_weightedGreenPotential h27 hγ hγ2 hρ1 hr hball hx' hψc hM
    apply (aemeasurable_const.sub (aemeasurable_const.mul hpot)).congr
    filter_upwards [hrepr] with ω hω
    exact (congrFun hω x).symm
  · filter_upwards [hrepr, hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 hρ1,
      hS.isLQGMeasure] with ω hω hv hm
    let : IsLocallyFiniteMeasure (S.μ ω) := hm.isLocallyFiniteMeasure
    obtain ⟨βm, βp, hv⟩ := hv
    rw [hω]
    have hpc := continuousOn_discPoissonExtension hr (hφc.mono sphere_subset_closedBall)
    obtain ⟨C, χ, hχ, -, hp⟩ := (greenPart_integrable_holder hv hr hball hψc hM).2
    exact (hpc.sub (continuousOn_const.mul (hp.continuousOn hχ))).mono
      (closedBall_subset_closedBall hr'r.le)

/-- Pointwise convergence and the finite-domain estimates imply local uniform
convergence for the corrected projected boundary data. -/
theorem projectedDirichletInteriorStep_of_pointwise_and_estimates
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (hfinite : FiniteDomainDirichletRepresentation) (hP : ProjectedDirichletPointwiseStep 𝒮) :
    ProjectedDirichletInteriorStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ F hdata r' hr' hr'r
  obtain ⟨hψb, hψh, hφ, hF⟩ := hdata
  let φ' := fun x => φ (ballRetraction z r x)
  have hφ' : ∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ' (closedBall z (r + s)) :=
    ⟨1, by norm_num, holder_ballRetraction hr (by linarith) z hφ⟩
  have h217 := boundedExitTimeRV_of_steps h27
  have h219 := expectedExitTimeExplicitBound_of_steps h217 h218
  have h31 := discretePotentialTightnessPrepared_of_inputs hm h217 h218 hH
  have h213 := maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)
  have hM := dirichletDiscreteModulusPreparedStep_of_estimates 𝒮 hm h218 h217 hfinite
  exact uniformInProbability_of_separate_moduli S.P (closedBall z r') (isCompact_closedBall z r')
    (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω)) (dirichletLimit S r z ψ φ')
    (fun y hy => hP γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ F ⟨hψb, hψh, hφ, hF⟩ y
      (mem_ball.2 ((mem_closedBall.1 hy).trans_lt hr'r)))
    (hM h31 h213 h219 h28 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ' hψb hψh hφ' F hF r' hr' hr'r)
    (fun t ht e he => projectedDirichletLimit_modulus_of_volumeGrowth 𝒮 h27 hγ hγ2 hρ1 S hS hr hball
      ψ φ hψb hψh hφ hr'r ht he)

/-- Corrected Lemma 3.5 follows from volume growth, local convergence and
the boundary-layer barrier. -/
theorem discreteDirichletProblemCorrected_of_projected_steps
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hinterior : ProjectedDirichletInteriorStep 𝒮)
    (hboundary : ProjectedDirichletBoundaryStep 𝒮) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ hψb hψh hφ F hF
  let f := dirichletLimit S r z ψ (fun x => φ (ballRetraction z r x))
  have hdata : ProjectedDirichletData S r z ψ φ F := ⟨hψb, hψh, hφ, hF⟩
  refine ⟨f, dirichletLimit_projected_ae_properties 𝒮 h27 hγ hγ2 hρ1 S hS hr hball ψ φ hψb hψh hφ, ?_⟩
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨r', hr'0, hr'r, hb⟩ := hboundary γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball
    ψ φ F hdata δ hδ (e / 2) he2
  have hi := ENNReal.tendsto_nhds_zero.1
    (hinterior γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ F hdata r' hr'0 hr'r δ hδ) (e / 2) he2
  filter_upwards [hi, hb] with ε hi hb
  calc
    S.P {ω | ∃ x ∈ closedBall z r,
      δ < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x - f ω x|} ≤
      S.P ({ω | ∃ x ∈ closedBall z r',
        δ < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x - f ω x|} ∪
      {ω | ∃ x ∈ closedBall z r \ closedBall z r',
        δ < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x - f ω x|}) := by
      apply measure_mono
      rintro ω ⟨x, hx, herr⟩
      by_cases hx' : x ∈ closedBall z r'
      · exact Or.inl ⟨x, hx', herr⟩
      · exact Or.inr ⟨x, ⟨hx, hx'⟩, herr⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hi hb
    _ = e := ENNReal.add_halves e

/-- Corrected Lemma 3.5 from the projected pointwise and boundary-barrier
steps, the finite-domain representation, and the stated estimates. -/
theorem discreteDirichletProblemCorrected_of_pointwise_and_estimates
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (hfinite : FiniteDomainDirichletRepresentation) (hP : ProjectedDirichletPointwiseStep 𝒮)
    (hboundary : ProjectedDirichletBoundaryStep 𝒮) : DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  discreteDirichletProblemCorrected_of_projected_steps 𝒮 h27
    (projectedDirichletInteriorStep_of_pointwise_and_estimates 𝒮 h27 hm h218 hH h28 hfinite hP)
    hboundary

end MatedCRT

#print axioms MatedCRT.dirichletLimit_projected_ae_properties
#print axioms MatedCRT.discreteDirichletProblemCorrected_of_projected_steps
#print axioms MatedCRT.discreteDirichletProblemCorrected_of_pointwise_and_estimates
