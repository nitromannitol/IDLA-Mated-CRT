import MatedCRT.Proofs.Sec4.ConvergenceDivisible.WalkLawMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RescaleMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellDomainMeasurable
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit

/-! # Measurability of the discrete Green kernel and obstacle -/

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The number of visits before exit is jointly measurable in a measurable
random vertex set and a walk path. -/
theorem measurable_visitsBeforeExit_random_set
    {Ω : Type} [MeasurableSpace Ω] (V : Ω → Set ℤ) (hV : Measurable V) (b : ℤ) :
    Measurable (fun p : Ω × (ℕ → ℤ) => visitsBeforeExit (V p.1) b p.2) := by
  classical
  have hmem : ∀ n, MeasurableSet {p : Ω × (ℕ → ℤ) | p.2 n ∈ V p.1} := by
    intro n
    apply measurableSet_setOfPred.mpr
    exact measurable_countable_evaluation (fun p : Ω × (ℕ → ℤ) => p.2 n)
      ((measurable_pi_apply n).comp measurable_snd) (fun k p => k ∈ V p.1)
      (fun k => ((measurable_set_mem k).comp hV).comp measurable_fst)
  have hexit : ∀ n : ℕ, MeasurableSet {p : Ω × (ℕ → ℤ) | (n : ℕ∞) < vExitTime (V p.1) p.2} := by
    intro n
    have heq : {p : Ω × (ℕ → ℤ) | (n : ℕ∞) < vExitTime (V p.1) p.2} =
        ⋂ j ∈ Finset.range (n + 1), {p : Ω × (ℕ → ℤ) | p.2 j ∈ V p.1} := by
      ext p
      simp [ConstantOrderDiv.lt_vExitTime_iff']
    rw [heq]
    exact Finset.measurableSet_biInter _ (fun j _ => hmem j)
  unfold visitsBeforeExit
  apply Measurable.tsum
  intro n
  have hb : MeasurableSet {p : Ω × (ℕ → ℤ) | p.2 n = b} := by
    change MeasurableSet ((fun p : Ω × (ℕ → ℤ) => p.2 n) ⁻¹' ({b} : Set ℤ))
    exact ((measurable_pi_apply n).comp measurable_snd) (measurableSet_singleton b)
  exact Measurable.ite ((hexit n).inter hb) measurable_const measurable_const

/-- Green functions for a measurable random vertex set are measurable. -/
theorem MatedCRTEnv.IsValid.measurable_greenFn
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (V : Ω → Set ℤ) (hV : Measurable V) (a b : ℤ) :
    Measurable (fun ω => greenFn (S.mult ε ω) (V ω) a b) := by
  let κ : Kernel Ω (ℕ → ℤ) := ⟨fun ω => srwLaw (S.mult ε ω) a, hS.measurable_srwLaw ε a⟩
  have : IsMarkovKernel κ := ⟨fun ω => isProbabilityMeasure_srwLaw _ _⟩
  have h := (measurable_visitsBeforeExit_random_set V hV b).lintegral_kernel_prod_right' (κ := κ)
  exact h.ennreal_toReal

/-- The degree-normalized Green kernel for a measurable random vertex set
is measurable. -/
theorem MatedCRTEnv.IsValid.measurable_greenKernel
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (V : Ω → Set ℤ) (hV : Measurable V) (a b : ℤ) :
    Measurable (fun ω => greenKernel (S.mult ε ω) (V ω) a b) := by
  unfold greenKernel
  exact (hS.measurable_greenFn ε V hV a b).div
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hS.measurable_mdeg ε b))

/-- The discrete obstacle has a measurable version at each vertex. -/
theorem MatedCRTEnv.IsValid.exists_measurable_matedObstacle
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε ρ t : ℝ) (a : ℤ) :
    ∃ f : Ω → ℝ, Measurable f ∧ ∀ᵐ ω ∂S.P,
      f ω = matedObstacle (S.mult ε ω) ε (S.η ω) ρ t a := by
  obtain ⟨V, hV, hVa⟩ := hS.exists_measurable_interiorCellVertices ε (Metric.ball 0 ρ)
    (Or.inl Metric.isOpen_ball)
  refine ⟨fun ω => -(t / ε) * greenKernel (S.mult ε ω) (V ω) 0 a,
    measurable_const.mul (hS.measurable_greenKernel ε V hV 0 a), ?_⟩
  filter_upwards [hVa] with ω hω
  simp only [matedObstacle, ballInterior, hω]

/-- The rescaled discrete obstacle has a jointly measurable version. -/
theorem MatedCRTEnv.IsValid.exists_measurable_rescaled_matedObstacle
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (ρ t m : ℝ) :
    ∃ f : Ω × ℂ → ℝ, Measurable f ∧ ∀ᵐ ω ∂S.P, ∀ x,
      f (ω, x) = rescale m ε (S.η ω)
        (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t) x := by
  classical
  choose g hg hga using fun a => hS.exists_measurable_matedObstacle ε ρ t a
  let u : Ω → ℤ → ℝ := fun ω a => g a ω
  obtain ⟨f, hf, hfa⟩ := hS.exists_measurable_rescale hε m u hg
  refine ⟨f, hf, ?_⟩
  filter_upwards [hfa, ae_all_iff.mpr hga] with ω h1 h2
  intro x
  rw [h1 x]
  congr 1
  funext a
  exact h2 a

end MatedCRT
