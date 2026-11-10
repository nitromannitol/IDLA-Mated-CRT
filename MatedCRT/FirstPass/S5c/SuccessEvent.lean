import MatedCRT.Proofs.IDLA.DiscreteClusterMeasurable
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentGreen
import MatedCRT.Proofs.Measurability.EnvSigmaCore

/-!
# FIRST PASS, Lemma 5.3 (three-inputs §7, reduced): null measurability of the success event `E ε`

The success event of `MeanValueSurplusLowerStep` (Proofs/Sec5/MeanValueInequality/SurplusSteps.lean:209) is a countable
intersection over `a ∈ ℤ` of the events `{a ∈ cluster → (δ < dist_a → c/ε ≤ LSS_a + t/ε G_a)}`. Each piece is null
measurable: cluster membership by `nullMeasurableSet_mem_matedDiscreteCluster`; the discrete least supersolution `LSS_a`
(`aemeasurable_matedLeastSupersolution`) and the Green kernel `G_a = greenKernel (mult) (ballInterior ε η ρ) 0 a`
(`exists_envSigma_measurable_greenKernel`, a.e. equal to an envSigma-measurable version) are a.e. measurable; `c` is
envSigma-measurable hence a.e. measurable. The distance event `δ < infDist (vertexPoint ε η a) (frontier (fillCells …))`
is the one remaining geometric input, taken here as the explicit hypothesis `hdist`.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric

variable {Ω : Type} [MeasurableSpace Ω]

/-- The implication `ω ∈ A → ω ∈ B → ω ∈ C` of three null measurable events is null measurable. -/
theorem nullMeasurableSet_imp_imp {P : Measure Ω} {A B C : Set Ω} (hA : NullMeasurableSet A P)
    (hB : NullMeasurableSet B P) (hC : NullMeasurableSet C P) :
    NullMeasurableSet {ω | ω ∈ A → ω ∈ B → ω ∈ C} P := by
  have heq : {ω | ω ∈ A → ω ∈ B → ω ∈ C} = Aᶜ ∪ (Bᶜ ∪ C) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
    tauto
  rw [heq]
  exact hA.compl.union (hB.compl.union hC)

/-- A countable intersection `⋂ a, {ω | a ∈ D ω → Q a ω}` is the event `{ω | ∀ a ∈ D ω, Q a ω}`; it is null measurable
when each member is. -/
theorem nullMeasurableSet_forall_mem_of {P : Measure Ω} {D : Ω → Set ℤ} {Q : ℤ → Ω → Prop}
    (h : ∀ a : ℤ, NullMeasurableSet {ω | a ∈ D ω → Q a ω} P) :
    NullMeasurableSet {ω | ∀ a ∈ D ω, Q a ω} P := by
  have heq : {ω | ∀ a ∈ D ω, Q a ω} = ⋂ a : ℤ, {ω | a ∈ D ω → Q a ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact NullMeasurableSet.iInter h

/-- The vertex-`a` piece of the success event is null measurable (given the distance event at `a`). -/
theorem nullMeasurableSet_vertex_imp {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ' : γ < 2) {ε : ℝ} (hε : 0 < ε) (ρ t δ : ℝ) (ht : 0 < t)
    (c : Ω → ℝ) (hc : Measurable[S.envSigma] c)
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {x | S.mult ε ω b x ≠ 0}.Finite) (a : ℤ)
    (hdist : NullMeasurableSet {ω | a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t →
        δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)))} S.P) :
    NullMeasurableSet {ω | a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t →
      δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) →
      c ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
        t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a} S.P := by
  have hmem : NullMeasurableSet {ω | a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t} S.P :=
    hS.nullMeasurableSet_mem_matedDiscreteCluster hγ hγ' hε ρ t ht a hlf
  have hc' : AEMeasurable c S.P := hS.aemeasurable_of_envSigma hc
  have hL : AEMeasurable (fun ω => matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a) S.P :=
    hS.aemeasurable_matedLeastSupersolution hγ hγ' hε ρ t ht a hlf
  have hG : AEMeasurable (fun ω => greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a) S.P := by
    obtain ⟨g, hgm, hg⟩ := hS.exists_envSigma_measurable_greenKernel ε (ball 0 ρ) (Or.inl isOpen_ball)
      (fun _ => (0 : ℤ)) measurable_const
    refine AEMeasurable.congr (hS.aemeasurable_of_envSigma (hgm a)) ?_
    filter_upwards [hg] with ω hω
    exact hω a
  have hineq : NullMeasurableSet {ω | c ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
      t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a} S.P :=
    nullMeasurableSet_le (hc'.div_const ε) (hL.add (hG.const_mul (t / ε)))
  refine NullMeasurableSet.congr (nullMeasurableSet_imp_imp hmem hdist hineq)
    (Filter.eventuallyEqSet_iff.2 (Filter.Eventually.of_forall fun ω => ?_))
  try simp only [mem_ofPred_eq]
  tauto

/-- **Fixed-mesh null measurability of the success event** (three-inputs §7, reduced to the distance events `hdist`):
for every `ε > 0` the event `E ε` of `MeanValueSurplusLowerStep` is null measurable. -/
theorem nullMeasurableSet_success {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ' : γ < 2) {ε : ℝ} (hε : 0 < ε) (ρ t δ : ℝ) (ht : 0 < t)
    (c : Ω → ℝ) (hc : Measurable[S.envSigma] c)
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {x | S.mult ε ω b x ≠ 0}.Finite)
    (hdist : ∀ a : ℤ, NullMeasurableSet {ω | a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t →
        δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)))} S.P) :
    NullMeasurableSet {ω | ∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
      δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) →
      c ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
        t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a} S.P :=
  nullMeasurableSet_forall_mem_of (Q := fun a ω =>
      δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) →
      c ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
        t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a)
    (fun a => nullMeasurableSet_vertex_imp hS hγ hγ' hε ρ t δ ht c hc hlf a (hdist a))

end MatedCRT.S5c
