import MatedCRT.FirstPass.Derived.AnnealedWalksStartLawIntegral
import LatticeProb.Prob.ConditionalLawCloseJointConvergence

/-!
# Joint convergence of the datum and the annealed embedded walk

If the data `D_n` converge in law under `S.P`, and the quenched walk law `Q^{ε_n}(k_n(ω))` from the random vertex
is close in Lévy–Prokhorov distance, in probability under the annealed laws, to a continuous function `π (D_n)` of
the datum, then the pair `(D_n, X_n)` of the datum and the interpolated embedded walk converges in law to
`νD ⊗ₘ π`.  This is the hypothesis `hlaw` of the Markov step `ae_markovAt_of_walk_markov_step_at`.

* `tendsto_integral_annealedWalksAt_of_levyProkhorov_close`: the statement above, for the annealed laws
  `annealedWalksAt`; the proof applies
  `LatticeProb.tendsto_integral_integral_of_tendstoInMeasure_levyProkhorovDist` on the product space and the
  identity `integral_annealedWalksAt_integral_walkPathLaw_eq`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb Preorder
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Joint convergence in law of the datum and the annealed embedded walk from a close conditional law.**
Let `D_n = d n` converge in law under `S.P` to `νD`, `π : S₀ → ProbabilityMeasure C(ℝ≥0, ℂ)` continuous, and
assume the Lévy–Prokhorov distance between the quenched walk law `Q^{ε_n}(k_n)` and `π (D_n)` tends to `0` in
probability under `annealedWalksAt`.  Then `(D_n, X_n)` converges in law to `νD ⊗ₘ κ₀` for the kernel
`κ₀ s = π s`. -/
theorem tendsto_integral_annealedWalksAt_of_levyProkhorov_close
    {S₀ : Type*} [PseudoMetricSpace S₀] [SecondCountableTopology S₀] [MeasurableSpace S₀]
    [BorelSpace S₀]
    [MeasurableSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, ℂ)))]
    [BorelSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, ℂ)))]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) {k : ℕ → Ω → ℤ}
    (hk : ∀ n, Measurable (k n)) {v : ℕ → Ω → ℤ → ℂ} (hv : ∀ n, Measurable (v n)) {m : ℕ → ℝ}
    (hm : ∀ n, 0 < m n) {d : ℕ → Ω → S₀} (hd : ∀ n, Measurable (d n))
    {νD : Measure S₀} [IsProbabilityMeasure νD]
    (hlawD : ∀ f : S₀ →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (d n ω) ∂S.P) atTop (𝓝 (∫ s, f s ∂νD)))
    {π : S₀ → ProbabilityMeasure C(ℝ≥0, ℂ)} (hπ : Continuous π)
    (hclose : TendstoInMeasure (annealedWalksAt hS ε hk)
      (fun n (p : ℕ → Ω × (ℕ → ℤ)) => levyProkhorovDist
        (walkPathLaw S (v n) (hm n).le (ε n) (k n (p n).1) (p n).1 : Measure C(ℝ≥0, ℂ))
        (π (d n (p n).1) : Measure C(ℝ≥0, ℂ))) atTop 0)
    {κ₀ : Kernel S₀ C(ℝ≥0, ℂ)} (hκ₀ : ∀ s, κ₀ s = (π s : Measure C(ℝ≥0, ℂ)))
    (g : (S₀ × C(ℝ≥0, ℂ)) →ᵇ ℝ) :
    Tendsto (fun n => ∫ p, g (d n (p n).1, interpPathCM (v n (p n).1) (hm n).le (p n).2)
        ∂annealedWalksAt hS ε hk) atTop (𝓝 (∫ q, g q ∂(νD ⊗ₘ κ₀))) := by
  have : IsMarkovKernel κ₀ := ⟨fun s => by rw [hκ₀ s]; infer_instance⟩
  have hfst : ∀ n, Measurable fun p : ℕ → Ω × (ℕ → ℤ) => (p n).1 := fun n =>
    measurable_fst.comp (measurable_pi_apply n)
  have h := LatticeProb.tendsto_integral_integral_of_tendstoInMeasure_levyProkhorovDist
    (P := annealedWalksAt hS ε hk) (D := fun n p => d n (p n).1)
    (fun n => ((hd n).comp (hfst n)).aemeasurable)
    (κ := fun n p => walkPathLaw S (v n) (hm n).le (ε n) (k n (p n).1) (p n).1)
    (fun n => (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.measurable.comp
      ((measurable_walkPathLaw_start hS (hv n) (hm n).le (ε n) (hk n)).comp (hfst n))).aemeasurable)
    hπ (ν := νD) (tendsto_integral_annealedWalksAt_comp_fst hS ε hk hd hlawD) hclose g
  have hint : ∫ q, g q ∂(νD ⊗ₘ κ₀) = ∫ s, ∫ x, g (s, x) ∂(π s : Measure C(ℝ≥0, ℂ)) ∂νD := by
    rw [Measure.integral_compProd (Integrable.of_bound g.continuous.measurable.aestronglyMeasurable
      ‖g‖ (Filter.Eventually.of_forall fun q => by simpa using g.norm_coe_le_norm _))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [hκ₀ s]
  rw [hint]
  refine h.congr fun n => ?_
  exact integral_annealedWalksAt_integral_walkPathLaw_eq hS ε hk hv hm hd g n

end MatedCRT.FirstPass.Derived
