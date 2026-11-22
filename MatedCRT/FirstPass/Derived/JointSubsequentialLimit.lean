import LatticeProb.Prob.SubsequentialWeakLimit
import LatticeProb.Prob.TightnessProduct
import LatticeProb.Prob.TightnessPushforward

/-!
# Joint subsequential weak limits with an extra coordinate of fixed law

If the laws of pairs `(D, W n)` of random elements of Polish spaces converge weakly to `ν`, and `Y` is a further
random element of a Polish space, then the laws of `((D, Y), W n)` are tight: the laws of `(D, Y)` do not depend
on `n`, and a weakly convergent sequence of probability measures is tight. By Prokhorov's theorem they converge
along a subsequence, and the image of the limit under forgetting `Y` is `ν`.

## Main statements

* `isTightMeasureSet_range_of_tendsto_integral`: a weakly convergent sequence of probability measures on a Polish
  space is tight.
* `exists_subseq_tendsto_integral_prod_of_tendsto_integral`: joint subsequential limits with the extra
  coordinate, projecting to the given limit.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped BoundedContinuousFunction

namespace MatedCRT

section Tightness

variable {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]

/-- **A weakly convergent sequence of probability measures on a Polish space is tight.** Its range together with
its limit is compact for the topology of convergence in distribution, so the closure of the range is compact. -/
theorem isTightMeasureSet_range_of_tendsto_integral (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (h : ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))) :
    IsTightMeasureSet (range μ) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable E
  let q : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, inferInstance⟩
  let q₀ : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hq : Tendsto q atTop (𝓝 q₀) := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 h
  have hK := hq.isCompact_insert_range
  have hcl : IsCompact (closure (range q)) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal (subset_insert _ _) hK.isClosed)
  convert isTightMeasureSet_of_isCompact_closure hcl using 1
  ext m
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨q n, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩

end Tightness

section Extraction

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A B C : Type*} [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace C] [PolishSpace C] [MeasurableSpace C] [BorelSpace C]

/-- **Joint subsequential limits with an extra coordinate.** Let `D`, `Y` be random elements of Polish spaces and
`W n` almost everywhere measurable random elements of a Polish space such that the laws of `(D, W n)` converge
weakly to `ν`. Then along a subsequence the laws of `((D, Y), W n)` converge weakly to a probability measure `ν₂`
whose image under `((d, y), w) ↦ (d, w)` is `ν`. -/
theorem exists_subseq_tendsto_integral_prod_of_tendsto_integral {D : Ω → A} (hD : Measurable D)
    {Y : Ω → B} (hY : Measurable Y) {W : ℕ → Ω → C} (hW : ∀ n, AEMeasurable (W n) P)
    {ν : Measure (A × C)} [IsProbabilityMeasure ν]
    (hconv : ∀ f : (A × C) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D ω, W n ω) ∂P) atTop (𝓝 (∫ p, f p ∂ν))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν₂ : Measure ((A × B) × C), IsProbabilityMeasure ν₂ ∧
      (∀ f : ((A × B) × C) →ᵇ ℝ,
        Tendsto (fun k => ∫ ω, f ((D ω, Y ω), W (φ k) ω) ∂P) atTop (𝓝 (∫ q, f q ∂ν₂))) ∧
      ν₂.map (fun q => (q.1.1, q.2)) = ν := by
  have hDY : Measurable fun ω => (D ω, Y ω) := hD.prodMk hY
  have hJ : ∀ n, AEMeasurable (fun ω => ((D ω, Y ω), W n ω)) P := fun n =>
    hDY.aemeasurable.prodMk (hW n)
  have hJ' : ∀ n, AEMeasurable (fun ω => (D ω, W n ω)) P := fun n => hD.aemeasurable.prodMk (hW n)
  let μ : ℕ → Measure ((A × B) × C) := fun n => P.map fun ω => ((D ω, Y ω), W n ω)
  have : ∀ n, IsProbabilityMeasure (μ n) := fun n =>
    (inferInstance : IsProbabilityMeasure (P.map fun ω => ((D ω, Y ω), W n ω)))
  let μ' : ℕ → Measure (A × C) := fun n => P.map fun ω => (D ω, W n ω)
  have : ∀ n, IsProbabilityMeasure (μ' n) := fun n =>
    (inferInstance : IsProbabilityMeasure (P.map fun ω => (D ω, W n ω)))
  have hint' : ∀ (f : (A × C) →ᵇ ℝ) (n : ℕ), ∫ p, f p ∂μ' n = ∫ ω, f (D ω, W n ω) ∂P := fun f n =>
    integral_map (hJ' n) f.continuous.aestronglyMeasurable
  have hint : ∀ (f : ((A × B) × C) →ᵇ ℝ) (n : ℕ), ∫ q, f q ∂μ n = ∫ ω, f ((D ω, Y ω), W n ω) ∂P :=
    fun f n => integral_map (hJ n) f.continuous.aestronglyMeasurable
  have hμ' : IsTightMeasureSet (range μ') :=
    isTightMeasureSet_range_of_tendsto_integral μ' ν fun f => by
      simp only [hint']
      exact hconv f
  have h1 : IsTightMeasureSet ((fun m : Measure ((A × B) × C) => m.map Prod.fst) '' range μ) := by
    refine (isTightMeasureSet_singleton_of_innerRegular (μ := P.map fun ω => (D ω, Y ω))).subset ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    refine mem_singleton_iff.2 ?_
    change (P.map fun ω => ((D ω, Y ω), W n ω)).map Prod.fst = P.map fun ω => (D ω, Y ω)
    rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hJ n)]
    rfl
  have h2 : IsTightMeasureSet ((fun m : Measure ((A × B) × C) => m.map Prod.snd) '' range μ) := by
    refine (LatticeProb.isTightMeasureSet_image_map hμ' continuous_snd measurable_snd).subset ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    refine ⟨μ' n, ⟨n, rfl⟩, ?_⟩
    change (P.map fun ω => (D ω, W n ω)).map Prod.snd = (P.map fun ω => ((D ω, Y ω), W n ω)).map Prod.snd
    rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable (hJ' n),
      AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable (hJ n)]
    rfl
  obtain ⟨φ, hφ, ν₂, hν₂, hlim⟩ :=
    LatticeProb.exists_subseq_tendsto_integral_of_isTightMeasureSet μ (LatticeProb.isTightMeasureSet_prod h1 h2)
  refine ⟨φ, hφ, ν₂, hν₂, fun f => ?_, ?_⟩
  · simpa only [hint] using hlim f
  · have hpr : Continuous fun q : (A × B) × C => (q.1.1, q.2) :=
      (continuous_fst.comp continuous_fst).prodMk continuous_snd
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map hpr.aemeasurable f.continuous.aestronglyMeasurable]
    have h₁ := hlim (f.compContinuous ⟨fun q : (A × B) × C => (q.1.1, q.2), hpr⟩)
    simp only [hint] at h₁
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] at h₁
    exact tendsto_nhds_unique h₁ ((hconv f).comp hφ.tendsto_atTop)

end Extraction

end MatedCRT
