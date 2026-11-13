import MatedCRT.FirstPass.Derived.ConeAreaMeasureCode
import MatedCRT.FirstPass.Derived.LargestExitTimeTail

/-!
# Events of the quantum cone measure with probabilities independent of the cone field

The γ-LQG measure `μ_h` of a γ-quantum cone field is almost surely a Borel function of the whole-plane observable
process of the field (`exists_measurable_fieldCode_lqgMeasure_of_isQuantumCone`), and the law of the observable
process is the same for every γ-quantum cone field (`IsQuantumCone.observable_law_eq`). Hence for every Borel set
`A` of measures on `ℂ` the probability of `{μ_h ∈ A}` does not depend on the cone field.

Events such as "every ball `B_δ(z)`, `z ∈ B_ρ(0)`, satisfies a mass bound" quantify over uncountably many centres
and need not be Borel in `μ_h`. They are handled by a sandwich: if a Borel set `B` of measures lies between a
stronger event `E_s`, which has polynomially high probability for every cone field, and the event `E_w` of
interest, then the polynomial bound for `E_w` holds with constants that do not depend on the cone field.

## Main results

* `exists_measurable_lqgMeasure_factor_observable`: `μ_h = Φ(observable process)` almost surely, `Φ` Borel.
* `measure_lqgMeasure_mem_eq`: `P(μ_h ∈ A) = P₀(μ₀ ∈ A)` for Borel `A` and two γ-quantum cone fields.
* `exists_uniform_polyBound_of_sandwich`: the uniform polynomial bound for `E_w` from `E_s ⊆ B ⊆ E_w`.
-/

open MeasureTheory Set Filter HarmonicBalls
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The γ-LQG measure of a quantum cone field is a Borel function of the observable process.** There is a
Borel map `Φ`, depending only on `γ`, with `μ_h = Φ(observable process)` almost surely for every γ-quantum cone
field. -/
theorem exists_measurable_lqgMeasure_factor_observable (γ : ℝ) :
    ∃ Φ : (GFFObservable.Admissible → ℝ) → Measure ℂ, Measurable Φ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
        ∀ᵐ ω ∂P, μ ω = Φ (wholePlaneObservableProc hC hcirc ω) := by
  obtain ⟨M, hM, hrec⟩ := exists_measurable_fieldCode_lqgMeasure_of_isQuantumCone γ
  let R : (GFFObservable.Admissible → ℝ) → FieldPairingCode := fun x φ =>
    x ⟨GFFObservable.pairing φ.1, φ.2⟩
  have hR : Measurable R := measurable_pi_iff.2 fun φ => measurable_pi_apply _
  refine ⟨fun x => M (R x), hM.comp hR, fun Ω _ P hC hcirc μ hc => ?_⟩
  let S : MatedCRTEnv Ω := ⟨P, hC, hcirc, μ, fun _ _ => 0, fun _ _ _ => 0, fun _ => 0⟩
  filter_upwards [hrec (S := S) (μ := μ) hc.2.1 hc.2.2] with ω hω
  have hRω : R (wholePlaneObservableProc hC hcirc ω) = fieldPairingCode S ω := rfl
  rw [hRω, hω]

/-- **The law of the γ-LQG measure does not depend on the cone field.** For a Borel set `A` of measures on `ℂ`
and two γ-quantum cone fields, the events `{μ_h ∈ A}` have the same probability. -/
theorem measure_lqgMeasure_mem_eq {γ : ℝ} {A : Set (Measure ℂ)} (hA : MeasurableSet A)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hc : IsConeField γ P hC hcirc μ)
    {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ}
    {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ} (hc₀ : IsConeField γ P₀ hC₀ hcirc₀ μ₀) :
    P {ω | μ ω ∈ A} = P₀ {ω | μ₀ ω ∈ A} := by
  obtain ⟨Φ, hΦ, hfac⟩ := exists_measurable_lqgMeasure_factor_observable γ
  have := hc.1
  have := hc₀.1
  have hm := IsQuantumCone.measurable_wholePlaneObservableProc hc.2.1
  have hm₀ := IsQuantumCone.measurable_wholePlaneObservableProc hc₀.2.1
  have h1 : {ω | μ ω ∈ A} =ᵐ[P] (Φ ∘ wholePlaneObservableProc hC hcirc) ⁻¹' A := by
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hfac Ω P hC hcirc μ hc] with ω hω
    exact Iff.of_eq (congrArg (· ∈ A) hω)
  have h1₀ : {ω | μ₀ ω ∈ A} =ᵐ[P₀] (Φ ∘ wholePlaneObservableProc hC₀ hcirc₀) ⁻¹' A := by
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hfac Ω₀ P₀ hC₀ hcirc₀ μ₀ hc₀] with ω hω
    exact Iff.of_eq (congrArg (· ∈ A) hω)
  rw [measure_congr h1, measure_congr h1₀, ← Measure.map_apply (hΦ.comp hm) hA,
    ← Measure.map_apply (hΦ.comp hm₀) hA, ← Measure.map_map hΦ hm, ← Measure.map_map hΦ hm₀,
    Sec1.IsQuantumCone.observable_law_eq hc.2.1 hc₀.2.1]

/-- **Polynomial bounds uniform over cone fields, by a Borel sandwich.** Let `E_s ⊆ B ⊆ E_w` be sets of measures
on `ℂ` for all small `δ > 0`, with every `B δ` Borel. If `{μ_h ∈ E_s δ}` has polynomially high probability for
every γ-quantum cone field, then there are `p > 0`, `C` and `r₀ > 0`, independent of the cone field, with
`P(μ_h ∉ E_w δ) ≤ C δ^p` for all `δ ∈ (0, r₀)` and every γ-quantum cone field. -/
theorem exists_uniform_polyBound_of_sandwich {γ : ℝ} {Es Bm Ew : ℝ → Set (Measure ℂ)}
    (hB : ∀ δ, MeasurableSet (Bm δ)) {r₁ : ℝ} (hr₁ : 0 < r₁)
    (hsub : ∀ δ, 0 < δ → δ < r₁ → Es δ ⊆ Bm δ ∧ Bm δ ⊆ Ew δ)
    (hpoly : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      PolyHighProb P fun δ => {ω | μ ω ∈ Es δ}) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsConeField γ P hC hcirc μ → ∀ δ : ℝ, 0 < δ → δ < r₀ →
        P {ω | μ ω ∈ Ew δ}ᶜ ≤ ENNReal.ofReal (C * δ ^ p) := by
  by_cases hex : ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ)
      (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ), IsConeField γ P₀ hC₀ hcirc₀ μ₀
  · obtain ⟨Ω₀, _, P₀, hC₀, hcirc₀, μ₀, hc₀⟩ := hex
    obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := hpoly Ω₀ P₀ hC₀ hcirc₀ μ₀ hc₀
    refine ⟨p, hp, C, min r₀ r₁, lt_min hr₀ hr₁, fun Ω _ P hC hcirc μ hc δ hδ hδr => ?_⟩
    obtain ⟨h1, h2⟩ := hsub δ hδ (hδr.trans_le (min_le_right _ _))
    calc P {ω | μ ω ∈ Ew δ}ᶜ ≤ P {ω | μ ω ∈ (Bm δ)ᶜ} :=
          measure_mono fun ω hω hB' => hω (h2 hB')
      _ = P₀ {ω | μ₀ ω ∈ (Bm δ)ᶜ} := measure_lqgMeasure_mem_eq (hB δ).compl hc hc₀
      _ ≤ P₀ {ω | μ₀ ω ∈ Es δ}ᶜ := measure_mono fun ω hω hs => hω (h1 hs)
      _ ≤ ENNReal.ofReal (C * δ ^ p) := hb δ hδ (hδr.trans_le (min_le_left _ _))
  · exact ⟨1, one_pos, 0, 1, one_pos, fun Ω _ P hC hcirc μ hc =>
      (hex ⟨Ω, _, P, hC, hcirc, μ, hc⟩).elim⟩

end MatedCRT.FirstPass.Derived
