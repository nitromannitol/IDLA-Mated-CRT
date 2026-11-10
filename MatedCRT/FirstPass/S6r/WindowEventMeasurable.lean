import MatedCRT.FirstPass.S6r.ShortWindow
import MatedCRT.Proofs.Measurability.GoodScale

/-!
# Field measurability of the short-window event `Ew` (6.8, PRO step 3)

The event of `ShortWindowGoodRadiusPrevalenceStmt` (`FirstPass/S6r/ShortWindow.lean:61`) is
`Ew(ω) = {ω | ∃ z ∈ shortEligible ρ d a, ∀ r ∈ shortWindowRadii d a, ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z}`.

Both quantifiers of the window range over countable sets: the centres lie in the lattice `(d/100) ℤ²`
(`shortEligible`), the radii are the seven-adic radii `7^{-n}` (`shortWindowRadii`). No uncountable union occurs. The
uncountable suprema and infima over annuli, which enter through `IsGoodAnnulusEvent`, are handled by
`MatedCRT.measurableSet_isGoodAnnulusEvent` (`Proofs/Measurability/GoodScale.lean:250`, proved). Hence the set of
measures `{m | ∃ z ∈ shortEligible, ∀ r ∈ shortWindowRadii, ¬ IsGoodAnnulusEvent m c₀ C r z}` is Borel for `Measure ℂ`
(countable union of countable intersections), and `Ew` is the preimage of this set under the random measure.

* `measurableSet_shortWindowEvent`: the window set of measures is Borel.
* `measurableSet_shortWindowEvent_of_measurable`: `Ew` is `m'`-measurable for any `m'`-measurable random measure `μ'`.
* `shortWindowEvent_fieldInnerMeasurableAE_of_lqgMeasure`: under `LQGMeasureFieldMeasurableStep 𝒮`, `Ew` for `S.μ` has a
  `S.fieldSigma`-measurable inner approximation outside a `S.P`-null set (`IsFieldInnerMeasurableAE`, GoodScale.lean:300),
  the same pattern as `goodScaleEventMeasurableAEStep_of_lqgMeasure` (GoodScale.lean:345).

Terminology: LQG measure (Duplantier-Sheffield), good annuli and good radii (Berestycki-Powell, Armstrong-Kuusi-Mourrat).
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT

namespace WindowEventMeasurable

open MatedCRT.Lemma68Window

/-- The eligible centres lie in a countable lattice `(d/100) ℤ²`. -/
theorem countable_shortEligible (ρ d a : ℝ) : (shortEligible ρ d a).Countable := by
  refine (Set.countable_range (fun p : ℤ × ℤ => ((d / 100 : ℝ) : ℂ) * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))).mono ?_
  intro z hz
  obtain ⟨_, m, n, rfl⟩ := hz
  exact ⟨(m, n), rfl⟩

/-- The seven-adic radii form a countable set `{7^{-n} : n ∈ ℕ}`. -/
theorem countable_shortWindowRadii (d a : ℝ) : (shortWindowRadii d a).Countable := by
  refine (Set.countable_range (fun n : ℕ => (7 : ℝ)⁻¹ ^ n)).mono ?_
  intro r hr
  obtain ⟨⟨n, rfl⟩, _, _⟩ := hr
  exact ⟨n, rfl⟩

/-- Every seven-adic radius of the window is positive. -/
theorem pos_of_mem_shortWindowRadii {d a r : ℝ} (hr : r ∈ shortWindowRadii d a) : 0 < r := by
  obtain ⟨⟨n, rfl⟩, _, _⟩ := hr
  positivity

/-- **Window event as a set of measures.** The set of measures for which some eligible centre has no good
seven-adic radius in the short window is Borel for the σ-algebra of `Measure ℂ`: a countable union over centres of
countable intersections over radii of the complements of the good annulus events (GoodScale.lean:250). -/
theorem measurableSet_shortWindowEvent (ρ d a c₀ C : ℝ) :
    MeasurableSet {m : Measure ℂ | ∃ z ∈ shortEligible ρ d a, ∀ r ∈ shortWindowRadii d a,
      ¬ IsGoodAnnulusEvent m c₀ C r z} := by
  have h : {m : Measure ℂ | ∃ z ∈ shortEligible ρ d a, ∀ r ∈ shortWindowRadii d a,
      ¬ IsGoodAnnulusEvent m c₀ C r z} =
      ⋃ z ∈ shortEligible ρ d a, ⋂ r ∈ shortWindowRadii d a,
        {m : Measure ℂ | IsGoodAnnulusEvent m c₀ C r z}ᶜ := by
    ext m
    simp
  rw [h]
  refine MeasurableSet.biUnion (countable_shortEligible ρ d a) fun z _ => ?_
  refine MeasurableSet.biInter (countable_shortWindowRadii d a) fun r hr => ?_
  exact (measurableSet_isGoodAnnulusEvent c₀ C (pos_of_mem_shortWindowRadii hr) z).compl

/-- **Field measurability of `Ew` for a measurable random measure.** If the random measure `μ'` is `m'`-measurable,
the window event of `ShortWindowGoodRadiusPrevalenceStmt` is `m'`-measurable. -/
theorem measurableSet_shortWindowEvent_of_measurable {Ω : Type*} {m' : MeasurableSpace Ω}
    (μ : Ω → Measure ℂ) (hμ : Measurable[m'] μ) (ρ d a c₀ C : ℝ) :
    MeasurableSet[m'] {ω | ∃ z ∈ shortEligible ρ d a, ∀ r ∈ shortWindowRadii d a,
      ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z} := by
  have hA := measurableSet_shortWindowEvent ρ d a c₀ C
  exact hμ hA

/-- **Field measurability of `Ew`, almost-sure form.** Under `LQGMeasureFieldMeasurableStep 𝒮` (the LQG measure is a.s.
equal to a `σ(h)`-measurable random measure, GoodScale.lean:316), the window event of `S.μ` admits a `S.fieldSigma`-measurable
inner approximation outside a null set. -/
theorem shortWindowEvent_fieldInnerMeasurableAE_of_lqgMeasure (𝒮 : SpaceFillingSLEModel)
    (h : LQGMeasureFieldMeasurableStep 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ ρ d a c₀ C : ℝ, IsFieldInnerMeasurableAE S
        {ω | ∃ z ∈ shortEligible ρ d a, ∀ r ∈ shortWindowRadii d a, ¬ IsGoodAnnulusEvent (S.μ ω) c₀ C r z} := by
  intro γ hγ hγ2 Ω _ S hS ρ d a c₀ C
  obtain ⟨μ', hμ', hae⟩ := h γ hγ hγ2 Ω S hS
  have hA := measurableSet_shortWindowEvent ρ d a c₀ C
  exact S.isFieldInnerMeasurableAE_of_measurableSet hμ' hae hA

end WindowEventMeasurable

end MatedCRT

#print axioms MatedCRT.WindowEventMeasurable.countable_shortEligible
#print axioms MatedCRT.WindowEventMeasurable.measurableSet_shortWindowEvent
#print axioms MatedCRT.WindowEventMeasurable.measurableSet_shortWindowEvent_of_measurable
#print axioms MatedCRT.WindowEventMeasurable.shortWindowEvent_fieldInnerMeasurableAE_of_lqgMeasure
