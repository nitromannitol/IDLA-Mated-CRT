import MatedCRT.FirstPass.Derived.FiberwiseInvariance
import MatedCRT.FirstPass.Derived.AreaParametrization
import MatedCRT.FirstPass.Derived.SimilarityScaling

/-!
# Similarity transfer: the abstract assembly

The assembly step of the similarity transfer for a quantum cone and an independent space-filling curve.  Let
`X = (c', μ')` be the rescaled cone data and `G = (c, μ)` the cone data, with `X =d G`; let `ηL` be a measurable
Lebesgue-area representative which is independent of `G` and of `(X, R)`, where `R` is the random scale; and let the
law of `ηL` be invariant under the rescalings `scaleRep a`, `a > 0`.  Then the triple (rescaled data, curve
`s ↦ R⁻¹ η(b s)`) has the law of the triple (data, curve `η`), where the curves are the area parametrizations of
the representatives.

All hypotheses are about measurable (not only almost everywhere measurable) random variables; the almost
everywhere statements concern the area parametrization.
-/

open MeasureTheory ProbabilityTheory

namespace MatedCRT.FirstPass.Derived

/-- The area parametrization of a Lebesgue representative recovers a curve parametrized by the area of `μ`. -/
theorem areaParam_eq_of_isLebesgueRepresentative {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {η : ℝ → ℂ}
    {c : C(ℝ, ℂ)} (hη : IsAreaParametrized μ η) (hc : IsLebesgueRepresentative η c) :
    areaParam μ c = η := by
  obtain ⟨_, _, _, _, φ, hφ0, hηφ⟩ := hc
  funext t
  exact areaParam_eq hη φ hφ0 hηφ t

/-- The area parametrization is a measurable map of the pair (measure, representative), as a map into curves. -/
theorem measurable_areaParam_curve :
    Measurable fun p : Measure ℂ × C(ℝ, ℂ) => areaParam p.1 p.2 :=
  measurable_pi_iff.2 fun t => measurable_areaParam t

/-- Applying the area parametrization preserves identity in law. -/
theorem identDistrib_areaParam {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A : Type*}
    [MeasurableSpace A] {X G : Ω → A × Measure ℂ} {C C' : Ω → C(ℝ, ℂ)}
    (h : IdentDistrib (fun ω => (X ω, C' ω)) (fun ω => (G ω, C ω)) P P) :
    IdentDistrib (fun ω => ((X ω).1, (X ω).2, areaParam (X ω).2 (C' ω)))
      (fun ω => ((G ω).1, (G ω).2, areaParam (G ω).2 (C ω))) P P := by
  have hm : Measurable fun p : (A × Measure ℂ) × C(ℝ, ℂ) =>
      (p.1.1, p.1.2, areaParam p.1.2 p.2) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_areaParam_curve.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  exact h.comp hm

/-- A path rescaling is the identity at scale `1`. -/
theorem scaleRep_one (c : C(ℝ, ℂ)) : scaleRep 1 c = c := by
  ext t
  simp [scaleRep_apply]

/-- **Fibrewise invariance and independence give the joint law of the data and the rescaled representative.** -/
theorem identDistrib_scaleRep_of_indep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Type*} [MeasurableSpace T] {X G : Ω → T} {R : Ω → ℝ}
    {ηL : Ω → C(ℝ, ℂ)} (hX : Measurable X) (hR : Measurable R) (hηL : Measurable ηL)
    (hid : IdentDistrib X G P P) (hindX : IndepFun (fun ω => (X ω, R ω)) ηL P)
    (hindG : IndepFun G ηL P)
    (hinv : ∀ a : ℝ, 0 < a → (P.map ηL).map (scaleRep a) = P.map ηL) :
    IdentDistrib (fun ω => (X ω, scaleRep (if 0 < R ω then R ω else 1) (ηL ω)))
      (fun ω => (G ω, ηL ω)) P P := by
  have hpair : Measurable fun p : (T × ℝ) × C(ℝ, ℂ) => (p.1.2, p.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hΦ : Measurable fun p : (T × ℝ) × C(ℝ, ℂ) => scaleRep (if 0 < p.1.2 then p.1.2 else 1) p.2 :=
    (measurable_scaleRep.comp hpair : _)
  have hinv' : ∀ t : T × ℝ, (P.map ηL).map (fun c => scaleRep (if 0 < t.2 then t.2 else 1) c) =
      P.map ηL := by
    intro t
    by_cases h : 0 < t.2
    · simpa [h] using hinv t.2 h
    · simp only [h, ↓reduceIte, scaleRep_one]
      exact Measure.map_id
  have h1 := identDistrib_fiber_of_indepFun (hX.prodMk hR) hηL hindX
    (fun z c => scaleRep (if 0 < z.2 then z.2 else 1) c) hΦ hinv'
  have h2 : IdentDistrib (fun ω => (X ω, scaleRep (if 0 < R ω then R ω else 1) (ηL ω)))
      (fun ω => (X ω, ηL ω)) P P :=
    h1.comp (u := fun p : (T × ℝ) × C(ℝ, ℂ) => (p.1.1, p.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hindX' : IndepFun X ηL P :=
    hindX.comp (φ := fun z : T × ℝ => z.1) (ψ := id) measurable_fst measurable_id
  exact h2.trans (IdentDistrib.prodMk hid (IdentDistrib.refl hηL.aemeasurable) hindX' hindG)

/-- **Assembly of the similarity transfer.**  The rescaled data and the rescaled curve `s ↦ R⁻¹ η(b s)` have the
joint law of the data and the curve `η`, when the Lebesgue representative `ηL` of `η` is independent of both the
data and the rescaled data together with the scale, and its law is invariant under the rescalings. -/
theorem identDistrib_similarity_of_indep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Type*} [MeasurableSpace A] {c c' : Ω → A} {μ μ' : Ω → Measure ℂ}
    {R : Ω → ℝ} {ηL : Ω → C(ℝ, ℂ)} {η : Ω → ℝ → ℂ} {b : ℝ} (hb : 0 < b)
    (hX : Measurable fun ω => (c' ω, μ' ω)) (hR : Measurable R) (hηL : Measurable ηL)
    (hid : IdentDistrib (fun ω => (c' ω, μ' ω)) (fun ω => (c ω, μ ω)) P P)
    (hindX : IndepFun (fun ω => ((c' ω, μ' ω), R ω)) ηL P)
    (hindG : IndepFun (fun ω => (c ω, μ ω)) ηL P)
    (hinv : ∀ a : ℝ, 0 < a → (P.map ηL).map (scaleRep a) = P.map ηL)
    (hR0 : ∀ᵐ ω ∂P, 0 < R ω)
    (hμ' : ∀ᵐ ω ∂P, μ' ω = FPScaledMeasure (μ ω) (R ω) b)
    (hlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hrep : ∀ᵐ ω ∂P, IsLebesgueRepresentative (η ω) (ηL ω))
    (harea : ∀ᵐ ω ∂P, IsAreaParametrized (μ ω) (η ω)) :
    IdentDistrib (fun ω => (c' ω, μ' ω, fun s => ((R ω : ℝ) : ℂ)⁻¹ * η ω (b * s)))
      (fun ω => (c ω, μ ω, η ω)) P P := by
  have hs := identDistrib_scaleRep_of_indep hX hR hηL hid hindX hindG hinv
  have hΘ := identDistrib_areaParam hs
  have h1 : ∀ᵐ ω ∂P, (((c' ω, μ' ω).1, (c' ω, μ' ω).2,
      areaParam (c' ω, μ' ω).2 (scaleRep (if 0 < R ω then R ω else 1) (ηL ω)))) =
      (c' ω, μ' ω, fun s => ((R ω : ℝ) : ℂ)⁻¹ * η ω (b * s)) := by
    filter_upwards [hR0, hμ', hlf, hrep, harea] with ω h0 hm hl hr ha
    have hne : R ω ≠ 0 := h0.ne'
    have hl' : IsLocallyFiniteMeasure (FPScaledMeasure (μ ω) (R ω) b) :=
      isLocallyFiniteMeasure_fPScaledMeasure hne b
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [h0, ↓reduceIte, hm]
    exact areaParam_eq_of_isLebesgueRepresentative (isAreaParametrized_fPScaledMeasure hne hb ha)
      (isLebesgueRepresentative_scaleRep h0 hb hr)
  have h2 : ∀ᵐ ω ∂P, (((c ω, μ ω).1, (c ω, μ ω).2, areaParam (c ω, μ ω).2 (ηL ω))) =
      (c ω, μ ω, η ω) := by
    filter_upwards [hlf, hrep, harea] with ω hl hr ha
    exact Prod.ext rfl (Prod.ext rfl (areaParam_eq_of_isLebesgueRepresentative ha hr))
  exact ((IdentDistrib.of_ae_eq hΘ.aemeasurable_fst h1).symm.trans hΘ).trans
    (IdentDistrib.of_ae_eq hΘ.aemeasurable_snd h2)

end MatedCRT.FirstPass.Derived
