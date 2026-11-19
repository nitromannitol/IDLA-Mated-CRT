import MatedCRT.FirstPass.Derived.AeContinuousMapping
import MatedCRT.FirstPass.Derived.InterpWalkLawClassCloseInMeasure
import MatedCRT.FirstPass.Derived.MarkovTimeChange

/-!
# Identification of a weak limit of kernels from closeness in measure of the pushed-forward laws

Berestycki–Gwynne (2020), proof of Lemma 7.4.  Let `g n : Ω → 𝒬` be random elements of a topological space
`𝒬` converging in law to `ν`, let `ev : 𝒬 → Prob(A)` be continuous, `f : A → Y` measurable and `ν₀` a
probability measure on `Y`.  If, for every `κ > 0`, the probability that the Lévy–Prokhorov distance of
`(ev (g n ω)).map f` and `ν₀` exceeds `κ` tends to `0`, and for `ν`-almost every `q` the map `f` is
continuous `ev q`-almost everywhere, then `(ev q).map f = ν₀` for `ν`-almost every `q`.  The distance
`m ↦ d_LP (m.map f, ν₀)` is continuous at every `m` for which `f` is `m`-almost everywhere continuous
(continuous mapping theorem and the Lévy–Prokhorov metrisation of the weak topology), and a function
continuous `ν`-almost everywhere that is small along an approximating sequence vanishes `ν`-almost everywhere
(`AeContinuousMapping`).  No measurability of the distance is needed.

* `continuousAt_levyProkhorovDist_map`: continuity of `m ↦ d_LP (m.map f, ν₀)` at `m` with `f` `m`-a.e.
  continuous;
* `ae_map_eq_of_tendsto_of_levyProkhorovDist_gt`: the general identification;
* `ae_stoppedExitCurve_map_eq_of_ae_continuousAt`: the instance for the interpolated walk laws and the stopped
  class at the first exit from `ball 0 r`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.StopAtExitLevyProkhorov MatedCRT.FirstPass.Derived

namespace MatedCRT.ClassLawLimit

section General

variable {𝒬 A Y : Type*}
  [TopologicalSpace A] [TopologicalSpace.PseudoMetrizableSpace A] [TopologicalSpace.SeparableSpace A]
  [MeasurableSpace A] [BorelSpace A] [HasOuterApproxClosed A]
  [MetricSpace Y] [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **The Lévy–Prokhorov distance of the image law is continuous where `f` is almost everywhere
continuous.** -/
theorem continuousAt_levyProkhorovDist_map {f : A → Y} (hf : Measurable f) (ν₀ : ProbabilityMeasure Y)
    (m : ProbabilityMeasure A) (hc : ∀ᵐ a ∂(m : Measure A), ContinuousAt f a) :
    ContinuousAt (fun m' : ProbabilityMeasure A => levyProkhorovDist ((m' : Measure A).map f) (ν₀ : Measure Y))
      m := by
  have h1 : ContinuousAt (fun m' : ProbabilityMeasure A => m'.map f) m :=
    MatedCRT.AeContinuousMapping.tendsto_map_of_ae_continuousAt (L := 𝓝 m) (μs := id) tendsto_id hf hc
  have h2 : Continuous (fun ν : ProbabilityMeasure Y => levyProkhorovDist (ν : Measure Y) (ν₀ : Measure Y)) :=
    Continuous.dist (LevyProkhorov.probabilityMeasureHomeomorph (Ω := Y)).continuous
      (continuous_const (y := LevyProkhorov.ofMeasure ν₀))
  exact ContinuousAt.comp (g := fun ν : ProbabilityMeasure Y => levyProkhorovDist (ν : Measure Y) (ν₀ : Measure Y))
    (f := fun m' : ProbabilityMeasure A => m'.map f) h2.continuousAt h1


/-- **Identification of the limit.**  See the module docstring. -/
theorem ae_map_eq_of_tendsto_of_levyProkhorovDist_gt [TopologicalSpace 𝒬] [MeasurableSpace 𝒬]
    [OpensMeasurableSpace 𝒬] [HasOuterApproxClosed 𝒬] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℕ → Ω → 𝒬} (hg : ∀ n, AEMeasurable (g n) P) {ν : Measure 𝒬} [IsProbabilityMeasure ν]
    (hlaw : ∀ φ : 𝒬 →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, φ (g n ω) ∂P) atTop (𝓝 (∫ q, φ q ∂ν)))
    {ev : 𝒬 → ProbabilityMeasure A} (hev : Continuous ev) {f : A → Y} (hf : Measurable f)
    (ν₀ : ProbabilityMeasure Y)
    (hc : ∀ᵐ q ∂ν, ∀ᵐ a ∂(ev q : Measure A), ContinuousAt f a)
    (hclose : ∀ κ : ℝ, 0 < κ → Tendsto (fun n => P {ω | κ < levyProkhorovDist
      ((ev (g n ω) : Measure A).map f) (ν₀ : Measure Y)}) atTop (𝓝 0)) :
    ∀ᵐ q ∂ν, (ev q : Measure A).map f = (ν₀ : Measure Y) := by
  set μs : ℕ → ProbabilityMeasure 𝒬 := fun n => ⟨P.map (g n), inferInstance⟩ with hμs
  set μ : ProbabilityMeasure 𝒬 := ⟨ν, inferInstance⟩ with hμ
  have hlim : Tendsto μs atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro φ
    show Tendsto (fun n => ∫ ω, φ ω ∂(P.map (g n))) atTop (𝓝 (∫ q, φ q ∂ν))
    exact (hlaw φ).congr fun n => (integral_map (hg n) φ.continuous.aestronglyMeasurable).symm
  set F : 𝒬 → ℝ := fun q => levyProkhorovDist ((ev q : Measure A).map f) (ν₀ : Measure Y) with hF
  have hcF : ∀ᵐ q ∂(μ : Measure 𝒬), ContinuousAt F q := by
    filter_upwards [hc] with q hq
    exact (continuousAt_levyProkhorovDist_map hf ν₀ (ev q) hq).comp hev.continuousAt
  have hF0 := MatedCRT.AeContinuousMapping.ae_le_zero_of_tendsto_of_continuousAt hlim hcF
    (fun κ hκ O hO hOκ => by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hclose κ hκ)
        (fun _ => bot_le) (fun n => ?_)
      show (P.map (g n)) O ≤ _
      rw [Measure.map_apply_of_aemeasurable (hg n) hO.measurableSet]
      exact measure_mono fun ω hω => hOκ _ hω)
  filter_upwards [hF0] with q hq
  have hnn : 0 ≤ F q := ENNReal.toReal_nonneg
  have h0 : F q = 0 := le_antisymm hq hnn
  have hd : dist (LevyProkhorov.ofMeasure ((ev q).map f)) (LevyProkhorov.ofMeasure ν₀) = 0 := h0
  have h2' : LevyProkhorov.ofMeasure ((ev q).map f) = LevyProkhorov.ofMeasure ν₀ := dist_eq_zero.1 hd
  have h2 : (ev q).map f = ν₀ := by simpa using congrArg LevyProkhorov.toMeasure h2'
  simpa using congrArg (fun m : ProbabilityMeasure Y => (m : Measure Y)) h2

end General

section Interp

open MatedCRT

/-- **The stopped class law of a weak limit of interpolated walk laws is Brownian when the stopped class is
almost everywhere continuous** (Berestycki–Gwynne (2020), proof of Lemma 7.4).  Let `ν₂` be a subsequential
weak limit of the laws of `ω ↦ P̃^{ε_n}(ω)` and `‖z‖ < r`.  If for `ν₂`-almost every `P` the map
`stoppedExitCurve (ball 0 r)` is continuous `P z`-almost everywhere (finite regular exit), then for
`ν₂`-almost every `P` the law under `P z` of the stopped curve class at the exit from `ball 0 r` is that of
planar Brownian motion from `z`. -/
theorem ae_stoppedExitCurve_map_eq_of_ae_continuousAt
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hN4 : GMS21UniformStartInput 𝒮)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hmε : ∀ᶠ n in atTop, 0 < S.mε (ε n))
    {ν₂ : Measure PathLawFamily} [IsProbabilityMeasure ν₂]
    (hlaw : ∀ f : PathLawFamily →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂)))
    {z : ℂ} {r : ℝ} (hzr : ‖z‖ < r)
    (hc : ∀ᵐ P ∂ν₂, ∀ᵐ b ∂((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)),
      ContinuousAt (stoppedExitCurve (ball (0 : ℂ) r)) b) :
    ∀ᵐ P ∂ν₂, ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
        (stoppedExitCurve (ball (0 : ℂ) r)) =
      (planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) r)) := by
  have := hS.isProbabilityMeasure
  have hmeas := measurable_stoppedExitCurve (ball (0 : ℂ) r) isOpen_ball
  let ν₀ : ProbabilityMeasure (BouRabeeGwynne.CurveSpace 2) :=
    ⟨(planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) r)), inferInstance⟩
  refine ae_map_eq_of_tendsto_of_levyProkhorovDist_gt (ev := fun P : PathLawFamily => P z)
    (g := fun n ω => interpWalkLaw S η' (ε n) ω) (fun n => aemeasurable_interpWalkLaw hS hη' hae (hε0 n))
    hlaw (continuous_eval_const z) hmeas ν₀ hc ?_
  intro κ hκ
  have hρ : 0 < (‖z‖ + r) / 2 := by have := norm_nonneg z; linarith
  exact InterpClassClose.tendsto_measure_levyProkhorovDist_interpWalkLaw_stoppedExitCurve_gt hγ hγ2 hN4 hS hae
    hε0 hε hmε hρ (by linarith : (‖z‖ + r) / 2 < r) (by linarith : ‖z‖ < (‖z‖ + r) / 2) hκ

end Interp

end MatedCRT.ClassLawLimit
