import LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The Borel structure of `𝓓_K` and the pairing of a random distribution with a random test function

For a compact set `K ⊆ ℂ`, the Fréchet space `𝓓_K = 𝓓^{⊤}_{K}(ℂ, ℝ)` of smooth functions supported in `K` is a
Polish space: it is second countable (`LQGMetric.secondCountableTopology_testK`), complete
(`LQGMetric.completeSpace_testK`), its uniformity is countably generated
(`LQGMetric.isCountablyGenerated_uniformity_testK`), and it is Hausdorff, since `f ↦ (Dⁱf)ᵢ` embeds it into a
product of spaces of bounded continuous functions. We equip it with its Borel σ-algebra.

* `measurableEmbedding_testK_eval`: the values on a countable dense set of points form a measurable embedding of
  `𝓓_K` into `ℝ^ℕ` (an injective continuous map out of a Polish space; Lusin–Souslin);
* `measurable_testK_iff`: a map `T : Ω → 𝓓_K` is measurable iff `ω ↦ T ω x` is measurable for every point `x`;
* `measurable_distC_apply_testK`: the pairing `(g, h) ↦ ⟨h, g⟩` of `𝓓_K × 𝒟'(ℂ)` is jointly measurable, for the
  cylinder σ-algebra on `𝒟'(ℂ)` (continuous in `g`, measurable in `h`: a Carathéodory function on a Polish space).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped Distributions

namespace MatedCRT

section TestK

variable (K : Compacts ℂ)

/-- The Borel σ-algebra of the test function space `𝓓_K`. -/
instance testKMeasurableSpace : MeasurableSpace 𝓓^{⊤}_{K}(ℂ, ℝ) := borel _

instance testKBorelSpace : BorelSpace 𝓓^{⊤}_{K}(ℂ, ℝ) := ⟨rfl⟩

/-- Evaluation at a point is continuous on `𝓓_K`. -/
theorem continuous_testK_apply (y : ℂ) : Continuous fun f : 𝓓^{⊤}_{K}(ℂ, ℝ) => f y := by
  have h : Continuous fun f : 𝓓^{⊤}_{K}(ℂ, ℝ) =>
      ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0 f y (Fin.elim0 : Fin 0 → ℂ) :=
    (continuous_eval_const (Fin.elim0 : Fin 0 → ℂ)).comp
      ((continuous_eval_const y).comp (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0).continuous)
  refine h.congr fun f => ?_
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply, iteratedFDeriv_zero_apply]

/-- The values on a dense sequence of points depend continuously on `f ∈ 𝓓_K`. -/
theorem continuous_testK_eval :
    Continuous fun (f : 𝓓^{⊤}_{K}(ℂ, ℝ)) (n : ℕ) => f (denseSeq ℂ n) :=
  continuous_pi fun _ => continuous_testK_apply K _

/-- A test function of `𝓓_K` is determined by its values on a dense sequence of points. -/
theorem injective_testK_eval :
    Function.Injective fun (f : 𝓓^{⊤}_{K}(ℂ, ℝ)) (n : ℕ) => f (denseSeq ℂ n) := by
  intro f g hfg
  have h : (f : ℂ → ℝ) = g :=
    (denseRange_denseSeq ℂ).equalizer f.contDiff.continuous g.contDiff.continuous
      (funext fun n => congrFun hfg n)
  exact ContDiffMapSupportedIn.ext fun y => congrFun h y

/-- `𝓓_K` is Hausdorff: the values on a dense sequence of points are an injective continuous map into
the Hausdorff space `ℝ^ℕ`. -/
instance t2Space_testK : T2Space 𝓓^{⊤}_{K}(ℂ, ℝ) := by
  refine ⟨fun f g hfg => ?_⟩
  obtain ⟨u, v, hu, hv, hfu, hgv, huv⟩ :=
    t2_separation fun h => hfg (injective_testK_eval K h)
  exact ⟨_, _, hu.preimage (continuous_testK_eval K), hv.preimage (continuous_testK_eval K), hfu,
    hgv, huv.preimage _⟩

/-- `𝓓_K` is a Polish space. -/
instance polishSpace_testK : PolishSpace 𝓓^{⊤}_{K}(ℂ, ℝ) where
  toSecondCountableTopology := inferInstance
  toIsCompletelyMetrizableSpace := IsCompletelyMetrizableSpace.of_completeSpace_metrizable

/-- **The values on a dense sequence are a measurable embedding of `𝓓_K` into `ℝ^ℕ`.** -/
theorem measurableEmbedding_testK_eval :
    MeasurableEmbedding fun (f : 𝓓^{⊤}_{K}(ℂ, ℝ)) (n : ℕ) => f (denseSeq ℂ n) :=
  (continuous_testK_eval K).measurableEmbedding (injective_testK_eval K)

/-- **A map into `𝓓_K` is measurable iff its values at every point are measurable.** -/
theorem measurable_testK_iff {Ω : Type*} [MeasurableSpace Ω] {T : Ω → 𝓓^{⊤}_{K}(ℂ, ℝ)} :
    Measurable T ↔ ∀ x, Measurable fun ω => T ω x := by
  refine ⟨fun hT x => (continuous_testK_apply K x).measurable.comp hT, fun hT => ?_⟩
  refine (measurableEmbedding_testK_eval K).measurable_comp_iff.1 ?_
  exact measurable_pi_iff.2 fun n => hT _

theorem subset_top_opens : (K : Set ℂ) ⊆ (⊤ : Opens ℂ) :=
  fun x _ => by simp

/-- The inclusion `𝓓_K → 𝓓(ℂ)`. -/
def testKToTestC : 𝓓^{⊤}_{K}(ℂ, ℝ) →L[ℝ] LQGMetric.TestC :=
  TestFunction.ofSupportedInCLM ℝ (subset_top_opens K)

theorem testKToTestC_apply (g : 𝓓^{⊤}_{K}(ℂ, ℝ)) (x : ℂ) : testKToTestC K g x = g x :=
  rfl

/-- **The pairing of `𝒟'(ℂ)` with `𝓓_K` is jointly measurable** (cylinder σ-algebra on `𝒟'(ℂ)`, Borel
σ-algebra on `𝓓_K`). -/
theorem measurable_distC_apply_testK :
    Measurable fun p : 𝓓^{⊤}_{K}(ℂ, ℝ) × LQGMetric.DistC => p.2 (testKToTestC K p.1) :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (g : 𝓓^{⊤}_{K}(ℂ, ℝ)) (h : LQGMetric.DistC) => h (testKToTestC K g))
    (fun h => h.continuous.comp (testKToTestC K).continuous)
    (fun _ => LQGMetric.measurable_distOn_apply _)

end TestK

end MatedCRT
