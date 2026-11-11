import MatedCRT.FirstPass.S5qe
import MatedCRT.FirstPass.S6r.Constants

/-!
# Model inputs of the Lemma 6.8 one-test chain: the Green and counting binders

`shellOneTest_of_direct` (`FirstPass/S4S6c/ShellHoneInst68.lean:53`) takes model inputs about the environment that are
not deterministic at a fixed `η`:

* `hGreen`: the second conjunct of `GreenKernelLowerBoundStmt` (Lemma 2.16, `Draft/Section2.lean:212`);
* `hCountGood`: the lower half of `CountingMeasureConvergenceStmt` at `f ≡ 1` (Lemma 2.9, `Draft/Section2.lean:143`).

Both Draft statements hold with polynomially high probability (`PolyHighProb`, `HarmonicBalls/Defs/Notation.lean:27`:
`P (E r)ᶜ ≤ C r^p` for `0 < r < r₀`), i.e. on a good event `E ε ⊆ Ω`. Neither gives a bound at a fixed `η`. The
discharges below are therefore the event version over `S : MatedCRTEnv Ω`: for every small `ε` and every `ω` in the
good event, the binder holds at `η := S.η ω`, `m := S.mult ε ω`, `μ := S.μ ω`, together with the polynomial bound on
the complement. The constants of the Draft (`ω₀`, `C` of Lemma 2.16; `α`, `β` of Lemma 2.9) are explicit inputs;
`greenLower_constants_of_core` and `countingMeasure_of_core` take them from `CertifiedReferenceModelCore`.

Terminology: Duplantier–Sheffield (LQG measure `μ_h`), Berestycki–Gwynne (counting measure, BG20 Lemma A.4 in the Draft),
Armitage–Gardiner (Green function `G_A` and kernel `g_A`).
-/

namespace MatedCRT
namespace HoneModelInputs68

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open _root_.HarmonicBalls

variable {Ω : Type} [MeasurableSpace Ω]

/-- The good event of Lemma 2.16 for the environment `S` at scale `ε`, with the constants `ω₀` (exponent of the
mesh and of the ball radius) and `C` (Green constant) and the radius `ρc`: the body of `GreenKernelLowerBoundStmt`
(`Draft/Section2.lean:212`), both conjuncts (`g ≤ G` and the lower bound on `g^ε`). -/
def greenLowerGoodEvent (ω₀ C ρc : ℝ) (S : MatedCRTEnv Ω) (ε : ℝ) : Set Ω :=
  {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρc - ε ^ ω₀)), ∀ r : ℝ, ε ^ ω₀ ≤ r →
    r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρc) →
    ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r / 3)),
      greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a b ≤
        greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a b ∧
      C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
        else min (r / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1 ≤
      greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a b}

/-- The good event of Lemma 2.9 for the environment `S` at scale `ε`: the body of `CountingMeasureConvergenceStmt`
(`Draft/Section2.lean:143`) with the constants `α`, `β` and the radius `ρ`. -/
def countingGoodEvent (S : MatedCRTEnv Ω) (α β ρ : ℝ) (ε : ℝ) : Set Ω :=
  {ω | ∀ (D : Set ℂ) (f : ℂ → ℝ) (w : ℤ → ℂ), D ⊆ ball 0 ρ →
    (∀ x ∈ thickening (ε ^ α) D, 0 ≤ f x ∧ |f x| ≤ ε ^ (-β)) →
    (∀ x ∈ thickening (ε ^ α) D, ∀ y ∈ thickening (ε ^ α) D, |f x - f y| ≤ ε ^ (-β) * ‖x - y‖) →
    (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
    ε⁻¹ * ∫ x in D, f x ∂S.μ ω - ε ^ (-1 + α) ≤ ∑' k : cellVertices ε (S.η ω) D, f (w k) ∧
    ∑' k : cellVertices ε (S.η ω) D, f (w k) ≤ ε⁻¹ * ∫ x in thickening (ε ^ α) D, f x ∂S.μ ω + ε ^ (-1 + α)}

/-- **Lemma 2.16, lower Green bound, on the good event (the binder `hGreen` of `shellOneTest_of_direct`).**
Given the Draft event at the constants `ω₀`, `C` (`hGL`), the good event `greenLowerGoodEvent ω₀ C ρc S ε` has
polynomially high probability, and for every small `ε` and every `ω` in the good event the binder `hGreen` holds at
`η := S.η ω`, `m := S.mult ε ω` (with `ω₀ = K.ω`, `C = K.C` for the `K` of the leaf). This is the event version: the
fixed-`η` binder is not derived. -/
theorem hGreen_on_good_event {γ ρc : ℝ} {𝒮 : SpaceFillingSLEModel} (ω₀ C : ℝ)
    (hGL : ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P (greenLowerGoodEvent ω₀ C ρc S))
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    PolyHighProb S.P (greenLowerGoodEvent ω₀ C ρc S) ∧ ∃ r₀ > 0, ∀ ε : ℝ, 0 < ε → ε < r₀ →
      ∀ ω ∈ greenLowerGoodEvent ω₀ C ρc S ε,
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρc - ε ^ ω₀)), ∀ r : ℝ, ε ^ ω₀ ≤ r →
        r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρc) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r / 3)),
          C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
            else min (r / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1 ≤
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a b := by
  refine ⟨hGL Ω S hS, ?_⟩
  obtain ⟨_, _, _, r₀, hr₀, _⟩ := hGL Ω S hS
  exact ⟨r₀, hr₀, fun ε _ _ ω hω a ha r hr1 hr2 b hb => (hω a ha r hr1 hr2 b hb).2⟩

/-- **Lemma 2.9, lower half at `f ≡ 1`, on the good event (the binder `hCountGood` of `shellOneTest_of_direct`).**
Given the Draft event at `α`, `β` and `ρc` (`hCM`) with `0 < β`, for every small `ε` and every `ω` in the good event,
`ε⁻¹ μ(D) - ε^{-1+α} ≤ #V^ε(D)` for `D ⊆ B_ρc` and `w` a choice of cell points, with `μ := S.μ ω`, `η := S.η ω`. -/
theorem hCountGood_on_good_event {γ ρc α β : ℝ} {𝒮 : SpaceFillingSLEModel} (hβ : 0 < β)
    (hCM : ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P (countingGoodEvent S α β ρc))
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    PolyHighProb S.P (countingGoodEvent S α β ρc) ∧ ∃ r₀ > 0, ∀ ε : ℝ, 0 < ε → ε < min r₀ 1 →
      ∀ ω ∈ countingGoodEvent S α β ρc ε, ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ) := by
  refine ⟨hCM Ω S hS, ?_⟩
  obtain ⟨_, _, _, r₀, hr₀, _⟩ := hCM Ω S hS
  refine ⟨r₀, hr₀, fun ε hε0 hε1 ω hω D hD w hw => ?_⟩
  have hε1': ε < 1 := lt_of_lt_of_le hε1 (min_le_right _ _)
  have hpow : (1 : ℝ) ≤ ε ^ (-β) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1'.le (by linarith)
  have hω' := (show ∀ (D : Set ℂ) (f : ℂ → ℝ) (w : ℤ → ℂ), D ⊆ ball 0 ρc →
      (∀ x ∈ thickening (ε ^ α) D, 0 ≤ f x ∧ |f x| ≤ ε ^ (-β)) →
      (∀ x ∈ thickening (ε ^ α) D, ∀ y ∈ thickening (ε ^ α) D, |f x - f y| ≤ ε ^ (-β) * ‖x - y‖) →
      (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
      ε⁻¹ * ∫ x in D, f x ∂S.μ ω - ε ^ (-1 + α) ≤ ∑' k : cellVertices ε (S.η ω) D, f (w k) ∧
      ∑' k : cellVertices ε (S.η ω) D, f (w k) ≤ ε⁻¹ * ∫ x in thickening (ε ^ α) D, f x ∂S.μ ω + ε ^ (-1 + α) from hω)
  have hf : ∀ x ∈ thickening (ε ^ α) D, 0 ≤ (fun _ : ℂ => (1 : ℝ)) x ∧
      |(fun _ : ℂ => (1 : ℝ)) x| ≤ ε ^ (-β) := fun x _ => by
    simp only [abs_one]
    exact ⟨zero_le_one, hpow⟩
  have hL : ∀ x ∈ thickening (ε ^ α) D, ∀ y ∈ thickening (ε ^ α) D,
      |(fun _ : ℂ => (1 : ℝ)) x - (fun _ : ℂ => (1 : ℝ)) y| ≤ ε ^ (-β) * ‖x - y‖ := fun x _ y _ => by
    simp only [sub_self, abs_zero]
    exact mul_nonneg (Real.rpow_nonneg hε0.le _) (norm_nonneg _)
  exact (hω' D (fun _ => 1) w hD hf hL hw).1

/-- The counting-measure constants of Lemma 2.9 from the core certified model: the projection of conjunct 6 of
`CertifiedReferenceModel` (`FirstPass/SLERef/Certified.lean:54`), which the core keeps. -/
theorem countingMeasure_of_core {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hC : CertifiedReferenceModelCore ν 𝒮) : CountingMeasureConvergenceStmt 𝒮 :=
  hC.2.2.2.2.2.1

/-- The lower Green constants `ω₀`, `C` of Lemma 2.16 at a fixed `ρc`, from the core certified model (projection
`CertifiedReferenceModelCore.greenKernelLowerBound`, `S5qe.lean`). The witnesses are not chosen here: any `K` with
`K.ω = ω₀` and `K.C = C` gives the constants of `hGreen_on_good_event`. -/
theorem greenLower_constants_of_core {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hC : CertifiedReferenceModelCore ν 𝒮) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ρc : ℝ} (hρ0 : 0 < ρc)
    (hρ1 : ρc < 1) :
    ∃ ω₀ C : ℝ, 0 < ω₀ ∧ 0 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P (greenLowerGoodEvent ω₀ C ρc S) := by
  obtain ⟨ω₀, hω₀, h⟩ := hC.greenKernelLowerBound γ hγ0 hγ2
  obtain ⟨C, hC0, h'⟩ := h ρc hρ0 hρ1
  exact ⟨ω₀, C, hω₀, hC0, h'⟩

#print axioms MatedCRT.HoneModelInputs68.hGreen_on_good_event
#print axioms MatedCRT.HoneModelInputs68.hCountGood_on_good_event
#print axioms MatedCRT.HoneModelInputs68.countingMeasure_of_core
#print axioms MatedCRT.HoneModelInputs68.greenLower_constants_of_core

end HoneModelInputs68
end MatedCRT
