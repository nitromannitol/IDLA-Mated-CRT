import MatedCRT.FirstPass.S4S6c.HoneModelInputs68
import MatedCRT.FirstPass.S6e.Uniform
import MatedCRT.FirstPass.S6r.Amplification
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# Environment events of the one-test hone, from the Draft statements

Answering blocker B2.
rules that the binders `hGreen`,
`hCountGood`, `hGrLow`, `hlf`, `hcons` need no External Prop:

* `hGreen`: the good event `greenLowerGoodEvent` (Lemma 2.16, lower Green bound) is the body of
  `GreenKernelLowerBoundStmt` (Draft/Section2.lean:212), so it has polynomially high probability (`greenLower_polyHighProb`).
* `hCountGood`: the good event `countingGoodEvent` (Lemma 2.9, lower half at `f ≡ 1`) is the body of
  `CountingMeasureConvergenceStmt` (Draft/Section2.lean:143), the statement projected by `countingMeasure_of_core`
  (HoneModelInputs68.lean:112) (`countingGood_polyHighProb`).
* `hlf`, `hcons`: the almost-sure finiteness of the multiplicities is `FiniteExitAeStmt` (S6e/Uniform.lean:150), filtered
  into the common environment event `commonEnvEvent` (`finiteExit_of_mem`).
* `hGrLow` (l.231-251): derived from the Green event, the corrected walk hypothesis `hWalk` (the almost-sure form
  of HoneLeafAe68.lean:190 and :424) and `c₀ ≤ 1/24` (`Constants68.hc0'`, S6r/Constants.lean:70).

Terminology: polynomially high probability (Armstrong-Kuusi-Mourrat; `HarmonicBalls.PolyHighProb`), Lemma 2.9 and 2.16
(Berestycki-Gwynne; Berestycki-Powell), Green function and Green kernel (Armitage-Gardiner).
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal
open _root_.HarmonicBalls
open MatedCRT.Lemma68Window (prefixSet)

namespace MatedCRT
namespace HoneEnvEvents68

/-- **Lemma 2.16, lower Green bound: the good event has polynomially high probability.** The Draft statement
`GreenKernelLowerBoundStmt 𝒮` (Draft/Section2.lean:212) gives the exponent `ω₀` (not depending on `ρc`) and, for each
radius `ρc ∈ (0,1)`, the constant `C`; the event is the body of that statement (`greenLowerGoodEvent`,
HoneModelInputs68.lean:36). The argument is that of `greenLowEvent68_polyHighProb` (S6f/UniformEvents.lean:74). -/
theorem greenLower_polyHighProb {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ρc : ℝ} (hρ0 : 0 < ρc) (hρ1 : ρc < 1) :
    ∃ ω₀ C : ℝ, 0 < ω₀ ∧ 0 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P (HoneModelInputs68.greenLowerGoodEvent ω₀ C ρc S) := by
  obtain ⟨ω₀, hω₀, hGr⟩ := hG γ hγ0 hγ2
  obtain ⟨C, hC, h⟩ := hGr ρc hρ0 hρ1
  exact ⟨ω₀, C, hω₀, hC, h⟩

/-- **Lemma 2.9, lower half at `f ≡ 1`: the good event has polynomially high probability.** The Draft statement
`CountingMeasureConvergenceStmt 𝒮` (Draft/Section2.lean:143) gives the exponents `α`, `β` (not depending on `ρ`) and the
event for every radius `ρ ∈ (0,1)`; the event is `countingGoodEvent` (HoneModelInputs68.lean:48). -/
theorem countingGood_polyHighProb {𝒮 : SpaceFillingSLEModel} (hC : CountingMeasureConvergenceStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ρc : ℝ} (hρ0 : 0 < ρc) (hρ1 : ρc < 1) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρc) := by
  obtain ⟨α, β, hα, hβ, h⟩ := hC γ hγ0 hγ2
  refine ⟨α, β, hα, hβ, ?_⟩
  intro Ω _ S hS
  exact h ρc hρ0 hρ1 Ω S hS

/-- The almost-sure finiteness event of the environment `S`: for every `ε > 0` the multiplicities `S.mult ε ω` are
locally finite and `m k (k+1) ≠ 0` for all `k` (the body of `FiniteExitAeStmt`, S6e/Uniform.lean:150). -/
def finiteExitEvent {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) : Set Ω :=
  {ω | ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0}

/-- The finiteness event holds almost surely: `FiniteExitAeStmt` (S6e/Uniform.lean:150) at the valid environment `S`. -/
theorem finiteExit_ae {𝒮 : SpaceFillingSLEModel} (hF : Lemma68Uniform.FiniteExitAeStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, ω ∈ finiteExitEvent S :=
  hF γ hγ0 hγ2 Ω S hS

/-- The consumers `hlf` and `hcons` (S3f/Decomposition.lean:60; S6j/FiniteExit.lean:193) at the multiplicities
`S.mult ε ω`, for `ω` in the finiteness event. -/
theorem finiteExit_of_mem {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {ω : Ω}
    (hω : ω ∈ finiteExitEvent S) {ε : ℝ} (hε : 0 < ε) :
    IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 :=
  hω ε hε

/-- The common environment event of the one-test hone at scale `ε`, with the Green constants `ω₀`, `C` and the counting
exponents `α`, `β` at the radius `ρc`: the good Green event, the good counting event and the almost-sure finiteness
event. -/
def commonEnvEvent {Ω : Type} [MeasurableSpace Ω] (ω₀ C α β ρc : ℝ) (S : MatedCRTEnv Ω) (ε : ℝ) : Set Ω :=
  (HoneModelInputs68.greenLowerGoodEvent ω₀ C ρc S ε ∩ HoneModelInputs68.countingGoodEvent S α β ρc ε) ∩
    finiteExitEvent S

/-- The common environment event has polynomially high probability: union bound for the two good events
(`PolyHighProb.inter`) and intersection with a set of full measure (`PolyHighProb.inter_ae`). -/
theorem commonEnv_polyHighProb {Ω : Type} [MeasurableSpace Ω] {ω₀ C α β ρc : ℝ} {S : MatedCRTEnv Ω}
    (hG : PolyHighProb S.P (HoneModelInputs68.greenLowerGoodEvent ω₀ C ρc S))
    (hC : PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρc))
    (hF : ∀ᵐ ω ∂S.P, ω ∈ finiteExitEvent S) :
    PolyHighProb S.P (commonEnvEvent ω₀ C α β ρc S) :=
  (PolyHighProb.inter hG hC).inter_ae hF

/-- **The common environment event from the Draft statements.** For `γ ∈ (0,2)` and `ρc ∈ (0,1)` there are constants
`ω₀`, `C`, `α`, `β` (all positive) such that, for every valid environment, the common environment event has polynomially
high probability. The inputs are `GreenKernelLowerBoundStmt`, `CountingMeasureConvergenceStmt` and `FiniteExitAeStmt`. -/
theorem commonEnv_polyHighProb_of_draft {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮)
    (hC : CountingMeasureConvergenceStmt 𝒮) (hF : Lemma68Uniform.FiniteExitAeStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ρc : ℝ} (hρ0 : 0 < ρc) (hρ1 : ρc < 1) :
    ∃ ω₀ C α β : ℝ, 0 < ω₀ ∧ 0 < C ∧ 0 < α ∧ 0 < β ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        PolyHighProb S.P (commonEnvEvent ω₀ C α β ρc S) := by
  obtain ⟨ω₀, C, hω₀, hC0, hGr⟩ := greenLower_polyHighProb hG hγ0 hγ2 hρ0 hρ1
  obtain ⟨α, β, hα, hβ, hCr⟩ := countingGood_polyHighProb hC hγ0 hγ2 hρ0 hρ1
  refine ⟨ω₀, C, α, β, hω₀, hC0, hα, hβ, ?_⟩
  intro Ω _ S hS
  exact commonEnv_polyHighProb (hGr Ω S hS) (hCr Ω S hS) (finiteExit_ae hF hγ0 hγ2 S hS)

/-- The Green event of a point of the common environment event. -/
theorem greenLower_of_common {Ω : Type} [MeasurableSpace Ω] {ω₀ C α β ρc ε : ℝ} {S : MatedCRTEnv Ω} {ω : Ω}
    (hω : ω ∈ commonEnvEvent ω₀ C α β ρc S ε) :
    ω ∈ HoneModelInputs68.greenLowerGoodEvent ω₀ C ρc S ε :=
  hω.1.1

/-- The counting good event of a point of the common environment event. -/
theorem countingGood_of_common {Ω : Type} [MeasurableSpace Ω] {ω₀ C α β ρc ε : ℝ} {S : MatedCRTEnv Ω} {ω : Ω}
    (hω : ω ∈ commonEnvEvent ω₀ C α β ρc S ε) :
    ω ∈ HoneModelInputs68.countingGoodEvent S α β ρc ε :=
  hω.1.2

/-- **`hlf` and `hcons` on the common environment event:** at a point `ω` of the common environment event, for every
`ε > 0`, the multiplicities `S.mult ε ω` are locally finite with `m k (k+1) ≠ 0`. -/
theorem finiteExit_of_common {Ω : Type} [MeasurableSpace Ω] {ω₀ C α β ρc ε : ℝ} {S : MatedCRTEnv Ω} {ω : Ω}
    (hω : ω ∈ commonEnvEvent ω₀ C α β ρc S ε) {ε' : ℝ} (hε' : 0 < ε') :
    IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0 :=
  finiteExit_of_mem hω.2 hε'

/-- **The fixed-environment binder `hGreen` of the walk hone** (the lower bound of `greenLowerGoodEvent`, as in
`Lemma68Window.hone_exitQ_walk_of_env`, HoneInputs.lean:44-50), at the environment `S.η ω` and the multiplicities
`S.mult ε ω`, from membership in the good Green event. -/
theorem hGreen_of_mem {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {ω₀ C ρc ε : ℝ} {ω : Ω}
    (hω : ω ∈ HoneModelInputs68.greenLowerGoodEvent ω₀ C ρc S ε) :
    ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρc - ε ^ ω₀)), ∀ r : ℝ, ε ^ ω₀ ≤ r →
      r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r / 3)),
      C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
            else min (r / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1 ≤
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a b :=
  fun a ha r hr1 hr2 b hb => (hω a ha r hr1 hr2 b hb).2

/-- **The walk lower Green bound `hGrLow` at one walk state, from the fixed-environment binder `hGreen`.** The walk state
has vertex `a` in the domain `B(0, ρc - ε^ω₀)` of the Green event, `ε^ω₀ ≤ R/8 ≤ dist(v, ∂B(0,ρc))` (the walk hypothesis),
and `c₀ ≤ 1/24` gives `B(v, c₀R) ⊆ B(v, (R/8)/3)`, so the Green bound at the test radius `R/8` covers every `b ∈ B(v, c₀R)`.
Positivity of `R` follows from `ε^ω₀ ≤ R/8`. -/
theorem hGrLow_of_hGreen {ε ρc C ω₀ c0 R : ℝ} (hε : 0 < ε) (η : ℝ → ℂ) (m : ℤ → ℤ → ℕ) (a : ℤ)
    (hc0 : c0 ≤ 1 / 24)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ ω₀)), ∀ r : ℝ, ε ^ ω₀ ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
          greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : a ∈ cellVertices ε η (ball 0 (ρc - ε ^ ω₀)) ∧ ε ^ ω₀ ≤ R / 8 ∧
      R / 8 ≤ infDist (vertexPoint ε η a) (sphere 0 ρc)) :
    ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (c0 * R)),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
          greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) (R / 8))) a b := by
  intro b hb
  have hR : 0 ≤ R := by
    have h := (Real.rpow_nonneg hε.le ω₀).trans hWalk.2.1
    linarith
  have hc : c0 * R ≤ R / 8 / 3 := by
    have h := mul_le_mul_of_nonneg_right hc0 hR
    linarith
  have hsub : ball (vertexPoint ε η a) (c0 * R) ⊆ ball (vertexPoint ε η a) (R / 8 / 3) :=
    ball_subset_ball hc
  exact hGreen a hWalk.1 (R / 8) hWalk.2.1 hWalk.2.2 b
    (Set.Nonempty.mono (Set.inter_subset_inter_right _ hsub) hb)

/-- **The walk lower Green bound `hGrLow`, almost-sure form (the corrected `hWalk` of HoneLeafAe68.lean:190 and :424).**
For `k ≤ n` and almost every walk `x` (law `P`) in the prefix set of the exit time `T k`, the test radius `R k x / 8` at the
exit vertex gives the Green lower bound on `B(v, c₀ R k x)`. The pointwise bound is `hGrLow_of_hGreen`. -/
theorem hGrLow_ae {P : Measure (ℕ → ℤ)} {ε ρc C ω₀ c0 : ℝ} (hε : 0 < ε) (η : ℝ → ℂ) (m : ℤ → ℤ → ℕ)
    (hc0 : c0 ≤ 1 / 24) (A : Set ℤ) (τU : (ℕ → ℤ) → ℕ∞) (n : ℕ) (T : ℕ → (ℕ → ℤ) → ℕ∞)
    (R : ℕ → (ℕ → ℤ) → ℝ)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ ω₀)), ∀ r : ℝ, ε ^ ω₀ ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
          greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k ≤ n, ∀ᵐ x ∂P, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      x (T k x).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ ω₀)) ∧ ε ^ ω₀ ≤ R k x / 8 ∧
        R k x / 8 ≤ infDist (vertexPoint ε η (x (T k x).toNat)) (sphere 0 ρc)) :
    ∀ k ≤ n, ∀ᵐ x ∂P, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η (x (T k x).toNat)) (c0 * R k x)),
      C⁻¹ * Real.log (if vertexPoint ε η (x (T k x).toNat) = vertexPoint ε η b then ε⁻¹
            else min ((R k x / 8) / ‖vertexPoint ε η (x (T k x).toNat) - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
          greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η (x (T k x).toNat)) (R k x / 8)))
            (x (T k x).toNat) b := by
  intro k hk
  filter_upwards [hWalk k hk] with x hx hxp
  exact hGrLow_of_hGreen hε η m (x (T k x).toNat) hc0 hGreen (hx hxp)

/-- **`hGrLow` on the common environment event:** `hGrLow_ae` at `η := S.η ω` and `m := S.mult ε ω`, for `ω` in the common
environment event (its Green component supplies `hGreen`). The walk law is `srwLaw (S.mult ε ω) a`, i.e. `P` is the
walk measure of this environment. -/
theorem hGrLow_ae_of_common {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {ω₀ C α β ρc ε c0 : ℝ} {ω : Ω}
    (hω : ω ∈ commonEnvEvent ω₀ C α β ρc S ε) {P : Measure (ℕ → ℤ)} (hε : 0 < ε) (hc0 : c0 ≤ 1 / 24)
    (A : Set ℤ) (τU : (ℕ → ℤ) → ℕ∞) (n : ℕ) (T : ℕ → (ℕ → ℤ) → ℕ∞) (R : ℕ → (ℕ → ℤ) → ℝ)
    (hWalk : ∀ k ≤ n, ∀ᵐ x ∂P, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      x (T k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρc - ε ^ ω₀)) ∧ ε ^ ω₀ ≤ R k x / 8 ∧
        R k x / 8 ≤ infDist (vertexPoint ε (S.η ω) (x (T k x).toNat)) (sphere 0 ρc)) :
    ∀ k ≤ n, ∀ᵐ x ∂P, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) (x (T k x).toNat)) (c0 * R k x)),
      C⁻¹ * Real.log (if vertexPoint ε (S.η ω) (x (T k x).toNat) = vertexPoint ε (S.η ω) b then ε⁻¹
            else min ((R k x / 8) / ‖vertexPoint ε (S.η ω) (x (T k x).toNat) - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1 ≤
          greenKernel (S.mult ε ω)
            (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) (x (T k x).toNat)) (R k x / 8)))
            (x (T k x).toNat) b :=
  hGrLow_ae hε (S.η ω) (S.mult ε ω) hc0 A τU n T R (hGreen_of_mem (greenLower_of_common hω)) hWalk

#print axioms MatedCRT.HoneEnvEvents68.greenLower_polyHighProb
#print axioms MatedCRT.HoneEnvEvents68.countingGood_polyHighProb
#print axioms MatedCRT.HoneEnvEvents68.finiteExit_ae
#print axioms MatedCRT.HoneEnvEvents68.commonEnv_polyHighProb_of_draft
#print axioms MatedCRT.HoneEnvEvents68.finiteExit_of_common
#print axioms MatedCRT.HoneEnvEvents68.hGreen_of_mem
#print axioms MatedCRT.HoneEnvEvents68.hGrLow_of_hGreen
#print axioms MatedCRT.HoneEnvEvents68.hGrLow_ae_of_common

end HoneEnvEvents68
end MatedCRT
