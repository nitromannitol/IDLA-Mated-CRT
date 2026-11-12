import MatedCRT.Proofs.Sec1.EnvironmentScaling

/-!
# Boundary-length pair of the rescaled quantum cone

Let `(h, η)` be the `γ`-quantum cone and the space-filling SLE of a mating-of-trees coupling, with
boundary-length pair `bm = BL(h, η)`. For `b > 0` let `R_b` be the cone scale radius read off the radial part
of `h`, `h^b = h(R_b ·) + Q log R_b - γ⁻¹ log b` and `η^b = R_b⁻¹ η(b ·)`. Quantum length transforms by the
coordinate-change rule and by `ν_{h+c} = e^{γ c / 2} ν_h` (Duplantier-Miller-Sheffield (2014), (1.2)), so the
boundary-length pair of `(h^b, η^b)` is the Brownian rescaling `t ↦ b^{-1/2} bm(bt)`; this is the
`boundaryLength` field of the coupling.

This file restates that identity with the environment's rescaled pair `rescaledPair b`
(`(√b)⁻¹ • bm(b ·)`), and the rescaled curve as the explicit function `s ↦ R_b⁻¹ η(b s)`.

## Main statements

* `MatedCRT.Sec1.brownRescale_eq_rescaledPair`: for `b > 0`, `b^{-1/2} w(b ·) = (√b)⁻¹ • w(b ·)`.
* `MatedCRT.Sec1.coe_coneRescaleCurve`: `η^b = s ↦ R⁻¹ η(b s)` as a function.
* `MatedCRT.Sec1.exists_boundaryLength_rescaledPair`: the boundary-length functional `BL` of the coupling is
  Borel, `bm = BL(h, η)` a.s., and for each fixed `b > 0`, a.s. `BL(h^b, η^b) = rescaledPair b bm`.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace MatedCRT.Sec1

/-- For `b > 0`, the Brownian rescaling `t ↦ b^{-1/2} w(bt)` is `rescaledPair b w = (√b)⁻¹ • w(b ·)`. -/
theorem brownRescale_eq_rescaledPair {b : ℝ} (hb : 0 < b) (w : C(ℝ, ℝ × ℝ)) :
    MatedCRTHarmonic.MatedCRT.brownRescale b w = rescaledPair b w := by
  ext1 t
  rw [rescaledPair_apply, Real.sqrt_eq_rpow, ← Real.rpow_neg hb.le]
  rfl

/-- The rescaled curve `η^b = R⁻¹ η(b ·)` as a function. -/
theorem coe_coneRescaleCurve (R b : ℝ) (c : C(ℝ, ℂ)) :
    ⇑(MatedCRTHarmonic.MatedCRT.coneRescaleCurve R b c) = fun s => (R : ℂ)⁻¹ * c (b * s) := by
  funext s
  simp [MatedCRTHarmonic.MatedCRT.coneRescaleCurve]

/-- **Boundary-length pair of the rescaled cone.** In a mating-of-trees coupling, the boundary-length
pair is a Borel functional `BL` of the cone field and the curve, and for every fixed `b > 0`, almost surely the
boundary-length pair of the rescaled cone `(h^b, η^b)` (cone scale radius `R_b` of the radial part) is the
Brownian rescaling `rescaledPair b bm = (√b)⁻¹ • bm(b ·)`. -/
theorem exists_boundaryLength_rescaledPair {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → C(ℝ, ℝ × ℝ)}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ BL : MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) → C(ℝ, ℝ × ℝ), Measurable BL ∧
      (∀ᵐ ω ∂P, bm ω = BL (MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)), η ω)) ∧
      ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P,
        BL (MatedCRTHarmonic.MatedCRT.coneRescaleField γ
              (MatedCRTHarmonic.MatedCRT.coneScale γ γ (fun u => B u ω) (fun u => B' u ω) b) b
              (MatedCRTHarmonic.MatedCRT.coneField (X ω)
                (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))),
            MatedCRTHarmonic.MatedCRT.coneRescaleCurve
              (MatedCRTHarmonic.MatedCRT.coneScale γ γ (fun u => B u ω) (fun u => B' u ω) b) b (η ω)) =
          rescaledPair b (bm ω) := by
  obtain ⟨BL, hBL, hbm, hscale⟩ := h.boundaryLength
  refine ⟨BL, hBL, hbm, fun b hb => ?_⟩
  filter_upwards [hscale b hb] with ω hω
  rw [hω, brownRescale_eq_rescaledPair hb]

end MatedCRT.Sec1
