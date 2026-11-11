import MatedCRT.FirstPass.S6r.OneTest.FirstMoment

open MeasureTheory Set Filter Metric
open scoped ENNReal
namespace MatedCRT
namespace Lemma68Window

/-- The walk-centred test parameter `ρ w = (R w, η(ε X_{T w}))`. -/
noncomputable def walkParam (ε : ℝ) (η : ℝ → ℂ) (R : (ℕ → ℤ) → ℝ) (T : (ℕ → ℤ) → ℕ∞) (w : ℕ → ℤ) : ℝ × ℂ :=
  (R w, vertexPoint ε η (w (T w).toNat))


/-- **The first moment at a walk state** (`E_b[V_occ | h, η] ≥ (1/4) ε⁻¹ m₀`, `m₀ = μ(B_{c₀R}(x))`,
`x = η(ε y)`, `y` the walk state). This is `firstMoment_occCount_fm` with the sparsity radius `r = c₀R`
(`c₀R ≤ r` and `r² ≤ R` hold since `c₀ ≤ 1/24`, `R ≤ 1`). Named omega-wise inputs: `hdiam` (cell size, Lemma 2.8),
`hsp` (sparsity, Lemma 6.8), `hvol` (ball mass, Lemma 2.7), `hGr` (Green lower bound, Lemma 2.16), `hfinE`
(finite expected exit time, Lemma 2.18), `hL29` (lower count, Lemma 2.9), `hsc` (scale). -/
theorem firstMoment_walkState {γ ρc : ℝ} (K : Constants68 γ ρc) {μ : Measure ℂ} {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {ε R α : ℝ} {y : ℤ}
    (hη : Continuous η) (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hεc : ε ≤ 16 * K.c0) (hR : 0 < R) (hR1 : R ≤ 1)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η y) (R / 4)).Nonempty →
      diam (cell ε η k) ≤ K.c0 * R)
    (hsp : ∀ w : ℂ, ((A ∩ cellVertices ε η (ball w (K.c0 * R))).ncard : ℝ)
      < K.s1 * (K.c0 * R) ^ (2 * K.βm) / ε)
    (hvol : (K.c0 * R) ^ K.βm ≤ (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal)
    (hGr : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R)),
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b
          ≤ greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b ∧
        K.C⁻¹ * Real.log (if vertexPoint ε η y = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η y - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b)
    (hfinE : expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 4))) y ≠ ⊤)
    (hL29 : ε⁻¹ * (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal - ε ^ (-1 + α)
      ≤ ((cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R))).ncard : ℝ))
    (hsc : 4 * ε ^ α ≤ (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal) :
    (1 / 4 : ℝ) * ε⁻¹ * (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal
      ≤ ∫ w, occCount A (fun w => (vExitTime (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 4))) w).toNat) w ∂(srwLaw m y) := by
  have hc0 : 0 < K.c0 := K.hc0
  have hc1 : K.c0 ≤ 1 / 24 := K.hc0'
  have hcR : 0 < K.c0 * R := mul_pos hc0 hR
  have hx : K.c0 * R ≤ R := by nlinarith
  have hr2 : (K.c0 * R) ^ 2 ≤ R := by nlinarith [mul_le_mul hx hx hcR.le hR.le]
  exact firstMoment_occCount_fm K hη hprop hε hεc hR hcR hr2 le_rfl rfl hdiam hsp hvol hGr hfinE hL29 hsc

end Lemma68Window
end MatedCRT
