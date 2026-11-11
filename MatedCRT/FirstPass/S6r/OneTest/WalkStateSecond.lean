import MatedCRT.FirstPass.S6r.OneTest.SecondMoment

open MeasureTheory Set Filter Metric HarmonicBalls
open scoped ENNReal
namespace MatedCRT
namespace Lemma68Window

/-- **The second moment at a walk state** (`E_b[V_occ² | h, η] ≤ C₂ ε⁻² (1+log(1/R))² m₀²`).
This is `secondMoment_occCount` at the start `b = X_T`, `x = η(ε b)`, `ID = I(B_{R/4}(x))`, with the mass at
`B_{3c₀R}(x)` of `secondMoment_occCount` replaced by `m₀ = μ(B_{c₀R}(x))` through the named comparison `hdbl`
(`μ(B_{3c₀R}(x)) ≤ Dbl · μ(B_{c₀R}(x))`). The side conditions of `secondMoment_occCount` are named and passed. -/
theorem secondMoment_walkState {μ : Measure ℂ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    {ε R α ρ C_exit c₀ C_good βm h Dbl : ℝ} {N_cov : ℕ} {z : ℂ} {b : ℤ}
    (hε : 0 < ε) (hR : 0 < R) (hR1 : R ≤ 1) (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5) (hCg : 0 ≤ C_good)
    (hεα : ε ^ α ≤ R / 100) (hεmass : ε ^ α ≤ (R / 4) ^ βm)
    (hb : b ∈ cellVertices ε η (sphere z (4 * R / 3)))
    (hcell : ∀ p ∈ cell ε η b, ∀ q ∈ cell ε η b, dist p q ≤ h) (hh : h ≤ R / 100)
    (hx1 : ‖vertexPoint ε η b‖ < 1 - R / 4)
    (hvol : ∀ y ∈ ball (0 : ℂ) (1 - R / 4), ENNReal.ofReal ((R / 4) ^ βm) ≤ μ (ball y (R / 4)))
    (hρ : ball (vertexPoint ε η b) (R / 4) ⊆ ball 0 ρ)
    (hmom : ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : IsGoodAnnulusEvent μ c₀ C_good R z)
    (hN : ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
      (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : 0 < ⨅ w ∈ annulus z R (2 * R), μ (ball w (c₀ * R)))
    (hfin : μ (ball z (3 * R)) ≠ ⊤)
    (hatom : ∀ v ∈ annulus z R (2 * R), μ {v} = 0)
    (hfinD : μ (ball (vertexPoint ε η b) (3 * c₀ * R)) ≠ ⊤)
    (hdbl : (μ (ball (vertexPoint ε η b) (3 * c₀ * R))).toReal
      ≤ Dbl * (μ (ball (vertexPoint ε η b) (c₀ * R))).toReal) :
    ∫ w, occCount A (fun w => (vExitTime (interiorCellVertices ε η (ball (vertexPoint ε η b) (R / 4))) w).toNat) w ^ 2 ∂(srwLaw m b)
      ≤ 32 * C_exit ^ 2 * ((1 + N_cov * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 * ε⁻¹ ^ 2
          * (1 + Real.log (1 / R)) ^ 2 * (μ (ball (vertexPoint ε η b) (c₀ * R))).toReal ^ 2 := by
  have hS := secondMoment_occCount m μ η _ A ε R α ρ C_exit c₀ C_good βm h N_cov z (vertexPoint ε η b) b rfl
    hε hR hR1 hc₀ hc₀' hCg hεα hεmass hb rfl hcell hh hx1 hvol hρ hmom hgood hN hpos hfin hatom hfinD
  have hM : (μ (ball (vertexPoint ε η b) (3 * c₀ * R))).toReal ^ 2
      ≤ (Dbl * (μ (ball (vertexPoint ε η b) (c₀ * R))).toReal) ^ 2 :=
    pow_le_pow_left₀ ENNReal.toReal_nonneg hdbl 2
  have hK : 0 ≤ 32 * C_exit ^ 2 * ((1 + N_cov * Real.log 4) * C_good) ^ 2 * ε⁻¹ ^ 2
      * (1 + Real.log (1 / R)) ^ 2 := by positivity
  refine hS.trans ?_
  have h2 := mul_le_mul_of_nonneg_left hM hK
  have e : 32 * C_exit ^ 2 * ((1 + N_cov * Real.log 4) * C_good) ^ 2 * ε⁻¹ ^ 2
      * (1 + Real.log (1 / R)) ^ 2 * (Dbl * (μ (ball (vertexPoint ε η b) (c₀ * R))).toReal) ^ 2
      = 32 * C_exit ^ 2 * ((1 + N_cov * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 * ε⁻¹ ^ 2
          * (1 + Real.log (1 / R)) ^ 2 * (μ (ball (vertexPoint ε η b) (c₀ * R))).toReal ^ 2 := by ring
  nlinarith [h2, e]

end Lemma68Window
end MatedCRT
