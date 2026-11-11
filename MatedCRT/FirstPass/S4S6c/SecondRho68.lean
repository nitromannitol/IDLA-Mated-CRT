import MatedCRT.FirstPass.S6r.OneTest.WalkStateSecond

/-!
# Second moments with a free test radius

Serves Lemma 6.8 (`lemma:constant-order-lower-bound-div`) through its replacement proof [C26] (`eq:c26-second-moment`):
the second-moment estimates with the radius `1` in the hypotheses `hx1` and `hvol` replaced by a parameter `ρmom`.
Main declarations: `secondMoment_occCount_rho` (a copy of `secondMoment_occCount`) and `secondMoment_walkState_rho`
(a copy of `secondMoment_walkState`, `WalkStateSecond.lean`); the originals are unchanged.
-/

open MeasureTheory Set Filter Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT
namespace Lemma68Window

/-- Copy of `secondMoment_occCount` (SecondMoment.lean:147) with the radius `1` of `hx1` and `hvol`
replaced by `ρmom`. The original is unchanged. -/
theorem secondMoment_occCount_rho {ρmom : ℝ} (m : ℤ → ℤ → ℕ) (μ : Measure ℂ) (η : ℝ → ℂ) (ID A : Set ℤ)
    (ε R α ρ C_exit c₀ C_good βm h : ℝ) (N_cov : ℕ) (z x : ℂ) (b : ℤ)
    (hID : ID = interiorCellVertices ε η (ball x (R / 4)))
    (hε : 0 < ε) (hR : 0 < R) (hR1 : R ≤ 1) (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5) (hCg : 0 ≤ C_good)
    (hεα : ε ^ α ≤ R / 100) (hεmass : ε ^ α ≤ (R / 4) ^ βm)
    (hb : b ∈ cellVertices ε η (sphere z (4 * R / 3)))
    (hx : x = η (ε * b))
    (hcell : ∀ p ∈ cell ε η b, ∀ q ∈ cell ε η b, dist p q ≤ h) (hh : h ≤ R / 100)
    (hx1 : ‖x‖ < ρmom - R / 4)
    (hvol : ∀ y ∈ ball (0 : ℂ) (ρmom - R / 4), ENNReal.ofReal ((R / 4) ^ βm) ≤ μ (ball y (R / 4)))
    (hρ : ball x (R / 4) ⊆ ball 0 ρ)
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
    (hfinD : μ (ball x (3 * c₀ * R)) ≠ ⊤) :
    ∫ w, occCount A (fun w => (vExitTime ID w).toNat) w ^ 2 ∂(srwLaw m b)
      ≤ 32 * C_exit ^ 2 * ((1 + N_cov * Real.log 4) * C_good) ^ 2 * (ε⁻¹) ^ 2
          * (1 + Real.log (1 / R)) ^ 2 * (μ (ball x (3 * c₀ * R))).toReal ^ 2 := by
  subst hID
  have hxcell : x ∈ cell ε η b := by
    rw [hx]
    exact ⟨ε * b, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hxz : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100 := by
    obtain ⟨p, hp1, hp2⟩ := hb
    have hpz : ‖p - z‖ = 4 * R / 3 := by
      rw [← dist_eq_norm]; exact mem_sphere.1 hp2
    have hd : dist x p ≤ h := hcell x hxcell p hp1
    have h3 : |‖x - z‖ - ‖p - z‖| ≤ dist x p := by
      rw [dist_eq_norm]
      have := abs_norm_sub_norm_le (x - z) (p - z)
      rwa [show (x - z) - (p - z) = x - p by ring] at this
    rw [hpz] at h3
    have h5 := abs_le.1 (h3.trans (hd.trans hh))
    constructor <;> linarith [h5.1, h5.2]
  have hxA : x ∈ annulus z R (2 * R) := by
    rw [mem_annulus_iff]; constructor <;> linarith [hxz.1, hxz.2]
  have hδ0 : 0 ≤ ε ^ α := Real.rpow_nonneg hε.le α
  have hEA : Metric.thickening (ε ^ α) (ball x (R / 4)) ⊆ annulus z R (2 * R) :=
    thickening_ball_subset_annulus hR hεα hxz
  have hxball : x ∈ ball (0 : ℂ) (ρmom - R / 4) := by
    rw [mem_ball, dist_zero_right]; exact hx1
  have hmassD : ENNReal.ofReal (ε ^ α) ≤ μ (ball x (R / 4)) :=
    (ENNReal.ofReal_le_ofReal hεmass).trans (hvol x hxball)
  have hxID : b ∈ cellVertices ε η (ball x (R / 4)) :=
    ⟨x, hxcell, mem_ball_self (by linarith)⟩
  have hM := hmom (ball x (R / 4)) measurableSet_ball hρ hmassD b hxID 2
  set D0 := ball x (3 * c₀ * R) with hD0
  set Cg := (1 + N_cov * Real.log 4) * C_good with hCg_def
  have hlog4pos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hCg0 : 0 ≤ Cg :=
    mul_nonneg (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hlog4pos)) hCg
  have hgoodS : ScaleCovGoodAnnulusEvent (3 * c₀) Cg R z μ :=
    scaleCovGoodAnnulusEvent_of_isGoodAnnulusEvent hN hc₀ hc₀' hR hgood hpos hfin hatom
  have hPL : printedL R z μ ≤ ENNReal.ofReal (Cg * (1 + |Real.log (4 * R)|)) * μ D0 := by
    refine (printedL_le_of_event hR hCg0 hgoodS).trans ?_
    refine mul_le_mul' le_rfl ?_
    refine (iInf₂_le x (subset_closure hxA)).trans ?_
    exact bumpMass_le_mass_ball (by linarith) hR μ x
  have hS := (sup_log_le_printedL hR hεα hxz μ).trans hPL
  set t := (μ D0).toReal with ht
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hμt : μ D0 = ENNReal.ofReal t := (ENNReal.ofReal_toReal hfinD).symm
  set a := Cg * (1 + |Real.log (4 * R)|) with ha
  have ha0 : 0 ≤ a := mul_nonneg hCg0 (by positivity)
  have hSb : (⨆ z' ∈ ball x (R / 4), ∫⁻ w in Metric.thickening (ε ^ α) (ball x (R / 4)),
      ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ≤ ENNReal.ofReal (a * t) := by
    refine hS.trans (le_of_eq ?_)
    rw [hμt, ENNReal.ofReal_mul ha0]
  have hpow : (⨆ z' ∈ ball x (R / 4), ∫⁻ w in Metric.thickening (ε ^ α) (ball x (R / 4)),
      ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ 2 ≤ ENNReal.ofReal ((a * t) ^ 2) := by
    rw [ENNReal.ofReal_pow (mul_nonneg ha0 ht0)]
    exact pow_le_pow_left₀ zero_le hSb 2
  have hF0 : 0 ≤ ((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ)) := by
    have : 0 < ε ^ (-((2 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hε _
    positivity
  have hMQ : exitTimeMoment m (interiorCellVertices ε η (ball x (R / 4))) b 2
      ≤ ENNReal.ofReal (((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ)) * (a * t) ^ 2) := by
    calc exitTimeMoment m (interiorCellVertices ε η (ball x (R / 4))) b 2
        ≤ ENNReal.ofReal (((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ))) *
            (⨆ z' ∈ ball x (R / 4), ∫⁻ w in Metric.thickening (ε ^ α) (ball x (R / 4)),
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ 2 := hM
      _ ≤ ENNReal.ofReal (((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ))) *
            ENNReal.ofReal ((a * t) ^ 2) := mul_le_mul' le_rfl hpow
      _ = ENNReal.ofReal (((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ)) * (a * t) ^ 2) := by
          rw [ENNReal.ofReal_mul hF0]
  have hint := integral_le_toReal_of_lintegral_le (srwLaw m b) (fun w => sq_nonneg _) ENNReal.ofReal_ne_top
    ((lintegral_occCount_sq_le m A (interiorCellVertices ε η (ball x (R / 4))) b).trans hMQ)
  rw [ENNReal.toReal_ofReal (mul_nonneg hF0 (sq_nonneg _))] at hint
  have hL0 : 0 ≤ Real.log (1 / R) := Real.log_nonneg (one_le_one_div hR hR1)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hlogR : Real.log (4 * R) = Real.log 4 - Real.log (1 / R) := by
    rw [Real.log_mul (by norm_num) hR.ne', one_div, Real.log_inv]; ring
  have hlog : 1 + |Real.log (4 * R)| ≤ 4 * (1 + Real.log (1 / R)) := by
    rw [hlogR]
    have : |Real.log 4 - Real.log (1 / R)| ≤ 3 + Real.log (1 / R) :=
      abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hab : a ≤ Cg * (4 * (1 + Real.log (1 / R))) := mul_le_mul_of_nonneg_left hlog hCg0
  have hεpow : ε ^ (-((2 : ℕ) : ℝ)) = ε⁻¹ ^ 2 := by
    rw [Nat.cast_ofNat, Real.rpow_neg hε.le, Real.rpow_two, inv_pow]
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have hat : a * t ≤ Cg * (4 * (1 + Real.log (1 / R))) * t := mul_le_mul_of_nonneg_right hab ht0
  calc ∫ w, occCount A (fun w => (vExitTime (interiorCellVertices ε η (ball x (R / 4))) w).toNat) w ^ 2
        ∂(srwLaw m b)
      ≤ ((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ)) * (a * t) ^ 2 := hint
    _ ≤ ((Nat.factorial 2 : ℕ) : ℝ) * C_exit ^ 2 * ε ^ (-((2 : ℕ) : ℝ)) *
          (Cg * (4 * (1 + Real.log (1 / R))) * t) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg ha0 ht0) hat 2) hF0
    _ = 32 * C_exit ^ 2 * Cg ^ 2 * (ε⁻¹) ^ 2 * (1 + Real.log (1 / R)) ^ 2 * t ^ 2 := by
        rw [hεpow, hfac]; ring
    _ = 32 * C_exit ^ 2 * ((1 + N_cov * Real.log 4) * C_good) ^ 2 * (ε⁻¹) ^ 2
          * (1 + Real.log (1 / R)) ^ 2 * (μ (ball x (3 * c₀ * R))).toReal ^ 2 := by
        rw [hCg_def]

/-- Copy of `secondMoment_walkState` (WalkStateSecond.lean:12) with the radius `1` of `hx1` and `hvol`
replaced by `ρmom`. The original is unchanged. -/
theorem secondMoment_walkState_rho {ρmom : ℝ} {μ : Measure ℂ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    {ε R α ρ C_exit c₀ C_good βm h Dbl : ℝ} {N_cov : ℕ} {z : ℂ} {b : ℤ}
    (hε : 0 < ε) (hR : 0 < R) (hR1 : R ≤ 1) (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5) (hCg : 0 ≤ C_good)
    (hεα : ε ^ α ≤ R / 100) (hεmass : ε ^ α ≤ (R / 4) ^ βm)
    (hb : b ∈ cellVertices ε η (sphere z (4 * R / 3)))
    (hcell : ∀ p ∈ cell ε η b, ∀ q ∈ cell ε η b, dist p q ≤ h) (hh : h ≤ R / 100)
    (hx1 : ‖vertexPoint ε η b‖ < ρmom - R / 4)
    (hvol : ∀ y ∈ ball (0 : ℂ) (ρmom - R / 4), ENNReal.ofReal ((R / 4) ^ βm) ≤ μ (ball y (R / 4)))
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
  have hS := secondMoment_occCount_rho m μ η _ A ε R α ρ C_exit c₀ C_good βm h N_cov z (vertexPoint ε η b) b rfl
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

#print axioms MatedCRT.Lemma68Window.secondMoment_occCount_rho
#print axioms MatedCRT.Lemma68Window.secondMoment_walkState_rho
