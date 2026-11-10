import MatedCRT.FirstPass.S4S6c.HcGreen68
import MatedCRT.FirstPass.S4S6c.PrintedGreen68
import MatedCRT.FirstPass.S4S6c.AnnulusGeometry68
import MatedCRT.FirstPass.S4S6c.OpenAnnulus68

/-!
# The local test `hloc` of the per-configuration Lemma 6.8, from the event inputs (q2, task fp-S4S6c-envscaling-6-7-6-8)

`hloc_point` instantiates `HcGreen68.stayIn_le_printed_interior` at one start vertex `b` of the sphere band, with the
disk radius `R` (`R = rad y` in `Uniform68.config_exit_lower_bound`). Its inputs are named by their event:

* `hGreenLow`: the Green lower bound of Draft Lemma 2.16 (`GreenKernelLowerBoundStmt`) at the radius `r = R/8`;
* `hdraft`: the second moment of Draft Lemma 2.18 (`ExitTimeUpperBoundStmt`, `N = 2`) for `D = B_{R/4}(η(b))`;
* `hF`: the good-annulus bound (eq. (9) of LEMMA68; corrected event `E_R(z)` of the printed Lemma 6.4 family) on the
  annulus `A_{R,2R}(z)`, `z = ctr y`, with the mass `mr = μ(B_{c₀R}(η(b)))`;
* `hmr_eq`, `hs`, `hsp`, `hdiam`: the mass, sparsity and cell-size inputs; `hDA`, `hEA`, `hint`, `hμA`: the geometry.

Scale bookkeeping. `PrintedGreen68.draft_sup_le_of_annulus` bounds the kernel supremum by `κ mr (1 + log(1/R))` with
`κ = C_g (1 + (log 4 - 1)) / (1 - log 2)`. The stayIn lemma has its logarithmic factor only in the second-moment constant
`Cd`, so the supremum is rescaled: `S := ofReal(1/L) · S_true`, `L = 1 + log(1/R)`, `Cd := C_E L`. The second moment is
unchanged, `ofReal(F C_E² ε^{-2}) S_true² = ofReal(F (C_E L)² ε^{-2}) (S_true/L)²` (`ennreal_scale_aux`).
Then `L ≤ K_L (1 + log(1/r))` (input `hLR`, from `R ≥ r^p/2`) gives the constant `C0 = C_E K_L`.

Terminology: Green kernel and harmonic measure (Armitage-Gardiner), exit-time moments (Berestycki-Gwynne), LQG measure
(Duplantier-Sheffield), good annuli (Berestycki-Powell; Armstrong-Kuusi-Mourrat).
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT
namespace Uniform68Events

theorem one_sub_log_two_pos : 0 < 1 - Real.log 2 := by
  have h2 : Real.log 2 < 2 - 1 := Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
  linarith

theorem log_four_factor_pos : 0 < 1 + (Real.log 4 - 1) := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  linarith

/-- The constant of the sup-kernel bound: `κ = C_g (1 + (log 4 - 1)) / (1 - log 2)`. -/
noncomputable def kappaAnn (Cg : ℝ) : ℝ := Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)

theorem kappaAnn_pos {Cg : ℝ} (hCg : 0 < Cg) : 0 < kappaAnn Cg :=
  div_pos (mul_pos hCg log_four_factor_pos) one_sub_log_two_pos

/-- Deterministic scale bookkeeping: `ofReal(X L²) (ofReal(1/L) T)² = ofReal X T²` for `X ≥ 0`, `L > 0`. -/
theorem ennreal_scale_aux {X L : ℝ} (hX : 0 ≤ X) (hL : 0 < L) (T : ℝ≥0∞) :
    ENNReal.ofReal (X * L ^ 2) * (ENNReal.ofReal (1 / L) * T) ^ 2 = ENNReal.ofReal X * T ^ 2 := by
  have hLne : L ≠ 0 := hL.ne'
  have h1 : ENNReal.ofReal (L ^ 2) * ENNReal.ofReal (1 / L) ^ 2 = 1 := by
    rw [← ENNReal.ofReal_pow (one_div_pos.mpr hL).le, ← ENNReal.ofReal_mul (sq_nonneg L)]
    rw [show L ^ 2 * (1 / L) ^ 2 = 1 by field_simp]
    simp
  calc ENNReal.ofReal (X * L ^ 2) * (ENNReal.ofReal (1 / L) * T) ^ 2
      = ENNReal.ofReal X * (ENNReal.ofReal (L ^ 2) * ENNReal.ofReal (1 / L) ^ 2) * T ^ 2 := by
        rw [ENNReal.ofReal_mul hX]; ring
    _ = ENNReal.ofReal X * T ^ 2 := by rw [h1, mul_one]

/-- The sup-kernel bound of the good annulus, in the form `S_true ≤ ofReal(κ mr (1 + log(1/R)))`. -/
theorem sup_le_kappa {μ : Measure ℂ} [SFinite μ] {x z : ℂ} {R Cg mr δ : ℝ}
    (hR0 : 0 < R) (hR1 : R ≤ 1) (hδ : δ ≤ 1 / 2) (hCg : 0 < Cg) (hmr : 0 ≤ mr)
    (hμA : μ (openAnnulus z R) ≠ ⊤)
    (hDA : ball x (R / 4) ⊆ openAnnulus z R) (hEA : thickening δ (ball x (R / 4)) ⊆ openAnnulus z R)
    (hint : ∀ v ∈ ball x (R / 4),
      IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) (openAnnulus z R) μ)
    (hF : ∀ w ∈ openAnnulus z R, ∫ u in openAnnulus z R, (Real.log (R / ‖u - w‖) + 1) ∂μ ≤ Cg * mr) :
    (⨆ v ∈ ball x (R / 4), ∫⁻ u in thickening δ (ball x (R / 4)),
        ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) ≤
      ENNReal.ofReal (kappaAnn Cg * mr * (1 + Real.log (1 / R))) := by
  have h := draft_sup_le_of_annulus μ hR0 hR1 hδ (isOpen_openAnnulus z R).measurableSet
    (openAnnulus_subset_closedBall z R) hμA (sphere_subset_openAnnulus hR0) hDA hEA hCg.le hmr hint hF
  have he : Cg * mr * (1 + (Real.log 4 - 1)) * (1 + Real.log (1 / R)) / (1 - Real.log 2)
      = kappaAnn Cg * mr * (1 + Real.log (1 / R)) := by
    unfold kappaAnn; ring
  rw [he] at h
  exact h

/-- **Local test `hloc` of the printed Lemma 6.8 at one start vertex `b`** (`Uniform68.config_exit_lower_bound`, `hloc`).
The stay-in probability of the window `I(B_{R/4}(η(b)))` in `A = S' \ Θ` is at most `1 - q0/(1 + log(1/r))²`, with
`q0 = 1/(32 C0² κ²)`, `C0 = C_E K_L`. Obtained from `HcGreen68.stayIn_le_printed_interior` with the rescaled sup. -/
theorem hloc_point {μ : Measure ℂ} [SFinite μ] {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {A : Set ℤ} {b : ℤ}
    {ε R r c0 C C_E Cg δ s1 β KL mr : ℝ}
    (hap : IsAreaParametrized μ η) (hε : 0 < ε) (hR : 0 < R) (hR1 : R ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hδ : δ ≤ 1 / 2) (hCE : 0 < C_E) (hCg : 0 < Cg) (hKL : 0 < KL) (hC : 0 < C)
    (hc0 : 0 < c0) (hc0' : c0 < 1 / 8) (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16) (hεc : ε ≤ 16 * c0)
    (hmr_eq : mr = (μ (ball (vertexPoint ε η b) (c0 * R))).toReal)
    (hmfin : μ (ball (vertexPoint ε η b) (c0 * R)) ≠ ⊤) (hmr : 0 < mr)
    (hfinD : (cellVertices ε η (ball (vertexPoint ε η b) (c0 * R))).Finite)
    (hfinr : (cellVertices ε η (ball (vertexPoint ε η b) r)).Finite)
    (hRr : c0 * R ≤ r)
    (hsp : ((A ∩ cellVertices ε η (ball (vertexPoint ε η b) r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε)
    (hs : s1 * r ^ (2 * β) ≤ mr / 4)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η b) (R / 4)).Nonempty → diam (cell ε η k) ≤ c0 * R)
    (hGreenLow : ∀ b' ∈ cellVertices ε η (ball (vertexPoint ε η b) (c0 * R)),
      C⁻¹ * Real.log (if vertexPoint ε η b = vertexPoint ε η b' then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η b - vertexPoint ε η b'‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η b) (R / 8))) b b')
    (hdraft : exitTimeMoment m (interiorCellVertices ε η (ball (vertexPoint ε η b) (R / 4))) b 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * C_E ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
        (⨆ v ∈ ball (vertexPoint ε η b) (R / 4), ∫⁻ u in thickening δ (ball (vertexPoint ε η b) (R / 4)),
          ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) ^ (2 : ℕ))
    (z : ℂ)
    (hμA : μ (openAnnulus z R) ≠ ⊤)
    (hDA : ball (vertexPoint ε η b) (R / 4) ⊆ openAnnulus z R)
    (hEA : thickening δ (ball (vertexPoint ε η b) (R / 4)) ⊆ openAnnulus z R)
    (hint : ∀ v ∈ ball (vertexPoint ε η b) (R / 4),
      IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) (openAnnulus z R) μ)
    (hF : ∀ w ∈ openAnnulus z R, ∫ u in openAnnulus z R, (Real.log (R / ‖u - w‖) + 1) ∂μ ≤ Cg * mr)
    (hLR : 1 + Real.log (1 / R) ≤ KL * (1 + Real.log (1 / r))) :
    srwLaw m b (TestBound68.stayIn (fun b' => innerVertices (cell ε η) (ball (vertexPoint ε η b') (R / 4))) A b) ≤
      ENNReal.ofReal (1 - (1 / (32 * (C_E * KL) ^ 2 * (kappaAnn Cg) ^ 2 * 1 ^ 2)) / (1 + Real.log (1 / r)) ^ 2) := by
  have hmu : ENNReal.ofReal mr ≤ μ (ball (vertexPoint ε η b) (c0 * R)) :=
    le_of_eq (by rw [hmr_eq, ENNReal.ofReal_toReal hmfin])
  have hL0 : 0 < 1 + Real.log (1 / R) := by
    have h1R : (1 : ℝ) ≤ 1 / R := by rw [le_div_iff₀ hR]; linarith
    have := Real.log_nonneg h1R
    linarith
  have hSup := sup_le_kappa (x := vertexPoint ε η b) (z := z) hR hR1 hδ hCg hmr.le hμA hDA hEA hint hF
  set L := 1 + Real.log (1 / R) with hLdef
  set Strue := (⨆ v ∈ ball (vertexPoint ε η b) (R / 4), ∫⁻ u in thickening δ (ball (vertexPoint ε η b) (R / 4)),
        ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) with hStrue
  have hS : ENNReal.ofReal (1 / L) * Strue ≤ ENNReal.ofReal (kappaAnn Cg * mr) := by
    calc ENNReal.ofReal (1 / L) * Strue
        ≤ ENNReal.ofReal (1 / L) * ENNReal.ofReal (kappaAnn Cg * mr * L) := by gcongr
      _ = ENNReal.ofReal (kappaAnn Cg * mr) := by
          rw [← ENNReal.ofReal_mul (one_div_pos.mpr hL0).le]
          congr 1
          field_simp
  have hXnn : 0 ≤ ((2 : ℕ).factorial : ℝ) * C_E ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hCE.le _)) (Real.rpow_nonneg hε.le _)
  have hexit : exitTimeMoment m (interiorCellVertices ε η (ball (vertexPoint ε η b) (R / 4))) b 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * (C_E * L) ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
        (ENNReal.ofReal (1 / L) * Strue) ^ (2 : ℕ) := by
    refine hdraft.trans (le_of_eq ?_)
    have hX : ((2 : ℕ).factorial : ℝ) * (C_E * L) ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))
        = (((2 : ℕ).factorial : ℝ) * C_E ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) * L ^ (2 : ℕ) := by ring
    rw [hX, ennreal_scale_aux hXnn hL0 Strue]
  have hCd : C_E * L ≤ (C_E * KL) * (1 + Real.log (1 / r)) := by
    calc C_E * L ≤ C_E * (KL * (1 + Real.log (1 / r))) := mul_le_mul_of_nonneg_left hLR hCE.le
      _ = (C_E * KL) * (1 + Real.log (1 / r)) := by ring
  have hSm : kappaAnn Cg * mr ≤ kappaAnn Cg * 1 * mr := le_of_eq (by ring)
  exact HcGreen68.stayIn_le_printed_interior (μ := μ) (η := η) (m := m) (A := A) (y := b) (ε := ε)
    (R := R) (r := r) (mr := mr) (s1 := s1) (β := β) (C0 := C_E * KL) (C1 := kappaAnn Cg) (L := 1)
    (Sr := kappaAnn Cg * mr) (c0 := c0) (C := C) (Cd := C_E * L) (S := ENNReal.ofReal (1 / L) * Strue)
    (Aset := (hfinD.inter_of_right A).toFinset)
    hap hε hR hmr hC hc0 hc0' hc0C hεc hmu hfinD hfinr (Metric.ball_subset_ball hRr)
    (fun k => Set.Finite.mem_toFinset _) hsp hs hdiam hGreenLow (mul_pos hCE hKL) (kappaAnn_pos hCg)
    one_pos hr hr1 (mul_nonneg (kappaAnn_pos hCg).le hmr.le) hSm (mul_pos hCE hL0).le hCd hexit hS

end Uniform68Events
end MatedCRT

#print axioms MatedCRT.Uniform68Events.hloc_point
