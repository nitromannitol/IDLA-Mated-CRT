import MatedCRT.FirstPass.S4S6c.AnnulusGeometry68

/-!
# LEMMA68 uniform per-test bound (q2, task fp-S4S6c-envscaling-6-7-6-8; write-up B5, B18, C15-C16)

The per-test bound of the printed Lemma 6.8 in the form consumed by `TailBound68.printed68_tail_bound`:
`srwLaw (stayIn) ≤ ofReal (1 - q0 / (1 + log(1/r))²)` with the deterministic constant
`q0 = 1 / (288 Cd² C1²)`, `C1 = Cg (1 + (log 4 - 1)) / (1 - log 2)`.

Inputs (each traced in the write-up):
* the cell geometry: the test vertex `y` has its cell of diameter `≤ R/100` and meeting the sphere `∂B_{4R/3}(z)`
  (B5, cell-size bound; the good event supplies the diameter bound);
* the good-annulus bound `hF` with constant `Cg` and the mass `mr` (LEMMA68 eq (4), Lemma 1 hypothesis);
* the Draft Lemma 2.18 `N = 2` exit-time instance `hexit` with constant `Cd` (EXTERNAL, Draft `ExitTimeUpperBoundStmt`);
* the radius bound `r^p/2 < R` with `p ≤ 3` (write-up C16), which gives `1 + log(1/R) ≤ 3 (1 + log(1/r))`.

The choice `C0 = Cd/(1 + log(1/r))` in `GreenTest68.stayIn_le_printed_green_draft` makes its second moment the sharp
`2 Cd² ε⁻² Sr²` and turns its `(1 + log(1/r))⁻²` factor into `q0 (1 + log(1/r))⁻²`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace MatedCRT

/-- `1 + log(1/R) ≤ 3 (1 + log(1/r))` when `R > r^p/2` with `p ≤ 3` and `0 < r ≤ 1` (write-up C16). -/
theorem one_add_log_inv_le_three {R r p : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hp : p ≤ 3) (hR : 0 < R)
    (hRpow : r ^ p / 2 < R) :
    1 + Real.log (1 / R) ≤ 3 * (1 + Real.log (1 / r)) := by
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
  have h1 : 1 / R ≤ 2 / r ^ p := by
    rw [div_le_div_iff₀ hR hrp]
    linarith
  have h2 : Real.log (1 / R) ≤ Real.log (2 / r ^ p) :=
    Real.log_le_log (by positivity) h1
  have h3 : Real.log (2 / r ^ p) = Real.log 2 - p * Real.log r := by
    rw [Real.log_div (by norm_num) hrp.ne', Real.log_rpow hr]
  have h4 : Real.log (1 / r) = - Real.log r := by
    rw [one_div, Real.log_inv]
  have h5 : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have h6 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h7 : p * Real.log (1 / r) ≤ 3 * Real.log (1 / r) := mul_le_mul_of_nonneg_right hp h5
  have h8 : p * Real.log (1 / r) = - (p * Real.log r) := by
    rw [h4]
    ring
  linarith

/-- The vertex point `η(εk)` of a cell `η([ε(k-1), εk])` lies within the cell diameter `d` of any point of the cell,
so if the cell meets the sphere `∂B_{4R/3}(z)` the vertex lies in `{|x - z| ∈ [4R/3 - d, 4R/3 + d]}`. -/
theorem vertex_norm_sub_of_cell_meets_sphere {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε)
    {d R : ℝ} {z : ℂ} {k : ℤ} (hd : diam (cell ε η k) ≤ d)
    (hmeet : (cell ε η k ∩ sphere z (4 * R / 3)).Nonempty) :
    4 * R / 3 - d ≤ ‖vertexPoint ε η k - z‖ ∧ ‖vertexPoint ε η k - z‖ ≤ 4 * R / 3 + d := by
  obtain ⟨p, hpc, hps⟩ := hmeet
  have hv : vertexPoint ε η k ∈ cell ε η k := by
    unfold cell vertexPoint
    exact ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hbdd : Bornology.IsBounded (cell ε η k) := by
    unfold cell
    exact (isCompact_Icc.image hη).isBounded
  have hdist : dist (vertexPoint ε η k) p ≤ d :=
    (Metric.dist_le_diam_of_mem hbdd hv hpc).trans hd
  have hp : ‖p - z‖ = 4 * R / 3 := by
    rw [mem_sphere, dist_eq_norm] at hps
    exact hps
  have key : |‖vertexPoint ε η k - z‖ - ‖p - z‖| ≤ dist (vertexPoint ε η k) p := by
    rw [dist_eq_norm]
    have h := abs_norm_sub_norm_le (vertexPoint ε η k - z) (p - z)
    have e : (vertexPoint ε η k - z) - (p - z) = vertexPoint ε η k - p := by ring
    rw [e] at h
    exact h
  rw [hp] at key
  have h2 := abs_le.mp (key.trans hdist)
  constructor <;> linarith [h2.1, h2.2]

/-- **LEMMA68 per-test bound, uniform form** (write-up B18, C15-C16). For a test vertex `y` whose cell has diameter at most
`R/100` and meets the sphere `∂B_{4R/3}(z)`, with the good-annulus bound (`hF`, constant `Cg`, mass `mr`), the Draft
Lemma 2.18 second moment (`hexit`, constant `Cd`) and the radius bound `r^p/2 < R`, `p ≤ 3`, the walk from `y` stays in `A`
until it exits the test window with probability at most `1 - q0 / (1 + log(1/r))²`, `q0 = 1 / (288 Cd² C1²)`. -/
theorem printed_test_bound {μ : Measure ℂ} [SFinite μ] {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {W : ℤ → Set ℤ} {A : Set ℤ}
    {y : ℤ} {ε R r mr s1 β c0 C Cd Cg p δ : ℝ} {z : ℂ} {Aset : Finset ℤ}
    (hap : IsAreaParametrized μ η) (hη : Continuous η) (hε : 0 < ε) (hR : 0 < R) (hR1 : R ≤ 1)
    (hmr : 0 < mr) (hC : 0 < C) (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hc0 : 0 < c0) (hc0' : c0 < 1 / 8) (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16) (hεc : ε ≤ 16 * c0)
    (hr : 0 < r) (hr1 : r ≤ 1) (hp : p ≤ 3) (hRpow : r ^ p / 2 < R)
    (hmu : ENNReal.ofReal mr ≤ μ (ball (vertexPoint ε η y) (c0 * R)))
    (hfinD : (cellVertices ε η (ball (vertexPoint ε η y) (c0 * R))).Finite)
    (hfinr : (cellVertices ε η (ball (vertexPoint ε η y) r)).Finite)
    (hRr : ball (vertexPoint ε η y) (c0 * R) ⊆ ball (vertexPoint ε η y) r)
    (hWdef : W y = interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 4)))
    (hAs : ∀ k, k ∈ Aset ↔ k ∈ A ∩ cellVertices ε η (ball (vertexPoint ε η y) (c0 * R)))
    (hsp : ((A ∩ cellVertices ε η (ball (vertexPoint ε η y) r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε)
    (hs : s1 * r ^ (2 * β) ≤ mr / 4)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η y) (R / 4)).Nonempty → diam (cell ε η k) ≤ c0 * R)
    (hGreenAt : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η y) (c0 * R)),
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b ≤
          greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b ∧
        C⁻¹ * Real.log (if vertexPoint ε η y = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η y - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b)
    (hdy : diam (cell ε η y) ≤ R / 100) (hmeet : (cell ε η y ∩ sphere z (4 * R / 3)).Nonempty)
    (hδ : δ ≤ R / 100) (hμA : μ (closedAnnulus z R) ≠ ⊤)
    (hint : ∀ v ∈ ball (vertexPoint ε η y) (R / 4),
      IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) (closedAnnulus z R) μ)
    (hF : ∀ w ∈ closedAnnulus z R,
      ∫ u in closedAnnulus z R, (Real.log (R / ‖u - w‖) + 1) ∂μ ≤ Cg * mr)
    (hexit : exitTimeMoment m (W y) y 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * Cd ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
        (⨆ v ∈ ball (vertexPoint ε η y) (R / 4), ∫⁻ u in thickening δ (ball (vertexPoint ε η y) (R / 4)),
          ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) ^ (2 : ℕ)) :
    srwLaw m y (TestBound68.stayIn W A y) ≤
      ENNReal.ofReal (1 - (1 / (288 * Cd ^ 2 * (Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2)) /
        (1 + Real.log (1 / r)) ^ 2) := by
  have hlog : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hpos1 : 0 < 1 + Real.log (1 / r) := by linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hκ : 0 < 1 - Real.log 2 := by linarith
  have ha0 : 0 < 1 + (Real.log 4 - 1) := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 3 * (1 + Real.log (1 / r)) := ⟨_, rfl⟩
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ, C0 = Cd / (1 + Real.log (1 / r)) := ⟨_, rfl⟩
  obtain ⟨C1, hC1def⟩ : ∃ C1 : ℝ, C1 = Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2) := ⟨_, rfl⟩
  have hL : 0 < L := by rw [hLdef]; linarith
  have hC0 : 0 < C0 := by rw [hC0def]; exact div_pos hCd hpos1
  have hC1pos : 0 < C1 := by rw [hC1def]; exact div_pos (mul_pos hCg ha0) hκ
  have hCdC0 : Cd ≤ C0 * (1 + Real.log (1 / r)) := by
    rw [hC0def, div_mul_cancel₀ _ hpos1.ne']
  -- the Lemma 1 potential bound at the test vertex (B5, eq (21)) with the radius bound (C16)
  have hLR := one_add_log_inv_le_three hr hr1 hp hR hRpow
  have hS : (⨆ v ∈ ball (vertexPoint ε η y) (R / 4), ∫⁻ u in thickening δ (ball (vertexPoint ε η y) (R / 4)),
      ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) ≤ ENNReal.ofReal (C1 * L * mr) := by
    have hx : 4 * R / 3 - R / 100 ≤ ‖vertexPoint ε η y - z‖ ∧ ‖vertexPoint ε η y - z‖ ≤ 4 * R / 3 + R / 100 :=
      vertex_norm_sub_of_cell_meets_sphere hη hε hdy hmeet
    have hsum := draft_sup_le_of_centre μ hR hR1 hx hδ hμA hCg.le hmr.le hint hF
    have hK : 0 ≤ Cg * mr * (1 + (Real.log 4 - 1)) / (1 - Real.log 2) :=
      div_nonneg (mul_nonneg (mul_nonneg hCg.le hmr.le) ha0.le) hκ.le
    have key : Cg * mr * (1 + (Real.log 4 - 1)) * (1 + Real.log (1 / R)) / (1 - Real.log 2) ≤ C1 * L * mr := by
      rw [hC1def, hLdef]
      have e1 : Cg * mr * (1 + (Real.log 4 - 1)) * (1 + Real.log (1 / R)) / (1 - Real.log 2) =
          (Cg * mr * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) * (1 + Real.log (1 / R)) := by ring
      have e2 : Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2) * (3 * (1 + Real.log (1 / r))) * mr =
          (Cg * mr * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) * (3 * (1 + Real.log (1 / r))) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hLR hK
    exact hsum.trans (ENNReal.ofReal_le_ofReal key)
  have hS0 : 0 ≤ C1 * L * mr := mul_nonneg (mul_nonneg hC1pos.le hL.le) hmr.le
  have hres := stayIn_le_printed_green_draft hap hε hR hmr hC hc0 hc0' hc0C hεc hmu hfinD hfinr hRr hWdef hAs hsp
    hs hdiam hGreenAt hC0 hC1pos hL hr hr1 hS0 le_rfl hCd.le hCdC0 hexit hS
  have hne1 : (1 + Real.log (1 / r)) ≠ 0 := hpos1.ne'
  have hneCd : Cd ≠ 0 := hCd.ne'
  have hneCg : Cg ≠ 0 := hCg.ne'
  have hneκ : 1 - Real.log 2 ≠ 0 := hκ.ne'
  have hneA : 1 + (Real.log 4 - 1) ≠ 0 := ha0.ne'
  have hq : (1 / (32 * C0 ^ 2 * C1 ^ 2 * L ^ 2)) / (1 + Real.log (1 / r)) ^ 2 =
      (1 / (288 * Cd ^ 2 * (Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2)) /
        (1 + Real.log (1 / r)) ^ 2 := by
    rw [hC0def, hLdef, hC1def]
    field_simp
    ring
  rw [hq] at hres
  exact hres

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.one_add_log_inv_le_three
#print axioms MatedCRT.vertex_norm_sub_of_cell_meets_sphere
#print axioms MatedCRT.printed_test_bound
