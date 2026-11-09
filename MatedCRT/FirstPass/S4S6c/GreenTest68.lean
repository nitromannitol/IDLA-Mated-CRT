import MatedCRT.FirstPass.S4S6c.PrintedTest68

/-!
# The Green lower bound `hG` of the per-test bound of Lemma 6.8 (q2, task fp-S4S6c; LEMMA68 B4, B11-B13)

The test window `W y = I(B_{R/4}(x))` (interior vertices, `x = η(y)`) is killed on leaving the interior of the
disk. The expected visits `G_{W y}(y, b)` are bounded below through the Green kernel lower bound of the paper
(Draft `GreenKernelLowerBoundStmt`, Lemma 2.16, cited from Berestycki-Gwynne BG20 Lemma 4.4), used at radius `R/8`:
* domain monotonicity of the expected visits (`visitsBeforeExit_le_of_subset`), via `vExitTime` monotone in the domain;
* the inclusion `I(B_{R/8}(x)) ⊆ I(B_{R/4}(x))` from the cell-diameter bound `diam(H_k) ≤ c₀R` (`interiorCellVertices_mono_of_radius`);
* the distance bound `|η(v) - x| < 2 c₀ R` for `v ∈ V(B_{c₀R}(x))` (`cell_dist_lt`, eq. (B7)), which makes the clipped factor
  at least `1/(16 c₀)` and hence `C_G⁻¹ log(1/(16 c₀)) - 1 ≥ 1` for `c₀ ≤ e^{-2C_G}/16` (B12, B13).
The Green lower bound and the cell-diameter bound enter as explicit hypotheses (Draft Lemma 2.16 at the vertex, and the
cell-size event Draft `CellSizeEstimateStmt`).
-/

open MeasureTheory Set Metric Function Real
open scoped ENNReal

namespace MatedCRT
namespace GreenTest68

/-- Domain monotonicity of the exit time: a smaller domain is exited no later. -/
theorem vExitTime_le_of_subset {A B : Set ℤ} (hAB : A ⊆ B) (x : ℕ → ℤ) :
    vExitTime A x ≤ vExitTime B x := by
  classical
  unfold vExitTime
  by_cases hB : ∃ n, x n ∉ B
  · have hA : ∃ n, x n ∉ A := by
      obtain ⟨n, hn⟩ := hB
      exact ⟨n, fun h => hn (hAB h)⟩
    rw [dite_eq_left_of_eq_true (eq_true hA), dite_eq_left_of_eq_true (eq_true hB)]
    exact_mod_cast Nat.find_min' hA (m := Nat.find hB) (fun h => Nat.find_spec hB (hAB h))
  · rw [dite_eq_right_of_eq_false (eq_false hB)]
    exact le_top

/-- Expected visits to `b` before exit are monotone in the domain (`A ⊆ B`). -/
theorem visitsBeforeExit_le_of_subset {A B : Set ℤ} (hAB : A ⊆ B) (b : ℤ) (x : ℕ → ℤ) :
    visitsBeforeExit A b x ≤ visitsBeforeExit B b x := by
  unfold visitsBeforeExit
  refine ENNReal.tsum_le_tsum fun n => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨lt_of_lt_of_le h1.1 (vExitTime_le_of_subset hAB x), h1.2⟩ h2
  · exact zero_le
  · exact le_rfl

/-- The expected visits `∫⁻ visitsBeforeExit` equal the sum of the probabilities of the visit events (Tonelli). -/
theorem lintegral_visits_eq_tsum (μ : Measure (ℕ → ℤ)) (A : Set ℤ) (b : ℤ) :
    ∫⁻ x, visitsBeforeExit A b x ∂μ = ∑' n : ℕ, μ {x | (n : ℕ∞) < vExitTime A x ∧ x n = b} := by
  have hset : ∀ n : ℕ, MeasurableSet {x : ℕ → ℤ | (n : ℕ∞) < vExitTime A x ∧ x n = b} := fun n => by
    have h1 : MeasurableSet {x : ℕ → ℤ | x n = b} :=
      measurableSet_eq_fun (measurable_pi_apply n) measurable_const
    exact (ConstantOrderDiv.measurableSet_lt_vExitTime A n).inter h1
  have hind : ∀ n : ℕ,
      (fun x : ℕ → ℤ => if (n : ℕ∞) < vExitTime A x ∧ x n = b then (1 : ℝ≥0∞) else 0)
        = {x : ℕ → ℤ | (n : ℕ∞) < vExitTime A x ∧ x n = b}.indicator 1 := by
    intro n
    funext x
    by_cases h : (n : ℕ∞) < vExitTime A x ∧ x n = b
    · simp [h]
    · simp [h]
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun x : ℕ → ℤ => if (n : ℕ∞) < vExitTime A x ∧ x n = b then (1 : ℝ≥0∞) else 0) μ := fun n => by
    rw [hind n]
    exact (measurable_one.indicator (hset n)).aemeasurable
  unfold visitsBeforeExit
  rw [lintegral_tsum hmeas]
  refine tsum_congr fun n => ?_
  rw [hind n, lintegral_indicator_one (hset n)]

/-- A cell of diameter at most `d` meeting `B_r(x)` lies in `B_{r+d}(x)`. -/
theorem cell_dist_lt {η : ℝ → ℂ} (hη : Continuous η) {ε d r : ℝ} {k : ℤ} {x : ℂ}
    (hdiam : diam (cell ε η k) ≤ d) (hk : (cell ε η k ∩ ball x r).Nonempty) {w : ℂ}
    (hw : w ∈ cell ε η k) : dist w x < r + d := by
  obtain ⟨u, hu1, hu2⟩ := hk
  have hbdd : Bornology.IsBounded (cell ε η k) := by
    unfold cell
    exact (isCompact_Icc.image hη).isBounded
  have h1 : dist w u ≤ diam (cell ε η k) := dist_le_diam_of_mem hbdd hw hu1
  have h2 : dist u x < r := mem_ball.mp hu2
  have h3 := dist_triangle w u x
  linarith

/-- The vertex point `η(εk)` lies in the cell `H_k = η([ε(k-1), εk])`. -/
theorem vertexPoint_mem_cell {η : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨by nlinarith, le_rfl⟩, rfl⟩

/-- Cells of diameter at most `c₀ R` meeting `B_{R/8}(x)` avoid the sphere `∂B_{R/4}(x)` (eq. (B11)), hence
`I(B_{R/8}(x)) ⊆ I(B_{R/4}(x))` for `c₀ < 1/8`. -/
theorem interiorCellVertices_mono_of_radius {η : ℝ → ℂ} (hη : Continuous η) {ε R c0 : ℝ} {x : ℂ}
    (hR : 0 < R) (hc0' : c0 < 1 / 8)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball x (R / 4)).Nonempty → diam (cell ε η k) ≤ c0 * R) :
    interiorCellVertices ε η (ball x (R / 8)) ⊆ interiorCellVertices ε η (ball x (R / 4)) := by
  rintro v ⟨hv1, hv2⟩
  have hv1' : (cell ε η v ∩ ball x (R / 8)).Nonempty := hv1
  refine ⟨?_, ?_⟩
  · exact hv1'.mono (inter_subset_inter_right _ (ball_subset_ball (by linarith)))
  · intro hfr
    have hfr' : (cell ε η v ∩ frontier (ball x (R / 4))).Nonempty := hfr
    obtain ⟨w, hw1, hw2⟩ := hfr'
    rw [frontier_ball x (by positivity : R / 4 ≠ 0)] at hw2
    have hd := hdiam v (hv1'.mono (inter_subset_inter_right _ (ball_subset_ball (by linarith))))
    have hlt := cell_dist_lt hη hd hv1' hw1
    have hsph : dist w x = R / 4 := mem_sphere.mp hw2
    have hc : c0 * R < 1 / 8 * R := mul_lt_mul_of_pos_right hc0' hR
    linarith

/-- **Green lower bound at the test window (LEMMA68 B4, B11-B13).** Let `x = η(y)`, `R > 0`, `0 < c₀ < 1/8`,
`c₀ ≤ e^{-2C}/16` and `ε ≤ 16 c₀`. Assume the cell-diameter bound `diam H_k ≤ c₀R` on the cells meeting `B_{R/4}(x)`, and
the Green kernel lower bound of Draft Lemma 2.16 (`GreenKernelLowerBoundStmt`, at the start `y`, radius `R/8`, target `b`).
Then for each target `b ∈ V(B_{c₀R}(x))` the expected visits to `b` before exit of `I(B_{R/4}(x))` are at least `1/2`. -/
theorem hG_of_green {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {ε R c0 C : ℝ} {y b : ℤ}
    (hη : Continuous η) (hε : 0 < ε) (hR : 0 < R) (hC : 0 < C) (hc0 : 0 < c0) (hc0' : c0 < 1 / 8)
    (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16) (hεc : ε ≤ 16 * c0)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η y) (R / 4)).Nonempty → diam (cell ε η k) ≤ c0 * R)
    (hb : b ∈ cellVertices ε η (ball (vertexPoint ε η y) (c0 * R)))
    (hGreen : greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b
          ≤ greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b ∧
        C⁻¹ * Real.log (if vertexPoint ε η y = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η y - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b) :
    ENNReal.ofReal (1 / 2) ≤
      ∑' n : ℕ, srwLaw m y {x | (n : ℕ∞) < vExitTime
        (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 4))) x ∧ x n = b} := by
  set x := vertexPoint ε η y with hx
  have hpos16 : 0 < 16 * c0 := by linarith
  have hRne : R ≠ 0 := hR.ne'
  have hc0ne : c0 ≠ 0 := hc0.ne'
  -- (B7): the vertex point of `b` is within `2 c₀ R` of `x`
  have hb' : (cell ε η b ∩ ball x (c0 * R)).Nonempty := hb
  have hdb : diam (cell ε η b) ≤ c0 * R :=
    hdiam b (hb'.mono (inter_subset_inter_right _ (ball_subset_ball (by nlinarith))))
  have hdist : dist (vertexPoint ε η b) x < c0 * R + c0 * R :=
    cell_dist_lt hη hdb hb' (vertexPoint_mem_cell hε b)
  have hnorm : ‖x - vertexPoint ε η b‖ = dist (vertexPoint ε η b) x := by
    rw [dist_eq_norm, norm_sub_rev]
  have hle : ‖x - vertexPoint ε η b‖ ≤ 2 * c0 * R := by
    rw [hnorm]
    linarith [show 2 * c0 * R = c0 * R + c0 * R by ring]
  -- the clipped factor is at least `1 / (16 c₀)` (B12)
  have hεinv : 1 / (16 * c0) ≤ ε⁻¹ := by
    have h1 : ε⁻¹ = 1 / ε := (one_div ε).symm
    rw [h1]
    exact one_div_le_one_div_of_le hε hεc
  have hlogLB : 1 / (16 * c0) ≤
      (if x = vertexPoint ε η b then ε⁻¹ else min ((R / 8) / ‖x - vertexPoint ε η b‖) ε⁻¹) := by
    split_ifs with heq
    · exact hεinv
    · apply le_min
      · have hpos : 0 < ‖x - vertexPoint ε η b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
        have key : (R / 8) / (2 * c0 * R) = 1 / (16 * c0) := by
          field_simp
          ring
        rw [← key]
        exact div_le_div_of_nonneg_left (by positivity) hpos hle
      · exact hεinv
  -- `log (1/(16 c₀)) ≥ 2C` from `c₀ ≤ e^{-2C}/16`
  have h16 : 16 * c0 ≤ Real.exp (-(2 * C)) := by linarith [hc0C]
  have hexp : Real.exp (2 * C) ≤ 1 / (16 * c0) := by
    rw [le_div_iff₀ hpos16]
    calc Real.exp (2 * C) * (16 * c0) ≤ Real.exp (2 * C) * Real.exp (-(2 * C)) :=
          mul_le_mul_of_nonneg_left h16 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have h2C : 2 * C ≤ Real.log (1 / (16 * c0)) := by
    calc 2 * C = Real.log (Real.exp (2 * C)) := (Real.log_exp _).symm
      _ ≤ Real.log (1 / (16 * c0)) := Real.log_le_log (Real.exp_pos _) hexp
  have hlogif : 2 * C ≤ Real.log
      (if x = vertexPoint ε η b then ε⁻¹ else min ((R / 8) / ‖x - vertexPoint ε η b‖) ε⁻¹) :=
    le_trans h2C (Real.log_le_log (one_div_pos.mpr hpos16) hlogLB)
  have hCC : C⁻¹ * (2 * C) = 2 := by field_simp
  have hmul : C⁻¹ * (2 * C) ≤ C⁻¹ * Real.log
      (if x = vertexPoint ε η b then ε⁻¹ else min ((R / 8) / ‖x - vertexPoint ε η b‖) ε⁻¹) :=
    mul_le_mul_of_nonneg_left hlogif (inv_nonneg.mpr hC.le)
  -- real-valued bound on the window `I(B_{R/8}(x))`
  have hK : (1 / 2 : ℝ) ≤ greenFn m (interiorCellVertices ε η (ball x (R / 8))) y b := by
    linarith [hGreen.1, hGreen.2, hmul, hCC]
  -- domain monotonicity from `I(B_{R/8}(x))` to `I(B_{R/4}(x))`
  have hsub := interiorCellVertices_mono_of_radius (x := x) hη hR hc0' hdiam
  unfold greenFn at hK
  set X := ∫⁻ z, visitsBeforeExit (interiorCellVertices ε η (ball x (R / 8))) b z ∂srwLaw m y with hXdef
  have hXtop : X ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hK
    norm_num at hK
  have hXge : ENNReal.ofReal (1 / 2) ≤ X := by
    rw [← ENNReal.ofReal_toReal hXtop]
    exact ENNReal.ofReal_le_ofReal hK
  have hmono : X ≤ ∫⁻ z, visitsBeforeExit (interiorCellVertices ε η (ball x (R / 4))) b z ∂srwLaw m y :=
    lintegral_mono fun z => visitsBeforeExit_le_of_subset hsub b z
  rw [lintegral_visits_eq_tsum] at hmono
  exact hXge.trans hmono

/-- `ENNReal.ofReal (1/2) = 1/2`. -/
theorem ofReal_half : ENNReal.ofReal (1 / 2) = (1 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- Cells of diameter at most `c₀R` that meet `B_{R/4}(x)` and a ball `B_s(x)` with `s + c₀R < R/4` lie in the interior
window `I(B_{R/4}(x))`: the cell of a vertex of `V(B_s(x))` lies within `s + c₀R < R/4` of `x`, so it misses the sphere
`∂B_{R/4}(x)` (the cell-to-window inclusion of LEMMA68 C4, B11). -/
theorem cellVertices_sub_interior {η : ℝ → ℂ} (hη : Continuous η) {ε R c0 s : ℝ} {x : ℂ}
    (hR : 0 < R) (hc0 : 0 ≤ c0) (hsc : s + c0 * R < R / 4)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball x (R / 4)).Nonempty → diam (cell ε η k) ≤ c0 * R) :
    cellVertices ε η (ball x s) ⊆ interiorCellVertices ε η (ball x (R / 4)) := by
  intro v hv
  have hv' : (cell ε η v ∩ ball x s).Nonempty := hv
  have hs : s ≤ R / 4 := by linarith [mul_nonneg hc0 hR.le]
  have hv2 : (cell ε η v ∩ ball x (R / 4)).Nonempty :=
    hv'.mono (inter_subset_inter_right _ (ball_subset_ball hs))
  have hd := hdiam v hv2
  refine ⟨hv2, ?_⟩
  intro hfr
  have hfr' : (cell ε η v ∩ frontier (ball x (R / 4))).Nonempty := hfr
  obtain ⟨w, hw1, hw2⟩ := hfr'
  rw [frontier_ball x (by positivity : R / 4 ≠ 0)] at hw2
  have hlt := cell_dist_lt hη hd hv' hw1
  have hsph : dist w x = R / 4 := mem_sphere.mp hw2
  linarith

/-- **Per-test bound of Lemma 6.8 with the Green lower bound derived (LEMMA68 C15-C16, B4, B11-B13).** Let `x = η(y)`
be the start of a test window, `B_{c₀R}(x)` the target ball, `W y = I(B_{R/4}(x))` the window. Given the ball-mass
bound, the sparsity of `A`, the cell-diameter bound and the Draft Lemma 2.16 conjunct at every target, the walk from `y`
stays in `A` until it exits `W y` with probability at most `1 - q₀ (1 + log(1/r))⁻²`. The second moment `hmom` (B5) stays
an explicit hypothesis. -/
theorem stayIn_le_printed_green {μ : Measure ℂ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {W : ℤ → Set ℤ} {A : Set ℤ}
    {y : ℤ} {ε R r mr s1 β C0 C1 L Sr c0 C : ℝ} {Aset : Finset ℤ}
    (hap : IsAreaParametrized μ η) (hε : 0 < ε) (hR : 0 < R) (hmr : 0 < mr) (hC : 0 < C)
    (hc0 : 0 < c0) (hc0' : c0 < 1 / 8) (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16) (hεc : ε ≤ 16 * c0)
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
    (hC0 : 0 < C0) (hC1 : 0 < C1) (hL : 0 < L) (hr : 0 < r) (hr1 : r ≤ 1) (hS0 : 0 ≤ Sr)
    (hSm : Sr ≤ C1 * L * mr)
    (hmom : ∫⁻ x, (ENat.toENNReal (vExitTime (W y) x)) ^ 2 ∂(srwLaw m y) ≤
      ENNReal.ofReal (2 * (C0 * (1 + Real.log (1 / r))) ^ 2 * ε⁻¹ ^ 2 * Sr ^ 2)) :
    srwLaw m y (TestBound68.stayIn W A y) ≤
      ENNReal.ofReal (1 - (1 / (32 * C0 ^ 2 * C1 ^ 2 * L ^ 2)) / (1 + Real.log (1 / r)) ^ 2) := by
  have hsc : c0 * R + c0 * R < R / 4 := by nlinarith
  have hWy : cellVertices ε η (ball (vertexPoint ε η y) (c0 * R)) ⊆ W y := by
    rw [hWdef]
    exact cellVertices_sub_interior hap.1 hR hc0.le hsc hdiam
  have hG : ∀ b ∈ hfinD.toFinset \ Aset,
      (1 / 2 : ℝ≥0∞) ≤ ∑' n : ℕ, srwLaw m y {x | (n : ℕ∞) < vExitTime (W y) x ∧ x n = b} := by
    intro b hb
    have hbD : b ∈ cellVertices ε η (ball (vertexPoint ε η y) (c0 * R)) :=
      (Set.Finite.mem_toFinset hfinD).mp (Finset.mem_sdiff.mp hb).1
    rw [hWdef, ← ofReal_half]
    exact hG_of_green hap.1 hε hR hC hc0 hc0' hc0C hεc hdiam hbD (hGreenAt b hbD)
  exact PrintedTest68.stayIn_le_printed hap hε hmr hmu hfinD hfinr hRr hWy hAs hsp hs hC0 hC1 hL hr hr1 hS0 hSm
    hG hmom

end GreenTest68
end MatedCRT

#print axioms MatedCRT.GreenTest68.vExitTime_le_of_subset
#print axioms MatedCRT.GreenTest68.visitsBeforeExit_le_of_subset
#print axioms MatedCRT.GreenTest68.lintegral_visits_eq_tsum
#print axioms MatedCRT.GreenTest68.cell_dist_lt
#print axioms MatedCRT.GreenTest68.interiorCellVertices_mono_of_radius
#print axioms MatedCRT.GreenTest68.hG_of_green
#print axioms MatedCRT.GreenTest68.ofReal_half
#print axioms MatedCRT.GreenTest68.cellVertices_sub_interior
#print axioms MatedCRT.GreenTest68.stayIn_le_printed_green
