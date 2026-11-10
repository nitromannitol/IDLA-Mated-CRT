import MatedCRT.FirstPass.S6j.LocalCount
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.FirstPass.S4S6c.HcGreen68
import MatedCRT.FirstPass.S4S6c.PrintedTestLocal68
import MatedCRT.FirstPass.S4S6c.GreenTest68
import MatedCRT.FirstPass.S4S6c.PrintedGreen68
import MatedCRT.FirstPass.S4S6c.GoodAnnulusHF68
import MatedCRT.FirstPass.S4S6c.OpenAnnulus68
import MatedCRT.FirstPass.S4S6c.PerTest68

/-!
# The per-state local test bound at a middle vertex (fp-S6j; the state inputs of chat 183)

Written argument: the printed test at a middle vertex `v` of `∂B_{4R/3}(z)`, with the local scale `R` (the state
radius, the denominator `(1 + log(1/R))²`), the sparsity scale `r`, the mass `mr = μ(B_{c₀R}(v)).toReal`, and the window
`I(B_{R/4}(v))`. The local sparsity count `hA_local` is `hA_local_of_sparse` (S6j/LocalCount.lean); the bound itself is
`stayIn_le_printed_local` (S4S6c/PrintedTestLocal68.lean, q2).

Named hypotheses (the per-state form of the chat 183 inputs):
* `hsp`: the Lemma 6.8 hypothesis on `A` (corrected tex l.2792), at every centre, radius `r`;
* `hr2 : r ^ 2 ≤ R`: the explicit scale hypothesis (routed to the operator, request 30c);
* `hs1small : 44 s₁ ≤ c₀^β`: the smallness of `s₁`, depending only on `γ` through `c₀` and `β` (not `s₁ = 1/4`);
* `hvol`: the volume lower bound `(c₀R)^β ≤ μ(B_{c₀R}(v))` (Lemma 2.7, `VolumeGrowthStmt`, exponent `β = β⁻`);
* `hdy`, `hdiam`: the cell-size estimates (Lemma 2.8, `cellSize`);
* `hGreenLow`: the Green lower bound at the test vertex (Lemma 2.16, `GreenKernelLowerBoundStmt`);
* `hexit`: the second exit moment (Lemma 2.18 with `N = 2`, `ExitTimeUpperBoundStmt`);
* `hann`: the good-annulus event on the open annulus `A_{R,2R}(z)` (Lemma 6.4, `IsGoodAnnulusEvent`);
* `hβ : 1 ≤ β` (from `β⁻ > (2+γ)²/2 ≥ 2`) and `hp`-free: no `p` enters.
The state-level good predicate is the presence of these inputs at the state; the walk-level `hgood` of
`StateTestInputs` is assembled at S6h from the same guard.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal

namespace MatedCRT
namespace S6j

/-- A ball has finite `μ`-mass for a locally finite `μ` (local copy of `measure_ball_ne_top'`, StateGood.lean:35;
not imported, since StateGood's import closure clashes with `GoodAnnulusHF68`). -/
lemma perState_ball_ne_top {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (x : ℂ) (r : ℝ) :
    μ (Metric.ball x r) ≠ ⊤ :=
  ne_top_of_le_ne_top (measure_closedBall_lt_top (μ := μ) (x := x) (r := r)).ne
    (measure_mono Metric.ball_subset_closedBall)

/-- The cell vertices of a ball are finite (local copy of `cellVertices_ball_finite`, StateGood.lean:41). -/
lemma perState_cellVertices_ball_finite {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (x : ℂ) (r : ℝ) :
    (cellVertices ε η (Metric.ball x r)).Finite :=
  (cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall x r)).subset
    fun _ hk => hk.mono (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall)

/-- **The per-state local test bound at a middle vertex.** For the test vertex `v` of the state with centre `z`, local
radius `R` and sparsity radius `r`, the walk from `v` stays in `A` until it exits the window `I(B_{R/4}(v))` with
probability at most `1 - q₀/(1 + log(1/R))²`, `q₀ = 1/(288 C_d² K²)`, `K = C_g(1+(log 4 - 1))/(1-log 2)`. -/
theorem perState_local_bound_of_count {μ : Measure ℂ} [SFinite μ] [IsFiniteMeasureOnCompacts μ] {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {ε c0 C Cd Cg β R δ : ℝ} {z : ℂ} {v : ℤ}
    (hap : IsAreaParametrized μ η) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hC : 0 < C) (hCd : 0 < Cd) (hCg : 0 < Cg) (hc0 : 0 < c0) (hc0' : c0 < 1 / 8)
    (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16) (hεc : ε ≤ 16 * c0)
    (hδ : δ ≤ R / 100)
    (hmeet : (cell ε η v ∩ sphere z (4 * R / 3)).Nonempty)
    -- the local count of A-vertices in V(B_{c0 R}(v)) (hA_local_of_sparse, or the ball-inclusion count of S6r)
    (hloc : ((A ∩ cellVertices ε η (ball (vertexPoint ε η v) (c0 * R))).ncard : ℝ)
      ≤ (μ (ball (vertexPoint ε η v) (c0 * R))).toReal / (4 * ε))
    -- chat 183 inputs (named)
    (hvol : (c0 * R) ^ β ≤ (μ (ball (vertexPoint ε η v) (c0 * R))).toReal)
    (hdy : diam (cell ε η v) ≤ R / 100)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η v) (R / 4)).Nonempty → diam (cell ε η k) ≤ c0 * R)
    (hGreenLow : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η v) (c0 * R)),
      C⁻¹ * Real.log (if vertexPoint ε η v = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η v - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η v) (R / 8))) v b)
    (hexit : exitTimeMoment m (interiorCellVertices ε η (ball (vertexPoint ε η v) (R / 4))) v 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * Cd ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
        (⨆ w ∈ ball (vertexPoint ε η v) (R / 4),
          ∫⁻ u in thickening δ (ball (vertexPoint ε η v) (R / 4)),
            ENNReal.ofReal (Real.log (1 / ‖w - u‖) + 1) ∂μ) ^ (2 : ℕ))
    (hann : IsGoodAnnulusEvent μ c0 Cg R z) :
    srwLaw m v (TestBound68.stayIn
      (fun u => interiorCellVertices ε η (ball (vertexPoint ε η u) (R / 4))) A v) ≤
      ENNReal.ofReal (1 - (1 / (288 * Cd ^ 2 * (Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2)) /
        (1 + Real.log (1 / R)) ^ 2) := by
  classical
  -- the constants of printed_test_bound with the local scale R
  have hlogR : 0 ≤ Real.log (1 / R) := Real.log_nonneg (one_le_one_div hR hR1)
  have hpos1 : 0 < 1 + Real.log (1 / R) := by linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hκ : 0 < 1 - Real.log 2 := by linarith
  have ha0 : 0 < 1 + (Real.log 4 - 1) := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 3 * (1 + Real.log (1 / R)) := ⟨_, rfl⟩
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = Cd / (1 + Real.log (1 / R)) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; exact div_pos (mul_pos hCg ha0) hκ
  have hL0 : 0 < L := by rw [hL]; linarith
  have hC00 : 0 < C0 := by rw [hC0]; exact div_pos hCd hpos1
  -- the mass of the test ball
  have hmfin : μ (ball (vertexPoint ε η v) (c0 * R)) ≠ ⊤ := perState_ball_ne_top _ _
  have hvolpos : 0 < (c0 * R) ^ β := Real.rpow_pos_of_pos (mul_pos hc0 hR) β
  have hmr : 0 < (μ (ball (vertexPoint ε η v) (c0 * R))).toReal := lt_of_lt_of_le hvolpos hvol
  have hmu : ENNReal.ofReal (μ (ball (vertexPoint ε η v) (c0 * R))).toReal
      ≤ μ (ball (vertexPoint ε η v) (c0 * R)) := le_of_eq (ENNReal.ofReal_toReal hmfin)
  have hfinD := perState_cellVertices_ball_finite hη hprop hε (vertexPoint ε η v) (c0 * R)
  have hfinI : (A ∩ cellVertices ε η (ball (vertexPoint ε η v) (c0 * R))).Finite :=
    hfinD.subset Set.inter_subset_right
  have hAs : ∀ k, k ∈ hfinI.toFinset ↔ k ∈ A ∩ cellVertices ε η (ball (vertexPoint ε η v) (c0 * R)) :=
    fun k => hfinI.mem_toFinset
  have hcard : (hfinI.toFinset.card : ℝ) ≤ ε⁻¹ * ((μ (ball (vertexPoint ε η v) (c0 * R))).toReal / 4) := by
    have h1 : ((A ∩ cellVertices ε η (ball (vertexPoint ε η v) (c0 * R))).ncard : ℝ)
        = (hfinI.toFinset.card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hfinI]
    rw [← h1]
    refine hloc.trans (le_of_eq ?_)
    field_simp
  -- the Green half-hitting bound `hG` (hG_of_green)
  have hG : ∀ b ∈ hfinD.toFinset \ hfinI.toFinset,
      (1 / 2 : ℝ≥0∞) ≤ ∑' n : ℕ, srwLaw m v
        {x | (n : ℕ∞) < vExitTime (interiorCellVertices ε η (ball (vertexPoint ε η v) (R / 4))) x ∧ x n = b} := by
    intro b hb
    have hbD : b ∈ cellVertices ε η (ball (vertexPoint ε η v) (c0 * R)) :=
      hfinD.mem_toFinset.1 (Finset.mem_sdiff.1 hb).1
    have hGb := GreenTest68.hG_of_green hη hε hR hC hc0 hc0' hc0C hεc hdiam hbD
      ⟨HcGreen68.greenKernel_le_greenFn m _ _ b, hGreenLow b hbD⟩
    rwa [GreenTest68.ofReal_half] at hGb
  -- the window inclusion `cellVertices (B_{c₀R}(v)) ⊆ I(B_{R/4}(v))`
  have hWy : cellVertices ε η (ball (vertexPoint ε η v) (c0 * R)) ⊆
      interiorCellVertices ε η (ball (vertexPoint ε η v) (R / 4)) :=
    GreenTest68.cellVertices_sub_interior hη hR hc0.le (by nlinarith) hdiam
  -- the annulus input: the sup of the kernel integral (draft_sup_le_of_annulus on the open annulus)
  have hx : 4 * R / 3 - R / 100 ≤ ‖vertexPoint ε η v - z‖ ∧ ‖vertexPoint ε η v - z‖ ≤ 4 * R / 3 + R / 100 :=
    MatedCRT.vertex_norm_sub_of_cell_meets_sphere hη hε hdy hmeet
  have hxA : vertexPoint ε η v ∈ openAnnulus z R := by
    rw [mem_openAnnulus]
    constructor <;> linarith [hx.1, hx.2]
  have hμA : μ (openAnnulus z R) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_closedBall_lt_top (μ := μ) (x := z) (r := 2 * R)).ne
      (measure_mono (openAnnulus_subset_closedBall z R))
  have hint := hint_of_goodAnnulus (μ := μ) (c0 := c0) (C := Cg) hxA hann hmfin hμA
  have hF := hF_of_goodAnnulus (μ := μ) (c0 := c0) (C := Cg) hCg.le hxA hann hmfin
  have hsum := draft_sup_le_of_annulus (A := openAnnulus z R) (x := vertexPoint ε η v) (z := z) (R := R)
    (C := Cg) (mr := (μ (ball (vertexPoint ε η v) (c0 * R))).toReal) (δ := δ) μ hR hR1 (by linarith)
    (isOpen_openAnnulus z R).measurableSet (openAnnulus_subset_closedBall z R) hμA
    (sphere_subset_openAnnulus hR) (ball_subset_openAnnulus hR hx) (thickening_ball_subset_openAnnulus hR hx hδ)
    hCg.le hmr.le (fun w hw => hint w (ball_subset_openAnnulus hR hx hw)) hF
  have hS : (⨆ w ∈ ball (vertexPoint ε η v) (R / 4),
      ∫⁻ u in thickening δ (ball (vertexPoint ε η v) (R / 4)),
        ENNReal.ofReal (Real.log (1 / ‖w - u‖) + 1) ∂μ) ≤ ENNReal.ofReal (K * L * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal) := by
    refine hsum.trans (ENNReal.ofReal_le_ofReal ?_)
    have hX : 0 ≤ K * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal := mul_nonneg hK0.le hmr.le
    calc Cg * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal * (1 + (Real.log 4 - 1)) * (1 + Real.log (1 / R))
            / (1 - Real.log 2)
        = (K * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal) * (1 + Real.log (1 / R)) := by rw [hK]; ring
      _ ≤ (K * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal) * (3 * (1 + Real.log (1 / R))) :=
          mul_le_mul_of_nonneg_left (by linarith) hX
      _ = K * L * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal := by rw [hL]; ring
  -- the second moment `hmom` from hexit (N = 2) and hS
  have hεp : ε ^ (-((2 : ℕ) : ℝ)) = ε⁻¹ ^ 2 := by
    rw [Real.rpow_neg hε.le, Real.rpow_natCast, inv_pow]
  have hfac : (((2 : ℕ).factorial : ℝ)) = 2 := by norm_num [Nat.factorial]
  have hmom : ∫⁻ x, (ENat.toENNReal (vExitTime (interiorCellVertices ε η (ball (vertexPoint ε η v) (R / 4))) x)) ^ 2
      ∂(srwLaw m v) ≤ ENNReal.ofReal (2 * (C0 * (1 + Real.log (1 / R))) ^ 2 * ε⁻¹ ^ 2
        * (K * L * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal) ^ 2) := by
    have hCC : (C0 * (1 + Real.log (1 / R))) ^ 2 = Cd ^ 2 := by
      rw [hC0, div_mul_cancel₀ _ hpos1.ne']
    have hsq : (⨆ w ∈ ball (vertexPoint ε η v) (R / 4),
        ∫⁻ u in thickening δ (ball (vertexPoint ε η v) (R / 4)),
          ENNReal.ofReal (Real.log (1 / ‖w - u‖) + 1) ∂μ) ^ (2 : ℕ)
        ≤ ENNReal.ofReal (K * L * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal) ^ (2 : ℕ) :=
      by gcongr
    have hKLm : 0 ≤ K * L * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal :=
      mul_nonneg (mul_nonneg hK0.le hL0.le) hmr.le
    calc ∫⁻ x, (ENat.toENNReal (vExitTime (interiorCellVertices ε η (ball (vertexPoint ε η v) (R / 4))) x)) ^ 2
          ∂(srwLaw m v)
        = exitTimeMoment m (interiorCellVertices ε η (ball (vertexPoint ε η v) (R / 4))) v 2 := rfl
      _ ≤ ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * Cd ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
          (⨆ w ∈ ball (vertexPoint ε η v) (R / 4),
            ∫⁻ u in thickening δ (ball (vertexPoint ε η v) (R / 4)),
              ENNReal.ofReal (Real.log (1 / ‖w - u‖) + 1) ∂μ) ^ (2 : ℕ) := hexit
      _ ≤ ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * Cd ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
          ENNReal.ofReal (K * L * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal) ^ (2 : ℕ) :=
          by gcongr
      _ = ENNReal.ofReal (2 * (C0 * (1 + Real.log (1 / R))) ^ 2 * ε⁻¹ ^ 2
            * (K * L * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal) ^ 2) := by
          have hA0 : 0 ≤ ((2 : ℕ).factorial : ℝ) * Cd ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ)) := by
            rw [hεp]; positivity
          rw [← ENNReal.ofReal_pow hKLm, ← ENNReal.ofReal_mul hA0]
          congr 1
          rw [hεp, hfac, hCC]
  -- the printed test bound with the local denominator (q2, stayIn_le_printed_local)
  have hres := MatedCRT.PrintedTestLocal68.stayIn_le_printed_local (μ := μ) (η := η) (m := m) (y := v)
    (A := A) (W := fun u => interiorCellVertices ε η (ball (vertexPoint ε η u) (R / 4)))
    (z := vertexPoint ε η v) (ε := ε) (R := c0 * R) (r := R)
    (mr := (μ (ball (vertexPoint ε η v) (c0 * R))).toReal) (C0 := C0) (C1 := K) (L := L)
    (Sr := K * L * (μ (ball (vertexPoint ε η v) (c0 * R))).toReal) (Aset := hfinI.toFinset)
    hap hε hmr hmu hfinD hWy hAs hcard hC00 hK0 hL0 hR hR1
    (mul_nonneg (mul_nonneg hK0.le hL0.le) hmr.le) le_rfl hG hmom
  have hq : (1 / (32 * C0 ^ 2 * K ^ 2 * L ^ 2)) / (1 + Real.log (1 / R)) ^ 2 =
      (1 / (288 * Cd ^ 2 * (Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2)) /
        (1 + Real.log (1 / R)) ^ 2 := by
    rw [hC0, hL, ← hK]
    have h1 : (1 + Real.log (1 / R)) ≠ 0 := hpos1.ne'
    have h2 : Cd ≠ 0 := hCd.ne'
    have h3 : K ≠ 0 := hK0.ne'
    field_simp
    ring
  rw [hq] at hres
  exact hres

/-- **Per-state local test bound** (the printed test with the local denominator `(1 + log(1/R))²`). The local count
`hloc` of `A`-vertices in `V(B_{c₀R}(v))` is `hA_local_of_sparse` (covering of `B_{c₀R}` by balls of radius `r`; needs
`r² ≤ R`); the bound is `perState_local_bound_of_count`. Kept unchanged in statement (the p-schedule route). -/
theorem perState_local_bound {μ : Measure ℂ} [SFinite μ] [IsFiniteMeasureOnCompacts μ] {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {ε c0 C Cd Cg s1 β r R δ : ℝ} {z : ℂ} {v : ℤ}
    (hap : IsAreaParametrized μ η) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hs1 : 0 < s1) (hs1small : 44 * s1 ≤ c0 ^ β) (hβ : 1 ≤ β)
    (hr : 0 < r) (hr2 : r ^ 2 ≤ R)
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hC : 0 < C) (hCd : 0 < Cd) (hCg : 0 < Cg) (hc0 : 0 < c0) (hc0' : c0 < 1 / 8)
    (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16) (hεc : ε ≤ 16 * c0)
    (hδ : δ ≤ R / 100)
    (hmeet : (cell ε η v ∩ sphere z (4 * R / 3)).Nonempty)
    (hsp : ∀ w : ℂ, ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε)
    (hvol : (c0 * R) ^ β ≤ (μ (ball (vertexPoint ε η v) (c0 * R))).toReal)
    (hdy : diam (cell ε η v) ≤ R / 100)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η v) (R / 4)).Nonempty → diam (cell ε η k) ≤ c0 * R)
    (hGreenLow : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η v) (c0 * R)),
      C⁻¹ * Real.log (if vertexPoint ε η v = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η v - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η v) (R / 8))) v b)
    (hexit : exitTimeMoment m (interiorCellVertices ε η (ball (vertexPoint ε η v) (R / 4))) v 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * Cd ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
        (⨆ w ∈ ball (vertexPoint ε η v) (R / 4),
          ∫⁻ u in thickening δ (ball (vertexPoint ε η v) (R / 4)),
            ENNReal.ofReal (Real.log (1 / ‖w - u‖) + 1) ∂μ) ^ (2 : ℕ))
    (hann : IsGoodAnnulusEvent μ c0 Cg R z) :
    srwLaw m v (TestBound68.stayIn
      (fun u => interiorCellVertices ε η (ball (vertexPoint ε η u) (R / 4))) A v) ≤
      ENNReal.ofReal (1 - (1 / (288 * Cd ^ 2 * (Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2)) /
        (1 + Real.log (1 / R)) ^ 2) :=
  perState_local_bound_of_count hap hη hprop hε hR hR1 hC hCd hCg hc0 hc0' hc0C hεc hδ hmeet
    (hA_local_of_sparse (μ := μ) (x := vertexPoint ε η v) hε hr hR hR1 hc0 hc0'.le hs1.le hβ hr2
      hs1small (fun w => perState_cellVertices_ball_finite hη hprop hε w r) hsp hvol)
    hvol hdy hdiam hGreenLow hexit hann

end S6j
end MatedCRT
