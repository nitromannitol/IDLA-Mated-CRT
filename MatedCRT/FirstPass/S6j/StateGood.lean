import MatedCRT.FirstPass.S6j.PerState
import MatedCRT.FirstPass.S4S6c.HcGreen68

/-!
# The good-state inputs of the local test at the middle vertices (fp-S6j; `hloc` of `StateTestInputs`)

Written argument: `printed_test_bound` (PerTest68.lean:82) at each middle vertex `v` of `∂B_{4R/3}(z)`, with the local
scale `R`, the sparsity scale `r`, the mass `mr = μ(B_{c₀R}(v)).toReal` and the window `I(B_{R/4}(v))`.

* `GoodVertexInputs`: the good-event inputs of that test at one middle vertex. They are NAMED fields (the good event of
  the state, not derived here): `hsp`, `hs` (sparsity and mass lower bound at the scale `r`), `hdy`, `hdiam` (cell geometry),
  `hGreenLow` (Green lower bound; the upper bound is unconditional), `hint`, `hF` (logarithmic kernel on the closed annulus `A_{R,2R}(z)`) and `hexit` (exit moment).
* `printedVertex_of_good`: the local bound at `v` by `printed_test_bound`. Discharged here: `μ(B_{c₀R}(v)) ≠ ⊤` and
  `μ(A_{R,2R}(z)) ≠ ⊤` (`IsFiniteMeasureOnCompacts`), the finiteness of the cell vertices of the balls (properness of `η`),
  the set `Aset`, `0 < mr` (from `hs` and `0 < s1`), and the incidence `hmeet` (the middle vertex hypothesis).
* `hloc_of_goodState`: the `hloc` field of `StateTestInputs` (S6h/Schedule.lean:302) from the good-state predicate `Good`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MatedCRT
open WalkPotential

namespace S6j

/-- The closed annulus `A_{R,2R}(z)` has finite `μ`-mass for a locally finite `μ`. -/
lemma measure_closedAnnulus_ne_top {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (z : ℂ) (R : ℝ) :
    μ (closedAnnulus z R) ≠ ⊤ :=
  ne_top_of_le_ne_top (measure_closedBall_lt_top (μ := μ) (x := z) (r := 2 * R)).ne
    (measure_mono fun u hu => Metric.mem_closedBall.2
      (by rw [dist_eq_norm]; exact (show R ≤ ‖u - z‖ ∧ ‖u - z‖ ≤ 2 * R from hu).2))

/-- A ball has finite `μ`-mass for a locally finite `μ`. -/
lemma measure_ball_ne_top' {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (x : ℂ) (r : ℝ) :
    μ (Metric.ball x r) ≠ ⊤ :=
  ne_top_of_le_ne_top (measure_closedBall_lt_top (μ := μ) (x := x) (r := r)).ne
    (measure_mono Metric.ball_subset_closedBall)

/-- The cell vertices of a ball are finite (`cellVertices_finite_of_isCompact`, properness of `η`). -/
lemma cellVertices_ball_finite {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (x : ℂ) (r : ℝ) :
    (cellVertices ε η (Metric.ball x r)).Finite :=
  (cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall x r)).subset
    fun _ hk => hk.mono (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall)

/-- **Good-event inputs of the local test at a middle vertex `v`.** These are the hypotheses of `printed_test_bound`
(PerTest68.lean:82) other than the finiteness, the mass identity, the incidence and `δ ≤ R/100`; the sparsity scale is `r`,
the local scale `R`, the centre `z`, the thickening `δ`. -/
structure GoodVertexInputs (μ : Measure ℂ) (η : ℝ → ℂ) (m : ℤ → ℤ → ℕ) (A : Set ℤ)
    (ε c0 C Cd Cg s1 β δ r : ℝ) (z : ℂ) (R : ℝ) (v : ℤ) : Prop where
  hsp : ((A ∩ cellVertices ε η (Metric.ball (vertexPoint ε η v) r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε
  hs : s1 * r ^ (2 * β) ≤ (μ (Metric.ball (vertexPoint ε η v) (c0 * R))).toReal / 4
  hdy : Metric.diam (cell ε η v) ≤ R / 100
  hdiam : ∀ k : ℤ, (cell ε η k ∩ Metric.ball (vertexPoint ε η v) (R / 4)).Nonempty →
    Metric.diam (cell ε η k) ≤ c0 * R
  /-- The Green lower bound (open-parts write-up line 870, "a lower bound on both the Green's kernel and function"). The
  upper bound `greenKernel ≤ greenFn` is unconditional (`HcGreen68.greenKernel_le_greenFn`). -/
  hGreenLow : ∀ b ∈ cellVertices ε η (Metric.ball (vertexPoint ε η v) (c0 * R)),
      C⁻¹ * Real.log (if vertexPoint ε η v = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η v - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (Metric.ball (vertexPoint ε η v) (R / 8))) v b
  hint : ∀ w ∈ Metric.ball (vertexPoint ε η v) (R / 4),
    IntegrableOn (fun u : ℂ => Real.log (R / ‖u - w‖) + 1) (closedAnnulus z R) μ
  hF : ∀ w ∈ closedAnnulus z R, ∫ u in closedAnnulus z R, (Real.log (R / ‖u - w‖) + 1) ∂μ ≤
    Cg * (μ (Metric.ball (vertexPoint ε η v) (c0 * R))).toReal
  hexit : exitTimeMoment m (interiorCellVertices ε η (Metric.ball (vertexPoint ε η v) (R / 4))) v 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * Cd ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
        (⨆ w ∈ Metric.ball (vertexPoint ε η v) (R / 4),
          ∫⁻ u in Metric.thickening δ (Metric.ball (vertexPoint ε η v) (R / 4)),
            ENNReal.ofReal (Real.log (1 / ‖w - u‖) + 1) ∂μ) ^ (2 : ℕ)

/-- **The local bound at a middle vertex from its good-event inputs** (`printed_test_bound` with the sparsity scale `r`,
the local scale `R` and the window `I(B_{R/4}(v))`). The constant is `q₀ = 1/(288 C_d² K²)`, `K = C_g(1+(log 4-1))/(1-log 2)`;
the bound keeps the printed constant `q₀` and the logarithm of the sparsity scale `r`. -/
theorem printedVertex_of_good {μ : Measure ℂ} [SFinite μ] [IsFiniteMeasureOnCompacts μ] {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {ε c0 C Cd Cg s1 β p δ r R : ℝ} {z : ℂ} {v : ℤ}
    (hap : IsAreaParametrized μ η) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hs1 : 0 < s1)
    (hR : 0 < R) (hR1 : R ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : 0 < C) (hCd : 0 < Cd) (hCg : 0 < Cg) (hc0 : 0 < c0) (hc0' : c0 < 1 / 8)
    (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16) (hεc : ε ≤ 16 * c0) (hp : p ≤ 3) (hRpow : r ^ p / 2 < R)
    (hRr : c0 * R ≤ r) (hδ : δ ≤ R / 100)
    (hmeet : (cell ε η v ∩ Metric.sphere z (4 * R / 3)).Nonempty)
    (hG : GoodVertexInputs μ η m A ε c0 C Cd Cg s1 β δ r z R v) :
    srwLaw m v (TestBound68.stayIn
      (fun u => interiorCellVertices ε η (Metric.ball (vertexPoint ε η u) (R / 4))) A v) ≤
      ENNReal.ofReal (1 - (1 / (288 * Cd ^ 2 * (Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2)) /
        (1 + Real.log (1 / r)) ^ 2) := by
  have hmfin : μ (Metric.ball (vertexPoint ε η v) (c0 * R)) ≠ ⊤ := measure_ball_ne_top' _ _
  have hpos : 0 < s1 * r ^ (2 * β) := mul_pos hs1 (Real.rpow_pos_of_pos hr _)
  have hmr : 0 < (μ (Metric.ball (vertexPoint ε η v) (c0 * R))).toReal := by
    linarith [hG.hs]
  have hfinD := cellVertices_ball_finite hη hprop hε (vertexPoint ε η v) (c0 * R)
  have hfinr := cellVertices_ball_finite hη hprop hε (vertexPoint ε η v) r
  have hfinI : (A ∩ cellVertices ε η (Metric.ball (vertexPoint ε η v) (c0 * R))).Finite :=
    hfinD.subset Set.inter_subset_right
  have hRr' : Metric.ball (vertexPoint ε η v) (c0 * R) ⊆ Metric.ball (vertexPoint ε η v) r :=
    Metric.ball_subset_ball hRr
  have hP := printed_test_bound (W := fun u => interiorCellVertices ε η (Metric.ball (vertexPoint ε η u) (R / 4)))
    (y := v) (r := r) (R := R) (mr := (μ (Metric.ball (vertexPoint ε η v) (c0 * R))).toReal) (z := z)
    (Aset := hfinI.toFinset) hap hη hε hR hR1 hmr hC hCd hCg hc0 hc0' hc0C hεc hr hr1 hp hRpow
    (le_of_eq (ENNReal.ofReal_toReal hmfin)) hfinD hfinr hRr' rfl (fun _ => hfinI.mem_toFinset)
    hG.hsp hG.hs hG.hdiam (fun b hb => ⟨HcGreen68.greenKernel_le_greenFn m _ _ b, hG.hGreenLow b hb⟩) hG.hdy hmeet hδ (measure_closedAnnulus_ne_top z R) hG.hint hG.hF hG.hexit
  exact hP

/-- **`hloc` of `StateTestInputs` from the good-state predicate.** Centres `Z`, radii `Rs`, thickenings `δs`, the good-state
predicate `Good` and the schedule's scale `r` (S6h/Schedule.lean:302, `StateTestInputs p r`). At each good state `y`:
the selection bounds `hRs` (`0 < Rs y ≤ 1`, `r^p/2 < Rs y`, `c₀ Rs y ≤ r`, `δs y ≤ Rs y/100`) and the good-event inputs
`hGood` at every middle vertex of `∂B_{4Rs y/3}(Z y)` give the local bound with `min qStar 1` in the denominator
`(1 + log(1/Rs y))²`. The printed bound has the denominator `(1 + log(1/r))²`; the conversion is the named scale input
`hLR` (`1 + log(1/r) ≤ KL (1 + log(1/Rs y))` at good states) with `qStar KL² ≤ 1/(288 C_d² K²)`. -/
theorem hloc_of_goodState {μ : Measure ℂ} [SFinite μ] [IsFiniteMeasureOnCompacts μ] {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {ε c0 C Cd Cg s1 β p r qStar KL : ℝ} {Z : ℤ → ℂ} {Rs δs : ℤ → ℝ} {Good : ℤ → Prop}
    (hap : IsAreaParametrized μ η) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hs1 : 0 < s1)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : 0 < C) (hCd : 0 < Cd) (hCg : 0 < Cg) (hc0 : 0 < c0) (hc0' : c0 < 1 / 8)
    (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16) (hεc : ε ≤ 16 * c0) (hp : p ≤ 3)
    (hRs : ∀ y, Good y → 0 < Rs y ∧ Rs y ≤ 1 ∧ r ^ p / 2 < Rs y ∧ c0 * Rs y ≤ r ∧ δs y ≤ Rs y / 100)
    (hGood : ∀ y, Good y → ∀ v ∈ middleVertices ε η (Z y) (Rs y),
      GoodVertexInputs μ η m A ε c0 C Cd Cg s1 β (δs y) r (Z y) (Rs y) v)
    (hKL : 0 < KL) (hLR : ∀ y, Good y → 1 + Real.log (1 / r) ≤ KL * (1 + Real.log (1 / Rs y)))
    (hqS : qStar ≤ 1 / (288 * Cd ^ 2 * (Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2) / KL ^ 2) :
    ∀ y, Good y → ∀ v ∈ middleVertices ε η (Z y) (Rs y),
      srwLaw m v (TestBound68.stayIn
        (fun u => interiorCellVertices ε η (Metric.ball (vertexPoint ε η u) (Rs y / 4))) A v) ≤
        ENNReal.ofReal (1 - min qStar 1 / (1 + Real.log (1 / Rs y)) ^ 2) := by
  intro y hy v hv
  obtain ⟨hR, hR1, hRpow, hRr, hδ⟩ := hRs y hy
  have hP := printedVertex_of_good hap hη hprop hε hs1 hR hR1 hr hr1 hC hCd hCg hc0 hc0' hc0C hεc hp hRpow
    hRr hδ hv (hGood y hy v hv)
  refine hP.trans (ENNReal.ofReal_le_ofReal ?_)
  have hLr : 0 < 1 + Real.log (1 / r) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / r by rw [le_div_iff₀ hr]; linarith)
    linarith
  have hLR0 : 0 < 1 + Real.log (1 / Rs y) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / Rs y by rw [le_div_iff₀ hR]; linarith)
    linarith
  set Q := 1 / (288 * Cd ^ 2 * (Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hA : min qStar 1 * KL ^ 2 ≤ Q :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg KL)).trans ((le_div_iff₀ (pow_pos hKL 2)).1 hqS)
  have hB : (1 + Real.log (1 / r)) ^ 2 ≤ KL ^ 2 * (1 + Real.log (1 / Rs y)) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hLr.le (hLR y hy) 2
  have hkey : min qStar 1 / (1 + Real.log (1 / Rs y)) ^ 2 ≤ Q / (1 + Real.log (1 / r)) ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hLR0 2) (pow_pos hLr 2)]
    rcases le_total (min qStar 1) 0 with h0 | h0
    · nlinarith [mul_nonneg (neg_nonneg.2 h0) (sq_nonneg (1 + Real.log (1 / r))),
        mul_nonneg hQ0 (sq_nonneg (1 + Real.log (1 / Rs y)))]
    · calc min qStar 1 * (1 + Real.log (1 / r)) ^ 2
          ≤ min qStar 1 * (KL ^ 2 * (1 + Real.log (1 / Rs y)) ^ 2) := mul_le_mul_of_nonneg_left hB h0
        _ = (min qStar 1 * KL ^ 2) * (1 + Real.log (1 / Rs y)) ^ 2 := by ring
        _ ≤ Q * (1 + Real.log (1 / Rs y)) ^ 2 := mul_le_mul_of_nonneg_right hA (sq_nonneg _)
  exact sub_le_sub_left hkey (1 : ℝ)

end S6j

end MatedCRT
