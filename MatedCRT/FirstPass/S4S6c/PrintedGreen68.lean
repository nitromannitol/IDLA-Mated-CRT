import MatedCRT.FirstPass.S4S6c.GreenTest68
import MatedCRT.FirstPass.S4S6c.ExitMoment68
import MatedCRT.FirstPass.S4S6c.SupKernel68

/-!
# LEMMA68 per-test bound with the Draft exit-time moment and the Lemma 1 potential bound (q2, task fp-S4S6c-envscaling-6-7-6-8)

`stayIn_le_printed_green` (GreenTest68.lean) with its second-moment hypothesis `hmom` discharged by the Draft Lemma 2.18
instance at `N = 2` (`hexit`, Draft `ExitTimeUpperBoundStmt`, EXTERNAL) and the potential bound `hS` (eq (21), from Lemma 1
of `SupKernel68.lean`). Write-up B5 (notes/fp-gaps/CHATGPT-lemma68-open-parts.md, eqs (B15)-(B17)).

Geometry used: for `D = B_{R/4}(x)` and `E = B_δ(D)` with `δ ≤ 1/2`, `R ≤ 1`, every `u ∈ E`, `v ∈ D` satisfy `|u - v| ≤ 1`
(`thickening_ball_dist_le_one`), so the kernel integrand of the Draft statement is nonnegative on `E`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace MatedCRT

/-- Points of the `δ`-thickening of `B_{R/4}(x)` are within distance `1` of the points of `B_{R/4}(x)`, when
`R ≤ 1` and `δ ≤ 1/2` (write-up B5: `|u - v| < R/2 + ε^α ≤ 1`). -/
theorem thickening_ball_dist_le_one {x u v : ℂ} {R δ : ℝ} (hR : R ≤ 1) (hδ : δ ≤ 1 / 2)
    (hu : u ∈ thickening δ (ball x (R / 4))) (hv : v ∈ ball x (R / 4)) :
    ‖u - v‖ ≤ 1 := by
  obtain ⟨p, hp, hup⟩ := Metric.mem_thickening_iff.mp hu
  have h1 : dist u p < δ := hup
  have h2 : dist p x < R / 4 := Metric.mem_ball.mp hp
  have h3 : dist v x < R / 4 := Metric.mem_ball.mp hv
  rw [← dist_eq_norm]
  have t1 := dist_triangle u x v
  have t2 := dist_triangle u p x
  have t3 := dist_comm x v
  linarith

/-- **Potential supremum for the Draft kernel** (LEMMA68 eq (21) for `D = B_{R/4}(x)`, `E = B_δ(D)`): with the good
annulus `A` containing `D` and `E`, the supremum in the Draft Lemma 2.18 statement is at most the Lemma 1 bound. -/
theorem draft_sup_le_of_annulus {A : Set ℂ} (μ : Measure ℂ) [SFinite μ] {x z : ℂ} {R C mr δ : ℝ}
    (hR0 : 0 < R) (hR1 : R ≤ 1) (hδ : δ ≤ 1 / 2)
    (hA : MeasurableSet A) (hAb : A ⊆ closedBall z (2 * R)) (hμA : μ A ≠ ⊤)
    (hsph : sphere z (3 * R / 2) ⊆ A)
    (hDA : ball x (R / 4) ⊆ A) (hEA : thickening δ (ball x (R / 4)) ⊆ A)
    (hC : 0 ≤ C) (hmr : 0 ≤ mr)
    (hint : ∀ v ∈ ball x (R / 4), IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) A μ)
    (hF : ∀ w ∈ A, ∫ u in A, (Real.log (R / ‖u - w‖) + 1) ∂μ ≤ C * mr) :
    (⨆ v ∈ ball x (R / 4), ∫⁻ u in thickening δ (ball x (R / 4)),
        ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) ≤
      ENNReal.ofReal (C * mr * (1 + (Real.log 4 - 1)) * (1 + Real.log (1 / R)) / (1 - Real.log 2)) :=
  sup_kernel_le_of_annulus μ hR0 hR1 hA hAb hμA hsph (Metric.isOpen_thickening.measurableSet) hEA hDA
    (fun _ hu _ hv => thickening_ball_dist_le_one hR1 hδ hu hv) hC hmr hint hF

/-- **LEMMA68 per-test bound, Draft second moment** (write-up B5 with `hmom` from Draft Lemma 2.18). Same conclusion and
hypotheses as `stayIn_le_printed_green`, except that the second moment is supplied by the `N = 2` instance `hexit` of the
Draft exit-time bound (constant `Cd`, supremum `S` over the centre of the kernel integral) and the potential bound `hS`. -/
theorem stayIn_le_printed_green_draft {μ : Measure ℂ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {W : ℤ → Set ℤ} {A : Set ℤ}
    {y : ℤ} {ε R r mr s1 β C0 C1 L Sr c0 C Cd : ℝ} {S : ℝ≥0∞} {Aset : Finset ℤ}
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
    (hCd0 : 0 ≤ Cd) (hCd : Cd ≤ C0 * (1 + Real.log (1 / r)))
    (hexit : exitTimeMoment m (W y) y 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * Cd ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) * S ^ (2 : ℕ))
    (hS : S ≤ ENNReal.ofReal Sr) :
    srwLaw m y (TestBound68.stayIn W A y) ≤
      ENNReal.ofReal (1 - (1 / (32 * C0 ^ 2 * C1 ^ 2 * L ^ 2)) / (1 + Real.log (1 / r)) ^ 2) :=
  GreenTest68.stayIn_le_printed_green hap hε hR hmr hC hc0 hc0' hc0C hεc hmu hfinD hfinr hRr hWdef hAs hsp hs hdiam hGreenAt
    hC0 hC1 hL hr hr1 hS0 hSm
    (hmom_of_exitTime_two hε hCd0 hS0 hCd hexit hS)

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.stayIn_le_printed_green_draft
#print axioms MatedCRT.draft_sup_le_of_annulus
