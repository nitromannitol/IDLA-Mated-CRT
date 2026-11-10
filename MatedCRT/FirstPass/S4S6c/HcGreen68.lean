import MatedCRT.FirstPass.S4S6c.PrintedGreen68
import MatedCRT.FirstPass.S4S6c.HcAssembly68

/-!
# The per-centre local test of the printed Lemma 6.8 from the Green estimates (q2, task fp-S4S6c-envscaling-6-7-6-8; LEMMA68 C4)

* `greenKernel_le_greenFn`: deterministic, the first conjunct of `hGreenAt` of
  `PrintedGreen68.stayIn_le_printed_green_draft`: `g_A(a,b) = G_A(a,b)/deg(b) ≤ G_A(a,b)` (Green kernel of Berestycki-Gwynne,
  Defs/RandomWalk `greenKernel`, `greenFn`).
* `stayIn_le_printed_interior`: the same bound with the window written as `innerVertices (cell ε η)` (the form that
  `HcAssembly68.hc_of_local` takes as `hloc`), and with the Green input reduced to the lower bound alone, which is the
  Draft Lemma 2.16 (`GreenKernelLowerBoundStmt` input, PolyHighProb).
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT

namespace HcGreen68

/-- Deterministic: the Green kernel is at most the Green function, `g_A(a,b) = G_A(a,b)/deg(b) ≤ G_A(a,b)`. -/
theorem greenKernel_le_greenFn (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) :
    greenKernel m A a b ≤ greenFn m A a b := by
  unfold greenKernel
  have hnn : 0 ≤ greenFn m A a b := by
    unfold greenFn
    exact ENNReal.toReal_nonneg
  rcases Nat.eq_zero_or_pos (mdeg m b) with h0 | hpos
  · simp [h0, hnn]
  · have h1 : (1 : ℝ) ≤ (mdeg m b : ℝ) := Nat.one_le_cast.mpr hpos
    exact div_le_self hnn h1

/-- **Local test from the Green estimates, window `innerVertices (cell ε η)`.** The printed per-centre bound of
`stayIn_le_printed_green_draft`, with the window `I(B_{R/4}(η(y)))` written as `innerVertices (cell ε η)` (equal to
`interiorCellVertices` by definition) and the Green hypothesis reduced to its lower bound (the first conjunct is
`greenKernel_le_greenFn`). -/
theorem stayIn_le_printed_interior {μ : Measure ℂ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    {y : ℤ} {ε R r mr s1 β C0 C1 L Sr c0 C Cd : ℝ} {S : ℝ≥0∞} {Aset : Finset ℤ}
    (hap : IsAreaParametrized μ η) (hε : 0 < ε) (hR : 0 < R) (hmr : 0 < mr) (hC : 0 < C)
    (hc0 : 0 < c0) (hc0' : c0 < 1 / 8) (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16) (hεc : ε ≤ 16 * c0)
    (hmu : ENNReal.ofReal mr ≤ μ (ball (vertexPoint ε η y) (c0 * R)))
    (hfinD : (cellVertices ε η (ball (vertexPoint ε η y) (c0 * R))).Finite)
    (hfinr : (cellVertices ε η (ball (vertexPoint ε η y) r)).Finite)
    (hRr : ball (vertexPoint ε η y) (c0 * R) ⊆ ball (vertexPoint ε η y) r)
    (hAs : ∀ k, k ∈ Aset ↔ k ∈ A ∩ cellVertices ε η (ball (vertexPoint ε η y) (c0 * R)))
    (hsp : ((A ∩ cellVertices ε η (ball (vertexPoint ε η y) r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε)
    (hs : s1 * r ^ (2 * β) ≤ mr / 4)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η y) (R / 4)).Nonempty → diam (cell ε η k) ≤ c0 * R)
    (hGreenLow : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η y) (c0 * R)),
      C⁻¹ * Real.log (if vertexPoint ε η y = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η y - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b)
    (hC0 : 0 < C0) (hC1 : 0 < C1) (hL : 0 < L) (hr : 0 < r) (hr1 : r ≤ 1) (hS0 : 0 ≤ Sr)
    (hSm : Sr ≤ C1 * L * mr)
    (hCd0 : 0 ≤ Cd) (hCd : Cd ≤ C0 * (1 + Real.log (1 / r)))
    (hexit : exitTimeMoment m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 4))) y 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * Cd ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) * S ^ (2 : ℕ))
    (hS : S ≤ ENNReal.ofReal Sr) :
    srwLaw m y (TestBound68.stayIn (fun b => innerVertices (cell ε η) (ball (vertexPoint ε η b) (R / 4))) A y) ≤
      ENNReal.ofReal (1 - (1 / (32 * C0 ^ 2 * C1 ^ 2 * L ^ 2)) / (1 + Real.log (1 / r)) ^ 2) :=
  stayIn_le_printed_green_draft (W := fun b => innerVertices (cell ε η) (ball (vertexPoint ε η b) (R / 4)))
    (y := y) (Aset := Aset) hap hε hR hmr hC hc0 hc0' hc0C hεc hmu hfinD hfinr hRr rfl hAs hsp hs hdiam
    (fun b hb => ⟨greenKernel_le_greenFn m _ y b, hGreenLow b hb⟩) hC0 hC1 hL hr hr1 hS0 hSm hCd0 hCd hexit hS

end HcGreen68

end MatedCRT

#print axioms MatedCRT.HcGreen68.greenKernel_le_greenFn
#print axioms MatedCRT.HcGreen68.stayIn_le_printed_interior
