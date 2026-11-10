import MatedCRT.FirstPass.S4S6c.PrintedTest68

/-!
# The printed test bound with the local sparsity hypothesis `hA_local` (q2, task fp-S4S6c-envscaling-6-7-6-8)

Operator note (05:35 UTC, chat 176, `notes/fp-gaps/CHATGPT-idla-6-8-hRr.md`): the sparsity count of the test ball
`B_{c0 R}(η(y))` is bounded by the single local estimate

  `|A ∩ V^ε(B_{c0 R}(η(y)))| ≤ μ(B_{c0 R}(η(y))) / (4 ε)`   (`hA_local`),

which replaces the trio `hRr`, `hsp`, `hs` of `PrintedTest68.stayIn_le_printed` (the count at the `r`-ball and the
`s1 r^{2β}` budget): no ball inclusion `B_{c0R} ⊆ B_r` is needed any more.

`stayIn_le_printed_local` is `PrintedTest68.stayIn_le_printed` with `s := mr/4`: the card hypothesis of
`TestBound68.stayIn_le_log` is exactly `hA_local` (`ε⁻¹ · (mr/4) = mr/(4ε)`), and `hs : s ≤ mr/4` holds with equality.

Terminology: Armitage-Gardiner potential; Berestycki-Gwynne killed walk; LQG measure `μ`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace MatedCRT

namespace PrintedTestLocal68

/-- The printed test bound with `hA_local` in place of `hRr`, `hsp`, `hs`. -/
theorem stayIn_le_printed_local {μ : Measure ℂ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {y : ℤ} {A : Set ℤ}
    {W : ℤ → Set ℤ} {z : ℂ} {ε R mr C0 C1 L Sr : ℝ} {r : ℝ} {Aset : Finset ℤ}
    (hap : IsAreaParametrized μ η) (hε : 0 < ε) (hmr : 0 < mr) (hmu : ENNReal.ofReal mr ≤ μ (ball z R))
    (hfinR : (cellVertices ε η (ball z R)).Finite) (hWy : cellVertices ε η (ball z R) ⊆ W y)
    (hAs : ∀ k, k ∈ Aset ↔ k ∈ A ∩ cellVertices ε η (ball z R))
    (hAloc : (Aset.card : ℝ) ≤ ε⁻¹ * (mr / 4))
    (hC0 : 0 < C0) (hC1 : 0 < C1) (hL : 0 < L) (hr : 0 < r) (hr1 : r ≤ 1) (hS0 : 0 ≤ Sr)
    (hSm : Sr ≤ C1 * L * mr)
    (hG : ∀ b ∈ hfinR.toFinset \ Aset,
      (1 / 2 : ℝ≥0∞) ≤ ∑' n : ℕ, srwLaw m y {x | (n : ℕ∞) < vExitTime (W y) x ∧ x n = b})
    (hmom : ∫⁻ x, (ENat.toENNReal (vExitTime (W y) x)) ^ 2 ∂(srwLaw m y) ≤
      ENNReal.ofReal (2 * (C0 * (1 + Real.log (1 / r))) ^ 2 * ε⁻¹ ^ 2 * Sr ^ 2)) :
    srwLaw m y (TestBound68.stayIn W A y) ≤
      ENNReal.ofReal (1 - (1 / (32 * C0 ^ 2 * C1 ^ 2 * L ^ 2)) / (1 + Real.log (1 / r)) ^ 2) :=
  TestBound68.stayIn_le_log (m := m) (y := y) (W := W) (A := A) (D0 := hfinR.toFinset) (Aset := Aset)
    (ε := ε) (m0 := mr) (C0 := C0) (C1 := C1) (L := L) (Sr := Sr) (e1 := 0) (s := mr / 4) (r := r)
    hε hmr hC0 hC1 hL hr hr1 hS0 hSm (by linarith) le_rfl
    (by simpa using PrintedTest68.hS_of_mass hap hε hfinR hmu)
    hAloc (PrintedTest68.hD_of_window hfinR hWy hAs) hG hmom

end PrintedTestLocal68

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.PrintedTestLocal68.stayIn_le_printed_local
