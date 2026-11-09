import MatedCRT.FirstPass.S4S6c.TestBound68
import MatedCRT.FirstPass.S5c.GreenCount

/-!
# Printed geometry for the per-test bound of Lemma 6.8 (q2, task fp-S4S6c; LEMMA68 B3, C4)

`TestBound68.stayIn_le_log` takes four environment inputs hS (counting), hT (sparsity), hD (target set inside the
window, outside `A`) and hG, hmom (Green lower bound and second moment). This file discharges the first three from the
printed objects:
* hS from the ball-mass lower bound `ofReal mr ≤ μ (ball z R)` and `S5c.card_ge_mass_div` (cell count, eq. (16));
* hT from the printed sparsity `|A ∩ V^ε(B_r(z))| < s₁ r^{2β} ε⁻¹` (Lemma 6.8 hypothesis), via `V^ε(B_R(z)) ⊆ V^ε(B_r(z))`;
* hD from `V^ε(B_R(z)) ⊆ W y` (window inclusion, C14) and the definition of the sparse set `Aset = A ∩ V^ε(B_R(z))`.
hG and hmom stay explicit hypotheses (B4, B5).
-/

open MeasureTheory Set Metric Function
open scoped ENNReal

namespace MatedCRT
namespace PrintedTest68

/-- Counting input hS of `TestBound68.stayIn_le_log` (LEMMA68 B3, eq. (16)): a ball `B_R(z)` of area mass at least
`mr` contains at least `mr ε⁻¹` cell vertices. -/
theorem hS_of_mass {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε R mr : ℝ} {z : ℂ}
    (hε : 0 < ε) (hfin : (cellVertices ε η (ball z R)).Finite)
    (hmr : ENNReal.ofReal mr ≤ μ (ball z R)) :
    ε⁻¹ * (mr - 0) ≤ ((hfin.toFinset).card : ℝ) := by
  have h := MatedCRT.S5c.card_ge_mass_div hap hε hap.2.2.1 hfin hmr
  rw [Set.ncard_eq_toFinset_card _ hfin] at h
  rw [sub_zero, mul_comm]
  exact h

/-- Sparsity input hT of `TestBound68.stayIn_le_log` (LEMMA68 Lemma 6.8 hypothesis): the sparse set
`Aset = A ∩ V^ε(B_R(z))` has at most `ε⁻¹ (s₁ r^{2β})` elements when `|A ∩ V^ε(B_r(z))| < s₁ r^{2β} ε⁻¹` and
`B_R(z) ⊆ B_r(z)`. -/
theorem hT_of_sparse {η : ℝ → ℂ} {ε r R s1 β : ℝ} {z : ℂ} {A : Set ℤ} {Aset : Finset ℤ}
    (hRr : ball z R ⊆ ball z r) (hfinr : (cellVertices ε η (ball z r)).Finite)
    (hAs : ∀ k, k ∈ Aset ↔ k ∈ A ∩ cellVertices ε η (ball z R))
    (hsp : ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε) :
    (Aset.card : ℝ) ≤ ε⁻¹ * (s1 * r ^ (2 * β)) := by
  have hVmono : cellVertices ε η (ball z R) ⊆ cellVertices ε η (ball z r) :=
    fun k hk => by
      rcases hk with ⟨x, hx1, hx2⟩
      exact ⟨x, hx1, hRr hx2⟩
  have hsub : A ∩ cellVertices ε η (ball z R) ⊆ A ∩ cellVertices ε η (ball z r) :=
    inter_subset_inter_right _ hVmono
  have hcoe : ((Aset : Finset ℤ) : Set ℤ) = A ∩ cellVertices ε η (ball z R) := by
    ext k
    simp [hAs]
  have hc : (Aset.card : ℝ) = ((A ∩ cellVertices ε η (ball z R)).ncard : ℝ) := by
    rw [← hcoe, Set.ncard_coe_finset]
  have hle : ((A ∩ cellVertices ε η (ball z R)).ncard : ℝ) ≤ ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub (hfinr.subset inter_subset_right)
  have h2 : s1 * r ^ (2 * β) / ε = ε⁻¹ * (s1 * r ^ (2 * β)) := by ring
  rw [hc]
  linarith [hle, hsp, h2]

/-- Target condition hD of `TestBound68.stayIn_le_log` (LEMMA68 C4, eq. (C14)): each target vertex of the test ball
`V^ε(B_R(z))` that is not in the sparse set lies in the window `W y` and outside `A`. -/
theorem hD_of_window {η : ℝ → ℂ} {ε R : ℝ} {z : ℂ} {A W : Set ℤ} {Aset : Finset ℤ}
    (hfin : (cellVertices ε η (ball z R)).Finite) (hW : cellVertices ε η (ball z R) ⊆ W)
    (hAs : ∀ k, k ∈ Aset ↔ k ∈ A ∩ cellVertices ε η (ball z R)) :
    ∀ b ∈ hfin.toFinset \ Aset, b ∈ W ∧ b ∉ A := by
  intro b hb
  simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, hAs] at hb
  exact ⟨hW hb.1, fun hA => hb.2 ⟨hA, hb.1⟩⟩

/-- **Per-test bound of Lemma 6.8 (LEMMA68 C15-C16, eq. (15)) on the printed geometry.** The probability that the
walk from `y` stays in `A` until it exits the window `W y` is at most `1 - q₀ (1 + log(1/r))⁻²`, where the test ball
`B_R(z)` has area mass at least `mr`, the printed sparsity bounds `|A ∩ V^ε(B_r(z))|`, and the window contains
`V^ε(B_R(z))`. The Green lower bound `hG` (B4) and the second moment `hmom` (B5) are the remaining inputs. -/
theorem stayIn_le_printed {μ : Measure ℂ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {y : ℤ} {A : Set ℤ}
    {W : ℤ → Set ℤ} {z : ℂ} {ε R r mr s1 β C0 C1 L Sr : ℝ} {Aset : Finset ℤ}
    (hap : IsAreaParametrized μ η) (hε : 0 < ε) (hmr : 0 < mr) (hmu : ENNReal.ofReal mr ≤ μ (ball z R))
    (hfinR : (cellVertices ε η (ball z R)).Finite) (hfinr : (cellVertices ε η (ball z r)).Finite)
    (hRr : ball z R ⊆ ball z r) (hWy : cellVertices ε η (ball z R) ⊆ W y)
    (hAs : ∀ k, k ∈ Aset ↔ k ∈ A ∩ cellVertices ε η (ball z R))
    (hsp : ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε)
    (hs : s1 * r ^ (2 * β) ≤ mr / 4)
    (hC0 : 0 < C0) (hC1 : 0 < C1) (hL : 0 < L) (hr : 0 < r) (hr1 : r ≤ 1) (hS0 : 0 ≤ Sr)
    (hSm : Sr ≤ C1 * L * mr)
    (hG : ∀ b ∈ hfinR.toFinset \ Aset,
      (1 / 2 : ℝ≥0∞) ≤ ∑' n : ℕ, srwLaw m y {x | (n : ℕ∞) < vExitTime (W y) x ∧ x n = b})
    (hmom : ∫⁻ x, (ENat.toENNReal (vExitTime (W y) x)) ^ 2 ∂(srwLaw m y) ≤
      ENNReal.ofReal (2 * (C0 * (1 + Real.log (1 / r))) ^ 2 * ε⁻¹ ^ 2 * Sr ^ 2)) :
    srwLaw m y (TestBound68.stayIn W A y) ≤
      ENNReal.ofReal (1 - (1 / (32 * C0 ^ 2 * C1 ^ 2 * L ^ 2)) / (1 + Real.log (1 / r)) ^ 2) :=
  TestBound68.stayIn_le_log (m := m) (y := y) (W := W) (A := A) (D0 := hfinR.toFinset) (Aset := Aset)
    (ε := ε) (m0 := mr) (C0 := C0) (C1 := C1) (L := L) (Sr := Sr) (e1 := 0) (s := s1 * r ^ (2 * β)) (r := r)
    hε hmr hC0 hC1 hL hr hr1 hS0 hSm (by linarith) hs
    (by simpa using hS_of_mass hap hε hfinR hmu)
    (hT_of_sparse hRr hfinr hAs hsp) (hD_of_window hfinR hWy hAs) hG hmom

end PrintedTest68
end MatedCRT

#print axioms MatedCRT.PrintedTest68.hS_of_mass
#print axioms MatedCRT.PrintedTest68.hT_of_sparse
#print axioms MatedCRT.PrintedTest68.hD_of_window
#print axioms MatedCRT.PrintedTest68.stayIn_le_printed
