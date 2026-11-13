import MatedCRT.FirstPass.S3i.LensDefs
import MatedCRT.FirstPass.S3i.Proof

/-!
# Lens hitting probability from the one-sided BE estimate (plan Lemma 6)

Plan section 6 "Apply BE to the lens hitting probability": the deterministic core `lensProb_le_of_BE_fp36`. Plan
Lemma 6 itself, with Lemmas 1 and 5 discharged, is `lensProb_le_fp36_closed` (`S3i/LensBEClosed.lean`). The exponent
is `boundary_power_le_fp36` (`S3i/Proof.lean:50`).

Terminology: discrete harmonic measure of the lens domain (Armitage-Gardiner: the exit distribution of the random walk
from the interior cells), one-sided boundary continuity (BE, Gwynne-Miller-Sheffield Theorem 3.9, eq. (3.31)).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- Deterministic core of plan Lemma 6: once the lens exit function `f` is bounded in `[0,1]`, is discrete
harmonic on the interior lens cells, and vanishes on the boundary cells of the lens within `B_{s/16}(q)`, the one-sided
BE property at `D = U` gives `f v ≤ A · 96^ν · ε^{νb/2}`, via the distance bound `d ≤ 6ε^b` of the lens. -/
lemma lensProb_le_of_BE_fp36
    {m : ℤ → ℤ → ℕ} {ε ρ₁ b ν A : ℝ} {η : ℝ → ℂ} {U : Set ℂ} {v : ℤ} {f : ℤ → ℝ}
    (hε : 0 < ε) (hν : 0 < ν) (hA : 0 < A)
    (hBE : FP36OneSidedBEAt m ε η ρ₁ ν A)
    (hUρ : U ⊆ ball 0 ρ₁) (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hUsc : SimplyConnectedSpace U)
    (hvU : v ∈ interiorCellVertices ε η U)
    (hrange : ∀ a, 0 ≤ f a ∧ f a ≤ 1)
    (hharm : ∀ x ∈ interiorCellVertices ε η U, matedLaplacian m f x = 0)
    (hbdry : ∀ k ∈ cellVertices ε η (frontier U ∩ ball (vertexPoint ε η v) (ε ^ (b / 2) / 16)), f k = 0)
    (hpos : 0 < infDist (vertexPoint ε η v) (frontier U))
    (hle : infDist (vertexPoint ε η v) (frontier U) ≤ 6 * ε ^ b) :
    f v ≤ A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2) := by
  have hsup0 : boundarySupNear ε η U f v (ε ^ (b / 2) / 16) = 0 := by
    unfold boundarySupNear
    exact le_antisymm
      (Real.iSup_le (fun k => Real.iSup_le (fun hk => (hbdry k hk).le) le_rfl) le_rfl)
      (Real.iSup_nonneg (fun k => Real.iSup_nonneg (fun hk => (hbdry k hk).ge)))
  have hdisc : discreteSupNorm ε η U f ≤ 1 := by
    unfold discreteSupNorm
    exact Real.iSup_le
      (fun k => Real.iSup_le (fun _ => abs_le.2 ⟨by linarith [(hrange k).1], (hrange k).2⟩) zero_le_one)
      zero_le_one
  have hbe : f v ≤ boundarySupNear ε η U f v (ε ^ (b / 2) / 16)
      + A * discreteSupNorm ε η U f
        * ((ε ^ (b / 2) / 16) / infDist (vertexPoint ε η v) (frontier U)) ^ (-ν) :=
    hBE U f hUρ hUopen hUconn hUsc hharm v hvU.1 (ε ^ (b / 2) / 16)
        (div_pos (Real.rpow_pos_of_pos hε _) (by norm_num))
  have hpow := boundary_power_le_fp36 (ε := ε) (b := b) (ν := ν) (c := 16) (K := 6)
    (t := ε ^ (b / 2) / 16) hε hν (by norm_num) (by norm_num) hpos hle (le_refl _)
  rw [show ((16 : ℝ) * 6) = 96 by norm_num] at hpow
  have hX : 0 ≤ ((ε ^ (b / 2) / 16) / infDist (vertexPoint ε η v) (frontier U)) ^ (-ν) :=
    Real.rpow_nonneg (div_nonneg (div_nonneg (Real.rpow_nonneg hε.le _) (by norm_num)) hpos.le) _
  rw [hsup0, zero_add] at hbe
  calc f v ≤ A * discreteSupNorm ε η U f
        * ((ε ^ (b / 2) / 16) / infDist (vertexPoint ε η v) (frontier U)) ^ (-ν) := hbe
    _ ≤ A * 1 * ((ε ^ (b / 2) / 16) / infDist (vertexPoint ε η v) (frontier U)) ^ (-ν) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdisc hA.le) hX
    _ ≤ A * 1 * ((96 : ℝ) ^ ν * ε ^ (ν * b / 2)) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hA.le zero_le_one)
    _ = A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2) := by ring

end FirstPass36
end MatedCRT

#print axioms MatedCRT.FirstPass36.lensProb_le_of_BE_fp36
