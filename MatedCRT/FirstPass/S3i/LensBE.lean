import MatedCRT.FirstPass.S3i.LensDefs
import MatedCRT.FirstPass.S3i.Proof

/-!
# Lens hitting probability from the one-sided BE estimate (plan Lemma 6)

Plan section 6 "Apply BE to the lens hitting
probability". Lemma 1 (`exitHitProb_basic`) and Lemma 5 (`lensGeometry_fp36`) enter as binders
with the plan's exact types until they land. The exponent is `boundary_power_le_fp36` (`S3i/Proof.lean:50`).

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

open Classical in
/-- Plan Lemma 6 (`lensProb_le_fp36`): the lens hitting probability of a boundary cell `v` of the disc `B_r(z)` is
at most `A · 96^ν · ε^{νb/2}`. The two binders are Lemma 1 (`exitHitProb_basic`) and Lemma 5 (`lensGeometry_fp36`)
of the plan, with their exact types. -/
lemma lensProb_le_fp36
    {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A r ε : ℝ} {z y : ℂ} {ω : Ω} {v : ℤ}
    (exitHitProb_basic : ∀ {m : ℤ → ℤ → ℕ} {A' B' : Set ℤ}, FiniteExitData m A' →
      (∀ a ∈ A', srwLaw m a {x | UsesEdges m a x ∧ vExitTime A' x < ⊤} = 1) ∧
      (∀ a : ℤ, 0 ≤ exitHitProb m A' B' a ∧ exitHitProb m A' B' a ≤ 1) ∧
      (∀ a ∈ A', mLaplacian m (exitHitProb m A' B') a = 0) ∧
      (∀ a ∉ A', exitHitProb m A' B' a = if a ∈ B' then 1 else 0))
    (lensGeometry_fp36 : ∀ {Ω' : Type} [MeasurableSpace Ω'] {S' : MatedCRTEnv Ω'}
      {ρ₀' ρ₁' b' ν' A' r' ε' : ℝ} {z' y' : ℂ} {ω' : Ω'} {v' : ℤ},
      0 < ε' → 0 < b' → 0 < r' → ρ₀' < ρ₁' → 64 * ε' ^ b' ≤ ε' ^ (b' / 2) →
      closure (ball z' (r' + 4 * ε' ^ b')) ⊆ ball 0 ρ₀' →
      FP36GoodEnv S' ρ₀' ρ₁' b' ν' A' r' z' y' ε' ω' →
      v' ∈ vBoundary (S'.mult ε' ω') (interiorCellVertices ε' (S'.η ω') (ball z' r')) →
      let δ := ε' ^ b'
      let s := ε' ^ (b' / 2)
      let η := S'.η ω'
      let q := vertexPoint ε' η v'
      let P := ballRetraction z' r' q
      let U := fp36LensDomain z' r' δ P s
      let B := fp36LensFarCells ε' η P s
      v' ∈ interiorCellVertices ε' η U ∧
      closure U ⊆ ball 0 ρ₀' ∧
      U ⊆ ball 0 ρ₁' ∧
      IsOpen U ∧ IsConnected U ∧ SimplyConnectedSpace U ∧
      0 < infDist q (frontier U) ∧
      infDist q (frontier U) ≤ 6 * δ ∧
      ∀ k ∈ cellVertices ε' η (frontier U ∩ ball q (s / 16)), k ∉ B)
    (hε : 0 < ε) (hb : 0 < b) (hν : 0 < ν)
    (hA : 0 < A) (hr : 0 < r) (hρ : ρ₀ < ρ₁)
    (hscale : 64 * ε ^ b ≤ ε ^ (b / 2))
    (houter : closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀)
    (hgood : FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω)
    (hv : v ∈ vBoundary (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) :
    let δ := ε ^ b
    let s := ε ^ (b / 2)
    let q := vertexPoint ε (S.η ω) v
    let P := ballRetraction z r q
    fp36LensProb (S.mult ε ω) ε (S.η ω) z r δ P s v
      ≤ A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2) := by
  intro δ s q P
  have hL5 := lensGeometry_fp36 hε hb hr hρ hscale houter hgood hv
  obtain ⟨hvU, hcl, hsubρ₁, hopenU, hconnU, hscU, hposd, hdle, hfarU⟩ := hL5
  unfold FP36GoodEnv at hgood
  obtain ⟨-, -, -, hfin, -, hBE⟩ := hgood
  have hfinU : FiniteExitData (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (fp36LensDomain z r δ P s)) :=
    (hfin _ hcl).2
  obtain ⟨-, hrange, hharm, hbdry⟩ :=
    exitHitProb_basic (B' := fp36LensFarCells ε (S.η ω) P s) hfinU
  have hbdry' : ∀ k ∈ cellVertices ε (S.η ω)
      (frontier (fp36LensDomain z r δ P s) ∩ ball (vertexPoint ε (S.η ω) v) (ε ^ (b / 2) / 16)),
      exitHitProb (S.mult ε ω) (interiorCellVertices ε (S.η ω) (fp36LensDomain z r δ P s))
        (fp36LensFarCells ε (S.η ω) P s) k = 0 := by
    intro k hk
    have hkB : k ∉ fp36LensFarCells ε (S.η ω) P s := hfarU k hk
    have hkF : k ∈ cellVertices ε (S.η ω) (frontier (fp36LensDomain z r δ P s)) := by
      obtain ⟨x, hx1, hx2⟩ := hk
      exact ⟨x, hx1, hx2.1⟩
    have hkI : k ∉ interiorCellVertices ε (S.η ω) (fp36LensDomain z r δ P s) :=
      fun hI => hI.2 hkF
    rw [hbdry k hkI]
    simp [hkB]
  exact lensProb_le_of_BE_fp36 hε hν hA hBE hsubρ₁ hopenU hconnU hscU hvU hrange hharm hbdry'
    hposd hdle

end FirstPass36
end MatedCRT

#print axioms MatedCRT.FirstPass36.lensProb_le_of_BE_fp36
#print axioms MatedCRT.FirstPass36.lensProb_le_fp36
