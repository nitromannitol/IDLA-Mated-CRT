import MatedCRT.FirstPass.S3i.LensBEClosed
import MatedCRT.FirstPass.S3i.LensFlooredLens
import MatedCRT.FirstPass.S3i.LensFloored

/-!
# The closed lens probability bound for the floored good environment

Floored copy of `lensProb_le_fp36_closed` (S3i/LensBEClosed.lean:39) for `FP36GoodEnvFloored` (S3i/LensFloored.lean).
The body is that of the original, with `H5.lensGeometry_fp36_floored` (S3i/LensFlooredLens.lean) and the floored core
`lensProb_le_of_BE_fp36_floored` (S3i/LensFloored.lean), which needs `b ≤ β` and `ε ≤ 1` (MQ-li-9 step 2).
The helper `exitHitProb_basic_conj234` does not take the environment and is reused.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Lens hitting probability, floored good environment** (copy of `lensProb_le_fp36_closed`,
S3i/LensBEClosed.lean:39). -/
theorem lensProb_le_fp36_closed_floored
    {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A β r ε : ℝ} {z y : ℂ} {ω : Ω} {v : ℤ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 < b) (hβb : b ≤ β) (hν : 0 < ν)
    (hA : 0 < A) (hr : 0 < r) (hρ : ρ₀ < ρ₁)
    (hscale : 64 * ε ^ b ≤ ε ^ (b / 2))
    (houter : closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀)
    (hgood : FP36GoodEnvFloored S ρ₀ ρ₁ b ν A β r z y ε ω)
    (hv : v ∈ vBoundary (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) :
    let δ := ε ^ b
    let s := ε ^ (b / 2)
    let q := vertexPoint ε (S.η ω) v
    let P := ballRetraction z r q
    fp36LensProb (S.mult ε ω) ε (S.η ω) z r δ P s v
      ≤ A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2) := by
  intro δ s q P
  have hL5 := H5.lensGeometry_fp36_floored hε hb hr hρ hscale houter hgood hv
  obtain ⟨hvU, hcl, hsubρ₁, hopenU, hconnU, hscU, hposd, hdle, hfarU⟩ := hL5
  unfold FP36GoodEnvFloored at hgood
  obtain ⟨-, -, -, hfin, -, hBE⟩ := hgood
  have hfinU : FiniteExitData (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (fp36LensDomain z r δ P s)) :=
    (hfin _ hcl).2
  obtain ⟨hrange, hharm, hbdry⟩ :=
    exitHitProb_basic_conj234 (B' := fp36LensFarCells ε (S.η ω) P s) hfinU
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
  exact lensProb_le_of_BE_fp36_floored hε hε1 hν hA hβb hBE hsubρ₁ hopenU hconnU hscU hvU hrange hharm hbdry'
    hposd hdle

end FirstPass36
end MatedCRT
