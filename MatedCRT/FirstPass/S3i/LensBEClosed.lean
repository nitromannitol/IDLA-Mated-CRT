import MatedCRT.FirstPass.S3i.LensBE
import MatedCRT.FirstPass.S3i.LensGeometry
import MatedCRT.FirstPass.S3i.ExitProbability

/-!
# Lens hitting probability, closed form (S3i): plan Lemma 6 with Lemmas 1 and 5 discharged

Closed form of `lensProb_le_fp36` (`MatedCRT/FirstPass/S3i/LensBE.lean`).

* Lemma 5 is `H5.lensGeometry_fp36` (`MatedCRT/FirstPass/S3i/LensGeometry.lean`). Its
  hypotheses and conclusion are the binder of `lensProb_le_fp36`, argument for argument, so it is
  applied directly.
* Lemma 1 enters Lemma 6 only through its conjuncts 2-4 (range in `[0,1]`, discrete harmonicity on
  the exit set, boundary values `1_B` off the exit set), proved in `MatedCRT/FirstPass/S3i/ExitProbability.lean`
  Conjunct 1 (almost-sure exit from the exit set) is not used by Lemma 6 and is not
  assumed here.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

open Classical in
/-- Plan Lemma 1, conjuncts 2-4, for a finite exit set `A'` (`FiniteExitData m A'`): the exit-hit
probability lies in `[0,1]`, is discretely harmonic on `A'`, and equals the indicator of `B'` off `A'`.
Conjunct 1 of the printed Lemma 1 is not included. -/
theorem exitHitProb_basic_conj234 {m : ℤ → ℤ → ℕ} {A' B' : Set ℤ} (hfin : FiniteExitData m A') :
    (∀ a : ℤ, 0 ≤ exitHitProb m A' B' a ∧ exitHitProb m A' B' a ≤ 1) ∧
    (∀ a ∈ A', mLaplacian m (exitHitProb m A' B') a = 0) ∧
    (∀ a ∉ A', exitHitProb m A' B' a = if a ∈ B' then 1 else 0) :=
  ⟨fun a => exitHitProb_nonneg_le_one m A' B' a,
    fun _ ha => exitHitProb_mLaplacian_eq_zero m hfin ha,
    fun _ ha => exitHitProb_of_not_mem m ha⟩

/-- Plan Lemma 6 (`lensProb_le_fp36`) with Lemma 5 (`H5.lensGeometry_fp36`) and Lemma 1 conjuncts 2-4
(`exitHitProb_basic_conj234`) discharged. The only hypotheses are those of the plan statement. -/
theorem lensProb_le_fp36_closed
    {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A r ε : ℝ} {z y : ℂ} {ω : Ω} {v : ℤ}
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
  have hL5 := H5.lensGeometry_fp36 hε hb hr hρ hscale houter hgood hv
  obtain ⟨hvU, hcl, hsubρ₁, hopenU, hconnU, hscU, hposd, hdle, hfarU⟩ := hL5
  unfold FP36GoodEnv at hgood
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
  exact lensProb_le_of_BE_fp36 hε hν hA hBE hsubρ₁ hopenU hconnU hscU hvU hrange hharm hbdry'
    hposd hdle

end FirstPass36
end MatedCRT

#print axioms MatedCRT.FirstPass36.exitHitProb_basic_conj234
#print axioms MatedCRT.FirstPass36.lensProb_le_fp36_closed
