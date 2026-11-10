import Mathlib
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.OfSteps
import MatedCRT.FirstPass.S6e.Cutoff

/-!
# FIRST PASS: the final event of LEMMA68 (D2) (task fp-S6e-lemma68-D123, z9)

Source: `notes/fp-gaps/CHATGPT-lemma68-open-parts.md`, D2 (lines 957-989). The good event `E ε` of the write-up
(the cell, counting, Green and exit-moment events of B1), the field event `G` of probability one (A1, A5) and the
radius bounds are abstract here. The per-configuration quenched bound on `E ε ∩ G` is the output of section C
(C12, C17): it enters as the hypothesis `hpt`, with the count `N` of (C17) satisfying `r^(-ζ)/200 ≤ N`.
The statement keeps the quantifier order of D2: first `ε`, then every `r ∈ [α ε, dd ω]` and every configuration `i`,
on the event `E ε ∩ G`. The numerical step is `Lemma68Cutoff.D1_le_half`.
-/

open MeasureTheory Filter Topology Set

namespace MatedCRT

namespace Lemma68Final

/-- (D2) If `E` has probability tending to one (`ProbTendsToOne`), the field event `G` has probability one, and on
`E ε ∩ G` every quenched configuration bound of (C17) holds for all admissible radii `r ∈ [α ε, dd ω]`, then the
uniform bound `≤ 1/2` of the printed Lemma 6.8 (`s₂ = 1/2`) holds with probability tending to one. -/
theorem probTendsToOne_uniform_half {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (hE : ProbTendsToOne P E) {G : Set Ω} (hG : P Gᶜ = 0)
    {α : ℝ → ℝ} (hα : ∀ ε, 0 < ε → 0 < α ε)
    {dd : Ω → ℝ} {R : ℝ} (hdd : ∀ ω, dd ω ≤ R) {ζ q0 : ℝ} (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ : 0 < ζ)
    (hζ' : ζ < 1 / 2) (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ) (Q : Ω → ℝ → ι → ℝ)
    (hpt : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι,
      ∃ N : ℕ, r ^ (-ζ) / 200 ≤ (N : ℝ) ∧ Q ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N) :
    ProbTendsToOne P (fun ε => {ω | ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι, Q ω r i ≤ 1 / 2}) := by
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hG
  have hGa : ProbTendsToOne P (fun _ => G) := probTendsToOne_of_ae hGae
  refine (hE.inter hGa).mono_pos ?_
  intro ε hε ω hω r hαr hrd i
  obtain ⟨N, hN, hQ⟩ := hpt ε hε ω hω r hαr hrd i
  have hr0 : 0 < r := (hα ε hε).trans_le hαr
  have hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ := (hrd.trans (hdd ω)).trans hR
  exact hQ.trans (Lemma68Cutoff.D1_le_half hq0 hq1 hζ hζ' hr0 hrA hN)

end Lemma68Final

end MatedCRT
