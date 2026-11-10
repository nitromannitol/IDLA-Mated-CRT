import Mathlib
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.OfSteps
import MatedCRT.FirstPass.S6e.Cutoff

/-!
# FIRST PASS: the final event of LEMMA68 (D2, bridge §2) (task fp-S6e-lemma68-D123 and fp-S6h, z9)

Source: `notes/fp-gaps/CHATGPT-lemma68-open-parts.md` D2 (lines 957-989), and the bridge answer
`notes/fp-gaps/CHATGPT-z9-6-8-bridge.md` §2.1 (admissibility guard, lines 95-135) and §2.2 (mesh argument,
lines 136-177). The configuration quantity `exitF ε ω r i` (the quenched exit probability `exitQ` of bridge §1) and
its admissibility guard `Adm ε ω r i` are parameters: z8 instantiates them in `FirstPass/S6h.lean`.

The quantifier order of D2 is kept: first `ε`, then every `r ∈ [α ε, dd ω]` and every configuration `i`, on
`E ε ∩ G`. The scalar `Q` depends on the mesh `ε` (bridge §2.2). Outside the guard `Adm` the scalar is `0`
(bridge §2.1): the guard is essential, since the raw exit probability of the empty configuration is `1`.
-/

open MeasureTheory Filter Topology Set

namespace MatedCRT

namespace Lemma68Final

open Classical in
/-- (bridge §2.1) The guarded scalar: the zero extension of `exitF` outside the admissible configurations `Adm`. -/
noncomputable def guardedExit {Ω ι : Type*} (Adm : ℝ → Ω → ℝ → ι → Prop) (exitF : ℝ → Ω → ℝ → ι → ℝ) :
    ℝ → Ω → ℝ → ι → ℝ :=
  fun ε ω r i => if Adm ε ω r i then exitF ε ω r i else 0

lemma guardedExit_of_adm {Ω ι : Type*} {Adm : ℝ → Ω → ℝ → ι → Prop} {exitF : ℝ → Ω → ℝ → ι → ℝ}
    {ε : ℝ} {ω : Ω} {r : ℝ} {i : ι} (h : Adm ε ω r i) :
    guardedExit Adm exitF ε ω r i = exitF ε ω r i := by
  simp [guardedExit, h]

lemma guardedExit_of_not_adm {Ω ι : Type*} {Adm : ℝ → Ω → ℝ → ι → Prop} {exitF : ℝ → Ω → ℝ → ι → ℝ}
    {ε : ℝ} {ω : Ω} {r : ℝ} {i : ι} (h : ¬ Adm ε ω r i) :
    guardedExit Adm exitF ε ω r i = 0 := by
  simp [guardedExit, h]

/-- (D2, mesh-indexed form; bridge §2.2) If `E` has probability tending to one (`ProbTendsToOne`), the field event `G`
has probability one, and on `E ε ∩ G` every quenched configuration bound of (C17) holds for all admissible radii
`r ∈ [α ε, dd ω]`, with the scalar `Q ε ω r i` depending on the mesh `ε`, then the uniform bound `≤ 1/2` of the printed
Lemma 6.8 (`s₂ = 1/2`) holds with probability tending to one. -/
theorem probTendsToOne_uniform_half {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (hE : ProbTendsToOne P E) {G : Set Ω} (hG : P Gᶜ = 0)
    {α : ℝ → ℝ} (hα : ∀ ε, 0 < ε → 0 < α ε)
    {dd : Ω → ℝ} {R : ℝ} (hdd : ∀ ω, dd ω ≤ R) {ζ q0 : ℝ} (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ : 0 < ζ)
    (hζ' : ζ < 1 / 2) (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ) (Q : ℝ → Ω → ℝ → ι → ℝ)
    (hpt : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι,
      ∃ N : ℕ, r ^ (-ζ) / 200 ≤ (N : ℝ) ∧ Q ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N) :
    ProbTendsToOne P (fun ε => {ω | ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι, Q ε ω r i ≤ 1 / 2}) := by
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hG
  have hGa : ProbTendsToOne P (fun _ => G) := probTendsToOne_of_ae hGae
  refine (hE.inter hGa).mono_pos ?_
  intro ε hε ω hω r hαr hrd i
  obtain ⟨N, hN, hQ⟩ := hpt ε hε ω hω r hαr hrd i
  have hr0 : 0 < r := (hα ε hε).trans_le hαr
  have hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ := (hrd.trans (hdd ω)).trans hR
  exact hQ.trans (Lemma68Cutoff.D1_le_half hq0 hq1 hζ hζ' hr0 hrA hN)

/-- (D2 with the guard; bridge §2.1 and §2.2) The bound `hpt` is needed only on the admissible configurations `Adm`;
outside `Adm` the guarded scalar is `0` and the witness `N = ⌈r^(-ζ)/200⌉₊` works, since `1 - q0/(1+log(1/r))² ≥ 0`
for `0 < r ≤ 1`. The conclusion is the guarded uniform bound of the printed Lemma 6.8. -/
theorem probTendsToOne_uniform_half_guarded {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (hE : ProbTendsToOne P E) {G : Set Ω} (hG : P Gᶜ = 0)
    {α : ℝ → ℝ} (hα : ∀ ε, 0 < ε → 0 < α ε)
    {dd : Ω → ℝ} {R : ℝ} (hdd : ∀ ω, dd ω ≤ R) {ζ q0 : ℝ} (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ : 0 < ζ)
    (hζ' : ζ < 1 / 2) (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ)
    (Adm : ℝ → Ω → ℝ → ι → Prop) (exitF : ℝ → Ω → ℝ → ι → ℝ)
    (hpt : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι, Adm ε ω r i →
      ∃ N : ℕ, r ^ (-ζ) / 200 ≤ (N : ℝ) ∧ exitF ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N) :
    ProbTendsToOne P (fun ε => {ω | ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι,
      guardedExit Adm exitF ε ω r i ≤ 1 / 2}) := by
  refine probTendsToOne_uniform_half hE hG hα hdd hq0 hq1 hζ hζ' hR (guardedExit Adm exitF) ?_
  intro ε hε ω hω r hαr hrd i
  by_cases hA : Adm ε ω r i
  · rw [guardedExit_of_adm hA]
    exact hpt ε hε ω hω r hαr hrd i hA
  · rw [guardedExit_of_not_adm hA]
    have hr0 : 0 < r := (hα ε hε).trans_le hαr
    have hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ := (hrd.trans (hdd ω)).trans hR
    have hA1 : Lemma68Cutoff.rAmp q0 ζ ≤ 1 := min_le_left _ _
    have hr1 : r ≤ 1 := hrA.trans hA1
    have hlog : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr0 hr1)
    have hbase : 0 ≤ 1 - q0 / (1 + Real.log (1 / r)) ^ 2 := by
      have h1 : q0 ≤ (1 + Real.log (1 / r)) ^ 2 := by nlinarith
      have h2 : q0 / (1 + Real.log (1 / r)) ^ 2 ≤ 1 :=
        (div_le_one (pow_pos (by linarith) 2)).2 h1
      linarith
    exact ⟨⌈r ^ (-ζ) / 200⌉₊, Nat.le_ceil _, pow_nonneg hbase _⟩

end Lemma68Final

end MatedCRT
