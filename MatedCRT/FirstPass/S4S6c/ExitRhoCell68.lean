import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.S6f.UniformEvents
import MatedCRT.FirstPass.S4S6c.HoneCellGood68

/-!
# The exit-time event at the cell radius `rhoCell68 ρ = (1 + ρ)/2` (fp-S4S6c-exit-rhocell, z10)

The hOne closures take `HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE)` as an input, and its source is the
Draft Lemma 2.18 `ExitTimeUpperBoundStmt` (Draft/Section2.lean:239), used by `meshEventsStmt_of_draft`
(Guard68S10.lean:222) at the radius `ρ`. Lemma 2.18 holds at every deterministic radius `ρ' ∈ (0,1)` with a constant
`C(ρ')`, so it holds at `ρ' = rhoCell68 ρ < 1`.

* `exitTimeEvent68_mono_CE`: the exit-time event grows with the constant `CE` (direct unfolding of the two conjuncts).
* `polyHighProb_of_subset`: `PolyHighProb` passes to a superset (`measure_mono` on the complements).
* `polyHighProb_exitTimeEvent68_rhoCell`: the exit event at `rhoCell68 ρ`, with the same `α` and an existential `CE`.
* `polyHighProb_exitTimeEvent68_rhoCell_of_stmt`: the same, with `α` and the bound taken from `ExitTimeUpperBoundStmt`.
* `polyHighProb_exitTimeEvent68_common_CE`: one common `CE` for the radii `ρ` and `rhoCell68 ρ`.

Terminology: Armstrong-Kuusi-Mourrat (exit times of the walk on cells, mesh), Duplantier-Sheffield (mated-CRT maps).
-/

namespace MatedCRT
namespace Lemma68ExitRhoCell

/-- Increasing the constant `CE` enlarges the exit-time event `exitTimeEvent68` (for `ε > 0`, `0 ≤ CE₁ ≤ CE₂`). -/
theorem exitTimeEvent68_mono_CE {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {α ρ CE₁ CE₂ : ℝ}
    (hCE₁ : 0 ≤ CE₁) (h : CE₁ ≤ CE₂) {ε : ℝ} (hε : 0 < ε) :
    exitTimeEvent68 S α ρ CE₁ ε ⊆ exitTimeEvent68 S α ρ CE₂ ε := by
  rintro ω ⟨h1, h2⟩
  refine ⟨fun D hD hDB hμ a ha N => ?_, fun D hDB a ha => ?_⟩
  · have hpow : CE₁ ^ N ≤ CE₂ ^ N := pow_le_pow_left₀ hCE₁ h N
    have hr : 0 ≤ ε ^ (-(N : ℝ)) := Real.rpow_nonneg hε.le _
    have hreal : (N.factorial : ℝ) * CE₁ ^ N * ε ^ (-(N : ℝ)) ≤ (N.factorial : ℝ) * CE₂ ^ N * ε ^ (-(N : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) hr
    exact (h1 D hD hDB hμ a ha N).trans
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hreal) zero_le)
  · obtain ⟨hn, he⟩ := h2 D hDB a ha
    refine ⟨hn, he.trans ?_⟩
    have hinv : 0 ≤ ε⁻¹ := (inv_pos.mpr hε).le
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h hinv)) zero_le

/-- `PolyHighProb` passes to a family of supersets, for `ε > 0`: the complements shrink (`measure_mono`). -/
theorem polyHighProb_of_subset {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    {E F : ℝ → Set Ω} (hEF : ∀ ε : ℝ, 0 < ε → E ε ⊆ F ε) (hE : HarmonicBalls.PolyHighProb P E) :
    HarmonicBalls.PolyHighProb P F := by
  obtain ⟨p, hp, C, r₀, hr₀, h⟩ := hE
  refine ⟨p, hp, C, r₀, hr₀, fun r hr0 hr1 => ?_⟩
  calc P (F r)ᶜ ≤ P (E r)ᶜ := MeasureTheory.measure_mono (Set.compl_subset_compl.mpr (hEF r hr0))
    _ ≤ ENNReal.ofReal (C * r ^ p) := h r hr0 hr1

/-- **The exit-time event at the cell radius.** Given the Lemma 2.18 bound at the exponent `α` for every radius
`ρ' ∈ (0,1)` (the `ExitTimeUpperBoundStmt` shape at `α`), the exit-time event at `rhoCell68 ρ = (1+ρ)/2 < 1` is of
polynomially high probability for some constant `CE`, for every valid environment. -/
theorem polyHighProb_exitTimeEvent68_rhoCell (𝒮 : SpaceFillingSLEModel) {γ α : ℝ}
    (hα : ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ' C))
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ CE : ℝ, 0 < CE ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE) := by
  have hpos : 0 < Lemma68HoneCellGood.rhoCell68 ρ := by
    unfold Lemma68HoneCellGood.rhoCell68
    linarith
  obtain ⟨CE, hCE, hEr⟩ := hα (Lemma68HoneCellGood.rhoCell68 ρ) hpos
    (Lemma68HoneCellGood.rhoCell68_lt_one hρ1)
  exact ⟨CE, hCE, hEr⟩

/-- **The exit-time event at the cell radius, from `ExitTimeUpperBoundStmt` (Draft Lemma 2.18).** The exponent `α` is
the one of the Draft statement at `γ`; for every `ρ ∈ (0,1)` the event at `rhoCell68 ρ` has polynomially high
probability for some `CE`. This is the source used by `meshEventsStmt_of_draft` (Guard68S10.lean:222), at the
radius `rhoCell68 ρ` instead of `ρ`. -/
theorem polyHighProb_exitTimeEvent68_rhoCell_of_stmt {𝒮 : SpaceFillingSLEModel}
    (hE : MatedCRT.ExitTimeUpperBoundStmt 𝒮) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ CE : ℝ, 0 < CE ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE) := by
  obtain ⟨α, hα0, hEα⟩ := hE γ hγ0 hγ2
  exact ⟨α, hα0, fun ρ hρ0 hρ1 => polyHighProb_exitTimeEvent68_rhoCell 𝒮 hEα ρ hρ0 hρ1⟩

/-- **One common constant for the radii `ρ` and `rhoCell68 ρ`.** For `ρ ∈ (0,1)`, one `CE` makes the exit-time event
of polynomially high probability at both radii, for every valid environment (`exitTimeEvent68_mono_CE` with
`CE := max C₁ C₂`). -/
theorem polyHighProb_exitTimeEvent68_common_CE (𝒮 : SpaceFillingSLEModel) {γ α : ℝ}
    (hα : ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ' C))
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ CE : ℝ, 0 < CE ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) ∧
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE) := by
  have hpos : 0 < Lemma68HoneCellGood.rhoCell68 ρ := by
    unfold Lemma68HoneCellGood.rhoCell68
    linarith
  obtain ⟨C₁, hC₁, h₁⟩ := hα ρ hρ0 hρ1
  obtain ⟨C₂, hC₂, h₂⟩ := hα (Lemma68HoneCellGood.rhoCell68 ρ) hpos (Lemma68HoneCellGood.rhoCell68_lt_one hρ1)
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), fun Ω _ S hS => ⟨?_, ?_⟩⟩
  · exact polyHighProb_of_subset S.P (fun ε hε => exitTimeEvent68_mono_CE S hC₁.le (le_max_left _ _) hε)
      (h₁ Ω S hS)
  · exact polyHighProb_of_subset S.P (fun ε hε => exitTimeEvent68_mono_CE S hC₂.le (le_max_right _ _) hε)
      (h₂ Ω S hS)

#print axioms MatedCRT.Lemma68ExitRhoCell.exitTimeEvent68_mono_CE
#print axioms MatedCRT.Lemma68ExitRhoCell.polyHighProb_exitTimeEvent68_rhoCell
#print axioms MatedCRT.Lemma68ExitRhoCell.polyHighProb_exitTimeEvent68_rhoCell_of_stmt
#print axioms MatedCRT.Lemma68ExitRhoCell.polyHighProb_exitTimeEvent68_common_CE

end Lemma68ExitRhoCell
end MatedCRT
