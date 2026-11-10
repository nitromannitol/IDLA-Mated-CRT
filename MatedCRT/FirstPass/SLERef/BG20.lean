import MatedCRT.FirstPass.SLERef.Reference
import MatedCRT.FirstPass.Frozen.S3c

/-!
# BG20 Proposition 5.1 and the reference package (fp-SLERef-closure-repair, item 3)

Operator note 07:50 UTC (Pro item 3): `BG20Prop51Ref ν` (`MatedCRT/FirstPass/Frozen/S3c.lean:54`) is circular. Its premise
is `SLEReferenceInput ν`, which already contains `ExitTimeUpperBoundStmt 𝒮` (Lemma 2.18), whose first clause is the
mass-restricted Proposition 5.1 statement. So `BG20Prop51Ref` adds nothing that the reference package does not already
give, and it cannot serve as an independent BG20 input for Lemma 2.18.

What this file proves (no new hypotheses):

* `bg20Prop51_of_exitTime`: the first clause of `ExitTimeUpperBoundStmt 𝒮` is exactly `BG20Prop51 𝒮` (same event, the
  second clause is dropped), so `BG20Prop51 𝒮` follows from `ExitTimeUpperBoundStmt 𝒮`.
* `bg20Prop51_of_reference`, `bg20Prop51Ref_of_reference`: the derived forms from `SLEReferenceInput ν`.

Consequence for the consumers (report only, files not owned here): an independent BG20 input for Lemma 2.18 is the per-model
`BG20Prop51 𝒮`, not `BG20Prop51Ref ν`; the existing per-model consumers are `firstPass_3_1_faithful_of_bg20Model` and
`firstPass_3_1_countable_of_bg20Model` (`MatedCRT/FirstPass/S3c.lean:154`, `:161`). The second clause of
`ExitTimeUpperBoundStmt` (unrestricted `D`, item 4) is not used here.
-/

namespace MatedCRT

open MeasureTheory

/-- Monotonicity of `HarmonicBalls.PolyHighProb` in the event: if `E r ⊆ F r` for all `r` and `E` has polynomially high
probability, then so does `F`. -/
theorem polyHighProb_of_subset_event {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (hE : HarmonicBalls.PolyHighProb P E) (hEF : ∀ r, E r ⊆ F r) : HarmonicBalls.PolyHighProb P F := by
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := hE
  refine ⟨p, hp, C, r₀, hr₀, fun r hr hrr => ?_⟩
  exact (measure_mono (Set.compl_subset_compl.mpr (hEF r))).trans (hb r hr hrr)

/-- BG20 Proposition 5.1 (`BG20Prop51 𝒮`, eq. (5.1)) is the first clause of `ExitTimeUpperBoundStmt 𝒮` (Lemma 2.18):
the two statements have the same mass-restricted event, and the second clause (unrestricted `D`) is dropped. -/
theorem bg20Prop51_of_exitTime {𝒮 : SpaceFillingSLEModel} (h : ExitTimeUpperBoundStmt 𝒮) : BG20Prop51 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨α, hα, hρ⟩ := h γ hγ0 hγ2
  refine ⟨α, hα, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨C, hC, hS⟩ := hρ ρ hρ0 hρ1
  refine ⟨C, hC, fun Ω _ S hv => ?_⟩
  exact polyHighProb_of_subset_event (hS Ω S hv) (fun _ ω hω => hω.1)

/-- Derived, not assumed: the certified reference package `SLEReferenceInput ν` gives `BG20Prop51 𝒮` for every model with
normalized law `ν` (through its cited component `ExitTimeUpperBoundStmt 𝒮`). -/
theorem bg20Prop51_of_reference {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : BG20Prop51 𝒮 :=
  bg20Prop51_of_exitTime (hν.2 𝒮 h).2.2.2.1

/-- `BG20Prop51Ref ν` is a theorem of the reference package (derived, not a frozen input). Its consumers should not
use it as an independent BG20 input; see the module docstring. -/
theorem bg20Prop51Ref_of_reference (ν : ℝ → Measure SLEPathCode) : BG20Prop51Ref ν :=
  fun hν _ h => bg20Prop51_of_reference hν h

end MatedCRT
