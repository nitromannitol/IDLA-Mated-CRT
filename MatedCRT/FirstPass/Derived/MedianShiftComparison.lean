import MatedCRT.Defs.Notation

/-!
# Lower medians of two exit times that differ by at most one

If two `[0, ∞]`-valued random times satisfy `X ≤ Y ≤ X + 1` almost surely, then their lower medians
(`medianOf`, eq:mo and eq:meps, lines 727-731, with the distribution-function convention
`s ↦ P[T ≤ s]` of `MatedCRTEnv.mε`) satisfy `med X ≤ med Y ≤ med X + 1`.

This compares the exit time of the embedded walk counted in steps (`embeddedExitTime`) with the exit time of its
linear interpolation: in a convex domain the interpolated path cannot leave between two consecutive vertices that
both lie in the domain, so `τ_linear ≤ τ_steps ≤ τ_linear + 1`, and the two lower medians differ by at most one.

No hypothesis beyond the almost sure comparison is needed: the median set `{m ≥ 0 : 1/2 ≤ P[T ≤ m]}` is bounded
below by `0`, and the comparison shows that the median set of `X` is empty exactly when that of `Y` is (both lower
medians are then `sInf ∅ = 0`). The measures need not be finite and the events need not be measurable (the
comparisons use only monotonicity of outer measure and of the lower Lebesgue integral).

## Main statements

* `MatedCRT.medianOf_le_and_le_add_one_of_cdf`: the deterministic comparison of lower medians of two distribution
  functions `F`, `G` with `G s ≤ F s ≤ G (s + 1)` for `s ≥ 0`.
* `MatedCRT.medianOf_measure_le_and_le_add_one`: the lower medians of `X ≤ Y ≤ X + 1` (a.e.) under one measure.
* `MatedCRT.medianOf_lintegral_le_and_le_add_one`: the same under an annealed mixture
  `∫⁻ ω, K ω {x | T ω x ≤ s} ∂P`, the form of `MatedCRTEnv.mε` (with `K ω` the law of the walk on paths
  `ℕ → ℤ` given the environment `ω`).
-/

namespace MatedCRT

open MeasureTheory Filter Set
open scoped ENNReal

/-- Comparison of the infima of two sets of nonnegative reals, one contained in the other, such that the shift by
one maps the larger set into the smaller. -/
theorem sInf_le_and_le_add_one_of_subset_of_add_one_mem {SF SG : Set ℝ} (hF0 : ∀ m ∈ SF, 0 ≤ m)
    (hG0 : ∀ m ∈ SG, 0 ≤ m) (hsub : SG ⊆ SF) (hshift : ∀ m ∈ SF, m + 1 ∈ SG) :
    sInf SF ≤ sInf SG ∧ sInf SG ≤ sInf SF + 1 := by
  have hbddF : BddBelow SF := ⟨0, hF0⟩
  have hbddG : BddBelow SG := ⟨0, hG0⟩
  rcases SF.eq_empty_or_nonempty with hF | hF
  · have hG : SG = ∅ := by
      rw [hF] at hsub
      exact Set.subset_empty_iff.1 hsub
    rw [hF, hG, Real.sInf_empty]
    norm_num
  · have hG : SG.Nonempty := by
      obtain ⟨m, hm⟩ := hF
      exact ⟨m + 1, hshift m hm⟩
    refine ⟨csInf_le_csInf hbddF hG hsub, ?_⟩
    have h : sInf SG - 1 ≤ sInf SF :=
      le_csInf hF fun m hm => by
        have := csInf_le hbddG (hshift m hm)
        linarith
    linarith

/-- **Lower medians of shifted distribution functions.** If `G s ≤ F s ≤ G (s + 1)` for every `s ≥ 0` (as for the
distribution functions of `X ≤ Y ≤ X + 1`, with `F` the one of `X` and `G` the one of `Y`), then
`medianOf F ≤ medianOf G ≤ medianOf F + 1`. -/
theorem medianOf_le_and_le_add_one_of_cdf {F G : ℝ → ℝ≥0∞} (hGF : ∀ s, 0 ≤ s → G s ≤ F s)
    (hFG : ∀ s, 0 ≤ s → F s ≤ G (s + 1)) :
    medianOf F ≤ medianOf G ∧ medianOf G ≤ medianOf F + 1 := by
  unfold medianOf
  refine sInf_le_and_le_add_one_of_subset_of_add_one_mem (fun m hm => hm.1) (fun m hm => hm.1)
    (fun m hm => ⟨hm.1, hm.2.trans (hGF m hm.1)⟩) fun m hm => ⟨?_, hm.2.trans (hFG m hm.1)⟩
  linarith [hm.1]

/-- If `X ≤ Y` almost everywhere then `μ[Y ≤ s] ≤ μ[X ≤ s]`. -/
theorem measure_le_ofReal_le_of_ae_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {X Y : α → ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, X x ≤ Y x) (s : ℝ) :
    μ {x | Y x ≤ ENNReal.ofReal s} ≤ μ {x | X x ≤ ENNReal.ofReal s} :=
  measure_mono_ae <| h.mono fun x hx (hy : Y x ≤ ENNReal.ofReal s) =>
    (hx.trans hy : X x ≤ ENNReal.ofReal s)

/-- If `Y ≤ X + 1` almost everywhere then `μ[X ≤ s] ≤ μ[Y ≤ s + 1]` for `s ≥ 0`. -/
theorem measure_le_ofReal_le_add_one_of_ae_le_add_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {X Y : α → ℝ≥0∞} (h : ∀ᵐ x ∂μ, Y x ≤ X x + 1) {s : ℝ} (hs : 0 ≤ s) :
    μ {x | X x ≤ ENNReal.ofReal s} ≤ μ {x | Y x ≤ ENNReal.ofReal (s + 1)} := by
  have hs1 : ENNReal.ofReal (s + 1) = ENNReal.ofReal s + 1 := by
    rw [ENNReal.ofReal_add hs zero_le_one, ENNReal.ofReal_one]
  refine measure_mono_ae <| h.mono fun x hx (hX : X x ≤ ENNReal.ofReal s) => ?_
  show Y x ≤ ENNReal.ofReal (s + 1)
  calc Y x ≤ X x + 1 := hx
    _ ≤ ENNReal.ofReal s + 1 := by gcongr
    _ = ENNReal.ofReal (s + 1) := hs1.symm

/-- **(a) Lower medians under one measure.** If `X ≤ Y ≤ X + 1` almost everywhere, then the lower medians of the
distribution functions `s ↦ P[X ≤ s]` and `s ↦ P[Y ≤ s]` satisfy `med X ≤ med Y ≤ med X + 1`. No finiteness of
`P` and no measurability of `X`, `Y` is needed. -/
theorem medianOf_measure_le_and_le_add_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X Y : Ω → ℝ≥0∞} (h : ∀ᵐ ω ∂P, X ω ≤ Y ω ∧ Y ω ≤ X ω + 1) :
    medianOf (fun s => P {ω | X ω ≤ ENNReal.ofReal s}) ≤
        medianOf (fun s => P {ω | Y ω ≤ ENNReal.ofReal s}) ∧
      medianOf (fun s => P {ω | Y ω ≤ ENNReal.ofReal s}) ≤
        medianOf (fun s => P {ω | X ω ≤ ENNReal.ofReal s}) + 1 :=
  medianOf_le_and_le_add_one_of_cdf
    (fun s _ => measure_le_ofReal_le_of_ae_le P (h.mono fun _ hω => hω.1) s)
    (fun _ hs => measure_le_ofReal_le_add_one_of_ae_le_add_one P (h.mono fun _ hω => hω.2) hs)

/-- **(b) Lower medians under an annealed mixture.** Let `K ω` be a measure on paths (for instance the law of the
random walk on `𝒢^ε` given the environment `ω`, on paths `ℕ → ℤ`) and let `X ω`, `Y ω` be two `[0, ∞]`-valued
functionals of the path (for instance the exit time of the linearly interpolated embedded walk and
`embeddedExitTime`, cast to `ℝ≥0∞`). If for `P`-a.e. `ω`, `X ω ≤ Y ω ≤ X ω + 1` holds `K ω`-a.e., then the lower
medians of the annealed distribution functions `s ↦ ∫⁻ ω, K ω {x | T ω x ≤ s} ∂P` (the form of
`MatedCRTEnv.mε`) satisfy `med X ≤ med Y ≤ med X + 1`. -/
theorem medianOf_lintegral_le_and_le_add_one {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (K : Ω → Measure α) {X Y : Ω → α → ℝ≥0∞}
    (h : ∀ᵐ ω ∂P, ∀ᵐ x ∂K ω, X ω x ≤ Y ω x ∧ Y ω x ≤ X ω x + 1) :
    medianOf (fun s => ∫⁻ ω, K ω {x | X ω x ≤ ENNReal.ofReal s} ∂P) ≤
        medianOf (fun s => ∫⁻ ω, K ω {x | Y ω x ≤ ENNReal.ofReal s} ∂P) ∧
      medianOf (fun s => ∫⁻ ω, K ω {x | Y ω x ≤ ENNReal.ofReal s} ∂P) ≤
        medianOf (fun s => ∫⁻ ω, K ω {x | X ω x ≤ ENNReal.ofReal s} ∂P) + 1 :=
  medianOf_le_and_le_add_one_of_cdf
    (fun s _ => lintegral_mono_ae <| h.mono fun ω hω =>
      measure_le_ofReal_le_of_ae_le (K ω) (hω.mono fun _ hx => hx.1) s)
    (fun _ hs => lintegral_mono_ae <| h.mono fun ω hω =>
      measure_le_ofReal_le_add_one_of_ae_le_add_one (K ω) (hω.mono fun _ hx => hx.2) hs)

end MatedCRT
