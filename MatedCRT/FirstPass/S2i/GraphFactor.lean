import MatedCRT.FirstPass.S2i.BorelFactor
import HarmonicBalls.Proofs.Sec5.AnalyticSetNullMeasurable

/-! # Borel factor of a full-measure graph of codes (FirstPass S2i, z2)

Lusin-Souslin type factorization for a measurable map `J` from a standard Borel probability space into the code space
`(ℕ → ℝ) × (ℝ × (ℕ → ℕ → Bool))`, whose values on a measurable full set `E0` form a graph over the first coordinate
(two samples in `E0` with the same circle code have the same second coordinate). The image `J '' E0` is analytic, hence
null-measurable for the law of `J` (Mathlib `MeasurableSet.analyticSet_image`; Harmonic-Balls-LQG
`HarmonicBalls.AnalyticSet.nullMeasurableSet_of_finite`, the capacitability argument), so it contains a Borel set of
full law, which is a Borel graph and is factored by `exists_measurable_graph_factor`
(Kechris, Classical Descriptive Set Theory, Thms 15.1, 14.12; Lusin-Souslin). -/

namespace MatedCRT

open MeasureTheory Set

/-- **Borel factor of the joint code.** Let `J` be measurable on a standard Borel probability space, `E0` a measurable
set of full measure on which the first coordinate determines the second. Then there are a Borel set `B` of first
coordinates and a Borel map `F` such that every `x ∈ B` is the first coordinate of some `ω ∈ E0` with
`J ω = (x, F x)`, and `J ω` has first coordinate in `B` almost surely. -/
theorem exists_canonical_factor {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (J : Ω → (ℕ → ℝ) × (ℝ × (ℕ → ℕ → Bool))) (hJ : Measurable J)
    (E0 : Set Ω) (hE0 : MeasurableSet E0) (hfull : P E0ᶜ = 0)
    (hgraph : ∀ ω ∈ E0, ∀ ω' ∈ E0, (J ω).1 = (J ω').1 → J ω = J ω') :
    ∃ (B : Set (ℕ → ℝ)) (F : (ℕ → ℝ) → ℝ × (ℕ → ℕ → Bool)), MeasurableSet B ∧ Measurable F ∧
      (∀ x ∈ B, ∃ ω ∈ E0, J ω = (x, F x)) ∧ ∀ᵐ ω ∂P, (J ω).1 ∈ B := by
  have hA := MeasurableSet.analyticSet_image hE0 hJ
  have hnull : NullMeasurableSet (J '' E0) (P.map J) :=
    HarmonicBalls.AnalyticSet.nullMeasurableSet_of_finite (P.map J) hA
  have hS0c : (P.map J) (J '' E0)ᶜ = 0 := by
    rw [Measure.map_apply₀ hJ.aemeasurable hnull.compl]
    refine measure_mono_null ?_ hfull
    intro ω hω hE
    exact hω ⟨ω, hE, rfl⟩
  obtain ⟨S, hSS0, hSm, hSae⟩ := hnull.exists_measurable_subset_ae_eq
  have hSc : (P.map J) Sᶜ = 0 := by
    rw [measure_congr hSae.compl]
    exact hS0c
  have hgr : IsGraphSet S := by
    intro x y y' h h'
    obtain ⟨ω, hω, hJω⟩ := hSS0 h
    obtain ⟨ω', hω', hJω'⟩ := hSS0 h'
    have hfst : (J ω).1 = (J ω').1 := by rw [hJω, hJω']
    have e := hgraph ω hω ω' hω' hfst
    rw [hJω, hJω'] at e
    exact (Prod.mk.inj e).2
  obtain ⟨B, F, hB, hF, hBS, hBy⟩ := exists_measurable_graph_factor hSm hgr
  refine ⟨B, F, hB, hF, ?_, ?_⟩
  · intro x hx
    obtain ⟨ω, hω, hJω⟩ := hSS0 (hBS x hx)
    exact ⟨ω, hω, hJω⟩
  · have h0 : P (J ⁻¹' Sᶜ) = 0 := by
      rw [← Measure.map_apply hJ hSm.compl]
      exact hSc
    have hae : ∀ᵐ ω ∂P, J ω ∈ S := by
      rw [ae_iff]
      exact h0
    filter_upwards [hae] with ω hω
    exact (hBy _ _ hω).1

end MatedCRT
