/- Adds the local-maximum variants to the Brownian local-extrema results of the shared library. -/
import MatedCRT.Proofs.MatingOfTrees.BMLocalMinProb
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Probability.BMLocalMin.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory NNReal Set

namespace MatedCRTHarmonic.MoTPort
namespace BMLocalMin

/-- Every local maximum of `f` on `I` is strict, distinct local maxima have distinct values, and the
set of local-maximum times is countable. -/
def LocMaxGood (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  (∀ t ∈ I, IsLocalMaxOn f I t → ∃ ε > 0, ∀ u ∈ I, u ≠ t → |u - t| < ε → f u < f t) ∧
  (∀ t₁ ∈ I, ∀ t₂ ∈ I, IsLocalMaxOn f I t₁ → IsLocalMaxOn f I t₂ → t₁ ≠ t₂ → f t₁ ≠ f t₂) ∧
  {t ∈ I | IsLocalMaxOn f I t}.Countable

lemma locMaxGood_of_neg {f : ℝ → ℝ} {I : Set ℝ} (h : LocMinGood (fun t => -f t) I) :
    LocMaxGood f I := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun t ht hl => ?_, fun t₁ h₁ t₂ h₂ hl₁ hl₂ hne heq => ?_, ?_⟩
  · obtain ⟨ε, hε, hs⟩ := h1 t ht hl.neg
    exact ⟨ε, hε, fun u hu hne hd => neg_lt_neg_iff.1 (hs u hu hne hd)⟩
  · exact h2 t₁ h₁ t₂ h₂ hl₁.neg hl₂.neg hne (by show -f t₁ = -f t₂; rw [heq])
  · refine h3.mono ?_
    rintro t ⟨ht, hl⟩
    exact ⟨ht, hl.neg⟩

/-- The family of intervals used on `[0, T]`: rational endpoints and `T`. -/
lemma countable_ratT (T : ℝ) : (insert T (range ((↑) : ℚ → ℝ))).Countable :=
  (countable_range _).insert T

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- **MP Thm 2.11 (a), (b)** for local minima of Brownian motion on `[0, T]`. -/
theorem ae_locMinGood_Icc (hB : IsBrownianReal B P) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, LocMinGood (path B ω) (Icc 0 T) := by
  filter_upwards [hB.cont, ae_sep hB (countable_ratT T)] with ω hc hS
  exact localMin_props (continuous_path hc) hS (countable_ratT T)
    (fine_Icc (fun u => mem_insert_of_mem _ (mem_range_self u)) hT (mem_insert T _))
    Icc_subset_Ici_self

/-- **MP Thm 2.11 (a), (b)** for local maxima of Brownian motion on `[0, T]`. -/
theorem ae_locMaxGood_Icc (hB : IsBrownianReal B P) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, LocMaxGood (path B ω) (Icc 0 T) := by
  filter_upwards [ae_locMinGood_Icc hB.neg hT] with ω h
  exact locMaxGood_of_neg h

/-- **MP Thm 2.11 (a), (b)** for local maxima of Brownian motion on `[0, ∞)`. -/
theorem ae_locMaxGood_Ici (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, LocMaxGood (path B ω) (Ici 0) := by
  filter_upwards [ae_locMinGood_Ici hB.neg] with ω h
  exact locMaxGood_of_neg h

/-- **MP Thm 2.11 (c)** for the maximum. -/
theorem ae_isMaxOn_unique (hB : IsBrownianReal B P) {a b : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ ω ∂P, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IsMaxOn (path B ω) (Icc a b) x →
      IsMaxOn (path B ω) (Icc a b) y → x = y := by
  filter_upwards [ae_isMinOn_unique hB.neg ha] with ω h x hx y hy hmx hmy
  exact h x hx y hy hmx.neg hmy.neg

end BMLocalMin
end MatedCRTHarmonic.MoTPort
