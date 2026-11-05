import MatedCRT.Draft.Section2
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.GMCInterfaces

/-!
# Lemma 2.7 in two halves: the lower and the upper volume bound

Lemma 2.7 (lemma:volume-growth, line 658; BG20 Lemma A.1) is the conjunction of two estimates with polynomially high
probability as `δ → 0`, for `z ∈ B_{1-δ}`:
* the **lower half** `δ^{β⁻} ≤ μ_h(B_δ(z))` for `β⁻ > (2+γ)²/2` (`VolumeGrowthLowerStmt`);
* the **upper half** `μ_h(B_δ(z)) ≤ δ^{β⁺}` for `β⁺ ∈ (0, (2-γ)²/2)` (`VolumeGrowthUpperStmt`).
`volumeGrowthStmt_iff_halves` proves `VolumeGrowthStmt ↔ VolumeGrowthLowerStmt ∧ VolumeGrowthUpperStmt`.

The lower half is derived (`MatedCRT/Proofs/Sec2/VolumeGrowthHalf/Main.lean`) from Leonardo Bonanno's formalization of
GMS19 Lemma 2.8 (`MatedCRTHarmonic.GMSLemma27.lemma28_wholePlane_strict`, adapted from Leonardo Bonanno's
lean-formalizations, https://github.com/leobon12/lean-formalizations, as ported to Lattice-Probability), his proof of
the GMC lower tail (`MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds`, GHM15 Lemma 3.12) and the comparison of the
quantum cone with the whole-plane GFF on the unit disk (`ConeAreaDominatesWholePlaneGFFStep`, below). The upper half
(the sharp exponent `(2-γ)²/2`) is not in Bonanno's code (it has only a non-sharp upper bound) and stays the cited
input.

Also: two elementary facts on events with polynomially high probability (monotonicity, intersection).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- An event containing an event with polynomially high probability has polynomially high probability. -/
theorem polyHighProb_mono_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (hE : PolyHighProb P E) (hEF : ∀ r, E r ⊆ F r) : PolyHighProb P F := by
  obtain ⟨p, hp, C, r₀, hr₀, h⟩ := hE
  exact ⟨p, hp, C, r₀, hr₀, fun r hr hrlt =>
    (measure_mono (compl_subset_compl.mpr (hEF r))).trans (h r hr hrlt)⟩

/-- An event containing the intersection of two events with polynomially high probability has polynomially high
probability (exponent `min p₁ p₂`, constant `max C₁ 0 + max C₂ 0`, for `r < 1`). -/
theorem polyHighProb_of_inter {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F G : ℝ → Set Ω}
    (hE : PolyHighProb P E) (hF : PolyHighProb P F) (hG : ∀ r, E r ∩ F r ⊆ G r) : PolyHighProb P G := by
  obtain ⟨p₁, hp₁, C₁, r₁, hr₁, h₁⟩ := hE
  obtain ⟨p₂, hp₂, C₂, r₂, hr₂, h₂⟩ := hF
  refine ⟨min p₁ p₂, lt_min hp₁ hp₂, max C₁ 0 + max C₂ 0, min (min r₁ r₂) 1,
    lt_min (lt_min hr₁ hr₂) one_pos, fun r hr hrlt => ?_⟩
  have hr1 : r < 1 := hrlt.trans_le (min_le_right _ _)
  have hrr₁ : r < r₁ := (hrlt.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
  have hrr₂ : r < r₂ := (hrlt.trans_le (min_le_left _ _)).trans_le (min_le_right _ _)
  have key : ∀ C q : ℝ, min p₁ p₂ ≤ q →
      ENNReal.ofReal (C * r ^ q) ≤ ENNReal.ofReal (max C 0 * r ^ min p₁ p₂) := fun C q hq =>
    ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr hr1.le hq) (le_max_right _ _)))
  calc P (G r)ᶜ ≤ P ((E r)ᶜ ∪ (F r)ᶜ) := by
        rw [← compl_inter]
        exact measure_mono (compl_subset_compl.mpr (hG r))
    _ ≤ P (E r)ᶜ + P (F r)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (max C₁ 0 * r ^ min p₁ p₂) + ENNReal.ofReal (max C₂ 0 * r ^ min p₁ p₂) :=
        add_le_add ((h₁ r hr hrr₁).trans (key C₁ p₁ (min_le_left _ _)))
          ((h₂ r hr hrr₂).trans (key C₂ p₂ (min_le_right _ _)))
    _ = ENNReal.ofReal ((max C₁ 0 + max C₂ 0) * r ^ min p₁ p₂) := by
        rw [add_mul, ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hr.le _))
          (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hr.le _))]

/-- **Lemma 2.7, lower half** (lemma:volume-growth, line 658; BG20 Lemma A.1, lower bound). For each
`β⁻ > (2+γ)²/2`, with polynomially high probability as `δ → 0`, `δ^{β⁻} ≤ μ_h(B_δ(z))` for all `z ∈ B_{1-δ}`. -/
def VolumeGrowthLowerStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ βm : ℝ, (2 + γ) ^ 2 / 2 < βm →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  PolyHighProb P fun δ => {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ βm) ≤ μ ω (ball z δ)}

/-- **Lemma 2.7, upper half** (lemma:volume-growth, line 658; BG20 Lemma A.1, upper bound). For each
`β⁺ ∈ (0, (2-γ)²/2)`, with polynomially high probability as `δ → 0`, `μ_h(B_δ(z)) ≤ δ^{β⁺}` for all `z ∈ B_{1-δ}`.
Cited (BG20 Lemma A.1); not in Bonanno's formalization. -/
def VolumeGrowthUpperStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ βp : ℝ, 0 < βp → βp < (2 - γ) ^ 2 / 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  PolyHighProb P fun δ => {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ), μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ βp)}

/-- **Lemma 2.7 is the conjunction of its two halves.** -/
theorem volumeGrowthStmt_iff_halves :
    VolumeGrowthStmt ↔ VolumeGrowthLowerStmt ∧ VolumeGrowthUpperStmt := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro γ hγ hγ2 βm hβm Ω _ P hC hcirc μ hcone
      have h2 : 0 < (2 - γ) ^ 2 := pow_pos (by linarith) 2
      exact polyHighProb_mono_of_subset
        (h γ hγ hγ2 ((2 - γ) ^ 2 / 4) βm (by linarith) (by linarith) hβm Ω P hC hcirc μ hcone)
        fun δ ω hω z hz => (hω z hz).1
    · intro γ hγ hγ2 βp hβp hβp' Ω _ P hC hcirc μ hcone
      exact polyHighProb_mono_of_subset
        (h γ hγ hγ2 βp ((2 + γ) ^ 2 / 2 + 1) hβp hβp' (by linarith) Ω P hC hcirc μ hcone)
        fun δ ω hω z hz => (hω z hz).2
  · rintro ⟨hl, hu⟩ γ hγ hγ2 βp βm hβp hβp' hβm Ω _ P hC hcirc μ hcone
    exact polyHighProb_of_inter (hl γ hγ hγ2 βm hβm Ω P hC hcirc μ hcone)
      (hu γ hγ hγ2 βp hβp hβp' Ω P hC hcirc μ hcone) fun δ ω hω z hz => ⟨hω.1 z hz, hω.2 z hz⟩

/-- **Step (the quantum cone dominates the whole-plane GFF on the unit disk).** The `γ`-LQG measure `μ_h` of the
circle average embedding of the `γ`-quantum cone dominates, on Borel subsets of `B_1`, the `γ`-LQG measure `μ̃` of a
whole-plane GFF `h̃` normalized by `h̃_1(0) = 0` realized on the same sample space: there are the circle average process
`H ε z ω = h̃_ε(z)` (Bonanno's `LQGDimension.IsGFFCircleAverage`) and its LQG measure `μ̃` (Bonanno's
`MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf`) with a.s. `μ̃(A) ≤ μ_h(A)` for all Borel `A ⊆ B_1`.

This is Bonanno's interface `MatedCRTHarmonic.GMSLemma27.AreaDominatesWholePlaneGFF` (the reduction in the proof of
GMS19 Lemma 2.8, "If `h` is a circle-average embedding of an `α`-quantum cone, then `h|_𝔻` agrees in law with a
whole-plane GFF normalized so that its circle average over `∂𝔻` is 0 plus `−α log|·|`. If `h` is a whole-plane GFF,
then `μ_{h−α log|·|}(A) ≥ μ_h(A)` for each Borel set `A ⊂ 𝔻`"), stated for our `IsConeField`. Bonanno proves it for
his constructive cone (`GMCFacts.areaDominates_of_cone`, not ported); for ours it is a provable step:
* coupling (Definition 2.1, eq:gff line 444, DMS14 Definition 4.10): the radial part of `h` outside `B_1` is
  independent of `h|_{B_1}` and non-atomic, so it generates an independent Brownian motion, and replacing the radial
  part of `h` outside `B_1` by it gives on the same sample space a whole-plane GFF `h̃` with
  `h|_{B_1} = (h̃ - γ log |·|)|_{B_1}` (circle averages `h_r(z) = h̃_r(z) - γ log max(r, |z|)` when `r + |z| ≤ 1`);
* existence of the LQG measure of `h̃` (DS11 Proposition 1.1);
* deterministic: `h_r(z) ≥ h̃_r(z)` for `r + |z| ≤ 1`, so the circle average approximations, and their vague limits,
  compare on `B_1` (outer regularity). -/
def ConeAreaDominatesWholePlaneGFFStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∃ (H : ℝ → ℂ → Ω → ℝ) (μ' : Ω → Measure ℂ), LQGDimension.IsGFFCircleAverage H P ∧
    MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ' P ∧
    ∀ᵐ ω ∂P, ∀ A : Set ℂ, MeasurableSet A → A ⊆ ball (0 : ℂ) 1 → μ' ω A ≤ μ ω A

end MatedCRT
