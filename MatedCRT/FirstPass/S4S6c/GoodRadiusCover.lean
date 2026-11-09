import MatedCRT.Draft.Section6
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Threshold

/-!
# Lemma 2, eq (9): good radii on dyadic scales with a field-measurable cutoff (q2, task fp-S4S6c; LEMMA68)

Written argument: notes/fp-gaps/LEMMA68.md, Lemma 2 item 2 (eq (9)), with the cover events of
`GoodAnnulusPrevalenceStmt` (Draft/Section6.lean:60). The polynomial failure bound of that statement, the dyadic
Borel-Cantelli step, and a field-measurable cutoff `δ_*` give: for every dyadic `δ < δ_*` and every grid centre
`z` of `B_{ρ-3√δ} \ B_{10√δ}`, a good radius `r ∈ [δ, √δ] ∩ {7^{-n}}` with `IsGoodAnnulusEvent`.

* `BallMassLower`-style threshold: `exists_dyadic_threshold` (generic, reuses `ConstantOrderDiv.exists_measurable_threshold`).
* `GoodAnnulusCoverEvent`: the event of `GoodAnnulusPrevalenceStmt` at scale `δ`, copied verbatim.
* `goodAnnulusCover_dyadic`: eq (9) from a polynomial bound and the field-measurability of the cover events.
  The measurability of the cover events is NOT yet proved (LEMMA68.md 620-636 gap; see the report).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRT

namespace GoodRadiusCover

/-- Borel-Cantelli on dyadic scales with a field-measurable cutoff: if the events `E((1/2)^n)` are `m'`-measurable and their
complements have polynomially small probability, then almost surely `ω ∈ E((1/2)^n)` for all dyadic `(1/2)^n < tStar ω`. -/
theorem exists_dyadic_threshold {Ω : Type*} {m' : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (E : ℝ → Set Ω)
    (hEm : ∀ n : ℕ, MeasurableSet[m'] (E ((1 / 2 : ℝ) ^ n)))
    (hE : HarmonicBalls.PolyHighProb P E) :
    ∃ tStar : Ω → ℝ, Measurable[m'] tStar ∧ ∀ᵐ ω ∂P, 0 < tStar ω ∧
      ∀ n : ℕ, (1 / 2 : ℝ) ^ n < tStar ω → ω ∈ E ((1 / 2 : ℝ) ^ n) := by
  obtain ⟨N, hNm, hN⟩ := ConstantOrderDiv.exists_measurable_threshold P
    (F := fun n : ℕ => E ((1 / 2 : ℝ) ^ n)) hEm (ConstantOrderDiv.tsum_dyadic_ne_top hE)
  refine ⟨fun ω => (1 / 2 : ℝ) ^ N ω,
    (measurable_from_nat (f := fun n : ℕ => (1 / 2 : ℝ) ^ n)).comp hNm, ?_⟩
  filter_upwards [hN] with ω hω
  refine ⟨by positivity, fun n hn => hω n ?_⟩
  by_contra h
  have hlt : n < N ω := not_le.1 h
  have hle : (1 / 2 : ℝ) ^ N ω ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt.le
  linarith

/-- The good-annulus cover event at scale `δ` with constant `C` (the event of `GoodAnnulusPrevalenceStmt`,
Draft/Section6.lean:64-66, copied verbatim). -/
def GoodAnnulusCoverEvent {Ω : Type*} (μ : Ω → Measure ℂ) (ρ c₀ C δ : ℝ) : Set Ω :=
  {ω | ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) (ρ - 3 * Real.sqrt δ) \ Metric.ball (0 : ℂ) (10 * Real.sqrt δ) →
    (∃ m n : ℤ, z = ((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)) →
    ∃ r : ℝ, δ ≤ r ∧ r ≤ Real.sqrt δ ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulusEvent (μ ω) c₀ C r z}

/-- **Lemma 2, eq (9)** (LEMMA68 Lemma 2 item 2). Given the polynomial bound of the cover events with constant `C`
(from `GoodAnnulusPrevalenceStmt`) and their field-measurability (OPEN, see the report), for almost every `ω` there is a
field-measurable cutoff `tStar ω > 0` such that for every dyadic `δ = (1/2)^n < tStar ω` every grid centre has a good radius. -/
theorem goodAnnulusCover_dyadic {Ω : Type*} {m' : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (μ : Ω → Measure ℂ) {ρ c₀ C : ℝ}
    (hpoly : HarmonicBalls.PolyHighProb P (fun δ => GoodAnnulusCoverEvent μ ρ c₀ C δ))
    (hmeas : ∀ n : ℕ, MeasurableSet[m'] (GoodAnnulusCoverEvent μ ρ c₀ C ((1 / 2 : ℝ) ^ n))) :
    ∃ tStar : Ω → ℝ, Measurable[m'] tStar ∧ ∀ᵐ ω ∂P, 0 < tStar ω ∧
      ∀ n : ℕ, (1 / 2 : ℝ) ^ n < tStar ω → ∀ z : ℂ,
        z ∈ Metric.ball (0 : ℂ) (ρ - 3 * Real.sqrt ((1 / 2 : ℝ) ^ n)) \
          Metric.ball (0 : ℂ) (10 * Real.sqrt ((1 / 2 : ℝ) ^ n)) →
        (∃ m k : ℤ, z = ((((1 / 2 : ℝ) ^ n) / 100 : ℝ) : ℂ) * (m + k * Complex.I)) →
        ∃ r : ℝ, (1 / 2 : ℝ) ^ n ≤ r ∧ r ≤ Real.sqrt ((1 / 2 : ℝ) ^ n) ∧ (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulusEvent (μ ω) c₀ C r z := by
  obtain ⟨tStar, htm, htS⟩ := exists_dyadic_threshold (fun δ => GoodAnnulusCoverEvent μ ρ c₀ C δ) hmeas hpoly
  refine ⟨tStar, htm, ?_⟩
  filter_upwards [htS] with ω hω
  exact ⟨hω.1, fun n hn z hz hzl => hω.2 n hn z hz hzl⟩


/-- The polynomial bound of the cover events, read off from `GoodAnnulusPrevalenceStmt` (Draft/Section6.lean:60):
for the constant `C` of that statement, every cone field gives `PolyHighProb` of the cover events. -/
theorem cover_polyHighProb_of_prevalence (hprev : GoodAnnulusPrevalenceStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      HarmonicBalls.PolyHighProb P (fun δ => GoodAnnulusCoverEvent μ ρ c₀ C δ) := by
  obtain ⟨C, hC0, h⟩ := hprev γ hγ hγ2 ρ hρ hρ1 c₀ hc₀ hc₀'
  exact ⟨C, hC0, h⟩

end GoodRadiusCover

end MatedCRT

#print axioms MatedCRT.GoodRadiusCover.goodAnnulusCover_dyadic
#print axioms MatedCRT.GoodRadiusCover.cover_polyHighProb_of_prevalence
