import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauScaling

/-! # Scaling inputs and deterministic scaling for `PlateauScaleInvarianceStep` (Proposition 4.2)

The scaling of draft
lines 245-256 and the probability identity of draft line 265.

With `c = e^{γ c_a}` as in the paper:
* `scaledMeasure μ a c = c⁻¹ · μ(a ·)` is the LQG measure `μ_{h_a}` of the scaled field (draft line 252);
* `scaledFamily Λ a c t = a⁻¹ Λ(c t)` is the scaled family `Λ^{h_a}_t` (draft line 254).

The file states the two inputs `InsertionLQGScalingLawStep` (K) and `ScaledRegularizedFamilyStep` (H), each in full with its
source, and proves from the definitions and `PlateauScaling.lean`: the time change and radius identity
`R_{Λ_a}(t) = a⁻¹ R_Λ(c t)`; the determinacy of a centre-0 regularized family by its measure; and the coordinate identity
`μ'' = scaledMeasure μ a c`. The conditional closure `PlateauScaleInvarianceStep` is `plateauScaleInvarianceStep_of_canonical`
in `PlateauCanonicalLaw.lean`. It uses the canonical measurable plateau event, so no measurability of the plateau predicate on
all measures is assumed.

`HarmonicBalls.UniquenessHarmonicBallsStmt` (HB Proposition 5.6) is not carried. The family in
`PlateauScaleInvarianceStep` is already a regularized cluster family at `0`, and the third conjunct of
`IsRegularizedClusterFamily` (`HarmonicBalls/Draft/Section5.lean:88`) determines such a family by its measure
(`eqOn_of_isRegularizedClusterFamily_zero`). The identification that the paper obtains from uniqueness is therefore not
needed for this statement. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls ProbabilityTheory
open scoped Pointwise ENNReal

/-- The scaled measure `μ_a = c⁻¹ · μ(a ·)`: the LQG measure `μ_{h_a}` of the scaled field, `μ_{h_a}(E) = e^{-γ c_a} μ_h(aE)`
(draft line 252). Since `(μ.map (· / a)) E = μ (a • E)`, this is `c⁻¹` times the image of `μ` under `x ↦ x / a`. -/
noncomputable def scaledMeasure (μ : Measure ℂ) (a c : ℝ) : Measure ℂ :=
  (ENNReal.ofReal c)⁻¹ • μ.map (fun x : ℂ => x / (a : ℂ))

/-- The scaled family `Λ_a(t) = a⁻¹ Λ(c t)`: `Λ^{h_a}_t = a⁻¹ Λ^h_{e^{γ c_a} t}` (draft line 254). -/
def scaledFamily (Λ : ℝ → Set ℂ) (a c : ℝ) : ℝ → Set ℂ :=
  fun t => (fun x : ℂ => ((a⁻¹ : ℝ) : ℂ) * x) '' Λ (c * t)

/-! ## Deterministic consequences (proved) -/

/-- **Time change and dilation.** The radius of the scaled family is `a⁻¹` times the radius at time `c t`. -/
theorem familyRadius_scaledFamily {Λ : ℝ → Set ℂ} {a : ℝ} (ha : 0 < a) (c t : ℝ) :
    familyRadius (scaledFamily Λ a c t) = a⁻¹ * familyRadius (Λ (c * t)) :=
  familyRadius_image_mul_of_pos (inv_pos.mpr ha) _

/-- **Plateau values of the scaled family** (`P(Λ_a) = a⁻¹ P(Λ)`, draft line 256), in the form
`r ∈ P(Λ_a) ↔ a r ∈ P(Λ)`, pathwise for a regularized family `Λ` (its radius is increasing). -/
theorem mem_plateauValues_scaledFamily_iff {Λ : ℝ → Set ℂ} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hmono : MonotoneOn (fun t => familyRadius (Λ t)) (Set.Ioi 0)) (r : ℝ) :
    r ∈ plateauValues (scaledFamily Λ a c) ↔ a * r ∈ plateauValues Λ :=
  mem_plateauValues_iff_mul_of_radius ha hc hmono (fun t _ => familyRadius_scaledFamily ha c t) r

/-- **Determinacy of the centre-0 regularized family.** Two regularized cluster families at `0` for the same measure
agree on `(0, ∞)`: each value is `regularizedCluster μ r 0 t` for every large `r`, by the third conjunct of
`IsRegularizedClusterFamily` (`HarmonicBalls/Draft/Section5.lean:88`), and each value is bounded (first conjunct). -/
theorem eqOn_of_isRegularizedClusterFamily_zero {μ : Measure ℂ} {Λ₁ Λ₂ : ℝ → Set ℂ}
    (h₁ : IsRegularizedClusterFamily μ Λ₁ 0) (h₂ : IsRegularizedClusterFamily μ Λ₂ 0) :
    EqOn Λ₁ Λ₂ (Ioi 0) := by
  have hball : ∀ Λ : ℝ → Set ℂ, IsRegularizedClusterFamily μ Λ 0 → ∀ t : ℝ, 0 < t →
      ∃ s : ℝ, 0 < s ∧ closure (Λ t) ⊆ ball 0 s := by
    intro Λ h t ht
    obtain ⟨R, hR⟩ := (h.1.isBounded t ht).subset_closedBall 0
    exact ⟨|R| + 1, by positivity,
      (closure_minimal hR Metric.isClosed_closedBall).trans
        (Metric.closedBall_subset_ball (by linarith [le_abs_self R]))⟩
  intro t ht
  obtain ⟨s₁, hs₁, hc₁⟩ := hball Λ₁ h₁ t ht
  obtain ⟨s₂, hs₂, hc₂⟩ := hball Λ₂ h₂ t ht
  have e₁ := h₁.2.2 t ht s₁ hs₁ hc₁ (max s₁ s₂) (le_max_left _ _)
  have e₂ := h₂.2.2 t ht s₂ hs₂ hc₂ (max s₁ s₂) (le_max_right _ _)
  exact e₁.trans e₂.symm

/-- Plateau values depend only on the family on `(0, ∞)`: one inclusion. -/
theorem plateauValues_subset_of_eqOn {Λ Λ' : ℝ → Set ℂ} (h : EqOn Λ Λ' (Ioi 0)) :
    plateauValues Λ ⊆ plateauValues Λ' := by
  rintro r ⟨hr, s, t, hs, hst, h1, h2⟩
  have ht : (0 : ℝ) < t := lt_trans hs hst
  exact ⟨hr, s, t, hs, hst, by rwa [← h hs], by rwa [← h ht]⟩

/-- Plateau values depend only on the family on `(0, ∞)`. -/
theorem plateauValues_congr {Λ Λ' : ℝ → Set ℂ} (h : EqOn Λ Λ' (Ioi 0)) :
    plateauValues Λ = plateauValues Λ' :=
  Set.Subset.antisymm (plateauValues_subset_of_eqOn h) (plateauValues_subset_of_eqOn h.symm)

/-- The coordinate identity determines the scaled measure: if `μ.map (· / a) = c • ν` with `c > 0`, then
`scaledMeasure μ a c = ν`. This is the coordinate rule of draft line 252 read as an identity of measures. -/
theorem scaledMeasure_eq_of_map {μ ν : Measure ℂ} {a c : ℝ} (hc : 0 < c)
    (h : μ.map (fun x : ℂ => x / (a : ℂ)) = ENNReal.ofReal c • ν) : scaledMeasure μ a c = ν := by
  unfold scaledMeasure
  rw [h, smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top, one_smul]

/-! ## The named inputs

Each input is a `Prop` in full, with its source. They are hypotheses of the conditional theorem of
`PlateauCanonicalLaw.lean`, never axioms. -/

/-- **Input K: the insertion-`α` LQG coordinate change, non-dyadic, in law.** Let `h = h^ℂ - α log|·|` be the field of a
whole-plane GFF with insertion `α` (`IsWholePlaneGFF`, `IsLQGMeasureOfField`), and `a > 0`. There is a scaled whole-plane
field `h''` (the affine transform `h^ℂ(a ·) - h^ℂ_a(0)` of draft line 245) whose insertion-`α` LQG measure `μ''` satisfies
`μ.map (· / a) = c • μ''` for a random constant `c > 0` (draft line 252, `μ_{h_a}(E) = e^{-γ c_a} μ_h(aE)`), and
`μ'' =_d μ` (draft line 245, `h_a =_d h^α`).
Sources: draft lines 245-256; DS11 Prop 2.1 (LQG coordinate change, all real scales); the dyadic gap. Not `WholePlaneLQGCoordinateChangeStep` (`MatedCRT/Steps/Sec6/AnnulusHit.lean:65`), which is the
`α = 0`, dyadic version. -/
def InsertionLQGScalingLawStep : Prop :=
  ∀ γ α : ℝ, 0 < γ → γ < 2 → α < lqgQ γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α hcirc μ →
  ∀ a : ℝ, 0 < a → ∃ (hC'' : Ω → (ℂ → ℝ) → ℝ) (hcirc'' : Ω → ℝ → ℂ → ℝ)
    (μ'' : Ω → Measure ℂ) (c : Ω → ℝ),
    IsWholePlaneGFF P hC'' hcirc'' ∧ IsLQGMeasureOfField P γ α hcirc'' μ'' ∧
    (∀ᵐ ω ∂P, 0 < c ω ∧ (μ ω).map (fun x : ℂ => x / (a : ℂ)) = ENNReal.ofReal (c ω) • μ'' ω) ∧
    IdentDistrib μ'' μ P P

/-- **Input H: the dilated regularized family (deterministic scaling).** For every measure `μ` and `a, c > 0`, if `Λ` is a
regularized cluster family at `0` for `μ`, then `t ↦ a⁻¹ Λ(c t)` is one for `μ_a = c⁻¹ μ(a ·)` at `0`.
The scaling of the mean-value property, mass parameter and family conditions; the
identity of the regularized clusters under the dilation, `cluster μ_a 1 0 t = a⁻¹ • cluster μ a 0 (c t)`, which is the
pathwise content of [HB] Lemma 5.7 (`ClusterScaleInvarianceStmt`, `HarmonicBalls/Draft/Section5.lean:226`; proof at
Harmonic-Balls-LQG corrected TeX lines 905-938), and the scaling of `IsSubharmonicBall`. The clauses (a)-(b) of
`SatisfiesHarmonicBallConditions` (`Section1.lean:58`) are routine, because `μ_a (a⁻¹ • S) = c⁻¹ μ S`. -/
def ScaledRegularizedFamilyStep : Prop :=
  ∀ (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (a c : ℝ), 0 < a → 0 < c →
    IsRegularizedClusterFamily μ Λ 0 → IsRegularizedClusterFamily (scaledMeasure μ a c) (scaledFamily Λ a c) 0

end MatedCRT
