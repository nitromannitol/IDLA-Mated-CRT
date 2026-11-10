import MatedCRT.FirstPass.Frozen.S3c
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitMonotone

/-!
# Exit-time bridge: `ExitTimeUpperBoundStmt` from BG20 Proposition 5.1 (task fp-S3c-3-1-fidelity-fix, route A; z12)

Audit `notes/fp-gaps/CHATGPT-idla-3-1-audit.md` §2.3. The mass-restricted first moment `BG20Prop51` (frozen,
`MatedCRT/FirstPass/Frozen/S3c.lean`) gives the first clause of `ExitTimeUpperBoundStmt` for `D` with `μ_h(D) ≥ ε^α`.
The second clause, for arbitrary `D ⊆ B_ρ`, is obtained by enlarging `D` to `D' = B_{ε^{2α}}(D)`, whose mass is at least
`ε^{α₀}` by the volume growth (Lemma 2.7), and using the monotonicity of the killed vertex sets: a cell that meets `D`
and avoids `∂D` is connected, hence lies in `int D ⊆ int D'`.

This file: the topological and probabilistic helpers.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace S3cBridge

/-- A cell `η([a - ε, a])` of a continuous curve is connected. -/
theorem cell_isPreconnected' {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    IsPreconnected (cell ε η k) :=
  isPreconnected_Icc.image η hη.continuousOn

/-- A connected set which meets `D` and avoids `∂D` lies in `int D`. -/
theorem subset_interior_of_not_frontier {c D : Set ℂ} (hc : IsPreconnected c) {x₀ : ℂ} (hx₀c : x₀ ∈ c)
    (hx₀D : x₀ ∈ D) (hcf : ∀ x ∈ c, x ∉ frontier D) : c ⊆ interior D := by
  have hcover : c ⊆ interior D ∪ interior Dᶜ := by
    intro x hx
    by_cases hxD : x ∈ closure D
    · left
      by_contra h
      exact hcf x hx ⟨hxD, h⟩
    · right
      rw [interior_compl]
      exact hxD
  have hdisj : Disjoint (interior D) (interior Dᶜ) :=
    Set.disjoint_left.mpr fun x hx hx' => (interior_subset hx' : x ∈ Dᶜ) (interior_subset hx)
  have hx₀int : x₀ ∈ interior D := by
    by_contra h
    exact hcf x₀ hx₀c ⟨subset_closure hx₀D, h⟩
  exact hc.subset_left_of_subset_union isOpen_interior isOpen_interior hdisj hcover ⟨x₀, hx₀c, hx₀int⟩

/-- Killed vertex sets are monotone in the domain: if `D ⊆ D'` and the curve is continuous, then
`V^ε_int(D) ⊆ V^ε_int(D')` (Audit §2.3: a cell meeting `D` and avoiding `∂D` lies in `int D ⊆ int D'`). -/
theorem interiorCellVertices_mono_of_subset {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {D D' : Set ℂ}
    (hDD' : D ⊆ D') : interiorCellVertices ε η D ⊆ interiorCellVertices ε η D' := by
  rintro k ⟨hk1, hk2⟩
  obtain ⟨x₀, hx₀c, hx₀D⟩ := hk1
  have hcf : ∀ x ∈ cell ε η k, x ∉ frontier D := fun x hx hxf =>
    hk2 (show (cell ε η k ∩ frontier D).Nonempty from ⟨x, hx, hxf⟩)
  have hsub : cell ε η k ⊆ interior D :=
    subset_interior_of_not_frontier (cell_isPreconnected' hη k) hx₀c hx₀D hcf
  refine ⟨⟨x₀, hx₀c, hDD' hx₀D⟩, ?_⟩
  rintro ⟨x, hxc, hxf⟩
  exact hxf.2 (interior_mono hDD' (hsub hxc))

/-- Enlarging the radius of a polynomially-high-probability event keeps it polynomially high, as long as the
inclusion holds for small radii (`r < r₁`). -/
theorem polyHighProb_mono_ae_small {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    {r₁ : ℝ} (hr₁ : 0 < r₁) (hE : PolyHighProb P E) {q : Ω → Prop} (hq : ∀ᵐ ω ∂P, q ω)
    (h : ∀ r : ℝ, 0 < r → r < r₁ → ∀ ω, ω ∈ E r → q ω → ω ∈ F r) : PolyHighProb P F := by
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := hE
  refine ⟨p, hp, C, min r₀ r₁, lt_min hr₀ hr₁, fun r hr hrr => ?_⟩
  have h0 : P {ω | ¬ q ω} = 0 := ae_iff.mp hq
  have hsub : (F r)ᶜ ⊆ (E r)ᶜ ∪ {ω | ¬ q ω} := by
    intro ω hω
    by_cases hE' : ω ∈ E r
    · by_cases hq' : q ω
      · exact absurd (h r hr (lt_of_lt_of_le hrr (min_le_right _ _)) ω hE' hq') hω
      · exact Or.inr hq'
    · exact Or.inl hE'
  calc P (F r)ᶜ ≤ P ((E r)ᶜ ∪ {ω | ¬ q ω}) := measure_mono hsub
    _ ≤ P (E r)ᶜ + P {ω | ¬ q ω} := measure_union_le _ _
    _ = P (E r)ᶜ := by rw [h0, add_zero]
    _ ≤ ENNReal.ofReal (C * r ^ p) := hb r hr (lt_of_lt_of_le hrr (min_le_left _ _))

/-- Polynomially high probability is preserved by a power change of the scale: `ε ↦ E (ε ^ k)` with `k > 0`
(exponent `k p`). Used for `δ = ε^{2α}` in the volume-growth event. -/
theorem polyHighProb_comp_rpow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    (hE : PolyHighProb P E) {k : ℝ} (hk : 0 < k) : PolyHighProb P (fun ε => E (ε ^ k)) := by
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := hE
  refine ⟨k * p, mul_pos hk hp, C, min 1 (r₀ ^ (1 / k)), lt_min one_pos (Real.rpow_pos_of_pos hr₀ _),
    fun r hr hrr => ?_⟩
  have h2 : r < r₀ ^ (1 / k) := lt_of_lt_of_le hrr (min_le_right _ _)
  have h3 : r ^ k < r₀ := by
    calc r ^ k < (r₀ ^ (1 / k)) ^ k := Real.rpow_lt_rpow hr.le h2 hk
      _ = r₀ := by rw [← Real.rpow_mul hr₀.le, one_div_mul_cancel hk.ne', Real.rpow_one]
  have h4 := hb (r ^ k) (Real.rpow_pos_of_pos hr k) h3
  rw [← Real.rpow_mul hr.le] at h4
  exact h4

end S3cBridge

end MatedCRT
