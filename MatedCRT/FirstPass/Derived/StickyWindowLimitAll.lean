import MatedCRT.FirstPass.Derived.StickyWindowLimit

/-!
# No sticking for a subsequential limit, for all window lengths and time horizons

`StickyWindowLimit.ae_apply_stickySet_eq_zero_of_tendsto_law` gives, for a weak limit `ν` of the laws of
`(D n, P̃^{ε_n})`, that `ν`-almost surely the limit kernel gives mass `0` to `stickySet (B(0, ρ)) a T` for one
window length `a > 0` and one horizon `T`.  The set `stickySet A a T` decreases in `a` and increases in `T`, so
the countably many pairs `a = 1 / (k + 1)`, `T = N` suffice: almost surely, for every starting point, every
window length `a > 0` and every horizon `T`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived MatedCRT.StickyWindowKernel

namespace MatedCRT
namespace StickyWindowLimitAll

/-- A window of length `a` before time `T` contains a window of any smaller length `a'` before any later
horizon `T'`. -/
theorem stickySet_subset_of_le {E : Type*} [PseudoMetricSpace E] (A : Set E) {a a' T T' : ℝ≥0}
    (ha : a' ≤ a) (hT : T ≤ T') : stickySet A a T ⊆ stickySet A a' T' := by
  rintro f ⟨s, hs, hA, hc⟩
  exact ⟨s, hs.trans hT, fun u hu => hA u (hu.trans (add_le_add le_rfl ha)),
    fun u h1 h2 => hc u h1 (h2.trans (add_le_add le_rfl ha))⟩

/-- **No sticking for a subsequential limit** (Berestycki-Gwynne, Proposition 6.1, last claim), for one ball
`B(0, ρ)`, `ν`-almost surely simultaneously for every starting point `z`, every window length `a > 0` and every
time horizon `T`. -/
theorem ae_forall_apply_stickySet_eq_zero_of_tendsto_law {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {D : ℕ → Ω → X} (hD : ∀ n, AEMeasurable (D n) S.P)
    {ν : Measure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hlaw : ∀ F : (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (D n ω, interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ p, F p ∂ν)))
    {ρ : ℝ} {q : ℝ} (hq : 0 < q) {ψ : ℝ → ℝ}
    (hψ : (∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ δ) ∧
      ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ δ) (𝓝[>] 0) (𝓝 0))
    (hLL : LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ),
          srwLaw (S.mult ε ω) x
            {X | ¬ ∀ j : ℕ, ((j + ⌊ε⁻¹ * δ ^ q⌋₊ : ℕ) : ℕ∞) ≤
                vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X →
              ∃ i₁ i₂ : ℕ, j ≤ i₁ ∧ i₁ ≤ i₂ ∧ i₂ < j + 2 * ⌊ε⁻¹ * δ ^ q⌋₊ ∧
                δ ≤ ‖vertexPoint ε (S.η ω) (X i₂) - vertexPoint ε (S.η ω) (X i₁)‖} ≤
            ENNReal.ofReal (ψ δ)}))
    (hmε : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → c₀ ≤ ε * S.mε ε) :
    ∀ᵐ p ∂ν, ∀ z : ℂ, ∀ a : ℝ≥0, 0 < a → ∀ T : ℝ≥0,
      ((p.2 z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        (stickySet (ball (0 : ℂ) ρ) a T) = 0 := by
  have h : ∀ kN : ℕ × ℕ, ∀ᵐ p ∂ν, ∀ z : ℂ,
      ((p.2 z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        (stickySet (ball (0 : ℂ) ρ) (((kN.1 : ℝ≥0) + 1)⁻¹) (kN.2 : ℝ≥0)) = 0 := fun kN =>
    StickyWindowLimit.ae_apply_stickySet_eq_zero_of_tendsto_law hS hη' hae hε0 hε hD hlaw hq hψ hLL hmε
      (a := ((kN.1 : ℝ≥0) + 1)⁻¹) (by positivity) (kN.2 : ℝ≥0)
  filter_upwards [ae_all_iff.2 h] with p hp z a ha T
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < a from ha)
  obtain ⟨N, hN⟩ := exists_nat_ge T
  have hka : (((k : ℝ≥0) + 1)⁻¹ : ℝ≥0) ≤ a := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [← one_div]
    exact hk.le
  exact measure_mono_null (stickySet_subset_of_le _ hka hN) (hp (k, N) z)

end StickyWindowLimitAll
end MatedCRT
