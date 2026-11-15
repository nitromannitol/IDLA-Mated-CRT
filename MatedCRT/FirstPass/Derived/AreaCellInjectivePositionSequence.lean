import MatedCRT.FirstPass.Derived.AreaCellScaledInjectivePosition

/-! # Injective positions on a sequence of area-cell networks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS ReflectedGMS.GMS
open scoped NNReal Topology

/-- A prescribed sequence of area-cell sets admits injective scaled positions
that are uniformly close to the endpoint positions as the tolerance vanishes. -/
theorem exists_areaCell_injective_position_sequence
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (m : ℕ → ℤ → ℤ → ℕ)
    {a : ℝ≥0} (ha : 0 < a)
    (R : ∀ n, Set (areaCellConfig h (hε n) (m n)).cells)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0)) :
    ∃ q : ∀ n, R n → Plane,
      (∀ n, Function.Injective (q n)) ∧
      (∀ n (v : R n), ∃ x ∈ (v.1.1 : Set Plane), q n v = (a : ℝ) • x) ∧
      (∀ n (v : R n),
        dist ((a : ℝ) • areaCellRepresentative h (hε n) (m n) v) (q n v) < t n) ∧
      ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v : R n,
        dist ((a : ℝ) • areaCellRepresentative h (hε n) (m n) v) (q n v) < δ := by
  classical
  have hex : ∀ n, ∃ q : R n → Plane, Function.Injective q ∧
      (∀ v : R n, ∃ x ∈ (v.1.1 : Set Plane), q v = (a : ℝ) • x) ∧
      ∀ v : R n,
        dist ((a : ℝ) • areaCellRepresentative h (hε n) (m n) v) (q v) < t n :=
    fun n => exists_areaCell_scaled_injective_position h (hε n) (m n) ha (ht n) (R n)
  choose q hqinj hqcell hqnear using hex
  refine ⟨q, hqinj, hqcell, hqnear, ?_⟩
  intro δ hδ
  filter_upwards [ht0.eventually_lt_const hδ] with n hn
  intro v
  exact (hqnear n v).trans hn

end MatedCRT
end
