import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.TwoMeshSupremum
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.UniformMetricSelection

/-! # Measurable uniform distances for two meshes -/

namespace MatedCRT

open Set MeasureTheory
open scoped UniformConvergence

/-- The uniform distance of functions encoded on a set is the supremum of
    the pointwise distances, with zero included for the empty set. -/
theorem uniformSetEncode_dist_eq_sSup
    {α Y : Type*} [MetricSpace Y] [BoundedSpace Y]
    (K : Set α) (b : ℝ → Y) (f g : α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ K, dist (b (f x)) (b (g x)) ≤ C) :
    dist (uniformSetEncode K b f) (uniformSetEncode K b g) =
      sSup (insert 0 {r | ∃ x ∈ K, r = dist (b (f x)) (b (g x))}) := by
  classical
  let S : Set ℝ := insert 0 {r | ∃ x ∈ K, r = dist (b (f x)) (b (g x))}
  have hS : BddAbove S := by
    refine ⟨C, ?_⟩
    intro r hr
    rcases (mem_insert_iff.mp hr) with rfl | ⟨x, hx, rfl⟩
    · exact hC
    · exact hbound x hx
  have hS0 : 0 ≤ sSup S := le_csSup hS (mem_insert 0 _)
  apply le_antisymm
  · apply (UniformFun.dist_le hS0).mpr
    intro x
    by_cases hx : x ∈ K
    · simpa [uniformSetEncode, hx] using
        (le_csSup hS (show dist (b (f x)) (b (g x)) ∈ S from
          mem_insert_of_mem _ ⟨x, hx, rfl⟩))
    · simpa [uniformSetEncode, hx] using hS0
  · apply csSup_le ⟨0, mem_insert 0 _⟩
    intro r hr
    rcases (mem_insert_iff.mp hr) with rfl | ⟨x, hx, rfl⟩
    · exact dist_nonneg
    · have h := (UniformFun.dist_le (show 0 ≤ dist (uniformSetEncode K b f)
        (uniformSetEncode K b g) from dist_nonneg)).mp le_rfl x
      simpa [uniformSetEncode, hx] using h

/-- A pair of measurable vertex fields at two meshes has a measurable
    bounded-encoding uniform distance on the common cell-selection event. -/
theorem exists_measurable_two_mesh_uniform_distance
    {Ω Y : Type*} [MeasurableSpace Ω] [MetricSpace Y] [BoundedSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (u w : Ω → ℤ → ℝ) (hu : ∀ a, Measurable fun ω => u ω a)
    (hw : ∀ a, Measurable fun ω => w ω a)
    (b : ℝ → Y) (hb : Measurable b) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x y : ℝ, dist (b x) (b y) ≤ C)
    (ε δ : ℝ) (K : Set ℂ) (hK : IsCompact K)
    (hε : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty)
    (hδ : ∀ k : ℤ, (Icc (δ * (k - 1)) (δ * k)).Nonempty) :
    ∃ d : Ω → ℝ, Measurable d ∧ ∀ ω,
      (∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) →
      (∃ M : ℤ, ∀ j < M, ∀ x ∈ K, x ∉ cell δ (η ω) j) →
      (∀ x ∈ K, x ∈ cell ε (η ω) (vertexOf ε (η ω) x)) →
      (∀ x ∈ K, x ∈ cell δ (η ω) (vertexOf δ (η ω) x)) →
      d ω = dist (uniformSetEncode K b (fun x => u ω (vertexOf ε (η ω) x)))
        (uniformSetEncode K b (fun x => w ω (vertexOf δ (η ω) x))) := by
  let v : Ω → ℤ → ℤ → ℝ := fun ω a c => dist (b (u ω a)) (b (w ω c))
  have hv : ∀ a c, Measurable fun ω => v ω a c := fun a c =>
    (hb.comp (hu a)).dist (hb.comp (hw c))
  have hvbound : ∀ ω a c, 0 ≤ v ω a c ∧ v ω a c ≤ C := fun ω a c =>
    ⟨dist_nonneg, hbound (u ω a) (w ω c)⟩
  obtain ⟨d, hdm, hd⟩ := exists_measurable_two_mesh_supremum η hη v hv C hC hvbound ε δ K hK hε hδ
  refine ⟨d, hdm, ?_⟩
  intro ω h₁ h₂ h₃ h₄
  rw [uniformSetEncode_dist_eq_sSup K b _ _ C hC (fun x hx => hbound _ _)]
  exact hd ω h₁ h₂ h₃ h₄

/-- The two meshes may be selected by measurable countable-valued indices. -/
theorem exists_measurable_random_two_mesh_uniform_distance
    {Ω Y : Type*} [MeasurableSpace Ω] [MetricSpace Y] [BoundedSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (u w : Ω → ℤ → ℝ) (hu : ∀ a, Measurable fun ω => u ω a)
    (hw : ∀ a, Measurable fun ω => w ω a)
    (b : ℝ → Y) (hb : Measurable b) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x y : ℝ, dist (b x) (b y) ≤ C)
    (e : ℕ → ℝ) (he : ∀ n (k : ℤ), (Icc (e n * (k - 1)) (e n * k)).Nonempty)
    (I J : Ω → ℕ) (hI : Measurable I) (hJ : Measurable J)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ d : Ω → ℝ, Measurable d ∧ ∀ ω,
      (∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell (e (I ω)) (η ω) j) →
      (∃ M : ℤ, ∀ j < M, ∀ x ∈ K, x ∉ cell (e (J ω)) (η ω) j) →
      (∀ x ∈ K, x ∈ cell (e (I ω)) (η ω) (vertexOf (e (I ω)) (η ω) x)) →
      (∀ x ∈ K, x ∈ cell (e (J ω)) (η ω) (vertexOf (e (J ω)) (η ω) x)) →
      d ω = dist (uniformSetEncode K b (fun x => u ω (vertexOf (e (I ω)) (η ω) x)))
        (uniformSetEncode K b (fun x => w ω (vertexOf (e (J ω)) (η ω) x))) := by
  choose d hdm hd using fun n m => exists_measurable_two_mesh_uniform_distance
    η hη u w hu hw b hb C hC hbound (e n) (e m) K hK (he n) (he m)
  have hm : ∀ n, Measurable fun ω => d n (J ω) ω := by
    intro n
    exact Tightness.measurable_comp_nat (hdm n) hJ
  refine ⟨fun ω => d (I ω) (J ω) ω, Tightness.measurable_comp_nat hm hI, ?_⟩
  intro ω h₁ h₂ h₃ h₄
  exact hd (I ω) (J ω) ω h₁ h₂ h₃ h₄

end MatedCRT
