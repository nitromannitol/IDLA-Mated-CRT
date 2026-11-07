import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.TwoMeshUniformDistance
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.UniformSelectionVersions

/-! # Measurable uniform selection for random meshes -/

namespace MatedCRT

open Set Filter Topology MeasureTheory
open scoped UniformConvergence

/-- Pathwise compactness on countably many good events admits one measurable
    subsequence for vertex fields evaluated at countably selected meshes. -/
theorem exists_measurable_subsequence_two_mesh_uniform
    {Ω Y : Type*} [MeasurableSpace Ω] [MetricSpace Y] [BoundedSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (e : ℕ → ℝ) (he : ∀ n (k : ℤ), (Icc (e n * (k - 1)) (e n * k)).Nonempty)
    (I : Ω → ℕ → ℕ) (hI : ∀ n, Measurable fun ω => I ω n)
    (K : ℕ → Set ℂ) (hK : ∀ j, IsCompact (K j))
    (u : Ω → ℕ → ℕ → ℤ → ℝ) (hu : ∀ j n a, Measurable fun ω => u ω j n a)
    (b : ℝ → Y) (hb : UniformContinuous b) (hbi : Function.Injective b)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x y, dist (b x) (b y) ≤ C)
    (P : Ω → ℕ → Prop)
    (hgood : ∀ ω j, P ω j → ∀ n,
      (∃ N : ℤ, ∀ a < N, ∀ x ∈ K j, x ∉ cell (e (I ω n)) (η ω) a) ∧
      (∀ x ∈ K j, x ∈ cell (e (I ω n)) (η ω) (vertexOf (e (I ω n)) (η ω) x)))
    (hc : ∀ ω j, P ω j → ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ,
        TendstoUniformlyOn (fun n x => u ω j (ψ (θ n))
          (vertexOf (e (I ω (ψ (θ n)))) (η ω) x)) w atTop (K j)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable fun ω => Φ ω k) ∧
      ∀ ω, StrictMono (Φ ω) ∧ ∀ j, P ω j → ∃ w : ℂ → ℝ,
        TendstoUniformlyOn (fun n x => u ω j (Φ ω n)
          (vertexOf (e (I ω (Φ ω n))) (η ω) x)) w atTop (K j) := by
  classical
  let F : Ω → ℕ → ℕ → ℂ → ℝ := fun ω j n x =>
    u ω j n (vertexOf (e (I ω n)) (η ω) x)
  choose d hdm hd using fun j n m => exists_measurable_random_two_mesh_uniform_distance
    η hη (fun ω => u ω j n) (fun ω => u ω j m) (hu j n) (hu j m)
    b hb.continuous.measurable C hC hbound e he (fun ω => I ω n) (fun ω => I ω m)
    (hI n) (hI m) (K j) (hK j)
  apply exists_measurable_subsequence_uniform_of_distance_versions b hb hbi K F d hdm P
  · intro ω j hP n m
    exact hd j n m ω (hgood ω j hP n).1 (hgood ω j hP m).1
      (hgood ω j hP n).2 (hgood ω j hP m).2
  · exact hc

end MatedCRT
