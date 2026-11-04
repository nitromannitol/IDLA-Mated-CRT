import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CompactTestInequalities
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import HarmonicBalls.Steps.Sec3.Basic

/-! # Countable approximation of continuous majorants -/

namespace MatedCRT

open Set TopologicalSpace MeasureTheory HarmonicBalls Metric Laplacian

/-- A family of continuous functions that is stable under adding positive
constants has a countable subfamily approximating every majorant from above,
uniformly and independently of the obstacle. -/
theorem exists_countable_approximation_of_majorants
    {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [SecondCountableTopology K] (V : Set C(K, ℝ))
    (hadd : ∀ u ∈ V, ∀ c : ℝ, 0 < c → u + ContinuousMap.const K c ∈ V) :
    ∃ C : Set C(K, ℝ), C.Countable ∧ C ⊆ V ∧
      ∀ (β : K → ℝ) (u : C(K, ℝ)), u ∈ V → (∀ x, β x ≤ u x) →
      ∀ ε : ℝ, 0 < ε → ∃ v ∈ C, (∀ x, β x ≤ v x) ∧
        ∀ x, |v x - u x| < ε := by
  obtain ⟨C, hcount, hsub, hdense⟩ := exists_countable_dense_subset V
  refine ⟨C, hcount, hsub, ?_⟩
  intro β u hu hβ ε hε
  have hshift : u + ContinuousMap.const K (ε / 2) ∈ V := hadd u hu _ (by linarith)
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp (hdense hshift) (ε / 2) (by linarith)
  refine ⟨v, hv, ?_, ?_⟩
  · intro x
    have hd := (ContinuousMap.dist_apply_le_dist (f := u + ContinuousMap.const K (ε / 2))
      (g := v) x).trans_lt hdist
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, Real.dist_eq] at hd
    have hlo := (abs_lt.mp hd).2
    linarith [hβ x]
  · intro x
    have hd := (ContinuousMap.dist_apply_le_dist (f := u + ContinuousMap.const K (ε / 2))
      (g := v) x).trans_lt hdist
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, Real.dist_eq] at hd
    rw [abs_lt] at hd ⊢
    constructor <;> linarith [hd.1, hd.2]

/-- Adding a constant preserves a distributional Laplacian upper bound. -/
theorem laplacianLE_add_constant {w : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ}
    (hw : LaplacianLE w μ U) (c : ℝ) : LaplacianLE (fun x => w x + c) μ U := by
  refine ⟨hw.1.add (locallyIntegrableOn_const c), fun φ hφ hφ0 hφμ => ?_⟩
  have hi := integrable_mul_laplacian_of_test hw.1 hφ
  have hc := (integrable_mul_laplacian_of_test (locallyIntegrableOn_const c) hφ)
  have heq : (fun x => (w x + c) * Δ φ x) =
      (fun x => w x * Δ φ x + c * Δ φ x) := by funext x; ring
  rw [heq, integral_add hi hc, integral_const_mul,
    integral_laplacian_eq_zero (hφ.1.of_le (by norm_cast)) hφ.2.1, mul_zero, add_zero]
  exact hw.2 φ hφ hφ0 hφμ

/-- There is a countable collection of continuous distributionally
superharmonic functions which approximates every such function from above
uniformly on a closed ball. -/
theorem exists_countable_superharmonic_majorants (R : ℝ) :
    ∃ D : Set (ℂ → ℝ), D.Countable ∧
      (∀ v ∈ D, ContinuousOn v (closedBall 0 R) ∧ LaplacianLE v 0 (ball 0 R)) ∧
      ∀ (u : ℂ → ℝ), ContinuousOn u (closedBall 0 R) → LaplacianLE u 0 (ball 0 R) →
        ∀ ε : ℝ, 0 < ε → ∃ v ∈ D, ∀ x ∈ closedBall (0 : ℂ) R,
          u x ≤ v x ∧ |v x - u x| < ε := by
  classical
  let K := closedBall (0 : ℂ) R
  let V : Set (ℂ → ℝ) := {u | ContinuousOn u K ∧ LaplacianLE u 0 (ball 0 R)}
  let f : V → C(K, ℝ) := fun u =>
    ⟨fun x => u.1 x, continuousOn_iff_continuous_domRestrict.mp u.2.1⟩
  have hadd : ∀ u ∈ range f, ∀ c : ℝ, 0 < c → u + ContinuousMap.const K c ∈ range f := by
    rintro _ ⟨u, rfl⟩ c hc
    let v : V := ⟨fun x => u.1 x + c, u.2.1.add continuousOn_const,
      laplacianLE_add_constant u.2.2 c⟩
    refine ⟨v, ?_⟩
    ext x
    rfl
  obtain ⟨C, hCc, hCV, hC⟩ := exists_countable_approximation_of_majorants (range f) hadd
  let g : C → V := fun x => Classical.choose (hCV x.property)
  have hg (x : C) : f (g x) = x := Classical.choose_spec (hCV x.property)
  have : Countable C := hCc.to_subtype
  let D : Set (ℂ → ℝ) := range (fun x : C => (g x).1)
  refine ⟨D, Set.countable_range _, ?_, ?_⟩
  · rintro v ⟨x, rfl⟩
    exact (g x).2
  · intro u huc huL ε hε
    let uu : V := ⟨u, huc, huL⟩
    obtain ⟨v, hvC, hvmajor, hvclose⟩ := hC (f uu) (f uu) ⟨uu, rfl⟩
      (fun _ => le_rfl) ε hε
    let vv : C := ⟨v, hvC⟩
    refine ⟨(g vv).1, ⟨vv, rfl⟩, ?_⟩
    intro x hx
    have hval := congrArg (fun a : C(K, ℝ) => a ⟨x, hx⟩) (hg vv)
    have hmaj := hvmajor ⟨x, hx⟩
    have hcl := hvclose ⟨x, hx⟩
    change (g vv).1 x = v ⟨x, hx⟩ at hval
    change u x ≤ v ⟨x, hx⟩ at hmaj
    change |v ⟨x, hx⟩ - u x| < ε at hcl
    exact ⟨hval ▸ hmaj, hval ▸ hcl⟩

end MatedCRT
