import MatedCRT.FirstPass.Derived.ExitDecomposition
import LatticeProb.Prob.ConditionalProductMixture
import LatticeProb.Prob.CommonContinuationCoupling

/-!
# Coupling of the walks from two vertices at their exit time from a finite set

For a finite exit datum `A` (`FiniteExitData m A`) and `x, y ∈ A`, the simple random walk laws
`srwLaw m x` and `srwLaw m y` are mixtures, over the exit position `v ∉ A`, of the product of a law of
the stopped path and the walk law `srwLaw m v` spliced after the exit (strong Markov property at the
exit time, `exists_mixture_of_conditional_product`).  A maximal coupling of the exit positions, with the
same continuation `srwLaw m v` for equal exit positions, couples the two walks so that the paths after
their exit times agree except on an event of probability at most the total variation distance of the
two exit-position laws (Berestycki–Gwynne (2020), Proposition 6.12, Step 1).
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCoupling

open MeasureTheory Set
open scoped ENNReal
open MatedCRT.ExitDecomposition
open MatedCRT.FirstPass36 (FiniteExitData)

/-- **The walk is a mixture over its exit position.**  For `a ∈ A` the law of the walk from `a` is
`∑_v P(x_τ = v) · ((𝒜_v ⊗ P^v) ∘ splice_v⁻¹)`, where `𝒜_v` is a probability law of the stopped path. -/
theorem srwLaw_exit_mixture {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hA : FiniteExitData m A) {a : ℤ}
    (ha : a ∈ A) :
    ∃ Ah : ℤ → Measure (ℕ → ℤ), (∀ v, IsProbabilityMeasure (Ah v)) ∧
      srwLaw m a = Measure.sum (fun v => srwLaw m a (vExitPosition A ⁻¹' {v}) •
        ((Ah v).prod (srwLaw m v)).map (fun p => splice A v p.1 p.2)) := by
  obtain ⟨Ah, h1, -, h3⟩ := LatticeProb.exists_mixture_of_conditional_product (srwLaw m a)
    (X := vExitPosition A) (pre := stoppedPath A) (post := postExit A)
    (measurable_vExitPosition A) (measurable_stoppedPath A) (measurable_postExit A)
    (fun v => srwLaw m v) (fun v p => splice A v p.1 p.2) (fun v => measurable_splice A v)
    (fun v B C hB hC => srwLaw_exit_rectangle hA ha v hB hC)
    (ae_splice_stoppedPath_postExit hA ha)
  exact ⟨Ah, h1, h3⟩

/-- The mass of a set of exit positions, as a sum over the points of the set. -/
lemma tsum_indicator_exitPosition (μ : Measure (ℕ → ℤ)) (A : Set ℤ) (S : Set ℤ) :
    ∑' v, S.indicator (fun v => μ (vExitPosition A ⁻¹' {v})) v = μ (vExitPosition A ⁻¹' S) := by
  rw [← tsum_subtype S (fun v => μ (vExitPosition A ⁻¹' {v}))]
  exact tsum_measure_preimage_singleton (Set.to_countable S)
    (fun v _ => measurable_vExitPosition A (measurableSet_singleton v))

/-- **Coupling of the walks from two vertices of `A` at their exit time.**  If the laws of the exit
positions of the walks from `x` and from `y` satisfy `P_x(x_τ ∈ S) ≤ P_y(x_τ ∈ S) + a` for every set
`S` of vertices (total variation distance at most `a`), the two walks have a coupling whose post-exit
paths differ with probability at most `a`. -/
theorem srwLaw_exit_coupling {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hA : FiniteExitData m A) {x y : ℤ}
    (hx : x ∈ A) (hy : y ∈ A) {a : ℝ≥0∞}
    (hTV : ∀ S : Set ℤ,
      srwLaw m x (vExitPosition A ⁻¹' S) ≤ srwLaw m y (vExitPosition A ⁻¹' S) + a) :
    ∃ ρ : Measure ((ℕ → ℤ) × (ℕ → ℤ)), ρ.map Prod.fst = srwLaw m x ∧
      ρ.map Prod.snd = srwLaw m y ∧ ρ (exitContinuationEvent A)ᶜ ≤ a := by
  obtain ⟨Ax, hAx, hxe⟩ := srwLaw_exit_mixture hA hx
  obtain ⟨Ay, hAy, hye⟩ := srwLaw_exit_mixture hA hy
  have hp : ∑' v, srwLaw m x (vExitPosition A ⁻¹' {v}) = 1 := by
    have := tsum_indicator_exitPosition (srwLaw m x) A univ
    simpa using this
  have hq : ∑' v, srwLaw m y (vExitPosition A ⁻¹' {v}) = 1 := by
    have := tsum_indicator_exitPosition (srwLaw m y) A univ
    simpa using this
  have hTV' : ∀ S : Set ℤ, ∑' v, S.indicator (fun v => srwLaw m x (vExitPosition A ⁻¹' {v})) v
      ≤ ∑' v, S.indicator (fun v => srwLaw m y (vExitPosition A ⁻¹' {v})) v + a := by
    intro S
    rw [tsum_indicator_exitPosition, tsum_indicator_exitPosition]
    exact hTV S
  have hEΦ : ∀ v : ℤ, srwLaw m x (vExitPosition A ⁻¹' {v}) ≠ 0 →
      srwLaw m y (vExitPosition A ⁻¹' {v}) ≠ 0 → ∀ (y₁ y₂ u : ℕ → ℤ),
      (splice A v y₁ u, splice A v y₂ u) ∈ exitContinuationEvent A := by
    intro v hpv _ y₁ y₂ u
    have hvA : v ∉ A := fun hv => hpv (srwLaw_exitPosition_null hA hx hv)
    exact splice_pair_mem_exitContinuationEvent hvA y₁ y₂ u
  obtain ⟨ρ, h1, h2, h3⟩ := LatticeProb.exists_coupling_mixture_common_continuation_of_tv
    (fun v => srwLaw m x (vExitPosition A ⁻¹' {v}))
    (fun v => srwLaw m y (vExitPosition A ⁻¹' {v})) hp hq hTV' Ax Ay (fun v => srwLaw m v)
    (fun v p => splice A v p.1 p.2) (fun v p => splice A v p.1 p.2) (measurable_splice A)
    (measurable_splice A) (measurableSet_exitContinuationEvent A) hEΦ
  exact ⟨ρ, h1.trans hxe.symm, h2.trans hye.symm, h3⟩

end ExitCoupling
end MatedCRT
