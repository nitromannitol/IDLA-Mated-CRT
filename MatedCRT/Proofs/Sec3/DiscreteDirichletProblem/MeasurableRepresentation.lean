import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.RandomExitMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LaplacianMeasurable

/-! # Measurable versions from the discrete Green representation -/

namespace MatedCRT.GreenEnvironment

open Set MeasureTheory

attribute [local instance] Classical.propDecidable

/-- A Green potential over a measurable random vertex set is measurable. The
finite-support sum is defined even on environments where the set is infinite. -/
theorem measurable_greenPotential {Ω : Type} [MeasurableSpace Ω]
    (M : Ω → ℤ → ℤ → ℕ) (hM : ∀ j k, Measurable fun ω => M ω j k)
    (V : Ω → Set ℤ) (hV : Measurable V) (q : Ω → ℤ → ℝ)
    (hq : ∀ b, Measurable fun ω => q ω b) (a : ℤ) :
    Measurable (fun ω => ∑ᶠ b, if b ∈ V ω then
      q ω b * greenFn (M ω) (V ω) a b else 0) := by
  classical
  apply measurable_finsum_real
  intro b
  have hb : MeasurableSet {ω | b ∈ V ω} :=
    measurableSet_setOfPred.mpr ((measurable_set_mem b).comp hV)
  exact Measurable.ite hb ((hq b).mul (measurable_greenFn M hM V hV a b)) measurable_const

/-- On finite domains the measurable Green potential is the usual finite sum. -/
theorem greenPotential_eq_sum {m : ℤ → ℤ → ℕ} {V : Set ℤ}
    (hV : V.Finite) (q : ℤ → ℝ) (a : ℤ) :
    (∑ᶠ b, if b ∈ V then q b * greenFn m V a b else 0) =
      ∑ b ∈ hV.toFinset, q b * greenFn m V a b := by
  classical
  calc
    (∑ᶠ b, if b ∈ V then q b * greenFn m V a b else 0) =
        ∑ b ∈ hV.toFinset, (if b ∈ V then q b * greenFn m V a b else 0) := by
      apply finsum_eq_sum_of_support_subset
      intro b hb
      by_contra hnot
      apply hb
      simp [show b ∉ V from fun h => hnot (hV.mem_toFinset.mpr h)]
    _ = ∑ b ∈ hV.toFinset, q b * greenFn m V a b := by
      apply Finset.sum_congr rfl
      intro b hb
      simp [hV.mem_toFinset.mp hb]

/-- A finite-domain Green representation gives an environment-measurable
version of a solution at every vertex where the representation holds. -/
theorem exists_measurable_local_solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k)
    (V W : Ω → Set ℤ) (hV : Measurable V)
    (q g F : Ω → ℤ → ℝ) (hq : ∀ b, Measurable fun ω => q ω b)
    (hg : ∀ b, Measurable fun ω => g ω b)
    (hfinite : ∀ᵐ ω ∂P, (V ω).Finite)
    (hrep : ∀ᵐ ω ∂P, ∀ a ∈ W ω, ∀ h : (V ω).Finite,
      F ω a = (∫ x, g ω (vExitPosition (V ω) x) ∂srwLaw (M ω) a) -
        ∑ b ∈ h.toFinset, q ω b * greenFn (M ω) (V ω) a b) :
    ∃ v : Ω → ℤ → ℝ, (∀ a, Measurable fun ω => v ω a) ∧
      ∀ᵐ ω ∂P, ∀ a ∈ W ω, v ω a = F ω a := by
  classical
  let v : Ω → ℤ → ℝ := fun ω a =>
    (∫ x, g ω (vExitPosition (V ω) x) ∂srwLaw (M ω) a) -
      ∑ᶠ b, if b ∈ V ω then q ω b * greenFn (M ω) (V ω) a b else 0
  refine ⟨v, fun a => (measurable_expected_exitValue M hM V hV g hg a).sub
    (measurable_greenPotential M hM V hV q hq a), ?_⟩
  filter_upwards [hfinite, hrep] with ω hω hrepr a ha
  dsimp [v]
  rw [greenPotential_eq_sum hω]
  exact (hrepr a ha hω).symm

end MatedCRT.GreenEnvironment
