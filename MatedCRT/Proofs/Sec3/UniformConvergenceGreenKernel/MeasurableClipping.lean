import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LaplacianMeasurable

/-! # Measurable clipping of discrete harmonic functions -/

namespace MatedCRT.GreenEnvironment

open Set MeasureTheory

/-- The degree-normalized Laplacian of measurable random graph data is measurable. -/
theorem measurable_matedLaplacian
    {Ω : Type} [MeasurableSpace Ω] (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k)
    (u : Ω → ℤ → ℝ) (hu : ∀ k, Measurable fun ω => u ω k) (j : ℤ) :
    Measurable fun ω => matedLaplacian (M ω) (u ω) j := by
  unfold matedLaplacian mLaplacian
  have hd : Measurable (fun ω => (mdeg (M ω) j : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_finsum_nat (fun ω k => M ω j k) (hM j))
  refine hd.inv.mul (measurable_finsum_real _ ?_)
  intro k
  exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (hM j k)).mul ((hu k).sub (hu j))

/-- Clipping a measurable random vertex function to zero on the event where
its local harmonicity or size bounds fail enforces both bounds everywhere. -/
theorem exists_measurable_clipped_harmonic
    {Ω : Type} [MeasurableSpace Ω] (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k)
    (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (u : Ω → ℤ → ℝ) (hu : ∀ k, Measurable fun ω => u ω k)
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ v : Ω → ℤ → ℝ, (∀ k, Measurable fun ω => v ω k) ∧
      (∀ ω a, a ∈ W ω → matedLaplacian (M ω) (v ω) a = 0) ∧
      (∀ ω a, a ∈ V ω → |v ω a| ≤ K / ε) ∧
      ∀ ω, (∀ a ∈ W ω, matedLaplacian (M ω) (u ω) a = 0) →
        (∀ a ∈ V ω, |u ω a| ≤ K / ε) → v ω = u ω := by
  classical
  let G : Set Ω := {ω | (∀ a ∈ W ω, matedLaplacian (M ω) (u ω) a = 0) ∧
    (∀ a ∈ V ω, |u ω a| ≤ K / ε)}
  have hG : MeasurableSet G := by
    have h1 : MeasurableSet {ω | ∀ a ∈ W ω, matedLaplacian (M ω) (u ω) a = 0} := by
      convert MeasurableSet.iInter (fun a : ℤ =>
        (measurableSet_setOfPred.mpr ((measurable_set_mem a).comp hW)).compl.union
          ((measurable_matedLaplacian M hM u hu a) (measurableSet_singleton 0))) using 1
      ext ω
      simp [imp_iff_not_or]
    have h2 : MeasurableSet {ω | ∀ a ∈ V ω, |u ω a| ≤ K / ε} := by
      convert MeasurableSet.iInter (fun a : ℤ =>
        (measurableSet_setOfPred.mpr ((measurable_set_mem a).comp hV)).compl.union
          (measurableSet_le (hu a).abs (measurable_const : Measurable (fun _ : Ω => K / ε)))) using 1
      ext ω
      simp [imp_iff_not_or]
    exact h1.inter h2
  let v : Ω → ℤ → ℝ := fun ω a => if ω ∈ G then u ω a else 0
  refine ⟨v, (fun a => (hu a).ite hG measurable_const), ?_, ?_, ?_⟩
  · intro ω a ha
    by_cases h : ω ∈ G
    · have hv : v ω = u ω := by funext b; simp [v, h]
      rw [hv]
      exact h.1 a ha
    · have hv : v ω = fun _ => 0 := by funext b; simp [v, h]
      rw [hv]
      simp [matedLaplacian, mLaplacian]
  · intro ω a ha
    by_cases h : ω ∈ G
    · simpa [v, h] using h.2 a ha
    · simp [v, h, div_nonneg hK hε.le]
  · intro ω hh hb
    funext a
    simp [v, show ω ∈ G from ⟨hh, hb⟩]

end MatedCRT.GreenEnvironment
