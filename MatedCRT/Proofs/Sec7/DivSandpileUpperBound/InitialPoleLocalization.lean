import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.FrontierMeasurable
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialLocalization
import MatedCRT.Proofs.Sec7.MassBoundOdometer.Count

/-! Countable localization around the source of a harmonic ball.
The mating-of-trees infrastructure includes work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set Metric

/-- An open ball around a point of an open set lies in the set when it does
not meet the frontier. -/
theorem ball_subset_of_frontier_inter_ball_empty {A : Set ℂ} (hopen : IsOpen A)
    {x : ℂ} {r : ℝ} (hx : x ∈ A) (hr : 0 < r)
    (hfront : ¬ (frontier A ∩ ball x r).Nonempty) : ball x r ⊆ A := by
  have hsub : ball x r ⊆ A ∪ (closure A)ᶜ := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact Or.inl hyA
    · right
      intro hycl
      apply hfront
      exact ⟨y, by simpa [frontier, hopen.interior_eq] using And.intro hycl hyA, hy⟩
  have hdisj : Disjoint A (closure A)ᶜ :=
    disjoint_left.mpr fun _ ha hc => hc (subset_closure ha)
  have hor := IsPreconnected.subset_or_subset hopen isClosed_closure.isOpen_compl
    hdisj hsub (isPreconnected_ball : IsPreconnected (ball x r))
  rcases hor with h | h
  · exact h
  · exact False.elim ((h (mem_ball_self hr)) (subset_closure hx))

/-- Before exit, containment of a fixed ball about the source is null measurable. -/
theorem nullMeasurableSet_beforeExit_ball_subset
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P)
    {r : ℝ} (hr : 0 < r) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ ball (0 : ℂ) r ⊆ Λ ω t} S.P := by
  have hm := hexit.diff (nullMeasurableSet_beforeExit_frontier_inter_ball
    hγ hγ' hS h27 hρ hρ' ht Λ hΛ hexit 0 r)
  apply hm.congr
  filter_upwards [hΛ] with ω hfam
  have hopen : IsOpen (Λ ω t) := (hfam.1 t ht).1
  have hzero : (0 : ℂ) ∈ Λ ω t := (hfam.1 t ht).2.1
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
  apply propext
  constructor
  · rintro ⟨hT, hfront⟩
    exact ⟨hT, ball_subset_of_frontier_inter_ball_empty hopen hzero hr
      (fun h => hfront ⟨hT, h⟩)⟩
  · rintro ⟨hT, hsub⟩
    refine ⟨hT, ?_⟩
    rintro ⟨_, y, hyfront, hyball⟩
    exact (disjoint_left.mp disjoint_interior_frontier)
      (by simpa [hopen.interior_eq] using hsub hyball) hyfront

/-- The decreasing source radii give an increasing null-measurable exhaustion
of the before-exit event. -/
theorem exists_beforeExit_source_ball_exhaustion
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    let G : ℕ → Set Ω := fun n => {ω | t < clusterExitTime (Λ ω) ρ ∧
      ball (0 : ℂ) (1 / ((n : ℝ) + 2)) ⊆ Λ ω t}
    Monotone G ∧ (∀ n, NullMeasurableSet (G n) S.P) ∧
      ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → ∃ n, ω ∈ G n := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro n m hnm ω hω
    refine ⟨hω.1, (ball_subset_ball ?_).trans hω.2⟩
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 2
  · intro n
    exact nullMeasurableSet_beforeExit_ball_subset hγ hγ' hS h27 hρ hρ' ht Λ hΛ hexit (by positivity)
  · filter_upwards [hΛ] with ω hfam hT
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hfam.1 t ht).1 0 (hfam.1 t ht).2.1
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
    refine ⟨n, hT, (ball_subset_ball ?_).trans hball⟩
    have hinv : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    exact hinv.trans hn.le

/-- A surjective space-filling curve's cells fill any set they meet. -/
theorem subset_fillCells_cellVertices_of_surjective {ε : ℝ} {η : ℝ → ℂ}
    (hε : 0 < ε) (hsurj : Function.Surjective η) (A : Set ℂ) :
    A ⊆ fillCells ε η (cellVertices ε η A) := by
  intro x hx
  obtain ⟨k, hk⟩ := exists_mem_cell hε hsurj x
  exact mem_iUnion₂.mpr ⟨k, ⟨x, hk, hx⟩, hk⟩

end MatedCRT.Sec7
