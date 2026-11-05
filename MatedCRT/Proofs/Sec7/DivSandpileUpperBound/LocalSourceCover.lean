import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialPoleLocalization
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LocalClusterMeasurable

/-! Measurable source-ball covers using bounded obstacle clusters.
The mating-of-trees infrastructure includes work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls

/-- Containment of a source ball in a regularized local cluster is null measurable. -/
theorem nullMeasurableSet_ball_subset_regularizedLocalCluster
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    {r : ℝ} (hr : 0 < r) :
    NullMeasurableSet {ω | ball (0 : ℂ) r ⊆
      interior (closure (cluster (S.μ ω) ρ 0 t))} S.P := by
  let A : Ω → Set ℂ := fun ω => interior (closure (cluster (S.μ ω) ρ 0 t))
  have hmem : ∀ z, NullMeasurableSet {ω | z ∈ A ω} S.P :=
    fun z => hS.nullMeasurableSet_mem_regularizedLocalCluster hγ hγ' h27 hρ hρ' ht z
  have hopen : ∀ᵐ ω ∂S.P, IsOpen (A ω) := Eventually.of_forall fun _ => isOpen_interior
  have hreg : ∀ᵐ ω ∂S.P, interior (closure (A ω)) = A ω := by
    apply Eventually.of_forall
    intro ω
    apply subset_antisymm
    · exact interior_mono (closure_minimal interior_subset isClosed_closure)
    · exact isOpen_interior.subset_interior_closure
  have hm := (hmem 0).diff (nullMeasurableSet_frontier_inter_ball_nonempty
    S.P A hmem hopen hreg 0 r)
  apply hm.congr
  filter_upwards [] with ω
  simp only [Set.mem_sdiff, mem_ofPred_eq]
  apply propext
  constructor
  · rintro ⟨hzero, hfront⟩
    exact ball_subset_of_frontier_inter_ball_empty isOpen_interior hzero hr hfront
  · intro hsub
    refine ⟨hsub (mem_ball_self hr), ?_⟩
    rintro ⟨y, hyfront, hyball⟩
    exact (disjoint_left.mp disjoint_interior_frontier)
      (by rw [isOpen_interior.interior_eq]; exact hsub hyball) hyfront

/-- Before exit, bounded obstacle clusters supply a measurable increasing cover
by events on which a fixed source ball lies in the cone harmonic ball. -/
theorem exists_localCluster_source_ball_cover
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) :
    let G : ℕ → Set Ω := fun n => {ω | ball (0 : ℂ) (1 / ((n : ℝ) + 2)) ⊆
      interior (closure (cluster (S.μ ω) ρ 0 t))}
    Monotone G ∧ (∀ n, NullMeasurableSet (G n) S.P) ∧
      (∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → ∃ n, ω ∈ G n) ∧
      (∀ᵐ ω ∂S.P, ∀ n, t < clusterExitTime (Λ ω) ρ → ω ∈ G n →
        ball (0 : ℂ) (1 / ((n : ℝ) + 2)) ⊆ Λ ω t) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m hnm ω hω
    apply (ball_subset_ball ?_).trans hω
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 2
  · intro n
    exact nullMeasurableSet_ball_subset_regularizedLocalCluster hγ hγ' hS h27 hρ hρ' ht (by positivity)
  · filter_upwards [hΛ] with ω hfam hT
    have hsub := coneFamily_subset_before_exit hfam ht hT
    have heq : Λ ω t = interior (closure (cluster (S.μ ω) ρ 0 t)) :=
      (hfam.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hfam.1 t ht).1 0 (hfam.1 t ht).2.1
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
    refine ⟨n, ?_⟩
    rw [← heq]
    apply (ball_subset_ball ?_).trans hball
    have hinv : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    exact hinv.trans hn.le
  · filter_upwards [hΛ] with ω hfam n hT hball
    have hsub := coneFamily_subset_before_exit hfam ht hT
    have heq : Λ ω t = interior (closure (cluster (S.μ ω) ρ 0 t)) :=
      (hfam.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1
    simpa [heq] using hball

end MatedCRT.Sec7
