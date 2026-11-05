import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RandomSetRegularization
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LocalClusterMeasurable
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ContinuumFrontier

/-! Pointwise measurability of boundaries of random open sets.
The mated-CRT environment includes the formalization of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Filter Topology TopologicalSpace Metric _root_.HarmonicBalls

/-- Pointwise null measurability of a random open set implies the same for its
closure. -/
theorem nullMeasurableSet_mem_closure_of_open_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → Set ℂ)
    (hmem : ∀ z : ℂ, NullMeasurableSet {ω | z ∈ A ω} P)
    (hopen : ∀ᵐ ω ∂P, IsOpen (A ω)) (x : ℂ) :
    NullMeasurableSet {ω | x ∈ closure (A ω)} P := by
  obtain ⟨C, hC, hdense⟩ := exists_countable_dense ℂ
  have hm := nullMeasurableSet_mem_closure_inter_countable P A hC (fun z _ => hmem z) x
  apply hm.congr
  filter_upwards [hopen] with ω hω
  have heq : closure (A ω) = closure (A ω ∩ C) :=
    (closure_minimal (hdense.open_subset_closure_inter hω) isClosed_closure).antisymm
      (closure_mono inter_subset_left)
  simp [heq]

/-- For a random open set with null-measurable point membership, every fixed
point has null-measurable frontier membership. -/
theorem nullMeasurableSet_mem_frontier_of_open_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → Set ℂ)
    (hmem : ∀ z : ℂ, NullMeasurableSet {ω | z ∈ A ω} P)
    (hopen : ∀ᵐ ω ∂P, IsOpen (A ω)) (x : ℂ) :
    NullMeasurableSet {ω | x ∈ frontier (A ω)} P := by
  have hm := (nullMeasurableSet_mem_closure_of_open_ae P A hmem hopen x).diff (hmem x)
  apply hm.congr
  filter_upwards [hopen] with ω hω
  simp [frontier, hω.interior_eq]


/-- Before exit, point membership in the cone harmonic ball is null measurable
from the local obstacle representation and a measurable exit event. -/
theorem nullMeasurableSet_beforeExit_mem_coneFamily
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) (x : ℂ) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ x ∈ Λ ω t} S.P := by
  have hm := hexit.inter (hS.nullMeasurableSet_mem_regularizedLocalCluster
    hγ hγ' h27 hρ hρ' ht x)
  apply hm.congr
  filter_upwards [hΛ] with ω hω
  by_cases hT : t < clusterExitTime (Λ ω) ρ
  · have hsub := coneFamily_subset_before_exit hω ht hT
    have heq : Λ ω t = interior (closure (cluster (S.μ ω) ρ 0 t)) :=
      (hω.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1
    simp [hT, heq]
  · simp [hT]

/-- Before exit, every fixed point has null-measurable membership in the cone
harmonic-ball frontier. -/
theorem nullMeasurableSet_beforeExit_mem_frontier
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) (x : ℂ) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ x ∈ frontier (Λ ω t)} S.P := by
  classical
  let A : Ω → Set ℂ := fun ω => if t < clusterExitTime (Λ ω) ρ then Λ ω t else ∅
  have hmem : ∀ z, NullMeasurableSet {ω | z ∈ A ω} S.P := by
    intro z
    have hm := nullMeasurableSet_beforeExit_mem_coneFamily hγ hγ' hS h27 hρ hρ' ht Λ hΛ hexit z
    convert hm using 1
    ext ω
    simp [A]
  have hopen : ∀ᵐ ω ∂S.P, IsOpen (A ω) := by
    filter_upwards [hΛ] with ω hω
    dsimp [A]
    split_ifs
    · exact (hω.1 t ht).1
    · exact isOpen_empty
  have hm := hexit.inter (nullMeasurableSet_mem_frontier_of_open_ae S.P A hmem hopen x)
  convert hm using 1
  ext ω
  by_cases hT : t < clusterExitTime (Λ ω) ρ <;> simp [A, hT]


/-- A ball meets the frontier of a regular open set exactly when it meets the
set and the complement of its closure. -/
theorem frontier_inter_ball_nonempty_iff {A : Set ℂ} (hopen : IsOpen A)
    (hregular : interior (closure A) = A) (x : ℂ) (r : ℝ) :
    (frontier A ∩ ball x r).Nonempty ↔
      (A ∩ ball x r).Nonempty ∧ ((closure A)ᶜ ∩ ball x r).Nonempty := by
  constructor
  · rintro ⟨y, hyF, hyball⟩
    have hycl : y ∈ closure A := frontier_subset_closure hyF
    have hynot : y ∉ A := by
      intro hyA
      exact (disjoint_left.mp disjoint_interior_frontier)
        (by simpa [hopen.interior_eq] using hyA) hyF
    have hycomp : y ∈ closure (closure A)ᶜ := by
      rw [closure_compl, hregular]
      exact hynot
    have h1 := (_root_.mem_closure_iff.mp hycl) (ball x r) isOpen_ball hyball
    have h2 := (_root_.mem_closure_iff.mp hycomp) (ball x r) isOpen_ball hyball
    exact ⟨inter_comm _ _ ▸ h1, inter_comm _ _ ▸ h2⟩
  · rintro ⟨⟨a, haA, haball⟩, ⟨b, hbA, hbball⟩⟩
    by_contra h
    have hsub : ball x r ⊆ A ∪ (closure A)ᶜ := by
      intro y hy
      by_cases hyA : y ∈ A
      · exact Or.inl hyA
      · right
        intro hycl
        apply h
        exact ⟨y, by simpa [frontier, hopen.interior_eq] using And.intro hycl hyA, hy⟩
    have hdisj : Disjoint A (closure A)ᶜ := disjoint_left.mpr fun _ ha hc => hc (subset_closure ha)
    have hor := IsPreconnected.subset_or_subset hopen isClosed_closure.isOpen_compl
      hdisj hsub (isPreconnected_ball : IsPreconnected (ball x r))
    rcases hor with hor | hor
    · exact hbA (subset_closure (hor hbball))
    · exact (hor haball) (subset_closure haA)


/-- For an almost surely regular open random set, the event that a fixed ball
meets its frontier is null measurable from pointwise membership. -/
theorem nullMeasurableSet_frontier_inter_ball_nonempty
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → Set ℂ)
    (hmem : ∀ z : ℂ, NullMeasurableSet {ω | z ∈ A ω} P)
    (hopen : ∀ᵐ ω ∂P, IsOpen (A ω))
    (hregular : ∀ᵐ ω ∂P, interior (closure (A ω)) = A ω)
    (x : ℂ) (r : ℝ) : NullMeasurableSet {ω | (frontier (A ω) ∩ ball x r).Nonempty} P := by
  classical
  obtain ⟨C, hC, hdense⟩ := exists_countable_dense ℂ
  have : Countable C := hC.to_subtype
  have hcl : ∀ z : ℂ, NullMeasurableSet {ω | z ∈ closure (A ω)} P :=
    nullMeasurableSet_mem_closure_of_open_ae P A hmem hopen
  have h1 : ∀ z : C, NullMeasurableSet {ω | (z : ℂ) ∈ ball x r ∧ (z : ℂ) ∈ A ω} P := by
    intro z
    by_cases hz : (z : ℂ) ∈ ball x r
    · simpa [hz] using hmem z
    · simp [hz]
  have h2 : ∀ z : C, NullMeasurableSet {ω | (z : ℂ) ∈ ball x r ∧ (z : ℂ) ∉ closure (A ω)} P := by
    intro z
    by_cases hz : (z : ℂ) ∈ ball x r
    · convert (hcl z).compl using 1
      ext ω
      simp [hz]
    · simp [hz]
  have hm := (NullMeasurableSet.iUnion h1).inter (NullMeasurableSet.iUnion h2)
  apply hm.congr
  filter_upwards [hopen, hregular] with ω ho hreg
  simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq]
  rw [frontier_inter_ball_nonempty_iff ho hreg]
  apply propext
  constructor
  · rintro ⟨⟨y, hyball, hyA⟩, ⟨z, hzball, hzA⟩⟩
    exact ⟨⟨y, hyA, hyball⟩, ⟨z, hzA, hzball⟩⟩
  · rintro ⟨⟨a, haA, hab⟩, ⟨b, hbA, hbb⟩⟩
    obtain ⟨y, ⟨hyA, hyball⟩, hyC⟩ := hdense.inter_open_nonempty
      (A ω ∩ ball x r) (ho.inter isOpen_ball) ⟨a, haA, hab⟩
    obtain ⟨z, ⟨hzA, hzball⟩, hzC⟩ := hdense.inter_open_nonempty
      ((closure (A ω))ᶜ ∩ ball x r) (isClosed_closure.isOpen_compl.inter isOpen_ball)
      ⟨b, hbA, hbb⟩
    exact ⟨⟨⟨y, hyC⟩, hyball, hyA⟩, ⟨⟨z, hzC⟩, hzball, hzA⟩⟩


/-- Before exit, intersection of the harmonic-ball frontier with a fixed ball
is null measurable. -/
theorem nullMeasurableSet_beforeExit_frontier_inter_ball
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) (x : ℂ) (r : ℝ) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
      (frontier (Λ ω t) ∩ ball x r).Nonempty} S.P := by
  classical
  let A : Ω → Set ℂ := fun ω => if t < clusterExitTime (Λ ω) ρ then Λ ω t else ∅
  have hmem : ∀ z, NullMeasurableSet {ω | z ∈ A ω} S.P := by
    intro z
    have hm := nullMeasurableSet_beforeExit_mem_coneFamily hγ hγ' hS h27 hρ hρ' ht Λ hΛ hexit z
    convert hm using 1
    ext ω
    simp [A]
  have hopen : ∀ᵐ ω ∂S.P, IsOpen (A ω) := by
    filter_upwards [hΛ] with ω hω
    dsimp [A]
    split_ifs
    · exact (hω.1 t ht).1
    · exact isOpen_empty
  have hregular : ∀ᵐ ω ∂S.P, interior (closure (A ω)) = A ω := by
    filter_upwards [hΛ] with ω hω
    dsimp [A]
    split_ifs with hT
    · have hsub := coneFamily_subset_before_exit hω ht hT
      have heq : Λ ω t = interior (closure (cluster (S.μ ω) ρ 0 t)) :=
        (hω.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1
      rw [heq]
      apply subset_antisymm
      · exact interior_mono (closure_minimal interior_subset isClosed_closure)
      · exact isOpen_interior.subset_interior_closure
    · simp
  have hm := hexit.inter (nullMeasurableSet_frontier_inter_ball_nonempty S.P A hmem hopen hregular x r)
  convert hm using 1
  ext ω
  by_cases hT : t < clusterExitTime (Λ ω) ρ <;> simp [A, hT]


/-- Before exit, fixed-point membership in an open frontier thickening is null
measurable. -/
theorem nullMeasurableSet_beforeExit_mem_frontier_thickening
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) (x : ℂ) (r : ℝ) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
      x ∈ thickening r (frontier (Λ ω t))} S.P := by
  have hm := nullMeasurableSet_beforeExit_frontier_inter_ball hγ hγ' hS h27 hρ hρ' ht Λ hΛ hexit x r
  convert hm using 1
  ext ω
  simp [mem_thickening_iff, Set.Nonempty, dist_comm]


/-- Membership in the closed thickening of a compact set is determined by
intersections with a decreasing countable family of open balls. -/
theorem mem_cthickening_iff_forall_inter_ball {K : Set ℂ} (hK : IsCompact K)
    {r : ℝ} (hr : 0 ≤ r) (x : ℂ) :
    x ∈ cthickening r K ↔ ∀ n : ℕ,
      (K ∩ ball x (r + 1 / ((n : ℝ) + 1))).Nonempty := by
  constructor
  · intro hx n
    rw [hK.cthickening_eq_biUnion_closedBall hr, mem_iUnion] at hx
    obtain ⟨y, hy⟩ := hx
    rw [mem_iUnion] at hy
    obtain ⟨hyK, hyball⟩ := hy
    refine ⟨y, hyK, ?_⟩
    rw [mem_closedBall, dist_comm] at hyball
    rw [mem_ball]
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro h
    obtain ⟨y, hyK, _⟩ := h 0
    have hne : K.Nonempty := ⟨y, hyK⟩
    have hdist : infDist x K ≤ r := by
      by_contra hnot
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < infDist x K - r by linarith)
      obtain ⟨z, hzK, hzball⟩ := h n
      have hzdist := infDist_le_dist_of_mem (x := x) hzK
      rw [mem_ball, dist_comm] at hzball
      linarith
    obtain ⟨z, hzK, hz⟩ := hK.exists_infDist_eq_dist hne x
    apply mem_cthickening_of_dist_le x z r K hzK
    linarith


/-- Before exit, fixed-point membership in a closed frontier thickening is
null measurable. -/
theorem nullMeasurableSet_beforeExit_mem_frontier_cthickening
    {𝒮 : SpaceFillingSLEModel} {γ ρ t : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hρ : 0 < ρ) (hρ' : ρ < 1) (ht : 0 < t)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P)
    (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
      x ∈ cthickening r (frontier (Λ ω t))} S.P := by
  have hm := NullMeasurableSet.iInter fun n : ℕ =>
    nullMeasurableSet_beforeExit_frontier_inter_ball hγ hγ' hS h27 hρ hρ' ht Λ hΛ hexit x
      (r + 1 / ((n : ℝ) + 1))
  apply hm.congr
  filter_upwards [hΛ] with ω hω
  by_cases hT : t < clusterExitTime (Λ ω) ρ
  · have hcompact := (coneFamily_frontier_compact_and_punctured hω hρ ht hT).1
    simp only [mem_iInter, mem_ofPred_eq, hT, true_and]
    exact propext (mem_cthickening_iff_forall_inter_ball hcompact hr x).symm
  · simp [hT]

end MatedCRT.Sec7
