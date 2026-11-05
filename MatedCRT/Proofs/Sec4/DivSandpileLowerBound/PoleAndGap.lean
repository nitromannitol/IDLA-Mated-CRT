import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.PoleProbability
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.RandomGapLimit

/-! # Combining the pole barrier and strict obstacle-gap coverage -/

namespace MatedCRT

open Filter Topology Set Metric MeasureTheory _root_.HarmonicBalls

/-- Coverage on two events implies coverage on their union. -/
theorem TendsToOneOn.union {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A B : Set Ω} {E : ℝ → Set Ω} (hA : TendsToOneOn P A E)
    (hB : TendsToOneOn P B E) : TendsToOneOn P (A ∪ B) E := by
  unfold TendsToOneOn at *
  have hsum := hA.add hB
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) ?_
  intro ε
  calc
    P ((A ∪ B) ∩ (E ε)ᶜ) = P ((A ∩ (E ε)ᶜ) ∪ (B ∩ (E ε)ᶜ)) := by rw [union_inter_distrib_right]
    _ ≤ P (A ∩ (E ε)ᶜ) + P (B ∩ (E ε)ᶜ) := measure_union_le _ _

/-- Countable localization without requiring the original events to be monotone. -/
theorem tendsToOneOn_iUnion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (F : ℕ → Set Ω) (E : ℝ → Set Ω)
    (hm : ∀ n, NullMeasurableSet (F n) P)
    (hE : ∀ n, TendsToOneOn P (F n) E) : TendsToOneOn P (⋃ n, F n) E := by
  let G : ℕ → Set Ω := fun n => ⋃ i ∈ Finset.range (n + 1), F i
  have hstep : ∀ n, G (n + 1) = G n ∪ F (n + 1) := by
    intro n
    ext ω
    simp only [G, Finset.mem_range, mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi, hω⟩
      by_cases heq : i = n + 1
      · exact Or.inr (heq ▸ hω)
      · exact Or.inl ⟨i, by omega, hω⟩
    · rintro (⟨i, hi, hω⟩ | hω)
      · exact ⟨i, by omega, hω⟩
      · exact ⟨n + 1, by omega, hω⟩
  have hmono : Monotone G := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hstep]
    exact subset_union_left
  have hmeas : ∀ n, NullMeasurableSet (G n) P := by
    intro n
    apply NullMeasurableSet.iUnion
    intro i
    by_cases hi : i ∈ Finset.range (n + 1)
    · simpa only [hi, iUnion_true] using hm i
    · simpa only [hi, iUnion_false] using (MeasurableSet.empty.nullMeasurableSet : NullMeasurableSet ∅ P)
  have hprob : ∀ n, TendsToOneOn P (G n) E := by
    intro n
    induction n with
    | zero => simpa [G] using hE 0
    | succ n ih =>
      rw [hstep]
      exact ih.union (hE (n + 1))
  have hset : (⋃ n, G n) = ⋃ n, F n := by
    ext ω
    simp only [mem_iUnion, G]
    constructor
    · rintro ⟨n, i, _, hi⟩
      exact ⟨i, hi⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, n, Finset.mem_range.mpr (Nat.lt_succ_self n), hn⟩
  rw [← hset]
  exact tendsToOneOn_iUnion_of_monotone P G E hmono hmeas hprob

/-- A random set in the inner comparison disc is covered in probability on
events with a continuum lower bound and a fixed positive obstacle gap away
from a deterministic neighbourhood of the pole. -/
theorem pole_and_gap_coverage_in_probability (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t L : ℝ) (ht : 0 < t) (hL : L < 0) (K : Ω → Set ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℝ, 0 < s → TendsToOneOn S.P
      {ω | t < clusterExitTime (Λ ω) ρ ∧ K ω ⊆ closedBall 0 (ρ / 2) ∧
        (∀ x ∈ ball (0 : ℂ) ρ, L + 2 ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
        ∀ x ∈ K ω \ ball 0 r, s ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
      (fun ε => {ω | K ω ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}) := by
  obtain ⟨r₀, hr₀, hpole⟩ := pole_coverage_on_lower_bound 𝒮 h41 h33 h28 γ hγ hγ'
    ρ hρ hρ' Ω S hS Λ hΛ t L ht hL
  let r := min r₀ (ρ / 4)
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hrr : r ≤ r₀ := min_le_left _ _
  have hrρ : r ≤ ρ / 4 := min_le_right _ _
  let O : Set ℂ := closedBall 0 (ρ / 2) \ ball 0 r
  have hO : O ⊆ ball (0 : ℂ) ρ := by
    intro x hx
    change dist x 0 < ρ
    have hx' : dist x 0 ≤ ρ / 2 := hx.1
    linarith
  have hO' : O ⊆ closedBall 0 ρ \ {0} := by
    intro x hx
    have hxlo : r ≤ dist x 0 := le_of_not_gt hx.2
    refine ⟨ball_subset_closedBall (hO hx), ?_⟩
    simp only [mem_singleton_iff]
    intro hx0
    subst x
    simp only [dist_self] at hxlo
    linarith
  have hOne : O.Nonempty := by
    refine ⟨(r : ℂ), ?_, ?_⟩
    · change dist (r : ℂ) 0 ≤ ρ / 2
      simpa using (show |r| ≤ ρ / 2 by rw [abs_of_pos hr]; linarith)
    · change ¬ dist (r : ℂ) 0 < r
      simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, lt_self_iff_false, not_false_eq_true]
  have hOdist : 0 < infDist (0 : ℂ) O := by
    apply lt_of_lt_of_le hr
    apply (le_infDist hOne).2
    intro x hx
    have hlo : r ≤ dist x 0 := le_of_not_gt hx.2
    simpa only [dist_comm] using hlo
  refine ⟨r, hr, ?_⟩
  intro s hs
  have hgap := random_inter_strict_gap_coverage_in_probability 𝒮 h41 h33 γ hγ hγ' ρ hρ hρ'
    Ω S hS Λ hΛ t s ht hs O K hO hO' hOdist
  unfold TendsToOneOn at hpole hgap ⊢
  have hsum := hpole.add hgap
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply le_trans ?_ (measure_union_le _ _)
  apply measure_mono
  rintro ω ⟨⟨hT, hK, hlower, hbound⟩, hbad⟩
  by_cases hp : ball (0 : ℂ) r₀ ⊆ fillCells ε (S.η ω)
      (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)
  · right
    refine ⟨⟨hT, ?_⟩, ?_⟩
    · intro x hx
      apply hbound x
      exact ⟨hx.1, hx.2.2⟩
    · intro hcov
      apply hbad
      intro x hx
      by_cases hxr : x ∈ ball (0 : ℂ) r
      · exact hp (ball_subset_ball hrr hxr)
      · exact hcov ⟨hx, hK hx, hxr⟩
  · exact Or.inl ⟨⟨hT, hlower⟩, hp⟩

/-- The fixed obstacle-gap threshold can be replaced by a sample-dependent
positive margin, provided its threshold events are null measurable. -/
theorem pole_and_positive_gap_coverage_in_probability (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t L : ℝ) (ht : 0 < t) (hL : L < 0) (K : Ω → Set ℂ) :
    ∃ r : ℝ, 0 < r ∧
      ((∀ n : ℕ, NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
        K ω ⊆ closedBall 0 (ρ / 2) ∧
        (∀ x ∈ ball (0 : ℂ) ρ, L + 2 ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
        ∀ x ∈ K ω \ ball 0 r, 1 / ((n : ℝ) + 1) ≤
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} S.P) →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ ∧
        K ω ⊆ closedBall 0 (ρ / 2) ∧
        (∀ x ∈ ball (0 : ℂ) ρ, L + 2 ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
        ∃ s : ℝ, 0 < s ∧ ∀ x ∈ K ω \ ball 0 r,
          s ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
      (fun ε => {ω | K ω ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)})) := by
  obtain ⟨r, hr, hcov⟩ := pole_and_gap_coverage_in_probability 𝒮 h41 h33 h28 γ hγ hγ'
    ρ hρ hρ' Ω S hS Λ hΛ t L ht hL K
  refine ⟨r, hr, ?_⟩
  intro hmeas
  let F : ℕ → Set Ω := fun n => {ω | t < clusterExitTime (Λ ω) ρ ∧
    K ω ⊆ closedBall 0 (ρ / 2) ∧
    (∀ x ∈ ball (0 : ℂ) ρ, L + 2 ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
    ∀ x ∈ K ω \ ball 0 r, 1 / ((n : ℝ) + 1) ≤
      S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
  have hmono : Monotone F := by
    intro n m hnm ω hω
    refine ⟨hω.1, hω.2.1, hω.2.2.1, ?_⟩
    intro x hx
    apply le_trans _ (hω.2.2.2 x hx)
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hF : ∀ n, TendsToOneOn S.P (F n) (fun ε => {ω | K ω ⊆
      fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}) := by
    intro n
    exact hcov _ (by positivity)
  have hset : (⋃ n, F n) = {ω | t < clusterExitTime (Λ ω) ρ ∧
      K ω ⊆ closedBall 0 (ρ / 2) ∧
      (∀ x ∈ ball (0 : ℂ) ρ, L + 2 ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
      ∃ s : ℝ, 0 < s ∧ ∀ x ∈ K ω \ ball 0 r,
        s ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} := by
    ext ω
    simp only [mem_iUnion, F, mem_ofPred_eq]
    constructor
    · rintro ⟨n, hT, hK, hlower, hgap⟩
      exact ⟨hT, hK, hlower, 1 / ((n : ℝ) + 1), by positivity, hgap⟩
    · rintro ⟨hT, hK, hlower, s, hs, hgap⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hs
      exact ⟨n, hT, hK, hlower, fun x hx => hn.le.trans (hgap x hx)⟩
  rw [← hset]
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  exact tendsToOneOn_iUnion_of_monotone S.P F _ hmono hmeas hF

/-- A compact set with a continuous, strictly positive obstacle gap away from
the pole belongs to one event in any positive-radius exhaustion. -/
theorem exists_pole_index_of_compact_strict_gap
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {ρ t : ℝ} (c : ℝ) (K : Set ℂ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hΛ : IsConeHarmonicBallFamily μ Λ) (hρ : 0 < ρ) (ht : 0 < t)
    (hT : t < clusterExitTime Λ ρ) (hK : IsCompact K)
    (hcont : ContinuousOn (fun x => c * leastSupersolution μ ρ 0 t x -
      (-t * c * greenFunction (ball 0 ρ) 0 x)) (K \ {0}))
    (hpos : ∀ x ∈ K \ {0}, 0 < c * leastSupersolution μ ρ 0 t x -
      (-t * c * greenFunction (ball 0 ρ) 0 x)) :
    ∃ n : ℕ, (∀ x ∈ ball (0 : ℂ) ρ, -((n : ℝ) + 3) + 2 ≤
      c * leastSupersolution μ ρ 0 t x) ∧
      ∃ s : ℝ, 0 < s ∧ ∀ x ∈ K \ ball 0 (r n),
        s ≤ c * leastSupersolution μ ρ 0 t x - (-t * c * greenFunction (ball 0 ρ) 0 x) := by
  obtain ⟨L, _, hL⟩ := exists_lower_bound_scaled_leastSupersolution c hΛ hρ ht hT
  obtain ⟨n, hn⟩ := exists_nat_gt (-L)
  refine ⟨n, ?_, ?_⟩
  · intro x hx
    have := hL x hx
    linarith
  · let A := K \ ball (0 : ℂ) (r n)
    have hA : IsCompact A := hK.diff isOpen_ball
    have hsub : A ⊆ K \ {0} := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      simp only [mem_singleton_iff]
      intro hx0
      subst x
      exact hx.2 (mem_ball_self (hr n))
    by_cases hne : A.Nonempty
    · obtain ⟨x, hx, hmin⟩ := hA.exists_isMinOn hne (hcont.mono hsub)
      exact ⟨_, hpos x (hsub hx), fun y hy => hmin hy⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim

/-- Countably many pole radii and gap thresholds yield coverage on their union.
Null measurability is required only for the threshold events. -/
theorem pole_and_gap_coverage_on_exhaustion (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t) (K : Ω → Set ℂ) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧
      ((∀ n m : ℕ, NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
        K ω ⊆ closedBall 0 (ρ / 2) ∧
        (∀ x ∈ ball (0 : ℂ) ρ, -((n : ℝ) + 3) + 2 ≤
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
        ∀ x ∈ K ω \ ball 0 (r n), 1 / ((m : ℝ) + 1) ≤
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} S.P) →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ ∧
        K ω ⊆ closedBall 0 (ρ / 2) ∧ ∃ n : ℕ,
        (∀ x ∈ ball (0 : ℂ) ρ, -((n : ℝ) + 3) + 2 ≤
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
        ∃ s : ℝ, 0 < s ∧ ∀ x ∈ K ω \ ball 0 (r n),
          s ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
      (fun ε => {ω | K ω ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)})) := by
  have hchoose : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧
      ((∀ m : ℕ, NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
        K ω ⊆ closedBall 0 (ρ / 2) ∧
        (∀ x ∈ ball (0 : ℂ) ρ, -((n : ℝ) + 3) + 2 ≤
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
        ∀ x ∈ K ω \ ball 0 r, 1 / ((m : ℝ) + 1) ≤
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} S.P) →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ ∧
        K ω ⊆ closedBall 0 (ρ / 2) ∧
        (∀ x ∈ ball (0 : ℂ) ρ, -((n : ℝ) + 3) + 2 ≤
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
        ∃ s : ℝ, 0 < s ∧ ∀ x ∈ K ω \ ball 0 r,
          s ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
      (fun ε => {ω | K ω ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)})) := by
    intro n
    exact pole_and_positive_gap_coverage_in_probability 𝒮 h41 h33 h28 γ hγ hγ' ρ hρ hρ'
      Ω S hS Λ hΛ t (-((n : ℝ) + 3)) ht (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) K
  choose r hr hcov using hchoose
  refine ⟨r, hr, ?_⟩
  intro hmeas
  let F : ℕ → Set Ω := fun n => {ω | t < clusterExitTime (Λ ω) ρ ∧
    K ω ⊆ closedBall 0 (ρ / 2) ∧
    (∀ x ∈ ball (0 : ℂ) ρ, -((n : ℝ) + 3) + 2 ≤
      S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
    ∃ s : ℝ, 0 < s ∧ ∀ x ∈ K ω \ ball 0 (r n),
      s ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
  have hFmeas : ∀ n, NullMeasurableSet (F n) S.P := by
    intro n
    let H : ℕ → Set Ω := fun m => {ω | t < clusterExitTime (Λ ω) ρ ∧
      K ω ⊆ closedBall 0 (ρ / 2) ∧
      (∀ x ∈ ball (0 : ℂ) ρ, -((n : ℝ) + 3) + 2 ≤
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
      ∀ x ∈ K ω \ ball 0 (r n), 1 / ((m : ℝ) + 1) ≤
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
    have hset : F n = ⋃ m, H m := by
      ext ω
      simp only [F, H, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hT, hK, hlower, s, hs, hgap⟩
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hs
        exact ⟨m, hT, hK, hlower, fun x hx => hm.le.trans (hgap x hx)⟩
      · rintro ⟨m, hT, hK, hlower, hgap⟩
        exact ⟨hT, hK, hlower, 1 / ((m : ℝ) + 1), by positivity, hgap⟩
    rw [hset]
    exact NullMeasurableSet.iUnion (hmeas n)
  have hFprob : ∀ n, TendsToOneOn S.P (F n) (fun ε => {ω | K ω ⊆
      fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}) :=
    fun n => hcov n (hmeas n)
  have hset : (⋃ n, F n) = {ω | t < clusterExitTime (Λ ω) ρ ∧
      K ω ⊆ closedBall 0 (ρ / 2) ∧ ∃ n : ℕ,
      (∀ x ∈ ball (0 : ℂ) ρ, -((n : ℝ) + 3) + 2 ≤
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
      ∃ s : ℝ, 0 < s ∧ ∀ x ∈ K ω \ ball 0 (r n),
        s ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} := by
    ext ω
    simp only [F, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨n, hT, hK, hlower, hgap⟩
      exact ⟨hT, hK, n, hlower, hgap⟩
    · rintro ⟨hT, hK, n, hlower, hgap⟩
      exact ⟨n, hT, hK, hlower, hgap⟩
  rw [← hset]
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  exact tendsToOneOn_iUnion S.P F _ hFmeas hFprob

/-- Compact strict-gap coverage, including the pole. The threshold-event
measurability is explicit and the target set itself need not be measurable. -/
theorem pole_and_compact_strict_gap_coverage_in_probability (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t) (K : Ω → Set ℂ) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧
      ((∀ n m : ℕ, NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
        K ω ⊆ closedBall 0 (ρ / 2) ∧
        (∀ x ∈ ball (0 : ℂ) ρ, -((n : ℝ) + 3) + 2 ≤
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) ∧
        ∀ x ∈ K ω \ ball 0 (r n), 1 / ((m : ℝ) + 1) ≤
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} S.P) →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ ∧
        K ω ⊆ closedBall 0 (ρ / 2) ∧ IsCompact (K ω) ∧
        ContinuousOn (fun x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)) (K ω \ {0}) ∧
        ∀ x ∈ K ω \ {0}, 0 < S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
      (fun ε => {ω | K ω ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)})) := by
  obtain ⟨r, hr, hcov⟩ := pole_and_gap_coverage_on_exhaustion 𝒮 h41 h33 h28 γ hγ hγ'
    ρ hρ hρ' Ω S hS Λ hΛ t ht K
  refine ⟨r, hr, ?_⟩
  intro hmeas
  have h := hcov hmeas
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono_ae
  filter_upwards [hΛ] with ω hΛω
  rintro ⟨⟨hT, hKsub, hK, hcont, hpos⟩, hbad⟩
  have hex := exists_pole_index_of_compact_strict_gap (S.c₀ / 6) (K ω) r hr
    hΛω hρ ht hT hK hcont hpos
  exact ⟨⟨hT, hKsub, hex⟩, hbad⟩

end MatedCRT
