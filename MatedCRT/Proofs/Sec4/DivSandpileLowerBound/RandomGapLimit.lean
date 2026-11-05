import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.RandomStrictGap

/-! # Coverage with a random obstacle-gap margin -/

namespace MatedCRT

open Filter Topology Set Metric MeasureTheory HarmonicBalls
open scoped ENNReal

/-- Localization on an increasing sequence of null-measurable events in a finite measure
space. The approximating events may themselves be arbitrary sets. -/
theorem tendsToOneOn_iUnion_of_monotone {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (F : ℕ → Set Ω) (E : ℝ → Set Ω)
    (hF : Monotone F) (hm : ∀ n, NullMeasurableSet (F n) P)
    (hE : ∀ n, TendsToOneOn P (F n) E) :
    TendsToOneOn P (⋃ n, F n) E := by
  let H : ℕ → Set Ω := fun n => (⋃ i, F i) \ F n
  have hHmeas : ∀ n, NullMeasurableSet (H n) P :=
    fun n => (NullMeasurableSet.iUnion hm).diff (hm n)
  have hHanti : Antitone H := by
    intro n m hnm ω hω
    exact ⟨hω.1, fun hmω => hω.2 (hF hnm hmω)⟩
  have hHinter : (⋂ n, H n) = ∅ := by
    ext ω
    simp only [mem_iInter, H, Set.mem_sdiff, mem_iUnion, mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨n, hn⟩ := (h 0).1
    exact (h n).2 hn
  have hHlim : Tendsto (fun n => P (H n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hHinter, measure_empty] using
      (tendsto_measure_iInter_atTop hHmeas hHanti ⟨0, measure_ne_top P _⟩)
  unfold TendsToOneOn
  apply ENNReal.tendsto_nhds_zero.2
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.1 hHlim) (e / 2) he2).exists
  have hen := (ENNReal.tendsto_nhds_zero.1 (hE n)) (e / 2) he2
  filter_upwards [hen] with ε hε
  have hsub : (⋃ i, F i) ∩ (E ε)ᶜ ⊆ H n ∪ (F n ∩ (E ε)ᶜ) := by
    intro ω hω
    by_cases hmem : ω ∈ F n
    · exact Or.inr ⟨hmem, hω.2⟩
    · exact Or.inl ⟨hω.1, hmem⟩
  calc
    P ((⋃ i, F i) ∩ (E ε)ᶜ) ≤ P (H n) + P (F n ∩ (E ε)ᶜ) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ e / 2 + e / 2 := add_le_add hn hε
    _ = e := ENNReal.add_halves e

/-- Coverage on the event of a positive, sample-dependent uniform obstacle gap. The
null-measurability requirement concerns only the threshold events for that gap; no
measurability is assumed for the discrete coverage events. -/
theorem random_positive_gap_coverage_in_probability (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t) (O : Set ℂ) (K : Ω → Set ℂ)
    (hO : O ⊆ ball 0 ρ) (hO' : O ⊆ closedBall 0 ρ \ {0})
    (hdist : 0 < infDist (0 : ℂ) O)
    (hmeas : ∀ n : ℕ, NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ K ω ⊆ O ∧
      ∀ x ∈ K ω, 1 / ((n : ℝ) + 1) ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} S.P) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ ∧ K ω ⊆ O ∧
      ∃ s : ℝ, 0 < s ∧ ∀ x ∈ K ω, s ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
      fun ε => {ω | K ω ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)} := by
  let F : ℕ → Set Ω := fun n => {ω | t < clusterExitTime (Λ ω) ρ ∧ K ω ⊆ O ∧
      ∀ x ∈ K ω, 1 / ((n : ℝ) + 1) ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
  have hmono : Monotone F := by
    intro n m hnm ω hω
    refine ⟨hω.1, hω.2.1, ?_⟩
    intro x hx
    apply le_trans _ (hω.2.2 x hx)
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hF : ∀ n, TendsToOneOn S.P (F n) (fun ε => {ω | K ω ⊆
      fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}) := by
    intro n
    exact random_strict_gap_coverage_in_probability 𝒮 h41 h33 γ hγ hγ' ρ hρ hρ'
      Ω S hS Λ hΛ t _ ht (by positivity) O K hO hO' hdist
  have hset : (⋃ n, F n) = {ω | t < clusterExitTime (Λ ω) ρ ∧ K ω ⊆ O ∧
      ∃ s : ℝ, 0 < s ∧ ∀ x ∈ K ω, s ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} := by
    ext ω
    simp only [mem_iUnion, F, mem_ofPred_eq]
    constructor
    · rintro ⟨n, hT, hK, hgap⟩
      exact ⟨hT, hK, 1 / ((n : ℝ) + 1), by positivity, hgap⟩
    · rintro ⟨hT, hK, s, hs, hgap⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hs
      exact ⟨n, hT, hK, fun x hx => hn.le.trans (hgap x hx)⟩
  rw [← hset]
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  exact tendsToOneOn_iUnion_of_monotone S.P F _ hmono hmeas hF

/-- On compact random sets, pointwise positivity and continuity supply the
sample-dependent uniform margin needed for coverage. -/
theorem compact_strict_gap_coverage_in_probability (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t) (O : Set ℂ) (K : Ω → Set ℂ)
    (hO : O ⊆ ball 0 ρ) (hO' : O ⊆ closedBall 0 ρ \ {0})
    (hdist : 0 < infDist (0 : ℂ) O)
    (hmeas : ∀ n : ℕ, NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ K ω ⊆ O ∧
      ∀ x ∈ K ω, 1 / ((n : ℝ) + 1) ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)} S.P) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ ∧ K ω ⊆ O ∧ IsCompact (K ω) ∧
      ContinuousOn (fun x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)) (K ω) ∧
      ∀ x ∈ K ω, 0 < S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
      fun ε => {ω | K ω ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)} := by
  have h := random_positive_gap_coverage_in_probability 𝒮 h41 h33 γ hγ hγ' ρ hρ hρ'
    Ω S hS Λ hΛ t ht O K hO hO' hdist hmeas
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono
  rintro ω ⟨⟨hT, hKO, hcompact, hcont, hpos⟩, hbad⟩
  refine ⟨⟨hT, hKO, ?_⟩, hbad⟩
  by_cases hne : (K ω).Nonempty
  · obtain ⟨x, hx, hmin⟩ := hcompact.exists_isMinOn hne hcont
    exact ⟨_, hpos x hx, fun y hy => hmin hy⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

end MatedCRT
