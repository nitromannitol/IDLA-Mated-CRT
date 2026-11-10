import MatedCRT.FirstPass.S1c.Measurability
import MatedCRT.FirstPass.S1c.Selection
import MatedCRT.FirstPass.Frozen.S1c

/-!
# The containment event of the fixed-time radius (Lemma 1, fleet note G-hT)

For a family of harmonic balls `Λ` of the cone field, `Λ_u ⊆ B̄_n` (integer `n`) is decided by the cluster identity
`Λ_u = int cl Λ_{B_R;0}(u)` at all integer radii `R` beyond the (finite) bound of `Λ_u`, as a countable Boolean
combination of the threshold events of `nullMeasurableSet_threshold`. The measurable radius then comes from
`exists_measurable_radius_of_null_measurable`. Only the three frozen external inputs enter.
-/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory HarmonicBalls

/-- Local finiteness gives finite mass on closed balls (finite on compacts, covered by finitely many neighbourhoods of
finite mass; the bridge `IsLocallyFiniteMeasure → IsFiniteMeasureOnCompacts` is not an instance in this Mathlib). -/
theorem measure_closedBall_lt_top_of_isLocallyFinite (ν : Measure ℂ) [IsLocallyFiniteMeasure ν] (r : ℝ) :
    ν (closedBall (0 : ℂ) r) < ⊤ := by
  have hloc : ∀ x : ℂ, ∃ U ∈ 𝓝 x, ν U < ⊤ := fun x => Measure.finiteAt_nhds ν x
  choose U hU hνU using hloc
  obtain ⟨t, -, ht⟩ := (isCompact_closedBall (0 : ℂ) r).elim_nhds_subcover U (fun x _ => hU x)
  calc ν (closedBall (0 : ℂ) r) ≤ ν (⋃ x ∈ t, U x) := measure_mono ht
    _ ≤ ∑ x ∈ t, ν (U x) := measure_biUnion_finset_le t U
    _ < ⊤ := ENNReal.sum_lt_top.2 fun x _ => hνU x

/-- The deterministic containment identity: for a harmonic-ball family `Λ` (its bound `Λ_u ⊆ B̄_r` and the obstacle
characterization), `Λ_u ⊆ B̄_n` iff for all integer radii `R ≥ N` no Gaussian rational point of the cluster `Λ_{B_R;0}(u)`
has modulus `> n`. -/
theorem containment_iff_exists_forall_cluster {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {u : ℝ} (hu : 0 < u)
    (hfam : IsConeHarmonicBallFamily μ Λ) (hF3 : FrozenDiskGreenNonnegCont) (n : ℕ) :
    Λ u ⊆ closedBall (0 : ℂ) (n : ℝ) ↔
      ∃ N : ℕ, ∀ R : ℕ, N ≤ R → ∀ p ∈ ratComplex, (n : ℝ) < ‖p‖ → p ∉ cluster μ (R : ℝ) 0 u := by
  obtain ⟨r, hr⟩ := (hfam.2.1.isBounded u hu).subset_closedBall (0 : ℂ)
  set M : ℕ := ⌈r⌉₊ with hMdef
  have hM : r ≤ (M : ℝ) := Nat.le_ceil r
  have hsubM : Λ u ⊆ ball (0 : ℂ) ((M : ℝ) + 1) := by
    intro x hx
    have h1 : ‖x‖ ≤ r := mem_closedBall_zero_iff.1 (hr hx)
    rw [mem_ball_zero_iff]
    linarith
  have key : ∀ R : ℕ, M + 2 ≤ R →
      (Λ u ⊆ closedBall (0 : ℂ) (n : ℝ) ↔ ∀ p ∈ ratComplex, (n : ℝ) < ‖p‖ → p ∉ cluster μ (R : ℝ) 0 u) := by
    intro R hR
    have hR' : ((M + 2 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    push_cast at hR'
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hob := hfam.2.2 u ((M : ℝ) + 1) hu (by linarith) hsubM (R : ℝ) (by linarith)
    rw [hob.1]
    exact interior_cluster_subset_closedBall_iff μ n hob.2.1 (hF3 (R : ℝ) (by linarith)).2
  constructor
  · intro h
    exact ⟨M + 2, fun R hR => (key R hR).1 h⟩
  · rintro ⟨N, hN⟩
    exact (key (N + (M + 2)) (by omega)).2 (hN _ (by omega))

/-- The rational points of the cluster event are countably many: the threshold family indexed by `ratComplex`. -/
theorem ratComplex_countable : ratComplex.Countable :=
  Set.countable_range _

/-- A single cluster point: the event that `p` is not in the cluster at radius `R0` is null-measurable (the cluster
membership off the pole is the threshold event; outside the ball `p` is never in the cluster). -/
theorem nullMeasurableSet_not_mem_cluster {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    {μ : Ω → Measure ℂ} {u R0 : ℝ} (hu : 0 < u) (hR0 : 0 ≤ R0)
    (hloc : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R0) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R0)
    (hdense : ∀ φ ∈ nonnegTest R0, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R0,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    {p : ℂ} (hp0 : p ≠ 0) :
    NullMeasurableSet {ω | p ∉ cluster (μ ω) R0 0 u} P := by
  by_cases hpb : p ∈ ball (0 : ℂ) R0
  · have hpos : 0 < R0 := lt_of_le_of_lt (norm_nonneg p) (mem_ball_zero_iff.1 hpb)
    have hG := (hF3 R0 hpos).1
    have hp : p ∈ closedBall (0 : ℂ) R0 := ball_subset_closedBall hpb
    have hset : {ω | p ∉ cluster (μ ω) R0 0 u} =
        {ω | -u * greenFunction (ball (0 : ℂ) R0) 0 p < leastSupersolution (μ ω) R0 0 u p}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, mem_cluster_iff_of_ne hp0, hpb, true_and]
    rw [hset]
    exact (nullMeasurableSet_threshold hF1 hR0 hu hloc hmeas φs hφs hdense hG hp hp0).compl
  · have hset : {ω | p ∉ cluster (μ ω) R0 0 u} = univ := by
      ext ω
      exact ⟨fun _ => mem_univ ω, fun _ h => hpb ((mem_cluster_iff_of_ne hp0).1 h).1⟩
    rw [hset]
    exact MeasurableSet.univ.nullMeasurableSet

/-- The event that no rational point of modulus `> n` lies in the cluster at integer radius `R`. -/
theorem nullMeasurableSet_forall_not_mem_cluster {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    {μ : Ω → Measure ℂ} {u : ℝ} (hu : 0 < u) (n : ℕ)
    (hloc : ∀ R : ℕ, ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) (R : ℝ)) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P)
    (φs : ℕ → ℕ → ℂ → ℝ) (hφs : ∀ (R : ℕ) (k : ℕ), φs R k ∈ nonnegTest (R : ℝ))
    (hdense : ∀ R : ℕ, ∀ φ ∈ nonnegTest (R : ℝ), ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) (R : ℝ),
        |φ x - φs R k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs R k) x| < ε)
    (R : ℕ) :
    NullMeasurableSet {ω | ∀ p ∈ ratComplex, (n : ℝ) < ‖p‖ → p ∉ cluster (μ ω) (R : ℝ) 0 u} P := by
  have : Countable ↥ratComplex := ratComplex_countable.to_subtype
  have hset : {ω | ∀ p ∈ ratComplex, (n : ℝ) < ‖p‖ → p ∉ cluster (μ ω) (R : ℝ) 0 u} =
      ⋂ p : ↥ratComplex, {ω | (n : ℝ) < ‖(p : ℂ)‖ → (p : ℂ) ∉ cluster (μ ω) (R : ℝ) 0 u} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, Subtype.forall]
  rw [hset]
  refine NullMeasurableSet.iInter fun p => ?_
  by_cases hnp : (n : ℝ) < ‖(p : ℂ)‖
  · have hp0 : (p : ℂ) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnp
      exact absurd hnp (not_lt.2 (Nat.cast_nonneg n))
    have hset' : {ω | (n : ℝ) < ‖(p : ℂ)‖ → (p : ℂ) ∉ cluster (μ ω) (R : ℝ) 0 u} =
        {ω | (p : ℂ) ∉ cluster (μ ω) (R : ℝ) 0 u} := by
      ext ω
      simp [hnp]
    rw [hset']
    exact nullMeasurableSet_not_mem_cluster hF1 hF3 hu (Nat.cast_nonneg R) (hloc R) hmeas (φs R) (hφs R)
      (hdense R) hp0
  · have hset' : {ω | (n : ℝ) < ‖(p : ℂ)‖ → (p : ℂ) ∉ cluster (μ ω) (R : ℝ) 0 u} = univ := by
      ext ω
      simp [hnp]
    rw [hset']
    exact MeasurableSet.univ.nullMeasurableSet

/-- The containment event `{ω | ∃ N, ∀ R ≥ N, Φ_R(ω)}` is null-measurable (countable union and intersection). -/
theorem nullMeasurableSet_exists_forall_cluster {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    {μ : Ω → Measure ℂ} {u : ℝ} (hu : 0 < u) (n : ℕ)
    (hloc : ∀ R : ℕ, ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) (R : ℝ)) < ⊤)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P)
    (φs : ℕ → ℕ → ℂ → ℝ) (hφs : ∀ (R : ℕ) (k : ℕ), φs R k ∈ nonnegTest (R : ℝ))
    (hdense : ∀ R : ℕ, ∀ φ ∈ nonnegTest (R : ℝ), ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) (R : ℝ),
        |φ x - φs R k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs R k) x| < ε) :
    NullMeasurableSet {ω | ∃ N : ℕ, ∀ R : ℕ, N ≤ R → ∀ p ∈ ratComplex,
      (n : ℝ) < ‖p‖ → p ∉ cluster (μ ω) (R : ℝ) 0 u} P := by
  have hset : {ω | ∃ N : ℕ, ∀ R : ℕ, N ≤ R → ∀ p ∈ ratComplex,
        (n : ℝ) < ‖p‖ → p ∉ cluster (μ ω) (R : ℝ) 0 u} =
      ⋃ N : ℕ, ⋂ R : ℕ, {ω | N ≤ R → ∀ p ∈ ratComplex, (n : ℝ) < ‖p‖ → p ∉ cluster (μ ω) (R : ℝ) 0 u} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
  rw [hset]
  refine NullMeasurableSet.iUnion fun N => NullMeasurableSet.iInter fun R => ?_
  by_cases hNR : N ≤ R
  · have hset' : {ω | N ≤ R → ∀ p ∈ ratComplex, (n : ℝ) < ‖p‖ → p ∉ cluster (μ ω) (R : ℝ) 0 u} =
        {ω | ∀ p ∈ ratComplex, (n : ℝ) < ‖p‖ → p ∉ cluster (μ ω) (R : ℝ) 0 u} := by
      ext ω
      simp [hNR]
    rw [hset']
    exact nullMeasurableSet_forall_not_mem_cluster hF1 hF3 hu n hloc hmeas φs hφs hdense R
  · have hset' : {ω | N ≤ R → ∀ p ∈ ratComplex, (n : ℝ) < ‖p‖ → p ∉ cluster (μ ω) (R : ℝ) 0 u} = univ := by
      ext ω
      simp [hNR]
    rw [hset']
    exact MeasurableSet.univ.nullMeasurableSet

/-- The fixed-time radius statement, from the three frozen external inputs (Lusin, field-level measurability of the
LQG measure, disc Green function). The conclusion is the body of `FixedTimeRadiusStep` (FirstPass/S1c.lean). -/
theorem fixedTimeRadiusBody_of_frozen (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) →
      ∀ u : ℝ, 0 < u → ∃ M : Ω → ℝ, Measurable M ∧ ∀ᵐ ω ∂P, Λ ω u ⊆ closedBall 0 (M ω) := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone Λ hfam u hu
  have : IsProbabilityMeasure P := hcone.1
  have hL : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
  have hloc : ∀ R : ℕ, ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) (R : ℝ)) < ⊤ := fun R =>
    hL.mono fun ω h => by
      have := h.isLocallyFiniteMeasure
      exact measure_closedBall_lt_top_of_isLocallyFinite (μ ω) (R : ℝ)
  choose φs hφs hdense using fun R : ℕ => exists_dense_nonnegTest_family (R : ℝ)
  have hmeas := hF2 γ hγ0 hγ2 Ω P hC hcirc μ hcone
  have hS : ∀ n : ℕ, NullMeasurableSet {ω | Λ ω u ⊆ closedBall (0 : ℂ) (n : ℝ)} P := by
    intro n
    have hset : {ω | Λ ω u ⊆ closedBall (0 : ℂ) (n : ℝ)} =ᵐ[P]
        {ω | ∃ N : ℕ, ∀ R : ℕ, N ≤ R → ∀ p ∈ ratComplex,
          (n : ℝ) < ‖p‖ → p ∉ cluster (μ ω) (R : ℝ) 0 u} := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hfam] with ω hω
      exact containment_iff_exists_forall_cluster hu hω hF3 n
    exact (nullMeasurableSet_exists_forall_cluster hF1 hF3 hu n hloc hmeas φs hφs hdense).congr hset.symm
  have hbdd : ∀ᵐ ω ∂P, ∃ n : ℕ, Λ ω u ⊆ closedBall (0 : ℂ) (n : ℝ) := hfam.mono fun ω hω => by
    obtain ⟨r, hr⟩ := (hω.2.1.isBounded u hu).subset_closedBall (0 : ℂ)
    exact ⟨⌈r⌉₊, hr.trans (closedBall_subset_closedBall (Nat.le_ceil r))⟩
  exact exists_measurable_radius_of_null_measurable P (fun ω => Λ ω u) hS hbdd

end MatedCRT
