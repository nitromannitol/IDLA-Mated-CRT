import MatedCRT.Proofs.Sec4.ConvergenceDivisible.DenseEvaluationMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EventMeasurabilityReduction

/-! # Convergence-event measurability from dense evaluations -/

namespace MatedCRT

open Set Filter MeasureTheory Metric HarmonicBalls Topology TopologicalSpace

/-- A measurable version on an event is determined by evaluations on a
spatially dense subset when sample paths are continuous on that event. -/
theorem exists_jointlyMeasurable_on_event_of_dense
    {Ω X : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X]
    [SecondCountableTopology X] [BorelSpace X]
    (U D : Set X) (hU : MeasurableSet U) (x₀ : X) (hx₀ : x₀ ∈ U)
    (hDU : D ⊆ U) (hdense : U ⊆ closure D)
    (E : Set Ω) (hE : MeasurableSet E) (f : Ω → X → ℝ)
    (hf : ∀ x ∈ D, AEMeasurable (fun ω => f ω x) P)
    (hc : ∀ᵐ ω ∂P, ω ∈ E → ContinuousOn (f ω) U) :
    ∃ g : Ω × X → ℝ, Measurable g ∧
      ∀ᵐ ω ∂P, ω ∈ E → ∀ x ∈ U, g (ω, x) = f ω x := by
  classical
  let F : Ω → X → ℝ := fun ω x => if ω ∈ E then f ω x else 0
  have hF : ∀ x ∈ D, AEMeasurable (fun ω => F ω x) P := by
    intro x hx
    refine ⟨fun ω => if ω ∈ E then (hf x hx).mk (fun ω => f ω x) ω else 0,
      (hf x hx).measurable_mk.ite hE measurable_const, ?_⟩
    filter_upwards [(hf x hx).ae_eq_mk] with ω hω
    simp [F, hω]
  have hFa : ∀ x ∈ U, AEMeasurable (fun ω => F ω x) P :=
    aemeasurable_on_event_of_ae_continuousOn_of_dense P U D hDU hdense E f hF hc
  let G : Ω → X → ℝ := fun ω x => if x ∈ U then F ω x else 0
  have hG : ∀ x, AEMeasurable (fun ω => G ω x) P := by
    intro x
    by_cases hx : x ∈ U
    · simpa [G, hx] using hFa x hx
    · simp [G, hx]
  have hGc : ∀ᵐ ω ∂P, ω ∈ E → ContinuousOn (G ω) U := by
    filter_upwards [hc] with ω hω hωE
    apply (hω hωE).congr
    intro x hx
    simp [G, F, hx, hωE]
  obtain ⟨g, hg, hgae⟩ := exists_jointlyMeasurable_on_event P U hU x₀ hx₀ E hE G hG hGc
  refine ⟨g, hg, ?_⟩
  filter_upwards [hgae] with ω hω hωE x hx
  simpa [G, F, hx, hωE] using hω hωE x hx

/-- Dense point evaluations suffice for measurable harmonic-ball membership. -/
theorem nullMeasurableSet_mem_coneFamily_of_dense_leastSupersolutions
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (Λ : Ω → ℝ → Set ℂ) (t : ℝ) (ht : 0 < t)
    (hfam : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    {C : Set ℂ} (hC : C.Countable) (hdense : Dense C) (hzero : (0 : ℂ) ∈ C)
    (hv : ∀ (n : ℕ) (z : ℂ), z ∈ C → AEMeasurable
      (fun ω => leastSupersolution (μ ω) ((n : ℝ) + 1) 0 t z) P)
    (x : ℂ) : NullMeasurableSet {ω | x ∈ Λ ω t} P := by
  classical
  apply nullMeasurableSet_mem_coneFamily_of_cluster_samples P μ Λ t ht hfam hC hdense hzero
  intro n z hzC
  by_cases hz : z ∈ ball (0 : ℂ) ((n : ℝ) + 1)
  · by_cases hz0 : z = 0
    · simp [cluster, hz0]
    · have h := nullMeasurableSet_lt
        (aemeasurable_const : AEMeasurable (fun _ : Ω => -t * greenFunction
          (ball 0 ((n : ℝ) + 1)) 0 z) P) (hv n z hzC)
      convert h using 1
      ext ω
      have hznorm : ‖z‖ < (n : ℝ) + 1 := by simpa only [mem_ball_zero_iff] using hz
      simp [cluster, hznorm, hz0]
  · have hznorm : ¬ ‖z‖ < (n : ℝ) + 1 := by simpa only [mem_ball_zero_iff] using hz
    simp [cluster, hznorm]

/-- The convergence error is measurable from continuum evaluations on one
countable dense set containing the origin. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_convergenceError_of_dense
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) {ρ t δ ε : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (hε : 0 < ε)
    (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite)
    {C : Set ℂ} (hC : C.Countable) (hdense : Dense C) (hzero : (0 : ℂ) ∈ C)
    (hv : ∀ (q : ℚ), 0 < (q : ℝ) → ∀ (n : ℕ) (z : ℂ), z ∈ C → AEMeasurable
      (fun ω => leastSupersolution (S.μ ω) ((n : ℝ) + 1) 0 q z) S.P)
    (hpoint : ∀ z ∈ C, AEMeasurable
      (fun ω => leastSupersolution (S.μ ω) ρ 0 t z) S.P) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
      δ < |rescaledMatedLeastSupersolution S ρ t ε ω x -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x|} S.P := by
  have hloc : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) := by
    filter_upwards [hS.isLQGMeasure] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hmem : ∀ (q : ℚ), 0 < (q : ℝ) → ∀ z : ℂ,
      NullMeasurableSet {ω | z ∈ Λ ω q} S.P := by
    intro q hq z
    exact nullMeasurableSet_mem_coneFamily_of_dense_leastSupersolutions S.P S.μ Λ q hq hΛ
      hC hdense hzero (hv q hq) z
  have hexit := nullMeasurableSet_lt_clusterExitTime_of_membership S.P S.μ Λ hΛ hloc hmem ρ t ht
  obtain ⟨E, hEsub, hE, hEae⟩ := hexit.exists_measurable_subset_ae_eq
  have hc : ∀ᵐ ω ∂S.P, ω ∈ E → ContinuousOn
      (fun x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) (ball 0 ρ) := by
    filter_upwards [hΛ] with ω hω hωE
    have hT : t < clusterExitTime (Λ ω) ρ := hEsub hωE
    exact continuousOn_const.mul
      ((coneFamily_leastSupersolution_continuous hω hρ ht hT).mono ball_subset_closedBall)
  have hdense' : ball (0 : ℂ) ρ ⊆ closure (C ∩ ball 0 ρ) := by
    simpa only [inter_comm] using hdense.open_subset_closure_inter isOpen_ball
  obtain ⟨f, hf, hfae⟩ := exists_jointlyMeasurable_on_event_of_dense S.P (ball (0 : ℂ) ρ)
    (C ∩ ball 0 ρ) isOpen_ball.measurableSet 0 (mem_ball_self hρ)
    inter_subset_right hdense' E hE
    (fun ω x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x)
    (fun x hx => aemeasurable_const.mul (hpoint x hx.1)) hc
  have hfc : ∀ᵐ ω ∂S.P, ω ∈ E → ContinuousOn (fun x => f (ω, x)) (ball 0 ρ) := by
    filter_upwards [hc, hfae] with ω hω hfω hωE
    exact (hω hωE).congr (fun x hx => hfω hωE x hx)
  have hm := hS.nullMeasurableSet_matedLeast_deviation_on_event hγ hγ' hε ρ t ht hlf
    isOpen_ball isBounded_ball f hf E hE hfc δ
  apply hm.congr
  filter_upwards [hEae, hfae] with ω he hfω
  apply propext
  have he' : ω ∈ E ↔ t < clusterExitTime (Λ ω) ρ := iff_of_eq he
  constructor
  · rintro ⟨hEω, x, hx, hd⟩
    exact ⟨he'.mp hEω, x, hx, by simpa [hfω hEω x hx] using hd⟩
  · rintro ⟨hT, x, hx, hd⟩
    have hEω := he'.mpr hT
    exact ⟨hEω, x, hx, by simpa [hfω hEω x hx] using hd⟩

/-- Dense pointwise measurability and the adjacent-cells property imply the
convergence-event measurability step. -/
theorem convergenceDivisibleEventMeasurable_of_dense_pointwise
    (𝒮 : SpaceFillingSLEModel) (hcell : AdjacentCellsMeetAeStep 𝒮)
    (C : Set ℂ) (hC : C.Countable) (hdense : Dense C) (hzero : (0 : ℂ) ∈ C)
    (hpoint : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (r t : ℝ), 0 < r → 0 < t → ∀ z ∈ C,
        AEMeasurable (fun ω => leastSupersolution (S.μ ω) r 0 t z) S.P) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  intro γ hγ hγ' ρ hρ _ Ω _ S hS Λ hΛ t δ ε ht _ hε
  have hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite := by
    filter_upwards [ae_locallyFinite_mult_of_adjacentCells hS hγ hγ' hcell] with ω hω
    exact hω ε hε
  apply hS.nullMeasurableSet_convergenceError_of_dense hγ hγ' hρ ht hε Λ hΛ hlf
    hC hdense hzero
  · intro q hq n z hz
    exact hpoint γ hγ hγ' Ω S hS ((n : ℝ) + 1) q (by positivity) hq z hz
  · exact hpoint γ hγ hγ' Ω S hS ρ t hρ ht

end MatedCRT
