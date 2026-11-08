import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxPathLimit
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxClockVersion

/-!
# Lemma 3.4 (item 4): joint measurability of the approximate path functional, and the expectations in the environment

Second clause of `LBMPathFunctionalMeasurableStep` (paper argument, `docs/campaign/GAPS-SEC3.md` item 4):

* a bounded Lipschitz functional of a continuous path depending measurably on a parameter is measurable in the parameter, when the
  evaluations are measurable in the parameter (grid approximation, `measurable_boundedLipschitz_comp`);
* the approximate clock of a quantum cone has a version `G`, measurable in `(ω, b, t)`, which is strictly increasing and continuous in
  `t` for every `(ω, b)`: it is replaced by the identity in time on a measurable null set of environments
  (`exists_measurable_clockApprox_modification`);
* hence the functional of the approximate path is jointly measurable in `(ω, b)`, and the expectation `ω ↦ ∫ F (path) dν(b)` is
  measurable by Fubini (`measurable_integral_boundedLipschitz_approxPath`).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal

/-- **Grid measurability with a parameter.** A bounded Lipschitz functional of a continuous path that depends measurably on a
parameter is measurable in the parameter, when the evaluations are measurable in the parameter. -/
theorem measurable_boundedLipschitz_comp {α : Type*} [MeasurableSpace α] {F : (ℝ≥0 → ℂ) → ℝ}
    (hF : IsBoundedLipschitzPathFunctional F) {X : α → ℝ≥0 → ℂ}
    (hX : ∀ t : ℝ≥0, Measurable fun p : α => X p t) (hcont : ∀ p : α, Continuous (X p)) :
    Measurable fun p : α => F (X p) := by
  have hLip := hF
  obtain ⟨-, L, hL⟩ := hLip
  have hmeasN : ∀ N : ℕ, Measurable fun p : α =>
      F (stepPath N fun j : ℕ => X p ((j : ℝ≥0) / (N : ℝ≥0))) := by
    intro N
    have hvec : Measurable fun p : α => fun j : ℕ => X p ((j : ℝ≥0) / (N : ℝ≥0)) :=
      measurable_pi_iff.mpr fun j => hX _
    exact (continuous_boundedLipschitz_stepPath hF N).measurable.comp hvec
  refine measurable_of_tendsto_metrizable hmeasN ?_
  rw [tendsto_pi_nhds]
  intro p
  have hd := (tendsto_localUniformDist_gridStep (hcont p)).const_mul L
  rw [mul_zero] at hd
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_) hd
  rw [Real.dist_eq]
  exact hL _ _

/-- **A jointly measurable approximate clock, strictly increasing and continuous in time for every environment and path.** The
time-joint version of the approximate clock of a quantum cone is replaced by the identity in time on a measurable null set of
environments, where it is not yet the approximate clock. -/
theorem exists_measurable_clockApprox_modification {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) (k : ℕ) :
    ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      (∀ (ω : Ω) (b : ContinuousPath ℂ), StrictMono fun t : ℝ≥0 => G ((ω, b), t)) ∧
      (∀ (ω : Ω) (b : ContinuousPath ℂ), Continuous fun t : ℝ≥0 => G ((ω, b), t)) ∧
      ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (t : ℝ≥0),
        G ((ω, b), t) = lqgClockApprox γ (hcirc ω) (dyadicScale k) b t := by
  classical
  obtain ⟨G0, hG0, hae0⟩ := IsQuantumCone.exists_measurable_clockApprox_time_version hcone k
  have hgood : ∀ᵐ ω ∂P, (∀ (b : ContinuousPath ℂ) (t : ℝ≥0),
      G0 ((ω, b), t) = lqgClockApprox γ (hcirc ω) (dyadicScale k) b t) ∧
      Continuous (hcirc ω (dyadicScale k)) := by
    filter_upwards [hae0, hcone.ae_continuousOn_circle] with ω h1 h2
    refine ⟨h1, ?_⟩
    apply continuousOn_univ.mp
    apply h2.comp (continuous_const.prodMk continuous_id).continuousOn
    intro z _
    exact ⟨dyadicScale_pos k, mem_univ z⟩
  obtain ⟨N, hsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hgoodAll : ∀ ω : Ω, ω ∉ N → (∀ (b : ContinuousPath ℂ) (t : ℝ≥0),
      G0 ((ω, b), t) = lqgClockApprox γ (hcirc ω) (dyadicScale k) b t) ∧
      Continuous (hcirc ω (dyadicScale k)) := by
    intro ω hω
    by_contra hn
    exact hω (hsub hn)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  refine ⟨fun q => if q.1.1 ∈ N then (q.2 : ℝ) else G0 q, ?_, ?_, ?_, ?_⟩
  · exact Measurable.ite (hNmeas.preimage (measurable_fst.comp measurable_fst))
      (NNReal.continuous_coe.measurable.comp measurable_snd) hG0
  · intro ω b
    show StrictMono fun t : ℝ≥0 => if ω ∈ N then (t : ℝ) else G0 ((ω, b), t)
    by_cases hω : ω ∈ N
    · have heq : (fun t : ℝ≥0 => if ω ∈ N then (t : ℝ) else G0 ((ω, b), t)) = fun t : ℝ≥0 => (t : ℝ) :=
        funext fun t => ite_eq_left hω
      rw [heq]
      intro a c h
      exact NNReal.coe_lt_coe.2 h
    · have heq : (fun t : ℝ≥0 => if ω ∈ N then (t : ℝ) else G0 ((ω, b), t)) =
          fun t : ℝ≥0 => lqgClockApprox γ (hcirc ω) (dyadicScale k) b t := by
        funext t
        rw [ite_eq_right hω]
        exact (hgoodAll ω hω).1 b t
      rw [heq]
      exact strictMono_lqgClockApprox (dyadicScale_pos k) (hgoodAll ω hω).2 b
  · intro ω b
    show Continuous fun t : ℝ≥0 => if ω ∈ N then (t : ℝ) else G0 ((ω, b), t)
    by_cases hω : ω ∈ N
    · have heq : (fun t : ℝ≥0 => if ω ∈ N then (t : ℝ) else G0 ((ω, b), t)) = fun t : ℝ≥0 => (t : ℝ) :=
        funext fun t => ite_eq_left hω
      rw [heq]
      exact NNReal.continuous_coe
    · have heq : (fun t : ℝ≥0 => if ω ∈ N then (t : ℝ) else G0 ((ω, b), t)) =
          fun t : ℝ≥0 => lqgClockApprox γ (hcirc ω) (dyadicScale k) b t := by
        funext t
        rw [ite_eq_right hω]
        exact (hgoodAll ω hω).1 b t
      rw [heq]
      exact continuous_lqgClockApprox_time (hgoodAll ω hω).2 b
  · filter_upwards [hNae] with ω hω' b t
    show (if ω ∈ N then (t : ℝ) else G0 ((ω, b), t)) = _
    rw [ite_eq_right hω']
    exact (hgoodAll ω hω').1 b t

/-- **Joint measurability of the approximate path functional.** For a clock `G` jointly measurable in `((ω, b), t)` and strictly
increasing and continuous in `t` for every `(ω, b)`, the functional `F` of the approximate path `t ↦ b (cutInv (G (ω, b)) n (m t))`
is jointly measurable in `(ω, b)`. -/
theorem measurable_boundedLipschitz_approxPath_joint {Ω : Type} [MeasurableSpace Ω] {F : (ℝ≥0 → ℂ) → ℝ}
    (hF : IsBoundedLipschitzPathFunctional F) {G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ} (hG : Measurable G)
    (hmono : ∀ (ω : Ω) (b : ContinuousPath ℂ), StrictMono fun t : ℝ≥0 => G ((ω, b), t))
    (hcontG : ∀ (ω : Ω) (b : ContinuousPath ℂ), Continuous fun t : ℝ≥0 => G ((ω, b), t)) (n m : ℝ≥0) :
    Measurable fun p : Ω × ContinuousPath ℂ =>
      F (fun t : ℝ≥0 => p.2 (cutInv (fun s : ℝ≥0 => G ((p.1, p.2), s)) n (m * t))) := by
  have hτ : ∀ t : ℝ≥0, Measurable fun p : Ω × ContinuousPath ℂ =>
      cutInv (fun s : ℝ≥0 => G ((p.1, p.2), s)) n (m * t) := by
    intro t
    exact (measurable_cutInv (C := fun (p : Ω × ContinuousPath ℂ) (s : ℝ≥0) => G ((p.1, p.2), s))
      (fun p => (hmono p.1 p.2).monotone) hG n).comp (measurable_id.prodMk measurable_const)
  have hX : ∀ t : ℝ≥0, Measurable fun p : Ω × ContinuousPath ℂ =>
      p.2 (cutInv (fun s : ℝ≥0 => G ((p.1, p.2), s)) n (m * t)) := fun t =>
    measurable_path_eval_pair.comp (measurable_snd.prodMk (hτ t))
  have hcont : ∀ p : Ω × ContinuousPath ℂ, Continuous fun t : ℝ≥0 =>
      p.2 (cutInv (fun s : ℝ≥0 => G ((p.1, p.2), s)) n (m * t)) := fun p =>
    p.2.continuous.comp ((continuous_cutInv (hmono p.1 p.2) (hcontG p.1 p.2) n).comp
      (continuous_const.mul continuous_id))
  exact measurable_boundedLipschitz_comp hF hX hcont

/-- **Measurability of the expectations in the environment.** For a quantum cone and a bounded Lipschitz functional `F`, the
expectation `ω ↦ ∫ F (approximate path of ω at scale k) dν` of the functional of the approximate path is almost surely equal to a
measurable function of the environment (Fubini). -/
theorem measurable_integral_boundedLipschitz_approxPath {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc)
    {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F) (k : ℕ) (n m : ℝ≥0)
    (ν : Measure (ContinuousPath ℂ)) [SFinite ν] :
    ∃ E : Ω → ℝ, Measurable E ∧ ∀ᵐ ω ∂P,
      E ω = ∫ b, F (fun t : ℝ≥0 =>
        b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ (hcirc ω) (dyadicScale k) b s) n (m * t))) ∂ν := by
  obtain ⟨G, hG, hmono, hcontG, hae⟩ := exists_measurable_clockApprox_modification hcone k
  have hjoint := measurable_boundedLipschitz_approxPath_joint hF hG hmono hcontG n m
  refine ⟨fun ω => ∫ b, F (fun t : ℝ≥0 => b (cutInv (fun s : ℝ≥0 => G ((ω, b), s)) n (m * t))) ∂ν, ?_, ?_⟩
  · exact (hjoint.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  · filter_upwards [hae] with ω hω
    simp only [hω]

end MatedCRT
