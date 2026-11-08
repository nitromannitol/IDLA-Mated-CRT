import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.JointCauchySubsequence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxPathJoint

/-!
# Lemma 3.4 (item 3): a jointly measurable limit of the approximate Liouville clocks

For a valid environment `S` and a starting point `y`, the approximate clocks `lqgClockApprox` at dyadic scales have
jointly measurable versions in `((ω, b), t)` (`exists_measurable_clockApprox_modification`). Along an
environment-independent subsequence `φ` (`exists_strictMono_joint_cauchy`, applied to the product measure
`S.P ⊗ planarBrownianMotion y`), their values at rational times converge almost surely, and the limit `L` is jointly
measurable in `(ω, b)`. It agrees with the clock `S.clock ω b` at rational times for almost every `(ω, b)`
(`exists_joint_clock_limit`): the clock is characterised only by convergence in probability (`IsLQGClock`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- Elementary: if `|a - a'| ≥ η` then one of `a, a'` is at distance at least `η/2` from `c`. -/
lemma half_le_abs_sub_of_le_abs_sub {a a' c η : ℝ} (h : η ≤ |a - a'|) :
    η / 2 ≤ |a - c| ∨ η / 2 ≤ |a' - c| := by
  rcases le_or_gt (η / 2) |a - c| with h1 | h1
  · exact Or.inl h1
  · right
    have htri := abs_sub_le a c a'
    rw [abs_sub_comm c a'] at htri
    linarith

/-- Jointly measurable versions of the approximate clocks of a valid environment: for each dyadic scale `k` the map
`((ω, b), t) ↦ G k ((ω, b), t)` is measurable and equals `lqgClockApprox γ (S.hcirc ω) (dyadicScale k) b t` for almost
every environment `ω`. -/
theorem exists_joint_clockApprox {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∃ G : ℕ → (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, (∀ k, Measurable (G k)) ∧
      ∀ k, ∀ᵐ ω ∂S.P, ∀ (b : ContinuousPath ℂ) (t : ℝ≥0),
        G k ((ω, b), t) = lqgClockApprox γ (S.hcirc ω) (dyadicScale k) b t := by
  choose G hG _hmono _hcont hae using fun k => exists_measurable_clockApprox_modification hS.isQuantumCone k
  exact ⟨G, hG, hae⟩

/-- **Joint limit of the clock approximations.** There are a strictly increasing subsequence `φ` and a family
`L p q` (`p : Ω × ContinuousPath ℂ`, `q : ℚ≥0`), measurable in `p` for each rational time, such that for almost every
environment `ω` and almost every Brownian path `b`, `L (ω, b) q = S.clock ω b q` at every rational time `q`. -/
theorem exists_joint_clock_limit {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (y : ℂ) :
    ∃ (φ : ℕ → ℕ) (L : (Ω × ContinuousPath ℂ) → ℚ≥0 → ℝ), StrictMono φ ∧
      (∀ q : ℚ≥0, Measurable fun p => L p q) ∧
      ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, ∀ q : ℚ≥0, L (ω, b) q = S.clock ω b (q : ℝ≥0) := by
  obtain ⟨G, hG, hae⟩ := exists_joint_clockApprox S hS
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have : IsProbabilityMeasure (planarBrownianMotion y) := inferInstance
  let Gq : ℕ → (Ω × ContinuousPath ℂ) → ℝ≥0 → ℝ := fun k p t => G k (p, t)
  have hGq : ∀ k (t : ℝ≥0), Measurable fun p => Gq k p t := fun k t =>
    (hG k).comp (measurable_id.prodMk measurable_const)
  set μ : Measure (Ω × ContinuousPath ℂ) := S.P.prod (planarBrownianMotion y) with hμ
  let A : ℝ → ℝ → ℕ → ℕ → Set (Ω × ContinuousPath ℂ) := fun T η k l =>
    {p | ∃ q : ℚ≥0, (q : ℝ) ≤ T ∧ η ≤ |Gq k p (q : ℝ≥0) - Gq l p (q : ℝ≥0)|}
  have hAmeas : ∀ T η k l, MeasurableSet (A T η k l) := by
    intro T η k l
    have hset : A T η k l =
        ⋃ q : ℚ≥0, ({p | (q : ℝ) ≤ T} ∩ {p | η ≤ |Gq k p (q : ℝ≥0) - Gq l p (q : ℝ≥0)|}) := by
      ext p
      simp only [A, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [hset]
    exact MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter
      (measurableSet_le measurable_const (((hGq k (q : ℝ≥0)).sub (hGq l (q : ℝ≥0))).abs))
  -- the joint convergence in measure of the approximations on the product
  have hconv : ∀ (T : ℕ) (η : ℝ), 0 < η → Tendsto (fun kl : ℕ × ℕ => μ {p | ∃ q : ℚ≥0, (q : ℝ) ≤ T ∧
      η ≤ |Gq kl.1 p (q : ℝ≥0) - Gq kl.2 p (q : ℝ≥0)|}) atTop (𝓝 0) := by
    intro T η hη
    have hfun : (fun kl : ℕ × ℕ => μ {p | ∃ q : ℚ≥0, (q : ℝ) ≤ T ∧
          η ≤ |Gq kl.1 p (q : ℝ≥0) - Gq kl.2 p (q : ℝ≥0)|})
        = fun kl => ∫⁻ ω, planarBrownianMotion y (Prod.mk ω ⁻¹' A (T : ℝ) η kl.1 kl.2) ∂S.P := by
      funext kl
      exact Measure.prod_apply (hAmeas (T : ℝ) η kl.1 kl.2)
    rw [hfun]
    -- for almost every environment the sections have measure tending to zero
    have hpt : ∀ᵐ ω ∂S.P, Tendsto (fun kl : ℕ × ℕ =>
        planarBrownianMotion y (Prod.mk ω ⁻¹' A (T : ℝ) η kl.1 kl.2)) atTop (𝓝 0) := by
      filter_upwards [hS.isLQGClock, ae_all_iff.2 hae] with ω hω hωae
      have hLQG := (hω y).1
      have hB := hLQG (T : ℝ≥0) (η / 2) (half_pos hη)
      let Bset : ℕ → Set (ContinuousPath ℂ) := fun k => {b | ∃ t : ℝ≥0, t ≤ (T : ℝ≥0) ∧
        η / 2 ≤ |lqgClockApprox γ (S.hcirc ω) (dyadicScale k) b t - S.clock ω b t|}
      have hBk : Tendsto (fun k => planarBrownianMotion y (Bset k)) atTop (𝓝 0) := hB
      have hsq : Tendsto (fun kl : ℕ × ℕ =>
          planarBrownianMotion y (Bset kl.1) + planarBrownianMotion y (Bset kl.2)) atTop (𝓝 0) := by
        have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop :=
          tendsto_atTop_atTop.2 fun n => ⟨(n, 0), fun a ha => (Prod.le_def.1 ha).1⟩
        have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop :=
          tendsto_atTop_atTop.2 fun n => ⟨(0, n), fun a ha => (Prod.le_def.1 ha).2⟩
        have h := (hBk.comp hfst).add (hBk.comp hsnd)
        rw [add_zero] at h
        exact h
      have hsub : ∀ kl : ℕ × ℕ, Prod.mk ω ⁻¹' A (T : ℝ) η kl.1 kl.2 ⊆ Bset kl.1 ∪ Bset kl.2 := by
        intro kl b hb
        simp only [Set.mem_preimage, A, Set.mem_ofPred_eq] at hb
        obtain ⟨q, hq, hη'⟩ := hb
        have ht : (q : ℝ≥0) ≤ (T : ℝ≥0) := by exact_mod_cast hq
        simp only [Gq] at hη'
        rw [hωae kl.1 b (q : ℝ≥0), hωae kl.2 b (q : ℝ≥0)] at hη'
        rcases half_le_abs_sub_of_le_abs_sub hη' with h2 | h2
        · exact Or.inl ⟨(q : ℝ≥0), ht, h2⟩
        · exact Or.inr ⟨(q : ℝ≥0), ht, h2⟩
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq
        (fun _ => zero_le) (fun kl => ?_)
      exact (measure_mono (hsub kl)).trans (measure_union_le _ _)
    -- dominated convergence in the environment
    have hlim := tendsto_lintegral_filter_of_dominated_convergence (μ := S.P) (l := atTop)
      (fun _ => (1 : ℝ≥0∞))
      (F := fun (kl : ℕ × ℕ) (ω : Ω) => planarBrownianMotion y (Prod.mk ω ⁻¹' A (T : ℝ) η kl.1 kl.2))
      (f := fun _ => (0 : ℝ≥0∞))
      (Eventually.of_forall fun kl => measurable_measure_prodMk_left (hAmeas (T : ℝ) η kl.1 kl.2))
      (Eventually.of_forall fun _ => Eventually.of_forall fun _ => prob_le_one)
      (by simp) hpt
    simpa using hlim
  -- the Borel–Cantelli subsequence and the limit at rational times
  obtain ⟨φ, hφ, hcauchy⟩ := exists_strictMono_joint_cauchy μ Gq hconv
  let L : (Ω × ContinuousPath ℂ) → ℚ≥0 → ℝ :=
    fun p q => Filter.limsup (fun j => Gq (φ j) p (q : ℝ≥0)) atTop
  have hLmeas : ∀ q : ℚ≥0, Measurable fun p => L p q := fun q =>
    Measurable.limsup fun j => hGq (φ j) (q : ℝ≥0)
  refine ⟨φ, L, hφ, hLmeas, ?_⟩
  -- the identification with the clock, for almost every environment and Brownian path
  have hcauchy' : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, ∀ q : ℚ≥0,
      CauchySeq (fun j => Gq (φ j) (ω, b) (q : ℝ≥0)) :=
    Measure.ae_ae_of_ae_prod hcauchy
  filter_upwards [hcauchy', hS.isLQGClock, ae_all_iff.2 hae] with ω hωc hω hωae
  have hLQG := (hω y).1
  have hfin : ∀ q : ℚ≥0, ∀ᵐ b ∂planarBrownianMotion y, L (ω, b) q = S.clock ω b (q : ℝ≥0) := by
    intro q
    refine ae_eq_of_ae_tendsto_of_outer (planarBrownianMotion y) (fun j b => Gq (φ j) (ω, b) (q : ℝ≥0))
      (fun b => L (ω, b) q) (fun b => S.clock ω b (q : ℝ≥0)) (fun j => ?_) ?_ ?_ ?_
    · exact (hGq (φ j) (q : ℝ≥0)).comp measurable_prodMk_left
    · exact (hLmeas q).comp measurable_prodMk_left
    · filter_upwards [hωc] with b hb
      obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (hb q)
      show Tendsto (fun j => Gq (φ j) (ω, b) (q : ℝ≥0)) atTop
        (𝓝 (Filter.limsup (fun j => Gq (φ j) (ω, b) (q : ℝ≥0)) atTop))
      rw [hx.limsup_eq]
      exact hx
    · intro η hη
      have hB := hLQG (q : ℝ≥0) η hη
      have hBφ := hB.comp hφ.tendsto_atTop
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hBφ
        (fun _ => zero_le) (fun j => measure_mono ?_)
      intro b hb
      change η ≤ |G (φ j) ((ω, b), (q : ℝ≥0)) - S.clock ω b (q : ℝ≥0)| at hb
      rw [hωae (φ j) b (q : ℝ≥0)] at hb
      exact ⟨(q : ℝ≥0), le_rfl, hb⟩
  exact ae_all_iff.2 hfin

end MatedCRT
