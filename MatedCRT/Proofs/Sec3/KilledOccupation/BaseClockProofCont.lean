import Mathlib
import HarmonicBalls.Defs.Green
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Defs.LBM
import HarmonicBalls.Defs.LQG
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockProof

/-!
# Lemma lem:occ-base for bounded continuous weights (paper tex:140-151, tex:166-177, tex:218-237)

`baseOccupationIdentity_of_GMC_cont` has the conclusion of `baseOccupationIdentity_of_GMC`
(BaseClockProof.lean). The input of the conditional GMC clock convergence `hLpath` is quantified only
over bounded nonnegative continuous weights, as in the printed input (appendix tex:166-177, Berestycki
2017 Thm 1.1). Step C follows the printed route (tex:234-237): a countable family dense in `C(cl D)`
(here `cl D = closedBall z r`, `r > 0`), uniform approximation, and equality of the two finite measures
on `cl D`. The truncation/`L¹` input `hconvB1` is unchanged (bounded Borel weights, printed as a
bounded weighted Lebesgue reference measure, tex:218-233).
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

/-- A path started in `ball z r` stays in `closedBall z r` on `[0, σ]`, where `σ` is its exit time
(paper tex:140-151, support of the occupation measure in `cl D`). -/
theorem path_mem_closedBall_of_start {z : ℂ} {r : ℝ} {y : ℂ} (hy : y ∈ ball z r)
    {b : ContinuousPath ℂ} (hb0 : b 0 = y) {u : ℝ≥0}
    (hu : u ∈ Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal) :
    b u ∈ closedBall z r := by
  have hS : IsClosed {v : ℝ≥0 | b v ∈ closedBall z r} := isClosed_closedBall.preimage b.continuous
  rcases eq_or_ne (pathExitTime (ball z r) b).toNNReal 0 with h0 | hne
  · have hu0 : u = 0 := by
      have h := hu.2
      rw [h0] at h
      exact le_antisymm h (by positivity)
    rw [hu0, hb0]
    exact ball_subset_closedBall hy
  · have hsub : Ico (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal ⊆
        {v : ℝ≥0 | b v ∈ closedBall z r} :=
      fun v hv => ball_subset_closedBall (mem_of_lt_exit_toNNReal b hv.2)
    have hcl := closure_minimal hsub hS
    rw [closure_Ico (Ne.symm hne)] at hcl
    exact hcl hu

/-- The base clock kernel `occKernel dA z r ω b` charges nothing outside `closedBall z r`, for a path
started at `y ∈ ball z r`. -/
theorem occKernel_compl_closedBall {Ω : Type*} (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (z : ℂ)
    (r : ℝ) {y : ℂ} (hy : y ∈ ball z r) (ω : Ω) {b : ContinuousPath ℂ} (hb0 : b 0 = y) :
    occKernel dA z r ω b (closedBall z r)ᶜ = 0 := by
  have hm : MeasurableSet (closedBall z r)ᶜ := isClosed_closedBall.measurableSet.compl
  have hempty : (fun u : ℝ≥0 => b u) ⁻¹' (closedBall z r)ᶜ ∩
      Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun u hu => ?_
    exact hu.1 (path_mem_closedBall_of_start hy hb0 hu.2)
  unfold occKernel
  rw [Measure.map_apply b.continuous.measurable hm,
    Measure.restrict_apply (b.continuous.measurable hm), hempty, measure_empty]

/-- The limit occupation measure `occMeasure` charges nothing outside `closedBall z r`, almost surely
in the field (its path measure is `planarBrownianMotion y`, started at `y ∈ ball z r`). -/
theorem occMeasure_compl_closedBall_eq_zero {Ω : Type*} (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (z : ℂ) (r : ℝ) {y : ℂ} (hy : y ∈ ball z r) (ω : Ω)
    (hκ : AEMeasurable (occKernel dA z r ω) (planarBrownianMotion y)) :
    occMeasure (planarBrownianMotion y) dA z r ω (closedBall z r)ᶜ = 0 := by
  rw [occMeasure_apply _ dA z r ω hκ isClosed_closedBall.measurableSet.compl]
  have h0 : (fun b : ContinuousPath ℂ => occKernel dA z r ω b (closedBall z r)ᶜ) =ᵐ[planarBrownianMotion y]
      fun _ => 0 := by
    filter_upwards [ae_planarBrownianMotion_eval_zero y] with b hb0
    exact occKernel_compl_closedBall dA z r hy ω hb0
  rw [lintegral_congr_ae h0, lintegral_zero]

/-- Elementary inequality: for `F ≥ 0`, truncating the approximant at `0` does not increase the error. -/
theorem abs_sub_max_zero_le (a F : ℝ) (hF : 0 ≤ F) : |F - max a 0| ≤ |F - a| := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, sub_zero, abs_of_nonneg hF, abs_of_nonneg (by linarith : (0 : ℝ) ≤ F - a)]
    linarith

/-- A countable family of nonnegative bounded continuous functions on `ℂ`, dense in `C(cl D, ℝ)` for
`cl D = closedBall z r` (paper tex:234-237: the countable dense family in `C(cl D)`). The members are
Tietze extensions of a dense sequence of `C(closedBall z r, ℝ)`, truncated to `[0, ‖·‖ + 1]`. -/
theorem exists_countable_cont_approx (z : ℂ) (r : ℝ) :
    ∃ φ : ℕ → ℂ → ℝ, (∀ j, Continuous (φ j)) ∧ (∀ j x, 0 ≤ φ j x) ∧
      (∀ j, ∃ C : ℝ, ∀ x, φ j x ≤ C) ∧
      ∀ F : ℂ → ℝ, Continuous F → (∀ x, 0 ≤ F x) → ∀ δ : ℝ, 0 < δ →
        ∃ j, ∀ x ∈ closedBall z r, |F x - φ j x| < δ := by
  classical
  have : CompactSpace (closedBall z r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall z r)
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (α := C(closedBall z r, ℝ))
  have hext : ∀ j, ∃ g : C(ℂ, ℝ), ∀ x : closedBall z r, g (x : ℂ) = u j x := by
    intro j
    obtain ⟨g, hg⟩ := ContinuousMap.exists_extension
      (IsClosed.isClosedEmbedding_subtypeVal isClosed_closedBall) (u j)
    refine ⟨g, fun x => ?_⟩
    have := congrFun (congrArg DFunLike.coe hg) x
    simpa using this
  choose G hG using hext
  refine ⟨fun j x => min (max (G j x) 0) (‖u j‖ + 1), ?_, ?_, ?_, ?_⟩
  · intro j
    exact ((G j).continuous.max continuous_const).min continuous_const
  · intro j x
    exact le_min (le_max_right _ _) (by positivity)
  · intro j
    exact ⟨‖u j‖ + 1, fun x => min_le_right _ _⟩
  · intro F hF hF0 δ hδ
    let Fk : C(closedBall z r, ℝ) := ⟨fun x => F x, hF.comp continuous_subtype_val⟩
    obtain ⟨j, hj⟩ := hu.exists_dist_lt Fk hδ
    refine ⟨j, fun x hx => ?_⟩
    have hdist : dist (Fk ⟨x, hx⟩) (u j ⟨x, hx⟩) ≤ dist Fk (u j) :=
      ContinuousMap.dist_apply_le_dist (f := Fk) (g := u j) ⟨x, hx⟩
    have h1 : |F x - u j ⟨x, hx⟩| < δ := by
      have h2 := lt_of_le_of_lt hdist hj
      rw [Real.dist_eq] at h2
      exact h2
    have hGx : G j x = u j ⟨x, hx⟩ := hG j ⟨x, hx⟩
    have hbound : |u j ⟨x, hx⟩| ≤ ‖u j‖ := by
      have := ContinuousMap.norm_coe_le_norm (u j) ⟨x, hx⟩
      rwa [Real.norm_eq_abs] at this
    have hval : min (max (G j x) 0) (‖u j‖ + 1) = max (u j ⟨x, hx⟩) 0 := by
      rw [hGx]
      apply min_eq_left
      exact max_le (by linarith [le_abs_self (u j ⟨x, hx⟩)]) (by positivity)
    show |F x - min (max (G j x) 0) (‖u j‖ + 1)| < δ
    rw [hval]
    exact lt_of_le_of_lt (abs_sub_max_zero_le _ _ (hF0 x)) h1

/-- Comparison of two finite measures carried by `K` through a family of test functions with equal
integrals and uniform approximation on `K` (the approximation step of tex:234-237). -/
theorem lintegral_le_of_approx {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {K : Set α} (hμK : μ Kᶜ = 0) (hνK : ν Kᶜ = 0)
    (f : α → ℝ≥0∞) (Q : ℕ → α → ℝ≥0∞)
    (hQeq : ∀ j, ∫⁻ x, Q j x ∂μ = ∫⁻ x, Q j x ∂ν)
    (happ : ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ⊤ → ∃ j, ∀ x ∈ K, f x ≤ Q j x + ε ∧ Q j x ≤ f x + ε) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x ∂ν := by
  have hμae : ∀ᵐ x ∂μ, x ∈ K := by
    rw [ae_iff]
    exact hμK
  have hνae : ∀ᵐ x ∂ν, x ∈ K := by
    rw [ae_iff]
    exact hνK
  have hle : ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ⊤ →
      ∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x ∂ν + ε * (μ univ + ν univ) := by
    intro ε hε0 hεt
    obtain ⟨j, hj⟩ := happ ε hε0 hεt
    calc ∫⁻ x, f x ∂μ ≤ ∫⁻ x, (Q j x + ε) ∂μ :=
          lintegral_mono_ae (hμae.mono fun x hx => (hj x hx).1)
      _ = ∫⁻ x, Q j x ∂μ + ε * μ univ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const]
      _ = ∫⁻ x, Q j x ∂ν + ε * μ univ := by rw [hQeq j]
      _ ≤ ∫⁻ x, (f x + ε) ∂ν + ε * μ univ :=
          add_le_add_left (lintegral_mono_ae (hνae.mono fun x hx => (hj x hx).2)) _
      _ = ∫⁻ x, f x ∂ν + ε * (μ univ + ν univ) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, mul_add]
          ring
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ≥0∞) < δ := ENNReal.coe_pos.2 hδ
  have hD : (μ univ + ν univ) + 1 ≠ 0 := (lt_of_lt_of_le one_pos le_add_self).ne'
  have hDt : (μ univ + ν univ) + 1 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨measure_ne_top μ _, measure_ne_top ν _⟩,
      ENNReal.one_ne_top⟩
  have he0 : 0 < (δ : ℝ≥0∞) / ((μ univ + ν univ) + 1) := ENNReal.div_pos hδ'.ne' hDt
  have heT : (δ : ℝ≥0∞) / ((μ univ + ν univ) + 1) ≠ ⊤ :=
    (ENNReal.div_lt_top ENNReal.coe_ne_top hD).ne
  have key := hle _ he0 heT
  refine key.trans (add_le_add_right ?_ _)
  calc (δ : ℝ≥0∞) / ((μ univ + ν univ) + 1) * (μ univ + ν univ)
        ≤ (δ : ℝ≥0∞) / ((μ univ + ν univ) + 1) * ((μ univ + ν univ) + 1) :=
          mul_le_mul_of_nonneg_left le_self_add (by positivity)
    _ = ((μ univ + ν univ) + 1) * ((δ : ℝ≥0∞) / ((μ univ + ν univ) + 1)) := mul_comm _ _
    _ ≤ δ := ENNReal.mul_div_le

/-- **Lemma lem:occ-base** for bounded continuous weights (paper tex:140-151, eq:occ-base) as the
quenched identity `BaseOccupationIdentity`. Compared with `baseOccupationIdentity_of_GMC`, the input
`hLpath` is quantified only over bounded nonnegative continuous weights (appendix tex:166-177), and
Step C follows the printed route (tex:234-237): the identity holds for each weight of a countable family
dense in `C(cl D)` (`cl D = closedBall z r`), the two finite measures on `cl D` agree on that family and
hence everywhere, and the Borel identity follows. `hconvB1` keeps bounded Borel weights (tex:218-233). -/
theorem baseOccupationIdentity_of_GMC_cont {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (r : ℝ) {y : ℂ}
    (hy : y ∈ ball z r) (hDB : ball z r ⊆ ball 0 1)
    (hS0 : KilledBrownianOccupationOnBall z r)
    (hτ : Integrable (fun b : ContinuousPath ℂ => (pathExitTime (ball z r) b).toReal)
      (planarBrownianMotion y))
    (hτmeas : Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b)
    (hGmeas : Measurable fun x => greenFunction (ball z r) y x)
    (hGint : IntegrableOn (fun x => greenFunction (ball z r) y x) (ball z r))
    (hw : ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hVar : ∀ᶠ k in atTop, ∀ x ∈ ball z r, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    (ν : Ω → Measure ℂ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (hνmeas : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν ω))
    (hconvB1 : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) →
      (∀ x ∉ ball 0 1, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P)
        atTop (𝓝 0))
    (hLjoint : ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun p : Ω × ContinuousPath ℂ => limitClockFun dA z r p.1 p.2 q)
    (hmeasKernel : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b : ContinuousPath ℂ => ∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal,
        q (b u) ∂(dA ω b))
    (hLpath : ∀ q : ℂ → ℝ≥0∞, Continuous q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∀ᵐ b ∂planarBrownianMotion y, Tendsto (fun k => clockGapMean P γ hcirc dA z r k q b) atTop (𝓝 0))
    (hσint : ∫⁻ b, ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) ∂planarBrownianMotion y ≠ ⊤) :
    BaseOccupationIdentity P (planarBrownianMotion y) (ball z r) (greenFunction (ball z r) y) ν dA
      (fun b => (pathExitTime (ball z r) b).toNNReal) := by
  have hconv : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) →
      (∀ x ∉ ball z r, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P)
        atTop (𝓝 0) :=
    fun ρ hρ hb hz => hconvB1 ρ hρ hb (fun x hx => hz x (fun h => hx (hDB h)))
  have hG'm : Measurable (greenWeight (ball z r) y) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hGmeas)
  -- Step B: the identity for one bounded continuous weight, almost surely in the field.
  have hcont : ∀ q : ℂ → ℝ≥0∞, Continuous q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∀ᵐ ω ∂P, ∫⁻ x, q x ∂(occMeasure (planarBrownianMotion y) dA z r ω)
        = ∫⁻ x, q x ∂(nuWeighted ν (ball z r) y ω) := by
    intro q hq hqb
    obtain ⟨M, hMt, hM⟩ := hqb
    have hid := limitClock_eq_nu_ae P γ hcirc z r hy hS0 hτ hτmeas hGmeas hGint hw hVar ν dA hνmeas
      hconv hLjoint hq.measurable hMt hM (hLpath q hq ⟨M, hMt, hM⟩) hσint
    filter_upwards [hid, hmeasKernel] with ω hω hk
    rw [lintegral_occMeasure_eq (planarBrownianMotion y) dA z r ω
        (occKernel_aemeasurable _ dA z r ω hk) hq.measurable, hω,
      lintegral_nuWeighted_eq ν (ball z r) y ω hG'm hq.measurable]
  -- finiteness of the Green-weighted GMC mass (as in `baseOccupationIdentity_of_GMC`)
  have hfin : ∀ᵐ ω ∂P, ∫⁻ x in ball z r, greenWeight (ball z r) y x ∂(ν ω) ≠ ⊤ := by
    have hR := measurable_nu_setLIntegral ν hνmeas (S := ball z r) measurableSet_ball hG'm
    have hGfin : ∫⁻ x in ball z r, greenWeight (ball z r) y x ≠ ⊤ :=
      ((hGint.const_mul 2).lintegral_lt_top).ne
    have hint : ∫⁻ ω, (∫⁻ x in ball z r, greenWeight (ball z r) y x ∂(ν ω)) ∂P ≠ ⊤ := by
      have h := lintegral_nu_expect_le P γ hcirc ν measurableSet_ball hw hVar hνmeas hconv
        (g := (ball z r).indicator (greenWeight (ball z r) y)) (hG'm.indicator measurableSet_ball)
        (fun x hx => Set.indicator_of_notMem hx _)
      simp only [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
        Set.inter_self] at h
      exact ne_top_of_le_ne_top hGfin h
    filter_upwards [ae_lt_top hR hint] with ω hω
    exact hω.ne
  have hfinmeas : ∀ᵐ ω ∂P, IsFiniteMeasure (nuWeighted ν (ball z r) y ω) := by
    filter_upwards [hfin] with ω hω
    refine ⟨?_⟩
    have h := lintegral_nuWeighted_eq ν (ball z r) y ω hG'm
      (measurable_const : Measurable fun _ : ℂ => (1 : ℝ≥0∞))
    simp only [lintegral_const, mul_one, one_mul] at h
    rw [h]
    exact lt_top_iff_ne_top.2 hω
  -- Step C data: a countable family of bounded continuous weights, dense in `C(cl D)`.
  obtain ⟨φ, hφc, hφ0, hφb, hφapp⟩ := exists_countable_cont_approx z r
  have hQc : ∀ j, Continuous fun x => ENNReal.ofReal (φ j x) := fun j =>
    ENNReal.continuous_ofReal.comp (hφc j)
  have hQb : ∀ j, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, ENNReal.ofReal (φ j x) ≤ M := by
    intro j
    obtain ⟨C, hC⟩ := hφb j
    exact ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun x => ENNReal.ofReal_le_ofReal (hC x)⟩
  have hfam : ∀ᵐ ω ∂P, ∀ j,
      ∫⁻ x, ENNReal.ofReal (φ j x) ∂(occMeasure (planarBrownianMotion y) dA z r ω)
        = ∫⁻ x, ENNReal.ofReal (φ j x) ∂(nuWeighted ν (ball z r) y ω) :=
    ae_all_iff.2 fun j => hcont _ (hQc j) (hQb j)
  have hone : ∀ᵐ ω ∂P, occMeasure (planarBrownianMotion y) dA z r ω univ
      = nuWeighted ν (ball z r) y ω univ :=
    (hcont (fun _ => 1) continuous_const ⟨1, ENNReal.one_ne_top, fun _ => le_rfl⟩).mono
      fun ω h => by simpa using h
  have hsupp : ∀ᵐ ω ∂P, occMeasure (planarBrownianMotion y) dA z r ω (closedBall z r)ᶜ = 0 :=
    hmeasKernel.mono fun ω hk => occMeasure_compl_closedBall_eq_zero dA z r hy ω
      (occKernel_aemeasurable _ dA z r ω hk)
  have hνK : ∀ ω, nuWeighted ν (ball z r) y ω (closedBall z r)ᶜ = 0 := by
    intro ω
    have hem : (closedBall z r)ᶜ ∩ ball z r = ∅ :=
      Set.eq_empty_of_subset_empty fun x hx => (hx.1 (ball_subset_closedBall hx.2)).elim
    unfold nuWeighted
    rw [withDensity_apply _ isClosed_closedBall.measurableSet.compl,
      Measure.restrict_restrict isClosed_closedBall.measurableSet.compl, hem, Measure.restrict_empty,
      lintegral_zero_measure]
  -- Step C: the two finite measures on `cl D` agree, almost surely in the field.
  have hμν : ∀ᵐ ω ∂P, occMeasure (planarBrownianMotion y) dA z r ω = nuWeighted ν (ball z r) y ω := by
    filter_upwards [hfam, hone, hsupp, hfinmeas] with ω hfω hωone hωsupp hωfin
    have hfinμ : IsFiniteMeasure (occMeasure (planarBrownianMotion y) dA z r ω) :=
      ⟨by rw [hωone]; exact measure_lt_top _ _⟩
    apply MeasureTheory.ext_of_forall_lintegral_eq_of_IsFiniteMeasure
    intro f
    have happ : ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ⊤ → ∃ j, ∀ x ∈ closedBall z r,
        (f x : ℝ≥0∞) ≤ ENNReal.ofReal (φ j x) + ε ∧ ENNReal.ofReal (φ j x) ≤ (f x : ℝ≥0∞) + ε := by
      intro ε hε0 hεt
      have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε0.ne' hεt
      obtain ⟨j, hj⟩ := hφapp (fun x => (f x : ℝ)) (NNReal.continuous_coe.comp f.continuous)
        (fun x => NNReal.coe_nonneg (f x)) _ hδ
      refine ⟨j, fun x hx => ?_⟩
      have hx' : |(f x : ℝ) - φ j x| < ε.toReal := hj x hx
      have hfx : (f x : ℝ≥0∞) = ENNReal.ofReal (f x : ℝ) := ENNReal.ofReal_coe_nnreal.symm
      have hε : ε = ENNReal.ofReal ε.toReal := (ENNReal.ofReal_toReal hεt).symm
      have hA : (f x : ℝ) ≤ φ j x + ε.toReal := by linarith [(abs_lt.1 hx').2]
      have hB : φ j x ≤ (f x : ℝ) + ε.toReal := by linarith [(abs_lt.1 hx').1]
      constructor
      · rw [hfx, hε, ← ENNReal.ofReal_add (hφ0 j x) hδ.le]
        exact ENNReal.ofReal_le_ofReal hA
      · rw [hfx, hε, ← ENNReal.ofReal_add (NNReal.coe_nonneg (f x)) hδ.le]
        exact ENNReal.ofReal_le_ofReal hB
    apply le_antisymm
    · exact lintegral_le_of_approx hωsupp (hνK ω) (fun x => (f x : ℝ≥0∞))
        (fun j x => ENNReal.ofReal (φ j x)) hfω happ
    · exact lintegral_le_of_approx (hνK ω) hωsupp (fun x => (f x : ℝ≥0∞))
        (fun j x => ENNReal.ofReal (φ j x)) (fun j => (hfω j).symm) happ
  -- Conclusion: the Borel identity from the equality of the measures.
  unfold BaseOccupationIdentity
  filter_upwards [hμν, hmeasKernel] with ω hμ hk
  intro q hq _
  have hκ := occKernel_aemeasurable (planarBrownianMotion y) dA z r ω hk
  calc ∫⁻ b, (∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal, q (b u) ∂(dA ω b))
        ∂(planarBrownianMotion y)
      = ∫⁻ x, q x ∂(occMeasure (planarBrownianMotion y) dA z r ω) :=
        (lintegral_occMeasure_eq (planarBrownianMotion y) dA z r ω hκ hq).symm
    _ = ∫⁻ x, q x ∂(nuWeighted ν (ball z r) y ω) := by rw [hμ]
    _ = ∫⁻ x in ball z r, ENNReal.ofReal (2 * greenFunction (ball z r) y x) * q x ∂(ν ω) :=
        lintegral_nuWeighted_eq ν (ball z r) y ω hG'm hq

end MatedCRT.KilledOccupation
