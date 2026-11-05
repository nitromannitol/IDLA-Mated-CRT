import MatedCRT.Proofs.Measurability.VagueWholePlane

/-!
# A measurable choice of vague limits

Let `ν n : Ω → Measure ℂ` be random measures whose integrals against continuous compactly supported functions are
random variables. There is a random measure `μ'` (`Measurable μ'`, Giry σ-algebra) which equals the vague limit of
`(ν n ω)_n` at every `ω` where the `ν n ω` are eventually finite on compacts and converge vaguely
(`exists_measurable_vagueLimit`). Construction: on the measurable event `G` where the integrals against a countable
dense family converge and the masses of the balls are eventually finite, a vague limit exists
(`exists_isVagueLimitOn_univ_of_family`); `μ'` is this limit on `G` and `0` off `G`. Measurability: the mass of an open
set `U` is the supremum of the integrals of the continuous cutoffs `cut U j ↑ 𝟙_U`, which are limits of the integrals
against `ν n ω`; the open sets form a π-system generating the Borel σ-algebra of `ℂ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT
namespace VagueWholePlane

/-! ### Continuous cutoffs of open sets -/

/-- `cut U j x = min 1 (j · dist(x, Uᶜ ∪ (B_j)ᶜ))`, continuous, supported in `closedBall 0 j`, increasing to `𝟙_U`. -/
def cut (U : Set ℂ) (j : ℕ) (x : ℂ) : ℝ := min 1 ((j : ℝ) * infDist x (Uᶜ ∪ (ball 0 j)ᶜ))

lemma continuous_cut (U : Set ℂ) (j : ℕ) : Continuous (cut U j) :=
  continuous_const.min (continuous_const.mul (continuous_infDist_pt _))

lemma cut_nonneg (U : Set ℂ) (j : ℕ) (x : ℂ) : 0 ≤ cut U j x :=
  le_min zero_le_one (mul_nonneg (Nat.cast_nonneg j) infDist_nonneg)

lemma cut_le_one (U : Set ℂ) (j : ℕ) (x : ℂ) : cut U j x ≤ 1 := min_le_left _ _

lemma cut_eq_zero {U : Set ℂ} {j : ℕ} {x : ℂ} (hx : x ∈ Uᶜ ∪ (ball 0 j)ᶜ) : cut U j x = 0 := by
  rw [cut, infDist_zero_of_mem hx, mul_zero, min_eq_right zero_le_one]

lemma hasCompactSupport_cut (U : Set ℂ) (j : ℕ) : HasCompactSupport (cut U j) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) j) fun _ hx =>
    cut_eq_zero (Or.inr fun h => hx (ball_subset_closedBall h))

lemma cut_mono (U : Set ℂ) (x : ℂ) : Monotone fun j => cut U j x := by
  intro j j' hjj'
  refine min_le_min le_rfl (mul_le_mul (Nat.cast_le.2 hjj') ?_ infDist_nonneg (Nat.cast_nonneg _))
  refine infDist_le_infDist_of_subset ?_ ?_
  · exact union_subset_union le_rfl (compl_subset_compl.2 (ball_subset_ball (Nat.cast_le.2 hjj')))
  · obtain ⟨y, hy⟩ : ((ball (0 : ℂ) j')ᶜ).Nonempty := by
      refine ⟨(j' : ℂ) + 1, fun h => ?_⟩
      rw [mem_ball, dist_zero_right] at h
      have : ‖((j' : ℂ) + 1)‖ = (j' : ℝ) + 1 := by
        rw [show ((j' : ℂ) + 1) = (((j' : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      linarith
    exact ⟨y, Or.inr hy⟩

lemma iSup_ofReal_cut (U : Set ℂ) (hU : IsOpen U) (x : ℂ) :
    ⨆ j : ℕ, ENNReal.ofReal (cut U j x) = U.indicator 1 x := by
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx, Pi.one_apply]
    refine le_antisymm (iSup_le fun j => ?_) ?_
    · rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (cut_le_one U j x)
    · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
      obtain ⟨j, hj⟩ := exists_nat_gt (max (‖x‖ + δ) (1 / δ))
      have hjx : ‖x‖ + δ < j := lt_of_le_of_lt (le_max_left _ _) hj
      have hjδ : 1 / δ < j := lt_of_le_of_lt (le_max_right _ _) hj
      have hinf : δ ≤ infDist x (Uᶜ ∪ (ball 0 j)ᶜ) := by
        refine (le_infDist ?_).2 fun y hy => ?_
        · exact ⟨(j : ℂ) + (j : ℂ) + 1, Or.inr fun h => by
            rw [mem_ball, dist_zero_right] at h
            have : ‖(j : ℂ) + (j : ℂ) + 1‖ = (j : ℝ) + j + 1 := by
              rw [show (j : ℂ) + (j : ℂ) + 1 = (((j : ℝ) + j + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
                Real.norm_of_nonneg (by positivity)]
            linarith⟩
        · by_contra hlt
          rw [not_le] at hlt
          have hyb : y ∈ ball x δ := by rw [mem_ball, dist_comm]; exact hlt
          rcases hy with hy | hy
          · exact hy (hball hyb)
          · apply hy
            rw [mem_ball, dist_zero_right]
            have := norm_le_norm_add_norm_sub' y x
            rw [mem_ball, dist_eq_norm] at hyb
            linarith
      have h1 : 1 ≤ (j : ℝ) * infDist x (Uᶜ ∪ (ball 0 j)ᶜ) := by
        have : 1 ≤ (j : ℝ) * δ := by
          rw [div_lt_iff₀ hδ] at hjδ
          linarith
        exact this.trans (mul_le_mul_of_nonneg_left hinf (Nat.cast_nonneg j))
      have hcut : cut U j x = 1 := min_eq_left h1
      calc (1 : ℝ≥0∞) = ENNReal.ofReal (cut U j x) := by rw [hcut, ENNReal.ofReal_one]
        _ ≤ ⨆ j : ℕ, ENNReal.ofReal (cut U j x) := le_iSup (fun j : ℕ => ENNReal.ofReal (cut U j x)) j
  · rw [indicator_of_notMem hx]
    refine le_antisymm (iSup_le fun j => ?_) (by simp)
    rw [cut_eq_zero (Or.inl hx), ENNReal.ofReal_zero]

/-- The mass of an open set is the supremum of the integrals of the cutoffs. -/
lemma measure_eq_iSup_integral_cut {m : Measure ℂ} (hm : ∀ K, IsCompact K → m K < ∞) {U : Set ℂ}
    (hU : IsOpen U) : m U = ⨆ j : ℕ, ENNReal.ofReal (∫ x, cut U j x ∂m) := by
  have hint : ∀ j, ENNReal.ofReal (∫ x, cut U j x ∂m) = ∫⁻ x, ENNReal.ofReal (cut U j x) ∂m := fun j =>
    ofReal_integral_eq_lintegral_ofReal
      (IsTestC.integrable (f := cut U j) ⟨continuous_cut U j, hasCompactSupport_cut U j⟩
        (hm _ (hasCompactSupport_cut U j).isCompact))
      (Eventually.of_forall (cut_nonneg U j))
  simp_rw [hint]
  rw [← lintegral_iSup (fun j => (continuous_cut U j).measurable.ennreal_ofReal)
    (fun j j' h x => ENNReal.ofReal_le_ofReal (cut_mono U x h))]
  simp_rw [iSup_ofReal_cut U hU]
  rw [lintegral_indicator hU.measurableSet]
  simp only [Pi.one_apply, setLIntegral_one]

/-! ### The measurable vague limit -/

open Classical in
/-- A chosen vague limit on `ℂ` (or `0`). -/
def vagueLimit (νs : ℕ → Measure ℂ) : Measure ℂ :=
  if h : ∃ μ, QuantumZipper.IsVagueLimitOn univ νs μ then h.choose else 0

lemma vagueLimit_eq {νs : ℕ → Measure ℂ} {μ : Measure ℂ} (h : QuantumZipper.IsVagueLimitOn univ νs μ) :
    vagueLimit νs = μ := by
  have hex : ∃ μ, QuantumZipper.IsVagueLimitOn univ νs μ := ⟨μ, h⟩
  unfold vagueLimit
  split
  · rename_i h'
    exact QuantumZipper.isVagueLimitOn_unique isOpen_univ h'.choose_spec h
  · exact absurd hex ‹_›

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **A measurable choice of vague limits.** -/
theorem exists_measurable_vagueLimit (ν : ℕ → Ω → Measure ℂ) (hν : ∀ n, Measurable (ν n))
    (hint : ∀ n (f : ℂ → ℝ), Continuous f → HasCompactSupport f → Measurable fun ω => ∫ z, f z ∂(ν n ω)) :
    ∃ μ' : Ω → Measure ℂ, Measurable μ' ∧ ∀ ω μ, (∀ K, IsCompact K → ∀ᶠ n in atTop, ν n ω K < ∞) →
      QuantumZipper.IsVagueLimitOn univ (fun n => ν n ω) μ → μ' ω = μ := by
  classical
  obtain ⟨F, hFc, hF⟩ := exists_denseTestFamilyC
  have : Countable F := hFc.to_subtype
  let G : Set Ω := {ω | (∀ f : F, ∃ l, Tendsto (fun n => ∫ z, (f : ℂ → ℝ) z ∂(ν n ω)) atTop (𝓝 l)) ∧
    ∀ j : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ν n ω (closedBall 0 j) < ∞}
  have hG : MeasurableSet G := by
    refine measurableSet_setOfPred.2 (Measurable.and (Measurable.forall fun f => measurableSet_setOfPred.1
      (measurableSet_exists_tendsto fun n => hint n f (hF.1 f f.2).1 (hF.1 f f.2).2))
      (Measurable.forall fun j => Measurable.exists fun N =>
        Measurable.forall fun n => measurable_const.imp (measurableSet_setOfPred.1 ?_)))
    exact measurableSet_lt ((Measure.measurable_coe measurableSet_closedBall).comp (hν n)) measurable_const
  have hfinG : ∀ ω ∈ G, ∀ K, IsCompact K → ∀ᶠ n in atTop, ν n ω K < ∞ := by
    intro ω hω K hK
    obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hK.isBounded
    obtain ⟨j, hj⟩ := exists_nat_ge r
    obtain ⟨N, hN⟩ := hω.2 j
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (measure_mono (hr.trans (closedBall_subset_closedBall hj))).trans_lt (hN n hn)
  have hexG : ∀ ω ∈ G, QuantumZipper.IsVagueLimitOn univ (fun n => ν n ω) (vagueLimit fun n => ν n ω) := by
    intro ω hω
    obtain ⟨μ, hμ⟩ := exists_isVagueLimitOn_univ_of_family (hfinG ω hω) hF fun f hf => hω.1 ⟨f, hf⟩
    rw [vagueLimit_eq hμ]
    exact hμ
  let μ' : Ω → Measure ℂ := fun ω => if ω ∈ G then vagueLimit (fun n => ν n ω) else 0
  have hloc : ∀ ω K, IsCompact K → μ' ω K < ∞ := by
    intro ω K hK
    by_cases hω : ω ∈ G
    · simp only [μ', hω, ↓reduceIte]
      exact (hexG ω hω).2.1 K hK (subset_univ _)
    · simp only [μ', hω, ↓reduceIte,Measure.coe_zero, Pi.zero_apply]
      exact ENNReal.zero_lt_top
  -- the masses of open sets
  have hopen : ∀ U : Set ℂ, IsOpen U → Measurable fun ω => μ' ω U := by
    intro U hU
    have e : (fun ω => μ' ω U) = G.indicator fun ω =>
        ⨆ j : ℕ, ENNReal.ofReal (limsup (fun n => ∫ x, cut U j x ∂(ν n ω)) atTop) := by
      funext ω
      by_cases hω : ω ∈ G
      · rw [indicator_of_mem hω]
        simp only [μ', hω, ↓reduceIte]
        rw [measure_eq_iSup_integral_cut (fun K hK => (hexG ω hω).2.1 K hK (subset_univ _)) hU]
        congr 1
        funext j
        rw [((hexG ω hω).2.2 (cut U j) (continuous_cut U j) (hasCompactSupport_cut U j)
          (subset_univ _)).limsup_eq]
      · rw [indicator_of_notMem hω]
        simp only [μ', hω, ↓reduceIte,Measure.coe_zero, Pi.zero_apply]
    rw [e]
    exact (Measurable.iSup fun j => ENNReal.measurable_ofReal.comp
      (Measurable.limsup fun n => hint n _ (continuous_cut U j) (hasCompactSupport_cut U j))).indicator hG
  -- the restrictions to balls
  have hball : ∀ j : ℕ, Measurable fun ω => (μ' ω).restrict (ball (0 : ℂ) j) := by
    intro j
    have : ∀ ω, IsFiniteMeasure ((μ' ω).restrict (ball (0 : ℂ) j)) := fun ω =>
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (measure_mono ball_subset_closedBall).trans_lt (hloc ω _ (isCompact_closedBall _ _))⟩
    refine Measurable.measure_of_isPiSystem (S := {s | IsOpen s}) BorelSpace.measurable_eq isPiSystem_isOpen
      (fun s hs => ?_) ?_
    · have hs' : IsOpen s := hs
      simp_rw [Measure.restrict_apply hs'.measurableSet]
      exact hopen _ (hs'.inter isOpen_ball)
    · simp_rw [Measure.restrict_apply_univ]
      exact hopen _ isOpen_ball
  refine ⟨μ', Measure.measurable_of_measurable_coe _ fun s hs => ?_, fun ω μ hfin hμ => ?_⟩
  · have e : (fun ω => μ' ω s) = fun ω => ⨆ j : ℕ, (μ' ω).restrict (ball (0 : ℂ) j) s := by
      funext ω
      simp_rw [Measure.restrict_apply hs]
      rw [← Monotone.measure_iUnion fun j j' h => inter_subset_inter_right _ (ball_subset_ball (Nat.cast_le.2 h)),
        ← inter_iUnion, iUnion_ball_nat, inter_univ]
    rw [e]
    exact Measurable.iSup fun j => (Measure.measurable_coe hs).comp (hball j)
  · have hω : ω ∈ G := by
      refine ⟨fun f => ⟨_, hμ.2.2 f (hF.1 f f.2).1 (hF.1 f f.2).2 (subset_univ _)⟩, fun j => ?_⟩
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hfin _ (isCompact_closedBall (0 : ℂ) j))
      exact ⟨N, hN⟩
    simp only [μ', hω, ↓reduceIte]
    exact vagueLimit_eq hμ

end VagueWholePlane
end MatedCRT
