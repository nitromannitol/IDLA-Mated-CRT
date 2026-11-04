import MatedCRT.Steps.Sec6.IDLAUpperBound
import MatedCRT.Steps.Sec2.ConeHarmonicBalls
import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LQGMassMeasurable
import MatedCRT.Proofs.Infra.Setting

/-!
# Measurability of the boundary layer of the harmonic balls (Proposition 6.1)

`BoundaryLayerMeasurableStep` (MatedCRT/Steps/Sec6/IDLAUpperBound.lean) asks for the null measurability of the events
`{t < T, μ_h(Λ_t \ B⁻_{δ₁}(Λ_t)) ≥ s}` for the harmonic ball family `Λ` of Theorem 2.3. We derive it from the
measurability of the harmonic balls of the cone (`ConeFamilyAEMeasurableStep`, implicit in the paper, lines 553, 562)
and Lemma 2.4 (`ConeHarmonicBallsUpToFixedTimeStmt`), which provides the family stopped at `∂B_{1/2}` to which that
step applies.

* **Traces on a countable dense set.** A regular open set `U = int(cl U)` is determined by its trace on the dense
  sequence `densePoint` of `ℂ`, and so is its boundary layer `U \ B⁻_δ(U) = {y ∈ U : dist(y, Uᶜ) < δ}`: it is the union
  of the sets `B_{1/(k+1)}(x_d) ∩ B_δ(x_e)` over the pairs of tests `innerBallTest` (the dense points of
  `B_{2/(k+1)}(x_d)` lie in `U`) and `exteriorBallTest` (no dense point of `B_{1/(k'+1)}(x_e)` lies in `U`)
  (`boundaryLayerOfTrace_eq`). Each test is a countable Boolean combination of the events `{x_j ∈ Λ_t}`.
* **Random countable unions.** The LQG mass of a union of deterministic Borel sets indexed by a random subset of a
  countable set, selected by measurable events, is a.e. measurable (`aemeasurable_measure_iUnion_of_events`): it is the
  supremum of the masses of its finite partial unions, each a finite sum of indicators of events times the mass of a
  deterministic Borel set (`MatedCRTEnv.IsValid.aemeasurable_lqg_mass`).
* **The stopping time.** `t < T = sup {t' : Λ_{t'} ⊆ B_{ρ/3}}` iff some rational `q > t` has `0 ∈ Λ_q` and every dense
  point of `Λ_q` in `cl B_{ρ/3}` (`lt_clusterExitTime_iff_of_familyProcess`), and such `q` are below the stopping time
  at `∂B_{1/2}` of Lemma 2.4, where the family process of `ConeFamilyAEMeasurableStep` sees `Λ`. This also gives the
  null measurability of the exit events `{t < T_ρ}` (`MatedCRTEnv.IsValid.nullMeasurableSet_lt_clusterExitTime`), the
  remaining hypothesis of the reduction of `ConvergenceDivisibleEventMeasurableStep` (Theorem 4.1) to Lemma 2.7.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-! ### Random countable unions -/

section RandomUnion

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}

/-- The mass of the `N`-th partial union of a random union selected by measurable events is a.e. measurable. -/
theorem aemeasurable_measure_accumulate_of_events
    (hμ : ∀ s, MeasurableSet s → AEMeasurable (fun ω => μ ω s) P)
    {C : ℕ → Set ℂ} (hC : ∀ n, MeasurableSet (C n)) {E : ℕ → Set Ω} (hE : ∀ n, MeasurableSet (E n)) (N : ℕ) :
    AEMeasurable (fun ω => μ ω (accumulate (fun n => ⋃ (_ : ω ∈ E n), C n) N)) P := by
  classical
  let B : (Fin (N + 1) → Bool) → Set Ω := fun β => ⋂ i, cond (β i) (E i) (E i)ᶜ
  let K : (Fin (N + 1) → Bool) → Set ℂ := fun β => ⋃ (i : Fin (N + 1)) (_ : β i = true), C i
  have hB : ∀ β, MeasurableSet (B β) := by
    intro β
    refine MeasurableSet.iInter fun i => ?_
    cases β i
    · exact (hE i).compl
    · exact hE i
  have hK : ∀ β, MeasurableSet (K β) := fun β =>
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hC i
  have hsum : AEMeasurable (fun ω => ∑ β : Fin (N + 1) → Bool, (B β).indicator (fun ω => μ ω (K β)) ω) P :=
    Finset.aemeasurable_fun_sum _ fun β _ => (hμ _ (hK β)).indicator (hB β)
  refine hsum.congr (Eventually.of_forall fun ω => ?_)
  dsimp only
  let β₀ : Fin (N + 1) → Bool := fun i => decide (ω ∈ E i)
  rw [Fintype.sum_eq_single β₀ ?_]
  · have hω : ω ∈ B β₀ := by
      refine mem_iInter.2 fun i => ?_
      by_cases h : ω ∈ E i
      · have hb : β₀ i = true := by simp [β₀, h]
        rw [hb]
        exact h
      · have hb : β₀ i = false := by simp [β₀, h]
        rw [hb]
        exact h
    rw [indicator_of_mem hω]
    congr 1
    ext x
    simp only [K, β₀, mem_accumulate, mem_iUnion, decide_eq_true_eq, exists_prop]
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨i, Nat.le_of_lt_succ i.2, hi, hx⟩
    · rintro ⟨n, hn, hn', hx⟩
      exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, hn', hx⟩
  · intro β hβ
    apply indicator_of_notMem
    intro hω
    apply hβ
    funext i
    have hi : ω ∈ cond (β i) (E i) (E i)ᶜ := mem_iInter.1 hω i
    cases hb : β i
    · rw [hb] at hi
      have h : ω ∉ E i := hi
      simp [β₀, h]
    · rw [hb] at hi
      have h : ω ∈ E i := hi
      simp [β₀, h]

/-- **Random countable unions.** If the masses of deterministic Borel sets are a.e. measurable, so is the mass of the
union `⋃_{n : ω ∈ E_n} C_n` of Borel sets selected by measurable events `E_n`. -/
theorem aemeasurable_measure_iUnion_of_events
    (hμ : ∀ s, MeasurableSet s → AEMeasurable (fun ω => μ ω s) P)
    {C : ℕ → Set ℂ} (hC : ∀ n, MeasurableSet (C n)) {E : ℕ → Set Ω} (hE : ∀ n, MeasurableSet (E n)) :
    AEMeasurable (fun ω => μ ω (⋃ n, ⋃ (_ : ω ∈ E n), C n)) P := by
  have h : (fun ω => μ ω (⋃ n, ⋃ (_ : ω ∈ E n), C n)) =
      fun ω => ⨆ N, μ ω (accumulate (fun n => ⋃ (_ : ω ∈ E n), C n) N) := by
    funext ω
    exact measure_iUnion_eq_iSup_accumulate
  rw [h]
  exact AEMeasurable.iSup fun N => aemeasurable_measure_accumulate_of_events hμ hC hE N

/-- `aemeasurable_measure_iUnion_of_events` for a countable index type. -/
theorem aemeasurable_measure_iUnion_of_events' {ι : Type*} [Countable ι] [Nonempty ι]
    (hμ : ∀ s, MeasurableSet s → AEMeasurable (fun ω => μ ω s) P)
    {C : ι → Set ℂ} (hC : ∀ i, MeasurableSet (C i)) {E : ι → Set Ω} (hE : ∀ i, MeasurableSet (E i)) :
    AEMeasurable (fun ω => μ ω (⋃ i, ⋃ (_ : ω ∈ E i), C i)) P := by
  obtain ⟨f, hf⟩ := exists_surjective_nat ι
  refine (aemeasurable_measure_iUnion_of_events hμ (fun n => hC (f n)) (fun n => hE (f n))).congr
    (Eventually.of_forall fun ω => ?_)
  exact congrArg (μ ω) (hf.iUnion_comp (fun i => ⋃ (_ : ω ∈ E i), C i))

end RandomUnion

/-! ### Regular open sets and their traces on a dense sequence -/

/-- The dense sequence of `ℂ` on which random open sets are tested. -/
noncomputable def densePoint : ℕ → ℂ := TopologicalSpace.denseSeq ℂ

theorem denseRange_densePoint : DenseRange densePoint := TopologicalSpace.denseRange_denseSeq ℂ

/-- Inner test: every dense point of `B_{2/(k+1)}(x_d)` lies in `V`. -/
def innerBallTest (V : Set ℂ) (d k : ℕ) : Prop :=
  ∀ j, densePoint j ∈ ball (densePoint d) (2 / ((k : ℝ) + 1)) → densePoint j ∈ V

/-- Exterior test: no dense point of `B_{1/(k+1)}(x_e)` lies in `V`. -/
def exteriorBallTest (V : Set ℂ) (e k : ℕ) : Prop :=
  ∀ j, densePoint j ∈ ball (densePoint e) (1 / ((k : ℝ) + 1)) → densePoint j ∉ V

/-- The boundary layer `U \ B⁻_δ(U)` of a regular open set `U`, computed from the trace `V ∩ {x_j}` of `U` on the dense
sequence (`boundaryLayerOfTrace_eq`). -/
def boundaryLayerOfTrace (δ : ℝ) (V : Set ℂ) : Set ℂ :=
  ⋃ (i : ℕ × ℕ × ℕ × ℕ) (_ : innerBallTest V i.1 i.2.1 ∧ exteriorBallTest V i.2.2.1 i.2.2.2),
    ball (densePoint i.1) (1 / ((i.2.1 : ℝ) + 1)) ∩ ball (densePoint i.2.2.1) δ

/-- A regular open set is the union of the balls `B_{1/(k+1)}(x_d)` which pass the inner test. -/
theorem mem_iff_exists_innerBallTest {U : Set ℂ} (hU : IsOpen U) (hreg : interior (closure U) = U) {x : ℂ} :
    x ∈ U ↔ ∃ d k : ℕ, innerBallTest U d k ∧ x ∈ ball (densePoint d) (1 / ((k : ℝ) + 1)) := by
  constructor
  · intro hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hε three_pos)
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h2 : (2 : ℝ) / ((k : ℝ) + 1) = 2 * (1 / ((k : ℝ) + 1)) := by ring
    obtain ⟨d, hd⟩ := denseRange_densePoint.exists_dist_lt x hk0
    refine ⟨d, k, fun j hj => hball ?_, mem_ball.2 hd⟩
    rw [mem_ball, h2] at hj
    rw [mem_ball]
    linarith [dist_triangle (densePoint j) (densePoint d) x, dist_comm (densePoint d) x]
  · rintro ⟨d, k, htest, hx⟩
    have hsub : ball (densePoint d) (2 / ((k : ℝ) + 1)) ⊆ U := by
      rw [← hreg]
      refine interior_maximal ?_ isOpen_ball
      refine (Dense.open_subset_closure_inter denseRange_densePoint isOpen_ball).trans (closure_mono ?_)
      rintro _ ⟨hz, j, rfl⟩
      exact htest j hz
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h2 : (2 : ℝ) / ((k : ℝ) + 1) = 2 * (1 / ((k : ℝ) + 1)) := by ring
    exact hsub (ball_subset_ball (by rw [h2]; linarith) hx)

/-- For a regular open set `U`, `dist(y, Uᶜ) < δ` iff `y ∈ B_δ(x_e)` for a dense point `x_e` passing an exterior test. -/
theorem infEDist_compl_lt_iff_exists_exteriorBallTest {U : Set ℂ} (hreg : interior (closure U) = U) {δ : ℝ}
    {y : ℂ} :
    infEDist y Uᶜ < ENNReal.ofReal δ ↔ ∃ e k : ℕ, exteriorBallTest U e k ∧ y ∈ ball (densePoint e) δ := by
  constructor
  · intro h
    obtain ⟨z, hz, hyz⟩ := infEDist_lt_iff.1 h
    rw [edist_lt_ofReal] at hyz
    set η := δ - dist y z with hη
    have hη0 : 0 < η := by linarith
    have hzcl : z ∈ closure (closure U)ᶜ := by
      rw [closure_compl, hreg]
      exact hz
    obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.1 hzcl (η / 3) (by positivity)
    obtain ⟨ε, hε, hεw⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl w hw
    have hm : 0 < min ε (η / 3) := lt_min hε (by positivity)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hm)
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hmε := min_le_left ε (η / 3)
    have hmη := min_le_right ε (η / 3)
    obtain ⟨e, he⟩ := denseRange_densePoint.exists_dist_lt w hk0
    refine ⟨e, k, fun j hj hjU => ?_, ?_⟩
    · have hjw : densePoint j ∈ ball w ε := by
        rw [mem_ball] at hj ⊢
        linarith [dist_triangle (densePoint j) (densePoint e) w, dist_comm (densePoint e) w]
      exact hεw hjw (subset_closure hjU)
    · rw [mem_ball]
      linarith [dist_triangle4 y z w (densePoint e), dist_comm (densePoint e) w]
  · rintro ⟨e, k, htest, hy⟩
    have he : densePoint e ∈ Uᶜ := htest e (mem_ball_self (by positivity))
    calc infEDist y Uᶜ ≤ edist y (densePoint e) := infEDist_le_edist_of_mem he
      _ < ENNReal.ofReal δ := edist_lt_ofReal.2 (mem_ball.1 hy)

/-- **The boundary layer from the trace.** If `U` is regular open and `V` has the same trace as `U` on the dense
sequence, then `boundaryLayerOfTrace δ V = U \ B⁻_δ(U)`. -/
theorem boundaryLayerOfTrace_eq {U V : Set ℂ} (hU : IsOpen U) (hreg : interior (closure U) = U)
    (hV : ∀ j, densePoint j ∈ V ↔ densePoint j ∈ U) (δ : ℝ) :
    boundaryLayerOfTrace δ V = U \ innerNbhd δ U := by
  have hVU : boundaryLayerOfTrace δ V = boundaryLayerOfTrace δ U := by
    simp only [boundaryLayerOfTrace, innerBallTest, exteriorBallTest, hV]
  rw [hVU]
  ext y
  have hdiff : y ∈ U \ innerNbhd δ U ↔ y ∈ U ∧ infEDist y Uᶜ < ENNReal.ofReal δ := by
    constructor
    · rintro ⟨hy, hn⟩
      exact ⟨hy, not_le.1 fun h => hn ⟨hy, h⟩⟩
    · rintro ⟨hy, hlt⟩
      exact ⟨hy, fun h => (not_le.2 hlt) h.2⟩
  rw [hdiff]
  simp only [boundaryLayerOfTrace, mem_iUnion, mem_inter_iff, exists_prop]
  constructor
  · rintro ⟨⟨d, k, e, k'⟩, ⟨h1, h2⟩, hy1, hy2⟩
    exact ⟨(mem_iff_exists_innerBallTest hU hreg).2 ⟨d, k, h1, hy1⟩,
      (infEDist_compl_lt_iff_exists_exteriorBallTest hreg).2 ⟨e, k', h2, hy2⟩⟩
  · rintro ⟨hy, hlt⟩
    obtain ⟨d, k, h1, hy1⟩ := (mem_iff_exists_innerBallTest hU hreg).1 hy
    obtain ⟨e, k', h2, hy2⟩ := (infEDist_compl_lt_iff_exists_exteriorBallTest hreg).1 hlt
    exact ⟨⟨d, k, e, k'⟩, ⟨h1, h2⟩, hy1, hy2⟩

section Measurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem measurable_innerBallTest {V : Ω → Set ℂ} (hV : ∀ j, Measurable fun ω => densePoint j ∈ V ω) (d k : ℕ) :
    Measurable fun ω => innerBallTest (V ω) d k := by
  unfold innerBallTest
  exact Measurable.forall fun j => measurable_const.imp (hV j)

theorem measurable_exteriorBallTest {V : Ω → Set ℂ} (hV : ∀ j, Measurable fun ω => densePoint j ∈ V ω)
    (e k : ℕ) : Measurable fun ω => exteriorBallTest (V ω) e k := by
  unfold exteriorBallTest
  exact Measurable.forall fun j => measurable_const.imp (hV j).not

/-- The mass of the boundary layer computed from a random trace with measurable membership events is a.e.
measurable. -/
theorem aemeasurable_measure_boundaryLayerOfTrace {μ : Ω → Measure ℂ}
    (hμ : ∀ s, MeasurableSet s → AEMeasurable (fun ω => μ ω s) P) {V : Ω → Set ℂ}
    (hV : ∀ j, Measurable fun ω => densePoint j ∈ V ω) (δ : ℝ) :
    AEMeasurable (fun ω => μ ω (boundaryLayerOfTrace δ (V ω))) P :=
  aemeasurable_measure_iUnion_of_events' (ι := ℕ × ℕ × ℕ × ℕ) hμ
    (C := fun i => ball (densePoint i.1) (1 / ((i.2.1 : ℝ) + 1)) ∩ ball (densePoint i.2.2.1) δ)
    (fun _ => measurableSet_ball.inter measurableSet_ball)
    (E := fun i => {ω | innerBallTest (V ω) i.1 i.2.1 ∧ exteriorBallTest (V ω) i.2.2.1 i.2.2.2})
    (fun _ => measurableSet_setOfPred.2
      ((measurable_innerBallTest hV _ _).and (measurable_exteriorBallTest hV _ _)))

end Measurable

/-! ### The event of the boundary layer -/

/-- A family of Lemma 2.4 for `ν` (stopped at `∂B_{1/2}`), chosen when one exists. -/
noncomputable def stoppedConeFamily (ν : Measure ℂ) : ℝ × (ℝ → Set ℂ) :=
  Classical.epsilon fun p => 0 < p.1 ∧ IsConeHarmonicBallFamilyOn ν p.2 p.1 ∧ IsStoppedAtHalfBall p.2 p.1

theorem stoppedConeFamily_spec {ν : Measure ℂ} (h : HasConeHarmonicBallsUpToHalfBall ν) :
    0 < (stoppedConeFamily ν).1 ∧ IsConeHarmonicBallFamilyOn ν (stoppedConeFamily ν).2 (stoppedConeFamily ν).1 ∧
      IsStoppedAtHalfBall (stoppedConeFamily ν).2 (stoppedConeFamily ν).1 := by
  obtain ⟨T, hT, Λ, h1, h2⟩ := h
  exact Classical.epsilon_spec (p := fun p : ℝ × (ℝ → Set ℂ) =>
    0 < p.1 ∧ IsConeHarmonicBallFamilyOn ν p.2 p.1 ∧ IsStoppedAtHalfBall p.2 p.1) ⟨(T, Λ), hT, h1, h2⟩

/-- **The exit time through the family process** (deterministic). Let `Λ` be a family of Theorem 2.3 and `Λ'` a
family of Lemma 2.4 stopped at `T`, whose family process is `X`. For `0 < ρ < 1` and `t > 0`, `t < T_ρ` iff some
rational `q > t` has `X(q, 0)` and every dense point `x_j` with `X(q, x_j)` lies in `cl B_{ρ/3}`; then `t < T`. -/
theorem lt_clusterExitTime_iff_of_familyProcess {μ : Measure ℂ} {Λ Λ' : ℝ → Set ℂ} {T : ℝ} {X : ℝ × ℂ → Prop}
    {ρ t : ℝ} (hΛ : IsConeHarmonicBallFamily μ Λ) (hT : 0 < T) (hΛ' : IsConeHarmonicBallFamilyOn μ Λ' T)
    (hstop : IsStoppedAtHalfBall Λ' T) (hX : ∀ (t' : ℝ) (x : ℂ), X (t', x) ↔ t' ∈ Ioo 0 T ∧ x ∈ Λ' t')
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (ht : 0 < t) :
    (t < clusterExitTime Λ ρ ↔
      ∃ q : ℚ, t < q ∧ X ((q : ℝ), 0) ∧ ∀ j, X ((q : ℝ), densePoint j) → ‖densePoint j‖ ≤ ρ / 3) ∧
      (t < clusterExitTime Λ ρ → t ∈ Ioo 0 T) := by
  have heq : EqOn Λ' Λ (Ioo 0 T) := by
    have h := (hΛ.isConeHarmonicBallFamilyOn hT).eqOn hΛ'
    rwa [min_self] at h
  have hcond := hΛ.2.1
  obtain ⟨t₀, ht₀, ht₀sub⟩ := hstop.2 (ρ / 3) (by linarith)
  have hlt₀ : ∀ t', 0 < t' → Λ t' ⊆ ball 0 (ρ / 3) → t' < t₀ := by
    intro t' ht' hsub
    by_contra hle
    exact ht₀sub (by rw [heq ht₀]; exact (hcond.monotoneOn ht₀.1 ht' (not_lt.1 hle)).trans hsub)
  have hbdd : BddAbove {t' : ℝ | 0 < t' ∧ Λ t' ⊆ ball 0 (ρ / 3)} :=
    ⟨t₀, fun t' ht' => (hlt₀ t' ht'.1 ht'.2).le⟩
  have hTdef : clusterExitTime Λ ρ = sSup {t' : ℝ | 0 < t' ∧ Λ t' ⊆ ball 0 (ρ / 3)} := rfl
  have hsup : t < clusterExitTime Λ ρ → ∃ t', (0 < t' ∧ Λ t' ⊆ ball 0 (ρ / 3)) ∧ t < t' := by
    intro h
    rw [hTdef] at h
    rcases Set.eq_empty_or_nonempty {t' : ℝ | 0 < t' ∧ Λ t' ⊆ ball 0 (ρ / 3)} with he | hne
    · rw [he, Real.sSup_empty] at h
      linarith
    · obtain ⟨t', ht', htt'⟩ := exists_lt_of_lt_csSup hne h
      exact ⟨t', ht', htt'⟩
  have hcl : t < clusterExitTime Λ ρ ↔
      ∃ q : ℚ, t < q ∧ X ((q : ℝ), 0) ∧ ∀ j, X ((q : ℝ), densePoint j) → ‖densePoint j‖ ≤ ρ / 3 := by
    constructor
    · intro h
      obtain ⟨t', ⟨ht'0, ht'sub⟩, htt'⟩ := hsup h
      obtain ⟨q, htq, hqt'⟩ := exists_rat_btwn htt'
      have hq0 : (0 : ℝ) < q := ht.trans htq
      have hqT : (q : ℝ) ∈ Ioo 0 T := ⟨hq0, hqt'.trans ((hlt₀ t' ht'0 ht'sub).trans ht₀.2)⟩
      have hΛq : Λ' q = Λ q := heq hqT
      refine ⟨q, htq, (hX _ _).2 ⟨hqT, ?_⟩, fun j hj => ?_⟩
      · rw [hΛq]
        exact hcond.mem q hq0
      · have hj' : densePoint j ∈ Λ' q := ((hX _ _).1 hj).2
        rw [hΛq] at hj'
        exact (mem_ball_zero_iff.1 (ht'sub (hcond.monotoneOn hq0 ht'0 hqt'.le hj'))).le
    · rintro ⟨q, htq, hq0X, hqX⟩
      have hqT : (q : ℝ) ∈ Ioo 0 T := ((hX _ _).1 hq0X).1
      have hΛq : Λ' q = Λ q := heq hqT
      have hopen : IsOpen (Λ q) := by
        rw [← hcond.isRegularOpen q hqT.1]
        exact isOpen_interior
      have hsub : Λ q ⊆ ball 0 (ρ / 3) := by
        rw [← interior_closedBall (0 : ℂ) (div_pos hρ three_pos).ne']
        refine interior_maximal ?_ hopen
        refine (Dense.open_subset_closure_inter denseRange_densePoint hopen).trans
          (closure_minimal ?_ isClosed_closedBall)
        rintro _ ⟨hz, j, rfl⟩
        rw [mem_closedBall_zero_iff]
        exact hqX j ((hX _ _).2 ⟨hqT, by rw [hΛq]; exact hz⟩)
      exact htq.trans_le (le_csSup hbdd ⟨hqT.1, hsub⟩)
  refine ⟨hcl, fun h => ?_⟩
  obtain ⟨t', ⟨ht'0, ht'sub⟩, htt'⟩ := hsup h
  exact ⟨ht, htt'.trans ((hlt₀ t' ht'0 ht'sub).trans ht₀.2)⟩

/-- **The event of the boundary layer through the family process** (deterministic). In the setting of
`lt_clusterExitTime_iff_of_familyProcess`, the event `{t < T_ρ, μ(Λ_t \ B⁻_δ(Λ_t)) ≥ s}` holds iff the exit test of
`lt_clusterExitTime_iff_of_familyProcess` holds and the boundary layer computed from the trace `{z : X(t, z)}` has
mass `≥ s`. -/
theorem boundaryLayerEvent_iff {μ : Measure ℂ} {Λ Λ' : ℝ → Set ℂ} {T : ℝ} {X : ℝ × ℂ → Prop} {ρ t δ s : ℝ}
    (hΛ : IsConeHarmonicBallFamily μ Λ) (hT : 0 < T) (hΛ' : IsConeHarmonicBallFamilyOn μ Λ' T)
    (hstop : IsStoppedAtHalfBall Λ' T) (hX : ∀ (t' : ℝ) (x : ℂ), X (t', x) ↔ t' ∈ Ioo 0 T ∧ x ∈ Λ' t')
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (ht : 0 < t) :
    (t < clusterExitTime Λ ρ ∧ ENNReal.ofReal s ≤ μ (Λ t \ innerNbhd δ (Λ t))) ↔
      ((∃ q : ℚ, t < q ∧ X ((q : ℝ), 0) ∧ ∀ j, X ((q : ℝ), densePoint j) → ‖densePoint j‖ ≤ ρ / 3) ∧
        ENNReal.ofReal s ≤ μ (boundaryLayerOfTrace δ {z | X (t, z)})) := by
  obtain ⟨hcl, htT⟩ := lt_clusterExitTime_iff_of_familyProcess hΛ hT hΛ' hstop hX hρ hρ1 ht
  have heq : EqOn Λ' Λ (Ioo 0 T) := by
    have h := (hΛ.isConeHarmonicBallFamilyOn hT).eqOn hΛ'
    rwa [min_self] at h
  have hcond := hΛ.2.1
  have hlayer : t ∈ Ioo 0 T → boundaryLayerOfTrace δ {z | X (t, z)} = Λ t \ innerNbhd δ (Λ t) := by
    intro htT
    have hopen : IsOpen (Λ t) := by
      rw [← hcond.isRegularOpen t ht]
      exact isOpen_interior
    refine boundaryLayerOfTrace_eq hopen (hcond.isRegularOpen t ht) (fun j => ?_) δ
    rw [← heq htT]
    exact (hX t (densePoint j)).trans (and_iff_right htT)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hcl.1 h1, ?_⟩
    rwa [hlayer (htT h1)]
  · rintro ⟨h1, h2⟩
    have h1' := hcl.2 h1
    refine ⟨h1', ?_⟩
    rwa [← hlayer (htT h1')]

/-- **The family of Lemma 2.4 has a measurable family process.** Under `ConeFamilyAEMeasurableStep` (i) and Lemma
2.4 there is a process `X` with measurable coordinates `ω ↦ X ω (t, x)` which is almost surely the family process of a
family of Lemma 2.4 for `μ_h`. -/
theorem MatedCRTEnv.IsValid.exists_measurable_familyProcess {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hfam : ConeFamilyAEMeasurableStep) (h24 : ConeHarmonicBallsUpToFixedTimeStmt) :
    ∃ X : Ω → ℝ × ℂ → Prop, (∀ p, Measurable fun ω => X ω p) ∧ ∀ᵐ ω ∂S.P, ∃ (T : ℝ) (Λ' : ℝ → Set ℂ),
      0 < T ∧ IsConeHarmonicBallFamilyOn (S.μ ω) Λ' T ∧ IsStoppedAtHalfBall Λ' T ∧
        ∀ (t : ℝ) (x : ℂ), X ω (t, x) ↔ t ∈ Ioo 0 T ∧ x ∈ Λ' t := by
  have hcone := hS.isConeField
  have hpr : ∀ᵐ ω ∂S.P, 0 < (stoppedConeFamily (S.μ ω)).1 ∧
      IsConeHarmonicBallFamilyOn (S.μ ω) (stoppedConeFamily (S.μ ω)).2 (stoppedConeFamily (S.μ ω)).1 ∧
      IsStoppedAtHalfBall (stoppedConeFamily (S.μ ω)).2 (stoppedConeFamily (S.μ ω)).1 := by
    filter_upwards [h24 γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hcone] with ω hω
    obtain ⟨T, hT, Λ', hΛ', hstop, -⟩ := hω
    exact stoppedConeFamily_spec ⟨T, hT, Λ', hΛ', hstop⟩
  have hY : AEMeasurable
      (fun ω => familyProcess (stoppedConeFamily (S.μ ω)).2 (stoppedConeFamily (S.μ ω)).1) S.P :=
    ((hfam γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hcone).1 (fun ω => (stoppedConeFamily (S.μ ω)).1)
      (fun ω => (stoppedConeFamily (S.μ ω)).2) hpr).snd
  obtain ⟨X, hXmeas, hXae⟩ := hY
  refine ⟨X, fun p => (measurable_pi_apply p).comp hXmeas, ?_⟩
  filter_upwards [hpr, hXae] with ω hprω hXω
  exact ⟨_, _, hprω.1, hprω.2.1, hprω.2.2, fun t x => Iff.of_eq (congrFun hXω (t, x)).symm⟩

/-- The exit test event of `lt_clusterExitTime_iff_of_familyProcess` is measurable. -/
theorem measurableSet_exitTest {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ × ℂ → Prop}
    (hXm : ∀ p, Measurable fun ω => X ω p) (t ρ : ℝ) :
    MeasurableSet {ω | ∃ q : ℚ, t < q ∧ X ω ((q : ℝ), 0) ∧
      ∀ j, X ω ((q : ℝ), densePoint j) → ‖densePoint j‖ ≤ ρ / 3} :=
  measurableSet_setOfPred.2 (Measurable.exists fun _ => measurable_const.and
    ((hXm _).and (Measurable.forall fun _ => (hXm _).imp measurable_const)))

/-- **The exit events are null measurable**: `{t < T_ρ}` for the harmonic ball family `Λ` (almost surely), from
`ConeFamilyAEMeasurableStep` and Lemma 2.4. This is the hypothesis `hexit` of
`convergenceDivisibleEventMeasurable_of_local_exit_inputs` (Theorem 4.1). -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_lt_clusterExitTime {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hfam : ConeFamilyAEMeasurableStep) (h24 : ConeHarmonicBallsUpToFixedTimeStmt) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) {t : ℝ}
    (ht : 0 < t) : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P := by
  obtain ⟨X, hXm, hX⟩ := hS.exists_measurable_familyProcess hγ hγ2 hfam h24
  refine (measurableSet_exitTest hXm t ρ).nullMeasurableSet.congr ?_
  filter_upwards [hΛ, hX] with ω hΛω hXω
  obtain ⟨T, Λ', hT, hΛ', hstop, hXω⟩ := hXω
  exact propext (lt_clusterExitTime_iff_of_familyProcess hΛω hT hΛ' hstop hXω hρ hρ1 ht).1.symm

/-- **`BoundaryLayerMeasurableStep` of Proposition 6.1** from the measurability of the harmonic balls of the cone
(`ConeFamilyAEMeasurableStep`, part (i)) and Lemma 2.4 (`ConeHarmonicBallsUpToFixedTimeStmt`, existence only). -/
theorem boundaryLayerMeasurableStep_of_coneFamilyAEMeasurable (𝒮 : SpaceFillingSLEModel)
    (hfam : ConeFamilyAEMeasurableStep) (h24 : ConeHarmonicBallsUpToFixedTimeStmt) :
    BoundaryLayerMeasurableStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ t δ₁ s ht _
  obtain ⟨X, hXm, hX⟩ := hS.exists_measurable_familyProcess hγ hγ2 hfam h24
  have hf : AEMeasurable (fun ω => S.μ ω (boundaryLayerOfTrace δ₁ {z | X ω (t, z)})) S.P :=
    aemeasurable_measure_boundaryLayerOfTrace hS.aemeasurable_lqg_mass (V := fun ω => {z | X ω (t, z)})
      (fun j => hXm (t, densePoint j)) δ₁
  have hF : NullMeasurableSet ({ω | ∃ q : ℚ, t < q ∧ X ω ((q : ℝ), 0) ∧
      ∀ j, X ω ((q : ℝ), densePoint j) → ‖densePoint j‖ ≤ ρ / 3} ∩
      {ω | ENNReal.ofReal s ≤ S.μ ω (boundaryLayerOfTrace δ₁ {z | X ω (t, z)})}) S.P :=
    (measurableSet_exitTest hXm t ρ).nullMeasurableSet.inter (hf.nullMeasurable measurableSet_Ici)
  refine hF.congr ?_
  filter_upwards [hΛ, hX] with ω hΛω hXω
  obtain ⟨T, Λ', hT, hΛ', hstop, hXω⟩ := hXω
  exact propext (boundaryLayerEvent_iff hΛω hT hΛ' hstop hXω hρ hρ1 ht).symm

end MatedCRT
