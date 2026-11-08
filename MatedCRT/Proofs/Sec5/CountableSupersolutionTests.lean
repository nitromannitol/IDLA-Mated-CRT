import MatedCRT.Proofs.Sec5.SupersolutionBorelCode

/-!
# Countable `C²`-dense families of nonnegative tests and the LaplacianLE bridge (steps2-r3, lines 1016-1026)

The Borel supersolution relation of `SupersolutionBorelCode.lean` takes two residuals as Props. This file proves them.

* `countableC2DenseStmt` (residual A) and `countableC2FamilyStmt` (residual A′): for every radius `R > 0` there is a
  countable family `φs` of nonnegative smooth tests supported in `ball 0 R` such that every nonnegative smooth test `φ`
  supported in `ball 0 R` is approximated uniformly on `ℂ`, for the function and for its Laplacian.
  The family is chosen inside the nonnegative tests. For a compact disk `K = closedBall 0 r`, `r < R`, the nonnegative
  tests supported in `K` are embedded as `ψ ↦ (ψ|K, Δψ|K) ∈ C(K,ℝ) × C(K,ℝ)`. The range is separable
  (`ContinuousMap.instSeparableSpace`), so it has a countable dense subset, and the preimages of that subset form a
  countable dense family of nonnegative tests on `K`. The disks `closedBall 0 (R - R/(n+2))` exhaust `ball 0 R`; the
  families over the exhaustion are united with the zero test. No sign change follows an approximation.
* `laplacianLESection_of_countable` (residual B): for a measure `μ` with `μ (ball 0 R) < ∞` and such a family, the
  countable distributional inequalities `∫ w̃ Δφ_j ≤ ∫ φ_j dμ` hold for a continuous trace `w` iff `LaplacianLE w̃ μ (ball 0 R)`,
  i.e. `Δw̃ ≤ μ` in `ball 0 R` in the sense of Armitage-Gardiner (distributional Laplacian on the disk).

No literature input is used. Mathematical source: steps2-r3.tex 1016-1026 (relation eq:supersolutionrelation at 957-961,
LaplacianLE identification at 962-966).
-/

open HarmonicBalls

namespace MatedCRT

namespace ConeOriginNull

open MeasureTheory Filter Topology Set Metric
open MatedCRT.CircleProcessSpace
open scoped ContDiff

/-! ### 1. Exhaustion of `ball 0 R` by closed disks -/

/-- The exhaustion radii `R - R/(n+2)` of `ball 0 R`: each is `< R`, and they increase to `R`. -/
noncomputable def exhaustionRadius (R : ℝ) (n : ℕ) : ℝ :=
  R - R / ((n : ℝ) + 2)

theorem exhaustionRadius_lt {R : ℝ} (hR : 0 < R) (n : ℕ) : exhaustionRadius R n < R := by
  unfold exhaustionRadius
  have : 0 < R / ((n : ℝ) + 2) := div_pos hR (by positivity)
  linarith

/-- Every compact support of a test function on `ball 0 R` lies in some closed exhaustion disk. -/
theorem exists_exhaustion_of_isTestFunction {R : ℝ} {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) R) φ) :
    ∃ n : ℕ, tsupport φ ⊆ closedBall (0 : ℂ) (exhaustionRadius R n) := by
  rcases (tsupport φ).eq_empty_or_nonempty with hempty | hne
  · exact ⟨0, by rw [hempty]; exact empty_subset _⟩
  obtain ⟨x, hxK, hmax⟩ := hφ.2.1.isCompact.exists_isMaxOn hne continuous_norm.continuousOn
  have hxR : ‖x‖ < R := mem_ball_zero_iff.1 (hφ.2.2 hxK)
  have hRρ : 0 < R - ‖x‖ := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (R / (R - ‖x‖))
  refine ⟨n, fun y hy => ?_⟩
  have hyx : ‖y‖ ≤ ‖x‖ := isMaxOn_iff.1 hmax y hy
  rw [mem_closedBall_zero_iff]
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hdiv : R / ((n : ℝ) + 2) ≤ R - ‖x‖ := by
    rw [div_le_iff₀ h2]
    rw [div_lt_iff₀ hRρ] at hn
    nlinarith
  unfold exhaustionRadius
  linarith

/-! ### 2. Nonnegative tests on a closed disk -/

/-- The nonnegative smooth tests supported in the closed disk `closedBall 0 r` (test functions of Armitage-Gardiner). -/
def nonnegTestsOn (r : ℝ) : Set (ℂ → ℝ) :=
  {ψ | IsTestFunction (closedBall (0 : ℂ) r) ψ ∧ ∀ z, 0 ≤ ψ z}

theorem nonnegTestsOn_isTest {r : ℝ} {ψ : ℂ → ℝ} (h : ψ ∈ nonnegTestsOn r) :
    IsTestFunction (closedBall (0 : ℂ) r) ψ :=
  h.1

theorem nonnegTestsOn_contDiff {r : ℝ} {ψ : ℂ → ℝ} (h : ψ ∈ nonnegTestsOn r) : ContDiff ℝ ∞ ψ :=
  h.1.1

/-- A function vanishing off the closed disk `closedBall 0 r` (with `tsupport` in it) has zero value and zero
Laplacian there. -/
theorem value_laplacian_eq_zero_of_notMem {r : ℝ} {f : ℂ → ℝ} (hf : tsupport f ⊆ closedBall (0 : ℂ) r) {z : ℂ}
    (hz : z ∉ closedBall (0 : ℂ) r) : f z = 0 ∧ Laplacian.laplacian f z = 0 :=
  ⟨image_eq_zero_of_notMem_tsupport fun h => hz (hf h),
    laplacian_eq_zero_of_notMem_tsupport fun h => hz (hf h)⟩

/-- The embedding `ψ ↦ (ψ|K, Δψ|K)` of a nonnegative test supported in the compact disk `K = closedBall 0 r` into
`C(K,ℝ) × C(K,ℝ)`: the function and its Laplacian restricted to `K`. -/
noncomputable def c2Embedding (r : ℝ) (ψ : nonnegTestsOn r) :
    C(closedBall (0 : ℂ) r, ℝ) × C(closedBall (0 : ℂ) r, ℝ) :=
  (⟨fun x => ψ.1 x.1, (nonnegTestsOn_contDiff ψ.2).continuous.comp continuous_subtype_val⟩,
    ⟨fun x => Laplacian.laplacian ψ.1 x.1,
      (continuous_laplacian_of_contDiff (nonnegTestsOn_contDiff ψ.2)).comp continuous_subtype_val⟩)

/-- The range of the embedding has a countable dense subset inside the range: `C(K,ℝ) × C(K,ℝ)` is second countable
for the compact metric space `K` (`ContinuousMap.instSeparableSpace`), so every subset is separable. -/
theorem exists_countable_dense_range_c2Embedding (r : ℝ) :
    ∃ T : Set (C(closedBall (0 : ℂ) r, ℝ) × C(closedBall (0 : ℂ) r, ℝ)), T.Countable ∧
      T ⊆ Set.range (c2Embedding r) ∧ Set.range (c2Embedding r) ⊆ closure T :=
  TopologicalSpace.exists_countable_dense_subset _

/-- **Countable dense family on one disk.** For each `r`, there is a countable set `D` of nonnegative smooth tests
supported in `closedBall 0 r` such that every nonnegative test `ψ` supported there is approximated within `δ` on `ℂ`,
for the function and for its Laplacian, by a member of `D`. The members of `D` are nonnegative (no sign change). -/
theorem exists_countable_dense_nonnegTestsOn (r : ℝ) :
    ∃ D : Set (ℂ → ℝ), D.Countable ∧ D ⊆ nonnegTestsOn r ∧
      ∀ ψ ∈ nonnegTestsOn r, ∀ δ : ℝ, 0 < δ → ∃ φ ∈ D,
        (∀ z, |φ z - ψ z| ≤ δ) ∧ ∀ z, |Laplacian.laplacian φ z - Laplacian.laplacian ψ z| ≤ δ := by
  obtain ⟨T, hTc, hTr, hTd⟩ := exists_countable_dense_range_c2Embedding r
  have hsurj : ∀ t : T, ∃ y : nonnegTestsOn r, c2Embedding r y = (t : _) := fun t => hTr t.2
  choose g hg using hsurj
  have : Countable T := hTc.to_subtype
  refine ⟨Set.range fun t : T => (g t).1, Set.countable_range _, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact (g t).2
  · intro ψ hψ δ hδ
    obtain ⟨t, htT, hdist⟩ := Metric.mem_closure_iff.1 (hTd (Set.mem_range_self ⟨ψ, hψ⟩)) δ hδ
    have hgt : c2Embedding r (g ⟨t, htT⟩) = t := hg ⟨t, htT⟩
    have hdist' : dist (c2Embedding r ⟨ψ, hψ⟩) (c2Embedding r (g ⟨t, htT⟩)) < δ := by
      rw [hgt]; exact hdist
    rw [Prod.dist_eq, max_lt_iff] at hdist'
    have hcl : ∀ z : ℂ, ∀ hz : z ∈ closedBall (0 : ℂ) r,
        |(g ⟨t, htT⟩).1 z - ψ z| ≤ δ ∧
          |Laplacian.laplacian (g ⟨t, htT⟩).1 z - Laplacian.laplacian ψ z| ≤ δ := by
      intro z hz
      have e1 := (ContinuousMap.dist_lt_iff hδ).1 hdist'.1 ⟨z, hz⟩
      have e2 := (ContinuousMap.dist_lt_iff hδ).1 hdist'.2 ⟨z, hz⟩
      rw [Real.dist_eq, abs_sub_comm] at e1 e2
      exact ⟨e1.le, e2.le⟩
    have hA : ∀ z, |(g ⟨t, htT⟩).1 z - ψ z| ≤ δ ∧
        |Laplacian.laplacian (g ⟨t, htT⟩).1 z - Laplacian.laplacian ψ z| ≤ δ := by
      intro z
      by_cases hz : z ∈ closedBall (0 : ℂ) r
      · exact hcl z hz
      · obtain ⟨g1, g2⟩ := value_laplacian_eq_zero_of_notMem (nonnegTestsOn_isTest (g ⟨t, htT⟩).2 |>.2.2) hz
        obtain ⟨p1, p2⟩ := value_laplacian_eq_zero_of_notMem (nonnegTestsOn_isTest hψ |>.2.2) hz
        simp [g1, g2, p1, p2, hδ.le]
    exact ⟨(g ⟨t, htT⟩).1, ⟨⟨t, htT⟩, rfl⟩, fun z => (hA z).1, fun z => (hA z).2⟩

/-! ### 3. The countable `C²`-dense family on `ball 0 R` (residuals A and A′) -/

/-- **Countable `C²`-dense family (steps2-r3 1016-1026; residual A′ and A).** For every `R > 0` there is a countable
family of nonnegative smooth tests supported in `ball 0 R`, which approximates every nonnegative smooth test supported
in `ball 0 R`, uniformly on `ℂ` for the function and for its Laplacian. -/
theorem exists_countable_c2DenseFamily {R : ℝ} (hR : 0 < R) :
    ∃ φs : ℕ → ℂ → ℝ, (∀ j, IsTestFunction (ball (0 : ℂ) R) (φs j) ∧ ∀ z, 0 ≤ φs j z) ∧
      CountableC2DenseStmt R φs := by
  choose D hDc hDsub hDdense using fun n : ℕ => exists_countable_dense_nonnegTestsOn (exhaustionRadius R n)
  obtain ⟨φs, hφs⟩ := ((Set.countable_iUnion hDc).insert 0).exists_eq_range (Set.insert_nonempty _ _)
  have htest : ∀ ψ ∈ insert (0 : ℂ → ℝ) (⋃ n, D n), IsTestFunction (ball (0 : ℂ) R) ψ ∧ ∀ z, 0 ≤ ψ z := by
    intro ψ hψ
    rcases mem_insert_iff.1 hψ with rfl | hψ
    · exact ⟨⟨contDiff_zero_fun, HasCompactSupport.zero, by simp⟩, fun z => by simp⟩
    · obtain ⟨n, hn⟩ := mem_iUnion.1 hψ
      obtain ⟨hI, hnn⟩ := hDsub n hn
      exact ⟨⟨hI.1, hI.2.1, hI.2.2.trans (closedBall_subset_ball (exhaustionRadius_lt hR n))⟩, hnn⟩
  refine ⟨φs, fun j => htest (φs j) (by rw [hφs]; exact Set.mem_range_self j), ?_⟩
  intro φ hφ hφ0 ε hε
  obtain ⟨n, hn⟩ := exists_exhaustion_of_isTestFunction (R := R) hφ
  obtain ⟨ψ, hψD, hψ1, hψ2⟩ := hDdense n φ ⟨⟨hφ.1, hφ.2.1, hn⟩, fun z => hφ0 z⟩ ε hε
  have hψS : ψ ∈ insert (0 : ℂ → ℝ) (⋃ n, D n) := mem_insert_of_mem _ (mem_iUnion.2 ⟨n, hψD⟩)
  rw [hφs] at hψS
  obtain ⟨j, rfl⟩ := hψS
  exact ⟨j, hψ1, hψ2⟩

/-- Residual A′ (steps2-r3 1016-1026): the countable `C²`-dense family exists for every radius. -/
theorem countableC2FamilyStmt_holds : CountableC2FamilyStmt :=
  fun _ hR => exists_countable_c2DenseFamily hR

/-! ### 4. The LaplacianLE bridge (residual B) -/

/-- A smooth test supported in `ball 0 R` is `μ`-integrable when `μ (ball 0 R) < ∞`. -/
theorem integrable_of_isTestFunction_ball {μ : Measure ℂ} {R : ℝ} (hμ : μ (ball (0 : ℂ) R) < ⊤)
    {ψ : ℂ → ℝ} (hψ : IsTestFunction (ball (0 : ℂ) R) ψ) : Integrable ψ μ := by
  have : Fact (μ (ball (0 : ℂ) R) < ⊤) := ⟨hμ⟩
  rw [← integrableOn_iff_integrable_of_support_subset ((subset_tsupport ψ).trans hψ.2.2)]
  exact Continuous.integrable_of_hasCompactSupport hψ.1.continuous hψ.2.1

/-- **LaplacianLE bridge (steps2-r3 1016-1026; residual B).** Let `μ (ball 0 R) < ∞` and let `φs` be a countable family
of nonnegative smooth tests in `ball 0 R` which is `C²`-dense (`CountableC2DenseStmt`). Then for every continuous trace
`w` the countable distributional inequalities `∫ w̃ Δφ_j ≤ ∫ φ_j dμ` hold iff `Δw̃ ≤ μ` in `ball 0 R`
(`LaplacianLE`). The forward direction passes from the countable family to all nonnegative tests by uniform
approximation of the tests and of their Laplacians on the common support disk. -/
theorem laplacianLESection_of_countable (μ : Measure ℂ) {R : ℝ} (hR : 0 < R) (φs : ℕ → ℂ → ℝ) :
    LaplacianLESectionStmt μ hR φs := by
  intro hμ hfam hC2 w
  constructor
  · intro h
    refine ⟨(continuous_extendClosedBall hR w).continuousOn.locallyIntegrableOn measurableSet_ball, ?_⟩
    intro φ hφ hφ0 hint
    have hWc : Continuous (extendClosedBall 0 R hR w) := continuous_extendClosedBall hR w
    obtain ⟨CW, hCW⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hWc.continuousOn
    have hCW0 : 0 ≤ CW := le_trans (norm_nonneg _) (hCW 0 (mem_closedBall_self hR.le))
    have hV0 : 0 ≤ volume.real (closedBall (0 : ℂ) R) := measureReal_nonneg
    have hm0 : 0 ≤ μ.real (ball (0 : ℂ) R) := measureReal_nonneg
    have hK : 0 < μ.real (ball (0 : ℂ) R) + CW * volume.real (closedBall (0 : ℂ) R) + 1 := by
      have := mul_nonneg hCW0 hV0
      linarith
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ,
        δ = ε / (μ.real (ball (0 : ℂ) R) + CW * volume.real (closedBall (0 : ℂ) R) + 1) := ⟨_, rfl⟩
    have hδ : 0 < δ := by rw [hδdef]; exact div_pos hε hK
    have hδK : δ * (μ.real (ball (0 : ℂ) R) + CW * volume.real (closedBall (0 : ℂ) R) + 1) = ε := by
      rw [hδdef]; exact div_mul_cancel₀ ε hK.ne'
    obtain ⟨j, hj1, hj2⟩ := hC2 φ hφ hφ0 δ hδ
    have hφj : IsTestFunction (ball (0 : ℂ) R) (φs j) := (hfam j).1
    have hAj : ∫ z, extendClosedBall 0 R hR w z * Laplacian.laplacian (φs j) z ≤ ∫ z, φs j z ∂μ := h j
    -- Step 1: the Laplacian error is at most `CW · δ · vol(closedBall 0 R)`.
    have hstep1 : (∫ z, extendClosedBall 0 R hR w z * Laplacian.laplacian φ z)
        - (∫ z, extendClosedBall 0 R hR w z * Laplacian.laplacian (φs j) z) ≤
          CW * δ * volume.real (closedBall (0 : ℂ) R) := by
      have hiA := integrable_extend_mul_laplacian hR w hφ.1 hφ.2.1
      have hiAj := integrable_extend_mul_laplacian hR w hφj.1 hφj.2.1
      rw [← integral_sub hiA hiAj]
      have hbound : ∀ z, ‖extendClosedBall 0 R hR w z * Laplacian.laplacian φ z
          - extendClosedBall 0 R hR w z * Laplacian.laplacian (φs j) z‖
            ≤ (closedBall (0 : ℂ) R).indicator (fun _ => CW * δ) z := by
        intro z
        by_cases hz : z ∈ closedBall (0 : ℂ) R
        · rw [indicator_of_mem hz]
          have h1 : ‖extendClosedBall 0 R hR w z‖ ≤ CW := hCW z hz
          have h2 : ‖Laplacian.laplacian φ z - Laplacian.laplacian (φs j) z‖ ≤ δ := by
            rw [Real.norm_eq_abs, abs_sub_comm]; exact hj2 z
          calc ‖extendClosedBall 0 R hR w z * Laplacian.laplacian φ z
                - extendClosedBall 0 R hR w z * Laplacian.laplacian (φs j) z‖
              = ‖extendClosedBall 0 R hR w z‖ *
                  ‖Laplacian.laplacian φ z - Laplacian.laplacian (φs j) z‖ := by
                rw [← mul_sub, norm_mul]
            _ ≤ CW * δ := mul_le_mul h1 h2 (norm_nonneg _) hCW0
        · rw [indicator_of_notMem hz]
          have e1 := (value_laplacian_eq_zero_of_notMem
            (hφ.2.2.trans ball_subset_closedBall) hz).2
          have e2 := (value_laplacian_eq_zero_of_notMem
            (hφj.2.2.trans ball_subset_closedBall) hz).2
          rw [e1, e2]
          simp
      have hint_ind : Integrable ((closedBall (0 : ℂ) R).indicator (fun _ => CW * δ)) :=
        (integrable_indicator_iff measurableSet_closedBall).2
          (integrableOn_const measure_closedBall_lt_top.ne)
      have hnorm := norm_integral_le_of_norm_le hint_ind (ae_of_all _ hbound)
      rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Real.norm_eq_abs] at hnorm
      linarith [le_abs_self (∫ z, (extendClosedBall 0 R hR w z * Laplacian.laplacian φ z
        - extendClosedBall 0 R hR w z * Laplacian.laplacian (φs j) z))]
    -- Step 2: the mass error is at most `δ · μ(ball 0 R)`.
    have hstep2 : ∫ z, φs j z ∂μ ≤ ∫ z, φ z ∂μ + δ * μ.real (ball (0 : ℂ) R) := by
      have hind : Integrable ((ball (0 : ℂ) R).indicator (fun _ => δ)) μ :=
        (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const hμ.ne)
      have hmono : ∫ z, φs j z ∂μ ≤ ∫ z, (φ z + (ball (0 : ℂ) R).indicator (fun _ => δ) z) ∂μ := by
        refine integral_mono (integrable_of_isTestFunction_ball hμ hφj) (hint.add hind) ?_
        intro z
        by_cases hz : z ∈ ball (0 : ℂ) R
        · simp only [indicator_of_mem hz]
          have := (abs_sub_le_iff.1 (hj1 z)).1
          linarith
        · simp only [indicator_of_notMem hz]
          have e1 : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hφ.2.2 h)
          have e2 : φs j z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hφj.2.2 h)
          rw [e1, e2]
          simp
      rw [integral_add hint hind, integral_indicator_const _ measurableSet_ball, smul_eq_mul] at hmono
      linarith
    -- Step 3: combine, using `δ · K = ε` for `K = μ(ball) + CW · vol + 1`.
    linarith [hstep1, hAj, hstep2, hδK, hδ]
  · intro hLE j
    exact hLE.2 (φs j) (hfam j).1 (fun z => (hfam j).2 z)
      (integrable_of_isTestFunction_ball hμ (hfam j).1)

/-! ### 5. Section of the relation with the residuals discharged -/

/-- The section of the Borel relation with residual B discharged by `laplacianLESection_of_countable`: the same
statement as `mem_supersolutionRelation_iff_of_residuals`, with the LaplacianLE residual supplied here. -/
theorem mem_supersolutionRelation_iff_of_countable (γ t : ℝ) {R : ℝ} (hR : 0 < R) {φs : ℕ → ℂ → ℝ}
    {ps : ℕ → ℂ} (hps : ∀ k, ps k ∈ closedBall (0 : ℂ) R \ {0})
    (hdense : ∀ x ∈ closedBall (0 : ℂ) R \ {0}, x ∈ closure (range ps))
    {μ : Measure ℂ} (hμ : μ (ball 0 R) < ⊤)
    (hfam : ∀ j, IsTestFunction (ball 0 R) (φs j) ∧ ∀ z, 0 ≤ φs j z)
    (hC2 : CountableC2DenseStmt R φs)
    (c : PosCircleFns) (hmass : ∀ j, massLimit γ (φs j) c = ∫ z, φs j z ∂μ) (w : BallFns R) :
    (c, w) ∈ supersolutionRelation γ t hR φs ps ↔ w ∈ superTraces μ R t :=
  mem_supersolutionRelation_iff_of_residuals γ t hR hps hdense hμ hfam hC2
    (laplacianLESection_of_countable μ hR φs) c hmass w

end ConeOriginNull

end MatedCRT
