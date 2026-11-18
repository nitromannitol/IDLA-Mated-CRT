import MatedCRT.FirstPass.Derived.AreaCellAbsorbedContinuousCurveLaw

/-! # Stopping a lattice path at an exit vertex does not change its continuous exit curve -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace MatedCRT

open MeasureTheory _root_.HarmonicBalls LatticeProb
open MatedCRT.ExitCouplingGlue
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped NNReal ENNReal

/-- Constant-step interpolation up to a knot depends only on the vertices up to that knot. -/
theorem constantStepPath_congr_of_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℝ} (hm : 0 ≤ m) (p p' : ℕ → E) (n₀ : ℕ) (hp : ∀ k ≤ n₀, p k = p' k)
    (t : ℝ≥0) (ht : m * (t : ℝ) ≤ n₀) :
    ConstantStepInterpolation.path m p t = ConstantStepInterpolation.path m p' t := by
  have h0 : 0 ≤ m * (t : ℝ) := mul_nonneg hm t.2
  unfold ConstantStepInterpolation.path
  dsimp only
  have hle : ⌊m * (t : ℝ)⌋₊ ≤ n₀ := Nat.floor_le_of_le ht
  rcases hle.lt_or_eq with hlt | heq
  · rw [hp _ hlt.le, hp _ (Nat.succ_le_of_lt hlt)]
  · have hfl : (⌊m * (t : ℝ)⌋₊ : ℝ) ≤ m * (t : ℝ) := Nat.floor_le h0
    have hz : m * (t : ℝ) - ⌊m * (t : ℝ)⌋₊ = 0 := by
      rw [heq] at hfl ⊢
      linarith
    simp only [hz, AffineMap.lineMap_apply_zero]
    exact hp _ heq.le

/-- At a knot the interpolation takes the vertex value. -/
theorem constantStepPath_knot {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℝ} (p : ℕ → E) (n₀ : ℕ) (t : ℝ≥0) (ht : m * (t : ℝ) = n₀) :
    ConstantStepInterpolation.path m p t = p n₀ := by
  unfold ConstantStepInterpolation.path
  dsimp only
  rw [ht, Nat.floor_natCast]
  simp

/-- Stopping a vertex path at an index whose scaled position lies outside `Ub` does not change
the continuous exit curve of the interpolated path. -/
theorem normalizedExitCurve_stopped_eq {X : Type*} (pos : X → EuclideanSpace ℝ (Fin 2)) (a : ℝ) {m : ℝ}
    (hm : 0 < m) (Ub : Set (EuclideanSpace ℝ (Fin 2))) (y : ℕ → X) (n₀ : ℕ) (hout : a • pos (y n₀) ∉ Ub) :
    normalizedPrefixCurve
      (ConstantStepInterpolation.continuousPlanePath m (fun n => a • pos (y (min n₀ n))))
      (continuousExitTime Ub 0 (ConstantStepInterpolation.continuousPlanePath m
        (fun n => a • pos (y (min n₀ n))))).toNNReal =
    normalizedPrefixCurve
      (ConstantStepInterpolation.continuousPlanePath m (fun n => a • pos (y n)))
      (continuousExitTime Ub 0 (ConstantStepInterpolation.continuousPlanePath m
        (fun n => a • pos (y n)))).toNNReal := by
  set p : ℕ → EuclideanSpace ℝ (Fin 2) := fun n => a • pos (y n) with hpdef
  set p' : ℕ → EuclideanSpace ℝ (Fin 2) := fun n => a • pos (y (min n₀ n)) with hp'def
  have hpp : ∀ k ≤ n₀, p k = p' k := by
    intro k hk
    simp [hpdef, hp'def, min_eq_right hk]
  set g := ConstantStepInterpolation.continuousPlanePath m p with hg
  set g' := ConstantStepInterpolation.continuousPlanePath m p' with hg'
  let t₀ : ℝ≥0 := ⟨n₀ / m, by positivity⟩
  have ht₀ : m * (t₀ : ℝ) = n₀ := by
    show m * ((n₀ : ℝ) / m) = n₀
    field_simp
  have hgg : ∀ t : ℝ≥0, t ≤ t₀ → g t = g' t := by
    intro t ht
    have : m * (t : ℝ) ≤ n₀ := by
      rw [← ht₀]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast ht) hm.le
    exact constantStepPath_congr_of_le hm.le p p' n₀ hpp t this
  have hgt₀ : g t₀ = a • pos (y n₀) := constantStepPath_knot p n₀ t₀ ht₀
  have hT : continuousExitTime Ub 0 g ≤ (t₀ : ℝ≥0∞) :=
    continuousExitTime_le_of_not_mem (by simpa [hgt₀] using hout)
  have hT' : continuousExitTime Ub 0 g' ≤ (t₀ : ℝ≥0∞) :=
    continuousExitTime_le_of_not_mem (t := t₀)
      (by rw [← hgg t₀ le_rfl, hgt₀]; simpa using hout)
  have hTT : continuousExitTime Ub 0 g' = continuousExitTime Ub 0 g := by
    apply le_antisymm
    · rw [continuousExitTime_eq_iInf Ub 0 g]
      refine le_iInf fun t => ?_
      by_cases ht : t.val ≤ t₀
      · refine continuousExitTime_le_of_not_mem ?_
        rw [← hgg _ ht]
        exact t.2
      · exact hT'.trans (by exact_mod_cast (not_le.1 ht).le)
    · rw [continuousExitTime_eq_iInf Ub 0 g']
      refine le_iInf fun t => ?_
      by_cases ht : t.val ≤ t₀
      · refine continuousExitTime_le_of_not_mem ?_
        rw [hgg _ ht]
        exact t.2
      · exact hT.trans (by exact_mod_cast (not_le.1 ht).le)
  rw [hTT]
  have hTle : (continuousExitTime Ub 0 g).toNNReal ≤ t₀ :=
    by simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top hT
  unfold normalizedPrefixCurve
  congr 1
  refine ContinuousMap.ext fun u => ?_
  simp only [normalizedPathPrefix_apply]
  refine (hgg _ ?_).symm
  have hu : (u : ℝ) * ((continuousExitTime Ub 0 g).toNNReal : ℝ) ≤ t₀ := by
    calc (u : ℝ) * ((continuousExitTime Ub 0 g).toNNReal : ℝ)
        ≤ 1 * ((continuousExitTime Ub 0 g).toNNReal : ℝ) :=
          mul_le_mul_of_nonneg_right u.2.2 (NNReal.coe_nonneg _)
      _ ≤ t₀ := by rw [one_mul]; exact_mod_cast hTle
  exact_mod_cast hu


/-- Almost surely, the integer simple random walk and the walk stopped on leaving the active
vertices have the same continuous exit curve, when the active cells are exactly those whose scaled
representative lies in `Ub` and the walk cannot step out of the finite set `R` from an active
vertex. -/
theorem areaCell_ae_normalizedExitCurve_stoppedPath
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) (A : Set R)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R → (areaCellConfig h hε (S.mult ε ω)).c v w = 0)
    {m : ℝ} (hm : 0 < m) (a : ℝ) (Ub : Set (EuclideanSpace ℝ (Fin 2)))
    (hout : ∀ x : R, x ∉ A →
      a • areaCellRepresentative h hε (S.mult ε ω) x.1 ∉ Ub)
    (v : R) :
    ∀ᵐ x ∂srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1),
      (fun x : ℕ → ℤ => normalizedPrefixCurve
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε (S.mult ε ω) (euclideanCellEquiv h hε (x n))))
        (continuousExitTime Ub 0 (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε (S.mult ε ω)
            (euclideanCellEquiv h hε (x n))))).toNNReal)
        (ExitDecomposition.stoppedPath {i | ∃ x ∈ A, euclideanCellEquiv h hε i = (x : (areaCellConfig h hε (S.mult ε ω)).cells)} x) =
      normalizedPrefixCurve
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε (S.mult ε ω) (euclideanCellEquiv h hε (x n))))
        (continuousExitTime Ub 0 (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε (S.mult ε ω)
            (euclideanCellEquiv h hε (x n))))).toNNReal := by
  classical
  obtain ⟨D, hDdef⟩ : ∃ D : Set ℤ, D = {i | ∃ x ∈ A, euclideanCellEquiv h hε i =
      (x : (areaCellConfig h hε (S.mult ε ω)).cells)} := ⟨_, rfl⟩
  rw [← hDdef]
  have hmemD : ∀ i, i ∈ D ↔ ∃ x ∈ A, euclideanCellEquiv h hε i =
      (x : (areaCellConfig h hε (S.mult ε ω)).cells) := by
    intro i; rw [hDdef]; rfl
  have hadj : ∀ᵐ x ∂srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1),
      ∀ n, x (n + 1) = x n ∨ S.mult ε ω (x n) (x (n + 1)) ≠ 0 := by
    rw [ae_all_iff]
    intro n
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (WalkSteps.srwLaw_nonadjacent_null (S.mult ε ω) n
        ((euclideanCellEquiv h hε).symm v.1))] with x hx
    exact Classical.not_not.1 hx
  filter_upwards [srwLaw_ae_start (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1), hadj]
    with x h0 hadj
  by_cases htop : vExitTime D x = ⊤
  · rw [ExitDecomposition.stoppedPath_of_top htop]
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 htop
  have hk' : vExitTime D x = (k : ℕ∞) := hk.symm
  obtain ⟨hxk, hj⟩ := (MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec D x k).1 hk'
  have hRk : euclideanCellEquiv h hε (x k) ∈ R := by
    cases k with
    | zero =>
      have hv := (euclideanCellEquiv h hε).apply_symm_apply v.1
      rw [h0]
      exact Eq.subst (motive := fun w => w ∈ R) hv.symm v.2
    | succ j =>
      by_contra hnot
      obtain ⟨z, hz, hzx⟩ := (hmemD _).1 (hj j (Nat.lt_succ_self j))
      rcases hadj j with hh | hh
      · exact hxk ((hmemD _).2 (hh ▸ ⟨z, hz, hzx⟩))
      · have hc := areaCellConfig_conductance h hε (S.mult ε ω) (x j) (x (j + 1))
        rw [hzx] at hc
        have := hretain z hz (euclideanCellEquiv h hε (x (j + 1))) hnot
        rw [hc] at this
        exact hh (by exact_mod_cast this)
  obtain ⟨w, hw⟩ : ∃ w : R, (w : (areaCellConfig h hε (S.mult ε ω)).cells) =
      euclideanCellEquiv h hε (x k) := ⟨⟨_, hRk⟩, rfl⟩
  have hwA : w ∉ A := fun hwA => hxk ((hmemD _).2 ⟨w, hwA, hw.symm⟩)
  have hstop : ∀ n, ExitDecomposition.stoppedPath D x n = x (min k n) := by
    intro n
    simp only [ExitDecomposition.stoppedPath, hk']
    rcases le_total k n with hkn | hkn
    · rw [min_eq_left (by exact_mod_cast hkn : (k : ℕ∞) ≤ n), min_eq_left hkn,
        ENat.toNat_natCast]
    · rw [min_eq_right (by exact_mod_cast hkn : (n : ℕ∞) ≤ k), min_eq_right hkn,
        ENat.toNat_natCast]
  have hout' := hout w hwA
  rw [hw] at hout'
  have key := normalizedExitCurve_stopped_eq
    (X := (areaCellConfig h hε (S.mult ε ω)).cells)
    (areaCellRepresentative h hε (S.mult ε ω)) a hm Ub
    (fun n => euclideanCellEquiv h hε (x n)) k hout'
  simp only [hstop]
  exact key


/-- The finite cell walk absorbed outside the active cells has the continuous exit-curve law of the
unstopped integer simple random walk, when the active cells are those whose scaled representative
lies in the open set `U`. -/
theorem areaCell_finite_sourceContinuousExitCurve_law_unstopped
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε) (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] (A : Set R)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R →
      (areaCellConfig h hε (S.mult ε ω)).c v w = 0)
    (hpos : ∀ v ∈ A, 0 < (LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).totalConductance v)
    (v : R) {m : ℝ} (hm : 0 < m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (hout : ∀ x : R, x ∉ A → a • areaCellRepresentative h hε (S.mult ε ω) x.1 ∉
      Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) :
    (((LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).trajectoryLaw A hpos v).map
      (fun p n => (p n : (areaCellConfig h hε (S.mult ε ω)).cells))).map
      (fun y => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (ConstantStepInterpolation.continuousPlanePath m
            (fun n => a • areaCellRepresentative h hε (S.mult ε ω) (y n)))
          (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
            (ConstantStepInterpolation.continuousPlanePath m
              (fun n => a • areaCellRepresentative h hε (S.mult ε ω) (y n)))).toNNReal)) =
    (srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1)).map
      (fun x => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (complexToEuclideanPath (a • interpPathCM (vertexPoint ε (S.η ω)) hm.le x))
          (pathExitTime U (a • interpPathCM (vertexPoint ε (S.η ω)) hm.le x)).toNNReal)) := by
  classical
  refine (areaCell_finite_sourceContinuousExitCurve_law S ω h hε hlf R A hretain hpos v hm.le a
    hU).trans ?_
  have hp : Measurable (fun x : ℕ → ℤ =>
      a • interpPathCM (vertexPoint ε (S.η ω)) hm.le x) :=
    ((continuous_interpPathCM (vertexPoint ε (S.η ω)) hm.le).const_smul a).measurable
  have hg := (CurveSpaceComparison.isometryEquiv 2).continuous.measurable.comp
    ((measurable_paperNormalizedExitCurve hU).comp hp)
  change Measurable (fun x : ℕ → ℤ => CurveSpaceComparison.isometryEquiv 2
    (normalizedPrefixCurve
      (complexToEuclideanPath (a • interpPathCM (vertexPoint ε (S.η ω)) hm.le x))
      (pathExitTime U (a • interpPathCM (vertexPoint ε (S.η ω)) hm.le x)).toNNReal)) at hg
  rw [Measure.map_map hg (ExitDecomposition.measurable_stoppedPath _)]
  refine Measure.map_congr ?_
  filter_upwards [areaCell_ae_normalizedExitCurve_stoppedPath S ω h hε R A hretain hm a
    (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) hout v] with x hx
  simp only [Function.comp_apply]
  rw [← areaCell_scaled_normalizedExitCurve_eq h hε (S.mult ε ω) hm.le a
    (ExitDecomposition.stoppedPath _ x) U, ← areaCell_scaled_normalizedExitCurve_eq h hε
    (S.mult ε ω) hm.le a x U]
  exact congrArg (CurveSpaceComparison.isometryEquiv 2) hx

end MatedCRT
end
