import MatedCRT.FirstPass.Derived.EqLawPerOmega
import LatticeProb.Prob.PathSpaceTightness

/-!
# The path modulus of the quenched walk laws from the cone-rescaled stopped walks

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), proof of Proposition 6.1 (the second condition of Lemma 6.3, equicontinuity of the paths of
the *unstopped* walks).  For a fixed environment `ω` we bound the probability that the interpolated walk of
speed `m_ε` from a vertex of `V^ε(B_{R+1})` has path modulus more than `1 / L` at scale `δ` on `[0, L]` (the
event `LatticeProb.pathModulusFailure L δ`) by estimates for the cone-rescaled curve `η2 s = R_b⁻¹ η(b s)` at
mesh `ε / b`:

* `measurableSet_pathModulusFailure_complex`: the modulus event is open, hence measurable;
* `interp_mem_pathModulusFailure_imp_oscillation`: deterministic bridge from the modulus event of the
  interpolated walk of speed `lam * m'` along `v = R_b v'`, `lam ≤ 1`, to the oscillation event of the walk of
  speed `m'` along `v'` before its exit time from `A`, when the exit time is at least `lam * m' * L`;
* `walkPathFailure_le_of_rescaled`: if (i) the walk of the rescaled curve from every vertex of
  `V^{ε/b}(B_{1/4})` leaves the interior vertices of `B_{1/2}` before time `s b / ε` with probability at most
  `κ` and (ii) the stopped interpolated walks of the rescaled curve from the vertices of `V^{ε/b}(B_{1/2})`
  have oscillation more than `1 / (L M)` over windows of length at most `δ` with probability at most `θ`, then
  the unstopped walks from the vertices of `V^ε(B_{R+1})` have path modulus more than `1 / L` at scale `δ`
  on `[0, L]` with probability at most `κ + θ`, whenever `4 (R + 2) < R_b ≤ M`.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric LatticeProb
open scoped ENNReal NNReal
open MarkovProcess (ContinuousPath)
open MatedCRT.ExitCouplingGlue

/-- The path modulus event `pathModulusFailure L δ` of complex-valued paths is open for the compact-open
topology, hence measurable. -/
theorem measurableSet_pathModulusFailure_complex (L : ℝ) (δ : ℝ≥0) :
    MeasurableSet (pathModulusFailure (E := ℂ) L δ) := by
  have h : pathModulusFailure (E := ℂ) L δ = ⋃ (s : ℝ≥0) (t : ℝ≥0)
      (_ : (s : ℝ) ≤ L ∧ (t : ℝ) ≤ L ∧ |(s : ℝ) - t| ≤ δ),
      {f : C(ℝ≥0, ℂ) | 1 / L < dist (f s) (f t)} := by
    ext f
    simp only [pathModulusFailure, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, and_assoc]
  rw [h]
  refine (isOpen_iUnion fun s => isOpen_iUnion fun t => isOpen_iUnion fun _ => ?_).measurableSet
  exact isOpen_lt continuous_const
    ((continuous_eval_const s).dist (continuous_eval_const t))

/-- **From the path modulus of the unstopped walk to the oscillation of the stopped walk.**  Let `v = R_b v'`,
`lam ≤ 1`, and suppose the exit time of the walk `X` from `A` is a natural number `n` with
`lam * m' * L ≤ n`.  If the interpolated walk of speed `lam * m'` along `v` has path modulus more than `1 / L`
at scale `δ` on `[0, L]`, then the interpolated walk of speed `m'` along `v'` has oscillation more than
`1 / (L M)` over a window of length at most `δ` before the exit time `n / m'`, when `R_b ≤ M`. -/
theorem interp_mem_pathModulusFailure_imp_oscillation {v v' : ℤ → ℂ} {Rb : ℝ} (hRb : 0 < Rb)
    (hv : ∀ k, v k = (Rb : ℂ) * v' k) {lam m' : ℝ≥0} (hlam : lam ≤ 1) (hm' : 0 < m') (A : Set ℤ)
    {L M : ℝ} (hL : 0 < L) (hRbM : Rb ≤ M) (δ : ℝ≥0) (X : ℕ → ℤ) {n : ℕ}
    (hn : vExitTime A X = n) (hnL : ((lam * m' : ℝ≥0) : ℝ) * L ≤ n)
    (hX : interpPathCM v (lam * m').coe_nonneg X ∈ pathModulusFailure (E := ℂ) L δ) :
    ∃ a c : ℝ≥0, a ≤ ((vExitTime A X).toNat : ℝ≥0) / m' ∧ c ≤ ((vExitTime A X).toNat : ℝ≥0) / m' ∧
      dist a c ≤ δ ∧ 1 / (L * M) < dist (interpPathFn v' m' X a) (interpPathFn v' m' X c) := by
  obtain ⟨s, t, hs, ht, hst, hlt⟩ := hX
  have hscale : ∀ u : ℝ≥0, interpPathCM v (lam * m').coe_nonneg X u =
      (Rb : ℂ) * interpPathFn v' m' X (lam * u) := fun u =>
    StoppedWalkScaling.interpPathCM_scale Rb v v' hv lam m' X u
  have htn : (vExitTime A X).toNat = n := by rw [hn]; simp
  have hle : ∀ u : ℝ≥0, (u : ℝ) ≤ L → lam * u ≤ ((vExitTime A X).toNat : ℝ≥0) / m' := by
    intro u hu
    rw [htn, le_div_iff₀ hm']
    rw [← NNReal.coe_le_coe]
    have h1 : ((lam * m' : ℝ≥0) : ℝ) * (u : ℝ) ≤ ((lam * m' : ℝ≥0) : ℝ) * L :=
      mul_le_mul_of_nonneg_left hu (NNReal.coe_nonneg _)
    push_cast at h1 hnL ⊢
    nlinarith
  refine ⟨lam * s, lam * t, hle s hs, hle t ht, ?_, ?_⟩
  · rw [NNReal.dist_eq]
    push_cast
    rw [← mul_sub, abs_mul, abs_of_nonneg lam.coe_nonneg]
    calc (lam : ℝ) * |(s : ℝ) - t| ≤ 1 * |(s : ℝ) - t| :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hlam) (abs_nonneg _)
      _ ≤ δ := by rw [one_mul]; exact hst
  · rw [hscale, hscale, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hRb.le, ← dist_eq_norm] at hlt
    have hd := dist_nonneg (x := interpPathFn v' m' X (lam * s)) (y := interpPathFn v' m' X (lam * t))
    have hMpos : 0 < M := lt_of_lt_of_le hRb hRbM
    rw [div_lt_iff₀ hL] at hlt
    rw [div_lt_iff₀ (mul_pos hL hMpos)]
    nlinarith [mul_le_mul_of_nonneg_left hRbM (mul_nonneg hd hL.le)]

/-- **The path modulus of the unstopped walks from the cone-rescaled stopped walks** (Berestycki–Gwynne
(2020), §6.4).  See the module docstring. -/
theorem walkPathFailure_le_of_rescaled {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (η' : Ω → C(ℝ, ℂ)) (ω : Ω) {eps b Rb R L M : ℝ} (δ : ℝ≥0) (hε : 0 < eps) (hb : 0 < b)
    (hRb : 4 * (R + 2) < Rb) (hRbM : Rb ≤ M) (hL : 0 < L) (η2 : ℝ → ℂ)
    (hη : ∀ s, η2 s = (Rb : ℂ)⁻¹ * η' ω (b * s)) (hlam : S.mε eps * (eps / b) ≤ 1) {κ θ s : ℝ}
    (hmL : S.mε eps * L ≤ (eps / b)⁻¹ * s)
    (hexit : ∀ x : ℤ, vertexPoint (eps / b) η2 x ∈ ball (0 : ℂ) (1 / 4) →
      srwLaw (S.mult eps ω) x
        {X | (vExitTime (interiorCellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2))) X : ℝ≥0∞) <
          ENNReal.ofReal ((eps / b)⁻¹ * s)} ≤ ENNReal.ofReal κ)
    (hnull : ∀ x : ℤ, srwLaw (S.mult eps ω) x
      {X | vExitTime (interiorCellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2))) X = ⊤} = 0)
    (hosc : ∀ x ∈ cellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2)),
      srwLaw (S.mult eps ω) x {X | ∃ a c : ℝ≥0,
        a ≤ ((vExitTime (interiorCellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2))) X).toNat : ℝ≥0) /
          ((eps / b)⁻¹).toNNReal ∧
        c ≤ ((vExitTime (interiorCellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2))) X).toNat : ℝ≥0) /
          ((eps / b)⁻¹).toNNReal ∧
        dist a c ≤ δ ∧ 1 / (L * M) < dist (interpPathFn (vertexPoint (eps / b) η2)
          ((eps / b)⁻¹).toNNReal X a) (interpPathFn (vertexPoint (eps / b) η2)
          ((eps / b)⁻¹).toNNReal X c)} ≤ ENNReal.ofReal θ) :
    ∀ j : ℤ, vertexPoint eps (⇑(η' ω)) j ∈ ball (0 : ℂ) (R + 1) →
      ((walkPathLaw S (fun ω => vertexPoint eps (⇑(η' ω))) (S.mε_nonneg eps) eps j ω :
        ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        (pathModulusFailure (E := ℂ) L δ) ≤ ENNReal.ofReal κ + ENNReal.ofReal θ := by
  intro j hj
  have hRpos : 0 < R + 1 := lt_of_le_of_lt (norm_nonneg _) (mem_ball_zero_iff.1 hj)
  have hRbpos : 0 < Rb := by linarith
  have hq : 0 < eps / b := div_pos hε hb
  have hvp : ∀ x, vertexPoint eps ⇑(η' ω) x = ((Rb : ℝ) : ℂ) * vertexPoint (eps / b) η2 x :=
    fun x => ConeScaledWalkData.vertexPoint_eq_mul_rescale hb (Complex.ofReal_ne_zero.2 hRbpos.ne')
      (⇑(η' ω)) η2 hη x
  have hnorm : ∀ x, ‖vertexPoint eps ⇑(η' ω) x‖ = Rb * ‖vertexPoint (eps / b) η2 x‖ := by
    intro x
    rw [hvp x, norm_mul, Complex.norm_real, Real.norm_of_nonneg hRbpos.le]
  have hsmall : ∀ x, vertexPoint eps ⇑(η' ω) x ∈ ball (0 : ℂ) (R + 1) →
      vertexPoint (eps / b) η2 x ∈ ball (0 : ℂ) (1 / 4) := by
    intro x hx
    rw [mem_ball_zero_iff] at hx ⊢
    rw [hnorm x] at hx
    by_contra hcon
    have hcon' := not_lt.1 hcon
    nlinarith
  have hmnn : 0 ≤ S.mε eps := S.mε_nonneg eps
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ≥0, lam = (S.mε eps * (eps / b)).toNNReal := ⟨_, rfl⟩
  obtain ⟨m', hm'def⟩ : ∃ m' : ℝ≥0, m' = ((eps / b)⁻¹).toNNReal := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Set ℤ, A = interiorCellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2)) := ⟨_, rfl⟩
  rw [← hm'def, ← hA] at hosc
  rw [← hA] at hexit hnull
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef]
    exact Real.toNNReal_le_iff_le_coe.2 (by simpa using hlam)
  have hlm : ((lam * m' : ℝ≥0) : ℝ) = S.mε eps := by
    rw [NNReal.coe_mul, hlamdef, hm'def, Real.coe_toNNReal _ (mul_nonneg hmnn hq.le),
      Real.coe_toNNReal _ (inv_nonneg.2 hq.le), mul_assoc, mul_inv_cancel₀ hq.ne', mul_one]
  have hm'pos : 0 < m' := by rw [hm'def]; exact Real.toNNReal_pos.2 (inv_pos.2 hq)
  have hbad : srwLaw (S.mult eps ω) j
      {X | ¬ ∃ n : ℕ, vExitTime A X = n ∧ ((lam * m' : ℝ≥0) : ℝ) * L ≤ n} ≤ ENNReal.ofReal κ := by
    have h1 := hexit j (hsmall j hj)
    have h0 := hnull j
    have hsub : {X | ¬ ∃ n : ℕ, vExitTime A X = n ∧ ((lam * m' : ℝ≥0) : ℝ) * L ≤ n} ⊆
        {X | (vExitTime A X : ℝ≥0∞) < ENNReal.ofReal ((eps / b)⁻¹ * s)} ∪
          {X | vExitTime A X = ⊤} := by
      intro X hX
      by_contra hcon
      apply hX
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hc2
      refine ⟨n, hn.symm, ?_⟩
      rw [← hn] at hc1
      have hc1' : ENNReal.ofReal ((eps / b)⁻¹ * s) ≤ ENNReal.ofReal (n : ℝ) := by
        simpa using hc1
      have hc1'' := (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg n)).1 hc1'
      rw [hlm]
      exact hmL.trans hc1''
    refine le_trans (measure_mono hsub) ((measure_union_le _ _).trans ?_)
    calc _ ≤ ENNReal.ofReal κ + 0 := add_le_add h1 h0.le
      _ = ENNReal.ofReal κ := add_zero _
  have hjc : j ∈ cellVertices (eps / b) η2 (ball (0 : ℂ) (1 / 2)) :=
    ⟨vertexPoint (eps / b) η2 j, Lemma68C12Geom.vertexPoint_mem_cell hq.le j,
      ball_subset_ball (by norm_num) (hsmall j hj)⟩
  show Measure.map (interpPathCM (vertexPoint eps ⇑(η' ω)) (S.mε_nonneg eps))
      (srwLaw (S.mult eps ω) j) (pathModulusFailure (E := ℂ) L δ) ≤ _
  rw [interpPathCM_congr (vertexPoint eps ⇑(η' ω)) hlm.symm (S.mε_nonneg eps) (NNReal.coe_nonneg _),
    Measure.map_apply (measurable_interpPathCM _ _) (measurableSet_pathModulusFailure_complex L δ)]
  refine le_trans (measure_mono (t := {X | ¬ ∃ n : ℕ, vExitTime A X = n ∧
    ((lam * m' : ℝ≥0) : ℝ) * L ≤ n} ∪ {X | ∃ a c : ℝ≥0,
        a ≤ ((vExitTime A X).toNat : ℝ≥0) / m' ∧ c ≤ ((vExitTime A X).toNat : ℝ≥0) / m' ∧
        dist a c ≤ δ ∧ 1 / (L * M) < dist (interpPathFn (vertexPoint (eps / b) η2) m' X a)
          (interpPathFn (vertexPoint (eps / b) η2) m' X c)}) ?_)
    ((measure_union_le _ _).trans (add_le_add hbad (hosc j hjc)))
  intro X hX
  by_cases hg : ∃ n : ℕ, vExitTime A X = n ∧ ((lam * m' : ℝ≥0) : ℝ) * L ≤ n
  · obtain ⟨n, hn, hnL⟩ := hg
    right
    exact interp_mem_pathModulusFailure_imp_oscillation hRbpos
      (fun x => hvp x) hlam1 hm'pos A hL hRbM δ X hn hnL hX
  · left
    exact hg

end MatedCRT.FirstPass.Derived
