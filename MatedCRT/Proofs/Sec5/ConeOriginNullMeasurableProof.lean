import MatedCRT.Proofs.Sec5.StoppedExterior
import MatedCRT.Proofs.Sec1.EnvironmentScaling.CircleProcessSpace
import MatedCRT.Proposed.PrestonAnalytic2008
import HarmonicBalls.Proofs.Potential.GreenBall

/-!
# The obstacle code for `ConeOriginNullMeasurableStep` (steps2.tex 796-1009)

Components, in the order of steps2 (proved here unless marked residual):

* `A` (transfer): a measurable `c : Ω → X` pulls back universally measurable sets to null-measurable sets of any
  finite measure on `Ω`; incomplete `Ω` causes no difficulty (steps2 954-955).
* `C` (Borel version): the a.s. continuous circle process of `IsQuantumCone` has a Borel version
  `c : Ω → PosCircleFns` that equals it off a measurable null set (`PosCircleFns = C((0,∞)×ℂ,ℝ)`, Polish).
  The family `Λ` is never assumed measurable.
* `G1-G4` (cluster-interior coding, steps2 957-990): for open `K`, `B ⊆ closure K` iff a countable rational code
  holds; the cluster `K_R(μ,t)` is open; `Λ_t = int cl K_R` turns the inclusion into the code; the cluster is a
  margin condition on the supersolutions, and the supersolution traces on `closedBall 0 R` have the same values.
* `P` (Borel code, steps2 838-955): the cluster code `A_{R,p}` is universally measurable, using the projection of a
  Borel relation (analytic) and the Preston input `PrestonAnalyticUniversallyMeasurableStmt` (hypothesis `hP`,
  staged in `Proposed/PrestonAnalytic2008.lean`, not yet a source-checked `External` input).
* `F` (steps2 992-1009): completion measurability of `{¬ B_s(0) ⊆ Λ_t}` from the Borel code. The theorem
  `coneOriginNullMeasurableStep_of_inputs` is `ConeOriginNullMeasurableStep 𝒮` under the two named inputs `hP` and
  the residual `CodeSectionStmt 𝒮` (the Borel relation whose a.s. section is the supersolution traces).

Not proved here (named residual `CodeSectionStmt`): the mass code (`IsLQGMeasure` on a countable test family), the
countable dense family of nonnegative test functions with `C²` approximation, and the Borel measurability of the
limits `J_φ`. This is implementation remaining; the written argument is steps2 838-926.
-/

open HarmonicBalls

namespace MatedCRT

namespace ConeOriginNull

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open MatedCRT.CircleProcessSpace Real

/-! ### A. Transfer of universal measurability along a measurable map -/

/-- If `c : Ω → X` is measurable and `B ⊆ X` is null-measurable for every finite Borel measure on `X`, then `c⁻¹ B`
is null-measurable for every finite measure `P` on `Ω`. Sandwich `B` by a measurable set `B'` with null difference for
the law `P.map c`, and pull that null difference back along `c`. -/
theorem nullMeasurableSet_preimage_of_univ {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] {c : Ω → X} (hc : Measurable c) {B : Set X}
    (hB : ∀ ν : Measure X, IsFiniteMeasure ν → NullMeasurableSet B ν) :
    NullMeasurableSet (c ⁻¹' B) P := by
  obtain ⟨B', hB'm, hBB'⟩ := hB (P.map c) inferInstance
  refine ⟨c ⁻¹' B', hc hB'm, ?_⟩
  have h1 : (fun x => x ∈ B) =ᵐ[P.map c] (fun x => x ∈ B') := by
    filter_upwards [hBB'] with x hx
    exact hx
  filter_upwards [ae_eq_comp hc.aemeasurable h1] with ω hω
  simp only [Function.comp_apply] at hω
  simp [hω]

/-! ### C. A Borel version of the cone circle process -/

/-- The circle process as a Borel map into `PosCircleFns = C((0,∞) × ℂ, ℝ)`. Off a measurable `P`-null set `N` it is
the continuous version given by `IsQuantumCone.ae_continuousOn_circle`; on `N` it is `0`. No measurability of the
family `Λ` (or of the process on exceptional outcomes) is used. -/
theorem exists_measurable_circleFns_version {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hcirc : Ω → ℝ → ℂ → ℝ) (hmeas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hae : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ∃ (c : Ω → PosCircleFns) (N : Set Ω), Measurable c ∧ MeasurableSet N ∧ P N = 0 ∧
      ∀ ω ∉ N, ∀ p : PosCircleIndex, c ω p = hcirc ω (p.1 : ℝ) p.2 := by
  classical
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  let F : Ω → PosCircleFns := fun ω =>
    if hω : ω ∈ N then 0 else
      ⟨fun p => hcirc ω (p.1 : ℝ) p.2, by
        have hc : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
          by_contra hbad
          have hmem : ω ∈ {a : Ω | ¬ ContinuousOn (fun p : ℝ × ℂ => hcirc a p.1 p.2) (Ioi 0 ×ˢ univ)} :=
            hbad
          exact hω (hsub hmem)
        exact hc.comp_continuous (f := fun p : PosCircleIndex => ((p.1 : ℝ), p.2))
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
          (fun p => ⟨p.1.2, mem_univ _⟩)⟩
  refine ⟨F, N, ?_, hNm, hN0, ?_⟩
  · refine measurable_iff_eval_posCircleFns.2 fun p => ?_
    have hfun : (fun ω => F ω p) = fun ω => if ω ∈ N then 0 else hcirc ω (p.1 : ℝ) p.2 := by
      funext ω
      by_cases hω : ω ∈ N <;> simp [F, hω]
    rw [hfun]
    exact Measurable.ite hNm measurable_const (hmeas _ _ p.1.2)
  · intro ω hω p
    simp [F, hω]

/-! ### G1. Rational coding of an open set (steps2 957-969) -/

/-- The Gaussian rationals `ℚ + iℚ`: a countable dense subset of `ℂ`. -/
def gaussRat : Set ℂ := range fun q : ℚ × ℚ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

theorem gaussRat_countable : gaussRat.Countable := countable_range _

theorem gaussRat_dense : Dense gaussRat := by
  intro z
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - ε / 2 < z.re by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - ε / 2 < z.im by linarith)
  refine ⟨(a : ℂ) + (b : ℂ) * Complex.I, ⟨(a, b), rfl⟩, ?_⟩
  have h : dist z ((a : ℂ) + (b : ℂ) * Complex.I) ≤ |z.re - a| + |z.im - b| := by
    rw [Complex.dist_eq]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp
  have ha : |z.re - a| < ε / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  have hb : |z.im - b| < ε / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  linarith

/-- **Rational coding of an open set.** If `K` and `B` are open and `D` is dense, then `B ⊆ closure K` iff every point
of `D ∩ B` is approximated, at every scale `1/k`, by a point of `D ∩ K`. -/
theorem subset_closure_iff_code {D K B : Set ℂ} (hD : Dense D) (hK : IsOpen K) (hB : IsOpen B) :
    B ⊆ closure K ↔ ∀ q ∈ D ∩ B, ∀ k : ℕ, 0 < k → ∃ p ∈ D ∩ K, dist p q < 1 / (k : ℝ) := by
  constructor
  · intro hBK q hq k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hqK : q ∈ closure K := hBK hq.2
    obtain ⟨x, hxK, hxq⟩ := Metric.mem_closure_iff.1 hqK (1 / (2 * (k : ℝ))) (by positivity)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hK x hxK
    have hpos : (0 : ℝ) < min δ (1 / (2 * (k : ℝ))) := lt_min hδ (by positivity)
    obtain ⟨p, hpD, hpU⟩ := hD.exists_mem_open isOpen_ball
      (⟨x, mem_ball_self hpos⟩ : (ball x (min δ (1 / (2 * (k : ℝ))))).Nonempty)
    have hpK : p ∈ K := hball (ball_subset_ball (min_le_left _ _) hpU)
    refine ⟨p, ⟨hpD, hpK⟩, ?_⟩
    have hpx : dist p x < 1 / (2 * (k : ℝ)) := lt_of_lt_of_le (mem_ball.1 hpU) (min_le_right _ _)
    have hxq' : dist x q < 1 / (2 * (k : ℝ)) := by rw [dist_comm]; exact hxq
    have e : 1 / (2 * (k : ℝ)) + 1 / (2 * (k : ℝ)) = 1 / (k : ℝ) := by
      field_simp
      ring
    calc dist p q ≤ dist p x + dist x q := dist_triangle _ _ _
      _ < 1 / (2 * (k : ℝ)) + 1 / (2 * (k : ℝ)) := add_lt_add hpx hxq'
      _ = 1 / (k : ℝ) := e
  · intro hcode x hxB
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨q, hq1, hxq⟩ :=
      Metric.mem_closure_iff.1 (hD.open_subset_closure_inter hB hxB) (ε / 2) (half_pos hε)
    obtain ⟨p, hp1, hpq⟩ := hcode q ⟨hq1.2, hq1.1⟩ (n + 1) (Nat.succ_pos n)
    refine ⟨p, hp1.2, ?_⟩
    have e : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e] at hpq
    have hqp : dist q p < ε / 2 := by
      rw [dist_comm]
      linarith
    calc dist x p ≤ dist x q + dist q p := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hxq hqp
      _ = ε := by ring

/-! ### G2. Openness of the cluster off and at the pole (steps2 971-990) -/

/-- The centred Green function of `B_R` at a point of the punctured ball: `G_{B_R}(0,y) = (2π)⁻¹ log(R/|y|)`
(`greenFunction_ball` with the explicit `greenBall` formula at the pole `0`). -/
theorem greenFunction_zero_eq {R : ℝ} (hR : 0 < R) {y : ℂ} (hy : y ∈ ball (0 : ℂ) R) (hy0 : y ≠ 0) :
    greenFunction (ball 0 R) 0 y = (2 * π)⁻¹ * Real.log (R / ‖y‖) := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  rw [greenFunction_ball h0 hy (fun h => hy0 h.symm), greenBall]
  have hn : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
  simp only [map_zero, zero_mul, sub_zero, zero_sub, norm_neg, hn]
  congr 2
  rw [pow_two, mul_div_mul_left _ _ hR.ne']

/-- Continuity of the centred Green function on the punctured ball. -/
theorem continuousOn_greenFunction_zero {R : ℝ} (hR : 0 < R) :
    ContinuousOn (fun y : ℂ => greenFunction (ball 0 R) 0 y) (ball (0 : ℂ) R \ {0}) := by
  have hH : ContinuousOn (fun y : ℂ => (2 * π)⁻¹ * Real.log (R / ‖y‖)) (ball (0 : ℂ) R \ {0}) := by
    refine continuousOn_const.mul (ContinuousOn.log (continuousOn_const.div continuous_norm.continuousOn ?_) ?_)
    · intro y hy
      exact norm_ne_zero_iff.2 (fun h => hy.2 (mem_singleton_iff.2 h))
    · intro y hy
      exact div_ne_zero hR.ne' (norm_ne_zero_iff.2 (fun h => hy.2 (mem_singleton_iff.2 h)))
  exact hH.congr (fun y hy => greenFunction_zero_eq hR hy.1 (fun h => hy.2 (mem_singleton_iff.2 h)))

/-- Real inequality behind the neighbourhood of the pole: `|y| < R exp(2π M / t)` gives `-t G(0,y) < M`. -/
theorem neg_mul_greenBall_lt {R t M : ℝ} (hR : 0 < R) (ht : 0 < t) {y : ℂ} (hpos : 0 < ‖y‖)
    (hy : ‖y‖ < R * Real.exp (2 * π * M / t)) :
    -t * ((2 * π)⁻¹ * Real.log (R / ‖y‖)) < M := by
  have hlogy : Real.log ‖y‖ < Real.log R + 2 * π * M / t := by
    have h := Real.log_lt_log hpos hy
    rwa [Real.log_mul hR.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  rw [Real.log_div hR.ne' hpos.ne']
  have key : -(2 * π * M / t) < Real.log R - Real.log ‖y‖ := by linarith
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have h3 : (2 * π)⁻¹ * (-(2 * π * M / t)) < (2 * π)⁻¹ * (Real.log R - Real.log ‖y‖) :=
    mul_lt_mul_of_pos_left key (inv_pos.2 h2π)
  have h4 : t * ((2 * π)⁻¹ * (-(2 * π * M / t))) < t * ((2 * π)⁻¹ * (Real.log R - Real.log ‖y‖)) :=
    mul_lt_mul_of_pos_left h3 ht
  have h5 : t * ((2 * π)⁻¹ * (-(2 * π * M / t))) = -M := by
    field_simp
  have e : -t * ((2 * π)⁻¹ * (Real.log R - Real.log ‖y‖)) =
      -(t * ((2 * π)⁻¹ * (Real.log R - Real.log ‖y‖))) := by ring
  rw [e]
  linarith

/-- A punctured neighbourhood of the pole lies in the cluster when the least supersolution is continuous on the
closed ball (steps2 971-990: `v_R` is bounded below near `0`, while `-t G_{B_R}(0,x) → -∞`). -/
theorem exists_ball_subset_cluster_zero {μ : Measure ℂ} {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hv : ContinuousOn (leastSupersolution μ R 0 t) (closedBall 0 R)) :
    ∃ ε > 0, ball (0 : ℂ) ε ⊆ cluster μ R 0 t := by
  have hlow : ∀ᶠ y in 𝓝[closedBall (0 : ℂ) R] 0,
      leastSupersolution μ R 0 t 0 - 1 < leastSupersolution μ R 0 t y :=
    (hv 0 (mem_closedBall_self hR.le)).eventually (lt_mem_nhds (by linarith))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hlow
  obtain ⟨δ, hδ, hδv⟩ := hlow
  have hε' : 0 < R * Real.exp (2 * π * (leastSupersolution μ R 0 t 0 - 1) / t) := by positivity
  refine ⟨min δ (min (R * Real.exp (2 * π * (leastSupersolution μ R 0 t 0 - 1) / t)) R),
    lt_min hδ (lt_min hε' hR), ?_⟩
  intro y hy
  have hyn : ‖y‖ < min δ (min (R * Real.exp (2 * π * (leastSupersolution μ R 0 t 0 - 1) / t)) R) :=
    mem_ball_zero_iff.1 hy
  have hyδ : ‖y‖ < δ := lt_of_lt_of_le hyn (min_le_left _ _)
  have hyε : ‖y‖ < R * Real.exp (2 * π * (leastSupersolution μ R 0 t 0 - 1) / t) :=
    lt_of_lt_of_le hyn (le_trans (min_le_right _ _) (min_le_left _ _))
  have hyR : ‖y‖ < R := lt_of_lt_of_le hyn (le_trans (min_le_right _ _) (min_le_right _ _))
  have hyball : y ∈ ball (0 : ℂ) R := mem_ball_zero_iff.2 hyR
  by_cases hy0 : y = 0
  · exact ⟨hyball, Or.inl hy0⟩
  · have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have h1 : leastSupersolution μ R 0 t 0 - 1 < leastSupersolution μ R 0 t y :=
      hδv (show dist y 0 < δ by rw [dist_zero_right]; exact hyδ)
        (mem_closedBall.2 (by rw [dist_zero_right]; exact hyR.le))
    have h2 : -t * greenFunction (ball 0 R) 0 y < leastSupersolution μ R 0 t 0 - 1 := by
      rw [greenFunction_zero_eq hR hyball hy0]
      exact neg_mul_greenBall_lt hR ht hpos hyε
    exact ⟨hyball, Or.inr (by linarith)⟩

/-- **Openness of the cluster `K_R(μ,t) = {0} ∪ {x : 0 < |x| < R, v_R(x) > -t G_{B_R}(0,x)}`** when the least
supersolution is continuous on the closed ball (`ConeOriginNull` route; steps2 971-990). -/
theorem isOpen_cluster_zero {μ : Measure ℂ} {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hv : ContinuousOn (leastSupersolution μ R 0 t) (closedBall 0 R)) :
    IsOpen (cluster μ R 0 t) := by
  have hGc := continuousOn_greenFunction_zero hR
  have hvc : ContinuousOn (leastSupersolution μ R 0 t) (ball 0 R \ {0}) :=
    hv.mono (Set.sdiff_subset.trans ball_subset_closedBall)
  have hf : ContinuousOn (fun y => leastSupersolution μ R 0 t y - (-t * greenFunction (ball 0 R) 0 y))
      (ball (0 : ℂ) R \ {0}) := hvc.sub (continuousOn_const.mul hGc)
  have hU : IsOpen ((ball (0 : ℂ) R \ {0}) ∩
      (fun y => leastSupersolution μ R 0 t y - (-t * greenFunction (ball 0 R) 0 y)) ⁻¹' Ioi 0) :=
    hf.isOpen_inter_preimage (isOpen_ball.sdiff isClosed_singleton) isOpen_Ioi
  obtain ⟨ε, hε, hball⟩ := exists_ball_subset_cluster_zero hR ht hv
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  by_cases hx0 : x = 0
  · exact ⟨ball 0 ε, hball, isOpen_ball, by rw [hx0]; exact mem_ball_self hε⟩
  · refine ⟨_, ?_, hU, ?_⟩
    · rintro y ⟨⟨hyb, hy0⟩, hpos⟩
      have hpos' : 0 < leastSupersolution μ R 0 t y - (-t * greenFunction (ball 0 R) 0 y) := hpos
      exact ⟨hyb, Or.inr (by linarith)⟩
    · have hxb : x ∈ ball (0 : ℂ) R := hx.1
      rcases hx.2 with h | h
      · exact absurd h hx0
      · exact ⟨⟨hxb, hx0⟩, by simp only [Set.mem_preimage, Set.mem_Ioi]; linarith⟩

/-! ### G3. Cluster-interior coding of a harmonic-ball family (steps2 957-969, 971-990) -/

/-- **The inclusion code for the cluster.** If `Λ = int cl K_R(μ,t)` with `K_R` the open cluster, then
`B_s ⊆ Λ` iff every rational point of `B_s` is a limit, at every scale, of rational points of the cluster. -/
theorem ball_subset_iff_code_of_cluster {μ : Measure ℂ} {Λt : Set ℂ} {R t s : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hΛ : Λt = interior (closure (cluster μ R 0 t)))
    (hv : ContinuousOn (leastSupersolution μ R 0 t) (closedBall 0 R)) :
    ball (0 : ℂ) s ⊆ Λt ↔
      ∀ q ∈ gaussRat ∩ ball (0 : ℂ) s, ∀ k : ℕ, 0 < k →
        ∃ p ∈ gaussRat ∩ cluster μ R 0 t, dist p q < 1 / (k : ℝ) := by
  rw [hΛ, isOpen_ball.subset_interior_iff]
  exact subset_closure_iff_code gaussRat_dense (isOpen_cluster_zero hR ht hv) isOpen_ball

/-! ### G4. The cluster as a margin condition on the supersolutions (steps2 957-969, 971-990) -/

/-- For a nonempty set of reals bounded below, `a < sInf S` iff some margin `1/(n+1)` lies below all of `S`. -/
theorem lt_sInf_iff_margin {S : Set ℝ} (hS : S.Nonempty) (hb : BddBelow S) (a : ℝ) :
    a < sInf S ↔ ∃ n : ℕ, ∀ x ∈ S, a + 1 / ((n : ℝ) + 1) ≤ x := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
    exact ⟨n, fun x hx => by have := csInf_le hb hx; linarith⟩
  · rintro ⟨n, hall⟩
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have := le_csInf hS hall
    linarith

/-- **The cluster as a margin condition.** For `x ∈ B_R \ {0}`, `x` lies in the cluster iff for some `n` every
supersolution lies above the obstacle by at least `1/(n+1)` at `x`. -/
theorem mem_cluster_iff_margin {μ : Measure ℂ} {R t : ℝ} (ht : 0 < t) {x : ℂ} (hx : x ∈ ball (0 : ℂ) R)
    (hx0 : x ≠ 0) :
    x ∈ cluster μ R 0 t ↔
      ∃ n : ℕ, ∀ w ∈ supersolutions μ R 0 t,
        -t * greenFunction (ball 0 R) 0 x + 1 / ((n : ℝ) + 1) ≤ w x := by
  have hS : ((fun w : ℂ → ℝ => w x) '' supersolutions μ R 0 t).Nonempty :=
    (supersolutions_nonempty μ R 0 ht.le).image _
  have hb : BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ R 0 t) :=
    bddBelow_supersolutions (ball_subset_closedBall hx) hx0
  constructor
  · intro hmem
    have hlt : -t * greenFunction (ball 0 R) 0 x < sInf ((fun w : ℂ → ℝ => w x) '' supersolutions μ R 0 t) :=
      hmem.2.resolve_left hx0
    obtain ⟨n, hall⟩ := (lt_sInf_iff_margin hS hb _).1 hlt
    exact ⟨n, fun w hw => hall _ ⟨w, hw, rfl⟩⟩
  · rintro ⟨n, hall⟩
    refine ⟨hx, Or.inr ?_⟩
    apply (lt_sInf_iff_margin hS hb _).2 ⟨n, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hall w hw

/-! ### P. The obstacle code as a Borel relation (steps2 838-955) -/

/-- The trace space `C(closedBall 0 R, ℝ)` of the supersolutions: a Polish space (`C(K,ℝ)`, `K` compact). -/
abbrev BallFns (R : ℝ) : Type := C(closedBall (0 : ℂ) R, ℝ)

instance ballFns_polishSpace (R : ℝ) : PolishSpace (BallFns R) := by
  have : CompactSpace (closedBall (0 : ℂ) R) := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  exact { toSecondCountableTopology := inferInstance
          toIsCompletelyMetrizableSpace := inferInstance }

/-- The restrictions to `closedBall 0 R` of the supersolutions of the obstacle problem `(μ, R, t)`. -/
def superTraces (μ : Measure ℂ) (R t : ℝ) : Set (BallFns R) :=
  {w | ∃ u ∈ supersolutions μ R 0 t, ∀ x : closedBall (0 : ℂ) R, u x = w x}

theorem restrict_mem_superTraces {μ : Measure ℂ} {R t : ℝ} {u : ℂ → ℝ} (hu : u ∈ supersolutions μ R 0 t) :
    (⟨fun x : closedBall (0 : ℂ) R => u x, hu.1.domRestrict⟩ : BallFns R) ∈ superTraces μ R t :=
  ⟨u, hu, fun _ => rfl⟩

/-- The cluster membership of `x ∈ B_R \ {0}` through the traces of supersolutions on the closed ball. -/
theorem mem_cluster_iff_traces {μ : Measure ℂ} {R t : ℝ} (ht : 0 < t) {x : ℂ} (hx : x ∈ ball (0 : ℂ) R)
    (hx0 : x ≠ 0) :
    x ∈ cluster μ R 0 t ↔ ∃ n : ℕ, ∀ w ∈ superTraces μ R t,
      -t * greenFunction (ball 0 R) 0 x + 1 / ((n : ℝ) + 1) ≤ w ⟨x, ball_subset_closedBall hx⟩ := by
  rw [mem_cluster_iff_margin ht hx hx0]
  have hxc : x ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hx
  have key : ∀ a : ℝ, (∀ u ∈ supersolutions μ R 0 t, a ≤ u x) ↔
      ∀ w ∈ superTraces μ R t, a ≤ w ⟨x, hxc⟩ := by
    intro a
    constructor
    · intro h w hw
      obtain ⟨u, hu, huw⟩ := hw
      have e : u x = w ⟨x, hxc⟩ := huw ⟨x, hxc⟩
      rw [← e]
      exact h u hu
    · intro h u hu
      exact h _ (restrict_mem_superTraces hu)
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (key _).1 hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (key _).2 hn⟩

/-- Projections of Borel relations are analytic, hence universally measurable by Preston (Theorem 7.1 as staged in
`Proposed/PrestonAnalytic2008.lean`, the hypothesis `hP`): `{c | ∃ w, (c,w) ∈ 𝒜 ∧ w(p) < a}`. -/
theorem univMeasurable_exists_lt (hP : PrestonAnalyticUniversallyMeasurableStmt) {R : ℝ}
    {𝒜 : Set (PosCircleFns × BallFns R)} (h𝒜 : MeasurableSet 𝒜) {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) R)
    (a : ℝ) (ν : Measure PosCircleFns) [IsFiniteMeasure ν] :
    NullMeasurableSet {c | ∃ w, (c, w) ∈ 𝒜 ∧ w ⟨p, hp⟩ < a} ν := by
  have hcont : Continuous fun x : PosCircleFns × BallFns R => x.2 ⟨p, hp⟩ :=
    (continuous_eval_const (⟨p, hp⟩ : closedBall (0 : ℂ) R)).comp continuous_snd
  have hmeas : MeasurableSet {x : PosCircleFns × BallFns R | x ∈ 𝒜 ∧ x.2 ⟨p, hp⟩ < a} :=
    h𝒜.inter (measurableSet_lt hcont.measurable measurable_const)
  have hset : {c | ∃ w, (c, w) ∈ 𝒜 ∧ w ⟨p, hp⟩ < a} =
      Prod.fst '' {x : PosCircleFns × BallFns R | x ∈ 𝒜 ∧ x.2 ⟨p, hp⟩ < a} := by
    ext c
    constructor
    · rintro ⟨w, hw, hlt⟩
      exact ⟨(c, w), ⟨hw, hlt⟩, rfl⟩
    · rintro ⟨⟨c', w⟩, ⟨hw, hlt⟩, rfl⟩
      exact ⟨w, hw, hlt⟩
  have han : AnalyticSet (Prod.fst '' {x : PosCircleFns × BallFns R | x ∈ 𝒜 ∧ x.2 ⟨p, hp⟩ < a}) :=
    AnalyticSet.image_of_continuous hmeas.analyticSet continuous_fst
  rw [hset]
  exact hP PosCircleFns _ han ν inferInstance

/-- The cluster code `A_{R,p}` (steps2 957-969): `A_{R,0}` holds, `A_{R,p}` fails outside `B_R`, and for
`p ∈ B_R \ {0}` it asserts that some margin `1/(n+1)` below the obstacle is attained by no trace. -/
def codeAt {R : ℝ} (𝒜 : Set (PosCircleFns × BallFns R)) (t : ℝ) (p : ℂ) (c : PosCircleFns) : Prop :=
  p = 0 ∨ ∃ hp : p ∈ ball (0 : ℂ) R, ∃ n : ℕ,
    ¬ ∃ w, (c, w) ∈ 𝒜 ∧
      w ⟨p, ball_subset_closedBall hp⟩ < -t * greenFunction (ball 0 R) 0 p + 1 / ((n : ℝ) + 1)

/-- Each cluster code is universally measurable in the circle process, given the Borel relation and Preston. -/
theorem univMeasurable_codeAt (hP : PrestonAnalyticUniversallyMeasurableStmt) {R t : ℝ}
    {𝒜 : Set (PosCircleFns × BallFns R)} (h𝒜 : MeasurableSet 𝒜) (p : ℂ)
    (ν : Measure PosCircleFns) [IsFiniteMeasure ν] : NullMeasurableSet {c | codeAt 𝒜 t p c} ν := by
  by_cases hp0 : p = 0
  · have e : {c | codeAt 𝒜 t p c} = univ := by
      ext c
      exact iff_of_true (Or.inl hp0) (mem_univ c)
    rw [e]
    exact nullMeasurableSet_univ
  by_cases hpb : p ∈ ball (0 : ℂ) R
  · have e : {c | codeAt 𝒜 t p c} = ⋃ n : ℕ,
        {c | ∃ w, (c, w) ∈ 𝒜 ∧ w ⟨p, ball_subset_closedBall hpb⟩ <
          -t * greenFunction (ball 0 R) 0 p + 1 / ((n : ℝ) + 1)}ᶜ := by
      ext c
      constructor
      · rintro (h | ⟨hp, n, hn⟩)
        · exact absurd h hp0
        · exact mem_iUnion.2 ⟨n, hn⟩
      · intro hc
        obtain ⟨n, hn⟩ := mem_iUnion.1 hc
        exact Or.inr ⟨hpb, n, hn⟩
    rw [e]
    exact NullMeasurableSet.iUnion fun n =>
      (univMeasurable_exists_lt hP h𝒜 (ball_subset_closedBall hpb) _ ν).compl
  · have e : {c | codeAt 𝒜 t p c} = ∅ := by
      ext c
      constructor
      · rintro (h | ⟨hp, _⟩)
        · exact absurd h hp0
        · exact absurd hp hpb
      · intro h
        exact h.elim
    rw [e]
    exact nullMeasurableSet_empty

/-- **Cluster code identity.** On the event where the section of `𝒜` is the trace set of the supersolutions,
`p ∈ K_R(μ,t)` iff the cluster code `A_{R,p}` holds. -/
theorem mem_cluster_iff_codeAt {μ : Measure ℂ} {R t : ℝ} (hR : 0 < R) (ht : 0 < t) {c : PosCircleFns}
    {𝒜 : Set (PosCircleFns × BallFns R)} (hsec : ∀ w : BallFns R, (c, w) ∈ 𝒜 ↔ w ∈ superTraces μ R t)
    (p : ℂ) : p ∈ cluster μ R 0 t ↔ codeAt 𝒜 t p c := by
  by_cases hp0 : p = 0
  · subst hp0
    exact iff_of_true ⟨mem_ball_self hR, Or.inl rfl⟩ (Or.inl rfl)
  · constructor
    · intro hmem
      have hpb : p ∈ ball (0 : ℂ) R := hmem.1
      obtain ⟨n, hn⟩ := (mem_cluster_iff_traces ht hpb hp0).1 hmem
      refine Or.inr ⟨hpb, n, fun ⟨w, hw, hlt⟩ => ?_⟩
      have hwS : w ∈ superTraces μ R t := (hsec w).1 hw
      exact absurd (hn w hwS) (not_le.2 hlt)
    · rintro (h | ⟨hpb, n, hn⟩)
      · exact absurd h hp0
      · refine (mem_cluster_iff_traces ht hpb hp0).2 ⟨n, fun w hw => ?_⟩
        by_contra hlt
        exact hn ⟨w, (hsec w).2 hw, not_le.1 hlt⟩

/-- The inclusion code `I_R` (steps2 957-969) pulled back along the circle process, as a set of outcomes. -/
def inclusionCodeSet {Ω : Type} (c : Ω → PosCircleFns) {R : ℝ} (𝒜 : Set (PosCircleFns × BallFns R)) (t s : ℝ) :
    Set Ω :=
  ⋂ q ∈ gaussRat ∩ ball (0 : ℂ) s, ⋂ k ∈ {k : ℕ | 0 < k},
    ⋃ p ∈ gaussRat ∩ {p | dist p q < 1 / (k : ℝ)}, c ⁻¹' {x | codeAt 𝒜 t p x}

theorem mem_inclusionCodeSet {Ω : Type} (c : Ω → PosCircleFns) {R : ℝ} (𝒜 : Set (PosCircleFns × BallFns R))
    (t s : ℝ) (ω : Ω) :
    ω ∈ inclusionCodeSet c 𝒜 t s ↔ ∀ q ∈ gaussRat ∩ ball (0 : ℂ) s, ∀ k : ℕ, 0 < k →
      ∃ p ∈ gaussRat ∩ {p | dist p q < 1 / (k : ℝ)}, codeAt 𝒜 t p (c ω) := by
  simp only [inclusionCodeSet, mem_iInter, mem_iUnion, mem_preimage, Set.mem_ofPred_eq, exists_prop]

theorem nullMeasurableSet_inclusionCodeSet {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (c : Ω → PosCircleFns)
    {R : ℝ} (𝒜 : Set (PosCircleFns × BallFns R)) (t s : ℝ)
    (h : ∀ p : ℂ, NullMeasurableSet (c ⁻¹' {x | codeAt 𝒜 t p x}) P) :
    NullMeasurableSet (inclusionCodeSet c 𝒜 t s) P := by
  unfold inclusionCodeSet
  refine NullMeasurableSet.biInter ((gaussRat_countable.mono inter_subset_left)) fun q _ =>
    NullMeasurableSet.biInter (Set.to_countable _) fun k _ =>
      NullMeasurableSet.biUnion ((gaussRat_countable.mono inter_subset_left)) fun p _ => h p

/-! ### F. Completion measurability of the origin inclusion event (steps2 992-1009) -/

/-- **Residual input: the Borel obstacle code (steps2 838-955).** For a Borel version `c` of the circle process and
every radius `R > 0` and time `t > 0` there is a Borel relation `𝒜 ⊆ C((0,∞)×ℂ,ℝ) × C(closedBall 0 R, ℝ)` whose
section at almost every outcome is the set of traces of the supersolutions of the obstacle problem for
`(μ_ω, R, t)`. Its proof needs the mass code (`IsLQGMeasure` on a countable test family), a countable dense family of
nonnegative test functions with `C²` approximation, and the Borel measurability of the limits `J_φ`. -/
def CodeSectionStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ c : Ω → PosCircleFns, Measurable c →
    (∀ᵐ ω ∂S.P, ∀ p : PosCircleIndex, c ω p = S.hcirc ω (p.1 : ℝ) p.2) →
    ∀ R : ℝ, 0 < R → ∀ t : ℝ, 0 < t →
      ∃ 𝒜 : Set (PosCircleFns × BallFns R), MeasurableSet 𝒜 ∧
        ∀ᵐ ω ∂S.P, ∀ w : BallFns R, (c ω, w) ∈ 𝒜 ↔ w ∈ superTraces (S.μ ω) R t

/-- **Completion measurability of the origin inclusion event, from the obstacle code.** Given the Preston input
`PrestonAnalyticUniversallyMeasurableStmt` and the residual Borel obstacle code `CodeSectionStmt`, the event
`{¬ B_s(0) ⊆ Λ_t}` is null-measurable for `P`, for every `t, s > 0`, with no measurability of `Λ` and no completeness
of `P`. This is `ConeOriginNullMeasurableStep 𝒮` conditional on the two named residual inputs. -/
theorem coneOriginNullMeasurableStep_of_inputs (𝒮 : SpaceFillingSLEModel)
    (hP : PrestonAnalyticUniversallyMeasurableStmt) (hC : CodeSectionStmt 𝒮) :
    ConeOriginNullMeasurableStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS Λ hΛ t ht s hs
  have := hS.isProbabilityMeasure
  obtain ⟨c, N, hc, hNm, hN0, hcN⟩ := exists_measurable_circleFns_version S.P S.hcirc
    hS.isQuantumCone.measurable_circle hS.isQuantumCone.ae_continuousOn_circle
  have hcae : ∀ᵐ ω ∂S.P, ∀ p : PosCircleIndex, c ω p = S.hcirc ω (p.1 : ℝ) p.2 := by
    have hNae : ∀ᵐ ω ∂S.P, ω ∉ N := by
      rw [ae_iff]
      simpa using hN0
    filter_upwards [hNae] with ω hω
    exact hcN ω hω
  choose 𝒜 h𝒜 hsec using fun n : ℕ => hC γ hγ hγ2 Ω S hS c hc hcae ((n : ℝ) + 1) (by positivity) t ht
  have hsecAll : ∀ᵐ ω ∂S.P, ∀ n : ℕ, ∀ w : BallFns ((n : ℝ) + 1),
      (c ω, w) ∈ 𝒜 n ↔ w ∈ superTraces (S.μ ω) ((n : ℝ) + 1) t := ae_all_iff.2 hsec
  -- the inclusion codes and their null-measurability
  have hI : ∀ n : ℕ, NullMeasurableSet (inclusionCodeSet c (𝒜 n) t s) S.P := fun n =>
    nullMeasurableSet_inclusionCodeSet S.P c (𝒜 n) t s fun p =>
      nullMeasurableSet_preimage_of_univ S.P hc fun ν hν => by
        have := hν
        exact univMeasurable_codeAt hP (h𝒜 n) p ν
  have hU : NullMeasurableSet (⋃ N : ℕ, ⋂ n ∈ {m : ℕ | N ≤ m}, (inclusionCodeSet c (𝒜 n) t s)ᶜ) S.P :=
    NullMeasurableSet.iUnion fun N =>
      NullMeasurableSet.biInter (Set.to_countable _) fun n _ => (hI n).compl
  have hgood := hΛ.and hsecAll
  have hEU : (⋃ N : ℕ, ⋂ n ∈ {m : ℕ | N ≤ m}, (inclusionCodeSet c (𝒜 n) t s)ᶜ) =ᵐ[S.P]
      {ω | ¬ ball (0 : ℂ) s ⊆ Λ ω t} := by
    filter_upwards [hgood] with ω hω
    obtain ⟨hfam, hsecω⟩ := hω
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 (hfam.2.1.isBounded t ht)
    have hR0 : (0 : ℝ) < |r| + 1 := by positivity
    have hsub : Λ ω t ⊆ ball (0 : ℂ) (|r| + 1) :=
      hr.trans (closedBall_subset_ball (by linarith [le_abs_self r]))
    obtain ⟨N0, hN0'⟩ := exists_nat_gt (|r| + 1)
    -- for each large radius the inclusion event is the ball inclusion
    have hiff : ∀ n : ℕ, N0 ≤ n → (ball (0 : ℂ) s ⊆ Λ ω t ↔ ω ∈ inclusionCodeSet c (𝒜 n) t s) := by
      intro n hn
      have hρ : |r| + 1 < (n : ℝ) + 1 := by
        have : (N0 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      obtain ⟨hΛeq, hv, -⟩ := hfam.2.2 t (|r| + 1) ht hR0 hsub ((n : ℝ) + 1) hρ
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hcl : ∀ p : ℂ, p ∈ cluster (S.μ ω) ((n : ℝ) + 1) 0 t ↔ codeAt (𝒜 n) t p (c ω) :=
        mem_cluster_iff_codeAt hpos ht (hsecω n)
      rw [ball_subset_iff_code_of_cluster hpos ht hΛeq hv, mem_inclusionCodeSet]
      refine forall₂_congr fun q _ => forall_congr' fun k => imp_congr_right fun _ => ?_
      constructor
      · rintro ⟨p, ⟨hpD, hpK⟩, hd⟩
        exact ⟨p, ⟨hpD, hd⟩, (hcl p).1 hpK⟩
      · rintro ⟨p, ⟨hpD, hd⟩, hcp⟩
        exact ⟨p, ⟨hpD, (hcl p).2 hcp⟩, hd⟩
    apply propext
    constructor
    · intro hU'
      obtain ⟨N, hN⟩ := mem_iUnion.1 hU'
      intro hball
      have hn : ω ∈ inclusionCodeSet c (𝒜 (max N N0)) t s :=
        (hiff (max N N0) (le_max_right _ _)).1 hball
      exact (mem_iInter₂.1 hN (max N N0) (le_max_left _ _)) hn
    · intro hnot
      refine mem_iUnion.2 ⟨N0, mem_iInter₂.2 fun n hn => ?_⟩
      intro hI'
      exact hnot ((hiff n hn).2 hI')
  exact NullMeasurableSet.congr hU hEU

end ConeOriginNull

end MatedCRT
