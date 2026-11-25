import MatedCRT.FirstPass.Derived.BrownianRegularExitSquare

/-!
# Regular exit of planar Brownian motion from an annulus

Planar Brownian motion started at a point of the annulus `U = B_R(0) \ closedBall 0 α` (`0 < α < R`) leaves `U` at a
finite time almost surely and exits it regularly (`MatedCRT.TruncatedLaws.RegularExit`): right after its exit time it
visits the complement of the closure of `U` at arbitrarily small positive times. This is used in the proof of
Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, case 1, where the walk and Brownian motion are compared
when stopped at their exits from annuli avoiding the origin: stopping at the exit of `U` is continuous, modulo time
parametrization, at almost every Brownian path.

At the outer circle the exit is regular because the post-exit increment has a positive pairing with the exit point
at arbitrarily small times (as for discs, `BrownianRegularExitBall.lean`). At the inner circle a half-plane does not
fit in the complement of `closure U`; there the post-exit increment `w` satisfies `-2⟪p, w⟫ - |w|² > 0`, which puts
`p + w` inside the open disc `B_α(0)`, at arbitrarily small times. Both cases are covered by one exit witness
`annulusExitWitness`. Positivity at arbitrarily small times follows from Blumenthal's zero-one law once the marginal
probability of positivity is bounded below at small times (`ae_forall_exists_rat_pos_of_marginal_ge`, the form of
`LatticeProb.PlanarBrownian.ae_forall_exists_rat_pos_of_marginal` with a lower bound in place of the value `1/2`),
together with the strong Markov property at the exit time (`MatedCRT.ExitRestart.exit_restart_planar`; Mörters–Peres,
*Brownian Motion*, Theorems 2.7 and 2.16). At the inner circle the lower bound is
`P(⟪-p, W_q⟫ > α √q) - P(|Re W_q| ≥ M √q) - P(|Im W_q| ≥ M √q)` for a large `M` and small `q`, by Brownian scaling.

## Main statements

* `ae_forall_exists_rat_pos_of_marginal_ge`: the Blumenthal step with a marginal lower bound.
* `ae_frequently_pos_of_indepFun_of_marginal`: positivity of `φ (N, W_s)` at arbitrarily small `s` for `N`
  independent of the planar Brownian motion `W`.
* `annulusExitWitness`, `notMem_closure_annulus_of_witness_pos`, `exists_marginal_annulusExitWitness`.
* `ae_regularExit_annulus_planarBrownian`: the regular exit from the annulus.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess ProbabilityTheory
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

open LatticeProb.PlanarBrownian

/-- **Blumenthal step with a lower bound on the marginals.** If a real process `X` with measurable coordinates is
positive at time `q` with probability at least `c > 0` for all small `q > 0`, and its germ σ-algebra is trivial, then
almost surely it is positive at rational times arbitrarily close to `0`. -/
theorem ae_forall_exists_rat_pos_of_marginal_ge {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ} (hXm : ∀ t, Measurable (X t)) {c : ℝ≥0∞} (hc : 0 < c)
    {q₀ : ℝ≥0} (hq₀ : 0 < q₀) (hmarg : ∀ q : ℝ≥0, 0 < q → q < q₀ → c ≤ P (X q ⁻¹' Ioi 0))
    (hBlum : ∀ A : Set Ω, MeasurableSet[⨅ n : ℕ, pathSigmaTo X (freqEps n)] A →
      P A = 0 ∨ P A = 1) :
    ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < freqEps m ∧ 0 < X (Real.toNNReal q) ω := by
  set A : Set Ω := ⋂ m : ℕ, positiveAtRationalBefore X (freqEps m) with hAdef
  have hAgerm : MeasurableSet[⨅ n : ℕ, pathSigmaTo X (freqEps n)] A :=
    measurableSet_germ_positiveAtRationalBefore X
  have hAmeas : MeasurableSet A :=
    (pathSigmaTo_le X hXm (freqEps 0)) A ((iInf_le (fun n : ℕ => pathSigmaTo X (freqEps n)) 0) A hAgerm)
  have hlow : c ≤ P A := by
    have hmeas : ∀ m : ℕ, NullMeasurableSet (positiveAtRationalBefore X (freqEps m)) P :=
      fun m => ((pathSigmaTo_le X hXm (freqEps m)) _
        (measurableSet_positiveAtRationalBefore X (freqEps m))).nullMeasurableSet
    have ht := tendsto_measure_iInter_atTop (μ := P) hmeas (positiveAtRationalBefore_anti X)
      ⟨0, measure_ne_top P _⟩
    refine ge_of_tendsto' ht fun m => ?_
    have hpos : (0 : ℝ) < min (freqEps m : ℝ) (q₀ : ℝ) :=
      lt_min (NNReal.coe_pos.2 (freqEps_pos m)) (NNReal.coe_pos.2 hq₀)
    obtain ⟨q, hq0, hqm⟩ := exists_rat_btwn hpos
    have hsub : X (Real.toNNReal q) ⁻¹' Ioi 0 ⊆ positiveAtRationalBefore X (freqEps m) :=
      fun ω hω => mem_iUnion.2 ⟨⟨q, hq0, lt_of_lt_of_le hqm (min_le_left _ _)⟩, hω⟩
    have hqq₀ : Real.toNNReal q < q₀ := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0.le]
      exact lt_of_lt_of_le hqm (min_le_right _ _)
    exact (hmarg _ (Real.toNNReal_pos.2 hq0) hqq₀).trans (measure_mono hsub)
  have hone : P A = 1 := by
    rcases hBlum A hAgerm with h | h
    · exact absurd h (ne_of_gt (lt_of_lt_of_le hc hlow))
    · exact h
  have hae : ∀ᵐ ω ∂P, ω ∈ A := ae_iff.2 ((prob_compl_eq_zero_iff hAmeas).2 hone)
  filter_upwards [hae] with ω hω m
  have hm' : ω ∈ positiveAtRationalBefore X (freqEps m) := mem_iInter.1 hω m
  obtain ⟨⟨q, hq⟩, hpos⟩ := mem_iUnion.1 hm'
  exact ⟨q, hq.1, hq.2, hpos⟩

/-- A measurable function of the coordinates is measurable with respect to the coordinates up to `u`. -/
theorem pathSigmaTo_comp_le {Ω : Type*} {W : ℝ≥0 → Ω → ℂ} {f : ℂ → ℝ} (hf : Measurable f) (u : ℝ≥0) :
    pathSigmaTo (fun t ω => f (W t ω)) u ≤ pathSigmaTo W u := by
  let g : (Set.Iic u → ℂ) → (Set.Iic u → ℝ) := fun h t => f (h t)
  have hg : Measurable g := measurable_pi_iff.2 fun t => hf.comp (measurable_pi_apply t)
  have hcomp : (fun ω (t : Set.Iic u) => f (W t ω)) = g ∘ (fun ω (t : Set.Iic u) => W t ω) := rfl
  unfold pathSigmaTo
  rw [hcomp]
  exact (hg.comp (comap_measurable (fun ω (t : Set.Iic u) => W t ω))).comap_le

/-- Pairs `(x, w)` such that `φ (x, w q) > 0` at rational times `q` arbitrarily close to `0`. -/
def frequentlyPosSet (φ : ℂ × ℂ → ℝ) : Set (ℂ × (ℝ≥0 → ℂ)) :=
  {p | ∀ m : ℕ, ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < freqEps m ∧ 0 < φ (p.1, p.2 (Real.toNNReal q))}

theorem measurableSet_frequentlyPosSet {φ : ℂ × ℂ → ℝ} (hφ : Measurable φ) :
    MeasurableSet (frequentlyPosSet φ) := by
  have hm : ∀ q : ℝ≥0, Measurable (fun p : ℂ × (ℝ≥0 → ℂ) => φ (p.1, p.2 q)) := fun q =>
    hφ.comp (measurable_fst.prodMk ((measurable_pi_apply q).comp measurable_snd))
  have heq : frequentlyPosSet φ = ⋂ m : ℕ, ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < freqEps m},
      {p : ℂ × (ℝ≥0 → ℂ) | 0 < φ (p.1, p.2 (Real.toNNReal q.1))} := by
    ext p
    constructor
    · intro h
      exact mem_iInter.2 fun m => by
        obtain ⟨q, h1, h2, h3⟩ := h m
        exact mem_iUnion.2 ⟨⟨q, h1, h2⟩, h3⟩
    · intro h m
      obtain ⟨⟨q, h1, h2⟩, h3⟩ := mem_iUnion.1 (mem_iInter.1 h m)
      exact ⟨q, h1, h2, h3⟩
  rw [heq]
  exact MeasurableSet.iInter fun m => MeasurableSet.iUnion fun q =>
    measurableSet_lt measurable_const (hm _)

/-- **Positivity at arbitrarily small times for an independent random parameter.** Let `W` be a planar Brownian
motion with trivial germ σ-algebra and `N` a random point independent of `W`. If for almost every value `x` of `N` the
probability that `φ (x, W_q) > 0` is bounded below by a positive constant for all small `q > 0`, then almost surely
`φ (N, W_s) > 0` for arbitrarily small `s > 0`. -/
theorem ae_frequently_pos_of_indepFun_of_marginal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → ℂ} (hW : IsPlanarBrownian W P)
    (hBlum : ∀ A : Set Ω, MeasurableSet[⨅ n : ℕ, pathSigmaTo W (freqEps n)] A →
      P A = 0 ∨ P A = 1)
    {N : Ω → ℂ} (hN : AEMeasurable N P) (hNW : IndepFun N (fun ω (s : ℝ≥0) => W s ω) P)
    {φ : ℂ × ℂ → ℝ} (hφ : Measurable φ)
    (hmarg : ∀ᵐ x ∂(P.map N), ∃ c : ℝ≥0∞, 0 < c ∧ ∃ q₀ : ℝ≥0, 0 < q₀ ∧
      ∀ q : ℝ≥0, 0 < q → q < q₀ → c ≤ P ((fun ω => φ (x, W q ω)) ⁻¹' Ioi 0)) :
    ∀ᵐ ω ∂P, ∃ᶠ s in 𝓝[>] (0 : ℝ≥0), 0 < φ (N ω, W s ω) := by
  have hWm : Measurable (fun ω (s : ℝ≥0) => W s ω) :=
    measurable_pi_iff.2 fun s => hW.measurable s
  have hmap : P.map (fun ω => (N ω, fun s : ℝ≥0 => W s ω)) =
      (P.map N).prod (P.map (fun ω (s : ℝ≥0) => W s ω)) :=
    (indepFun_iff_map_prod_eq_prod_map_map hN hWm.aemeasurable).1 hNW
  have hGm := measurableSet_frequentlyPosSet hφ
  have hpair : AEMeasurable (fun ω => (N ω, fun s : ℝ≥0 => W s ω)) P :=
    hN.prodMk hWm.aemeasurable
  have hsec : ∀ x : ℂ, (∃ c : ℝ≥0∞, 0 < c ∧ ∃ q₀ : ℝ≥0, 0 < q₀ ∧
      ∀ q : ℝ≥0, 0 < q → q < q₀ → c ≤ P ((fun ω => φ (x, W q ω)) ⁻¹' Ioi 0)) →
      P.map (fun ω (s : ℝ≥0) => W s ω) (Prod.mk x ⁻¹' frequentlyPosSet φ) = 1 := by
    rintro x ⟨c, hc, q₀, hq₀, hx⟩
    have hφx : Measurable fun z : ℂ => φ (x, z) := hφ.comp measurable_prodMk_left
    rw [Measure.map_apply_of_aemeasurable hWm.aemeasurable (measurable_prodMk_left hGm)]
    refine prob_preimage_eq_one_of_ae hWm.aemeasurable (measurable_prodMk_left hGm) ?_
    have hX := ae_forall_exists_rat_pos_of_marginal_ge (P := P)
      (X := fun t ω => φ (x, W t ω)) (fun t => hφx.comp (hW.measurable t)) hc hq₀ hx
      (fun A hA => hBlum A ((iInf_mono fun n => pathSigmaTo_comp_le hφx (freqEps n)) A hA))
    filter_upwards [hX] with ω hω
    exact hω
  have hPN : IsProbabilityMeasure (P.map N) := (Measure.isProbabilityMeasure_map_iff hN).2 inferInstance
  have hfull : P ((fun ω => (N ω, fun s : ℝ≥0 => W s ω)) ⁻¹' frequentlyPosSet φ) = 1 := by
    rw [← Measure.map_apply_of_aemeasurable hpair hGm, hmap, Measure.prod_apply hGm]
    have hconst : (fun x => (P.map (fun ω (s : ℝ≥0) => W s ω)) (Prod.mk x ⁻¹' frequentlyPosSet φ))
        =ᵐ[P.map N] fun _ => (1 : ℝ≥0∞) := by
      filter_upwards [hmarg] with x hx
      exact hsec x hx
    rw [lintegral_congr_ae hconst, lintegral_const, measure_univ, mul_one]
  filter_upwards [ae_mem_of_prob_preimage_eq_one hpair hGm hfull] with ω hω
  exact frequently_of_forall_exists_rat (f := fun s => φ (N ω, W s ω)) hω

/-! ### The exit witness of an annulus -/

/-- The exit witness of the annulus `B_R(0) \ closedBall 0 α` at the frontier point `p` for the increment `w`:
the radial pairing `⟪p, w⟫` near the outer circle, and `-2⟪p, w⟫ - |w|²` near the inner circle. -/
noncomputable def annulusExitWitness (α R : ℝ) (p : ℂ × ℂ) : ℝ :=
  if ‖p.1‖ < (α + R) / 2 then -(2 * pairing p.1 p.2) - ‖p.2‖ ^ 2 else pairing p.1 p.2

theorem measurable_annulusExitWitness (α R : ℝ) : Measurable (annulusExitWitness α R) := by
  unfold annulusExitWitness pairing
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) (by fun_prop)

theorem norm_add_sq_eq_pairing (p w : ℂ) : ‖p + w‖ ^ 2 = ‖p‖ ^ 2 + 2 * pairing p w + ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, pairing]
  ring

/-- The annulus `B_R(0) \ closedBall 0 α` is open. -/
theorem isOpen_annulus (α R : ℝ) : IsOpen (ball (0 : ℂ) R \ closedBall 0 α) :=
  isOpen_ball.sdiff isClosed_closedBall

/-- The closure of the annulus lies in `{α ≤ |z| ≤ R}`. -/
theorem closure_annulus_subset (α R : ℝ) :
    closure (ball (0 : ℂ) R \ closedBall 0 α) ⊆ closedBall (0 : ℂ) R ∩ {z : ℂ | α ≤ ‖z‖} :=
  closure_minimal (fun _ hz => ⟨ball_subset_closedBall hz.1,
      (not_le.1 fun h => hz.2 (mem_closedBall_zero_iff.2 h)).le⟩)
    (isClosed_closedBall.inter (isClosed_le continuous_const continuous_norm))

/-- The frontier points of the annulus lie on its two circles. -/
theorem norm_eq_of_mem_frontier_annulus {α R : ℝ} {p : ℂ}
    (hp : p ∈ frontier (ball (0 : ℂ) R \ closedBall 0 α)) : ‖p‖ = α ∨ ‖p‖ = R := by
  rw [(isOpen_annulus α R).frontier_eq] at hp
  obtain ⟨hcl, hnot⟩ := hp
  obtain ⟨h1, h2⟩ := closure_annulus_subset α R hcl
  have h1' : ‖p‖ ≤ R := mem_closedBall_zero_iff.1 h1
  have h2' : α ≤ ‖p‖ := h2
  rcases eq_or_lt_of_le h2' with h | h
  · exact Or.inl h.symm
  rcases eq_or_lt_of_le h1' with h' | h'
  · exact Or.inr h'
  exact absurd ⟨mem_ball_zero_iff.2 h', fun hc => (not_le.2 h) (mem_closedBall_zero_iff.1 hc)⟩ hnot

/-- A positive exit witness at a frontier point puts `p + w` outside the closure of the annulus. -/
theorem notMem_closure_annulus_of_witness_pos {α R : ℝ} (hα : 0 < α) (hαR : α < R) {p w : ℂ}
    (hp : ‖p‖ = α ∨ ‖p‖ = R) (hw : 0 < annulusExitWitness α R (p, w)) :
    p + w ∉ closure (ball (0 : ℂ) R \ closedBall 0 α) := by
  intro hcl
  obtain ⟨h1, h2⟩ := closure_annulus_subset α R hcl
  have h1' : ‖p + w‖ ≤ R := mem_closedBall_zero_iff.1 h1
  have h2' : α ≤ ‖p + w‖ := h2
  have hsq := norm_add_sq_eq_pairing p w
  have hw2 := sq_nonneg ‖w‖
  rcases hp with hp | hp
  · have hlt : ‖p‖ < (α + R) / 2 := by rw [hp]; linarith
    simp only [annulusExitWitness, hlt, ↓reduceIte] at hw
    have hle := pow_le_pow_left₀ hα.le h2' 2
    rw [hp] at hsq
    linarith
  · have hnlt : ¬ ‖p‖ < (α + R) / 2 := by rw [hp]; linarith
    simp only [annulusExitWitness, hnlt, ↓reduceIte] at hw
    have hle := pow_le_pow_left₀ (norm_nonneg _) h1' 2
    rw [hp] at hsq
    linarith

/-- The law of a centred Gaussian of variance `v` is the image of the standard Gaussian under `y ↦ √v y`. -/
theorem gaussianReal_zero_apply_eq (v : ℝ≥0) {S : Set ℝ} (hS : MeasurableSet S) :
    gaussianReal 0 v S = gaussianReal 0 1 ((fun y => Real.sqrt v * y) ⁻¹' S) := by
  have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (Real.sqrt v)
  rw [mul_zero] at h
  have h2 : (gaussianReal 0 1).map (fun y => Real.sqrt v * y) = gaussianReal 0 v := by
    rw [h]
    congr 1
    ext
    rw [NNReal.coe_mul, NNReal.coe_one, mul_one]
    exact Real.sq_sqrt (NNReal.coe_nonneg v)
  rw [← h2, Measure.map_apply (by fun_prop) hS]

/-- **The marginal lower bound for the exit witness of an annulus.** For a planar Brownian motion `W` and a point
`x` on one of the two circles, the probability that the exit witness of `(x, W_q)` is positive is bounded below by
a positive constant for all small `q > 0`. -/
theorem exists_marginal_annulusExitWitness {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → ℂ} (hW : IsPlanarBrownian W P) {α R : ℝ} (hα : 0 < α)
    (hαR : α < R) {x : ℂ} (hx : ‖x‖ = α ∨ ‖x‖ = R) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∃ q₀ : ℝ≥0, 0 < q₀ ∧ ∀ q : ℝ≥0, 0 < q → q < q₀ →
      c ≤ P ((fun ω => annulusExitWitness α R (x, W q ω)) ⁻¹' Ioi 0) := by
  rcases hx with hx | hx
  · -- the inner circle
    have hlt : ‖x‖ < (α + R) / 2 := by rw [hx]; linarith
    set c₁ : ℝ≥0∞ := gaussianReal 0 1 (Ioi (1 : ℝ)) with hc₁def
    have hc₁ : 0 < c₁ := by
      refine pos_iff_ne_zero.2 fun h => ?_
      have h' := gaussianReal_absolutelyContinuous' (0 : ℝ) (one_ne_zero : (1 : ℝ≥0) ≠ 0) h
      rw [Real.volume_Ioi] at h'
      exact ENNReal.top_ne_zero h'
    have hc₁top : c₁ ≠ ⊤ := measure_ne_top _ _
    set c₂ : ℝ≥0∞ := c₁ / 2 with hc₂def
    have hc₂ : 0 < c₂ / 2 := ENNReal.half_pos (ENNReal.half_pos hc₁.ne').ne'
    obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ gaussianReal 0 1 {y : ℝ | M ≤ |y|} ≤ c₂ / 2 := by
      have hmeas : ∀ n : ℕ, NullMeasurableSet {y : ℝ | (n : ℝ) + 1 ≤ |y|} (gaussianReal 0 1) :=
        fun n => (measurableSet_le measurable_const continuous_abs.measurable).nullMeasurableSet
      have hanti : Antitone fun n : ℕ => {y : ℝ | (n : ℝ) + 1 ≤ |y|} := by
        intro m n hmn y hy
        have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          have : (m : ℝ) ≤ n := by exact_mod_cast hmn
          linarith
        exact le_trans hmn' hy
      have hempty : (⋂ n : ℕ, {y : ℝ | (n : ℝ) + 1 ≤ |y|}) = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun y hy => ?_
        obtain ⟨n, hn⟩ := exists_nat_gt |y|
        have h := mem_iInter.1 hy n
        have h' : (n : ℝ) + 1 ≤ |y| := h
        linarith
      have ht := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
      rw [hempty, measure_empty] at ht
      obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hc₂)).exists
      exact ⟨(n : ℝ) + 1, by positivity, hn.le⟩
    have hαM : 0 < α / M ^ 2 := div_pos hα (by positivity)
    refine ⟨c₁ - c₂, tsub_pos_iff_lt.2 (ENNReal.half_lt_self hc₁.ne' hc₁top),
      Real.toNNReal ((α / M ^ 2) ^ 2), Real.toNNReal_pos.2 (by positivity), fun q hq hqq₀ => ?_⟩
    have hq' : (0 : ℝ) < q := NNReal.coe_pos.2 hq
    have hqq₀' : (q : ℝ) < (α / M ^ 2) ^ 2 := by
      have := (Real.lt_toNNReal_iff_coe_lt).1 hqq₀
      exact this
    have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq'
    have hsqlt : Real.sqrt q < α / M ^ 2 := by
      have h := Real.sqrt_lt_sqrt (NNReal.coe_nonneg q) hqq₀'
      rwa [Real.sqrt_sq hαM.le] at h
    have hMq : M ^ 2 * Real.sqrt q < α := by
      have h := mul_lt_mul_of_pos_left hsqlt (by positivity : (0 : ℝ) < M ^ 2)
      rwa [mul_div_cancel₀ _ (by positivity : M ^ 2 ≠ 0)] at h
    have hkey : M ^ 2 * q < α * Real.sqrt q := by
      calc M ^ 2 * (q : ℝ) = (M ^ 2 * Real.sqrt q) * Real.sqrt q := by
            rw [mul_assoc, Real.mul_self_sqrt (NNReal.coe_nonneg q)]
        _ < α * Real.sqrt q := mul_lt_mul_of_pos_right hMq hsq
    -- the three events
    set E₁ : Set Ω := (fun ω => pairing (-x) (W q ω)) ⁻¹' Ioi (α * Real.sqrt q) with hE₁
    set E₂ : Set Ω := (fun ω => (W q ω).re) ⁻¹' {y : ℝ | M * Real.sqrt q ≤ |y|} ∪
      (fun ω => (W q ω).im) ⁻¹' {y : ℝ | M * Real.sqrt q ≤ |y|} with hE₂
    have hnx : x.re ^ 2 + x.im ^ 2 = α ^ 2 := by
      rw [← hx, Complex.sq_norm, Complex.normSq_apply]
      ring
    have hvar : ((pairingVar (-x) q : ℝ≥0) : ℝ) = α ^ 2 * q := by
      have hre : ((sqNNReal (-x).re : ℝ≥0) : ℝ) = x.re ^ 2 := by
        show (-x).re ^ 2 = x.re ^ 2
        rw [Complex.neg_re, neg_sq]
      have him : ((sqNNReal (-x).im : ℝ≥0) : ℝ) = x.im ^ 2 := by
        show (-x).im ^ 2 = x.im ^ 2
        rw [Complex.neg_im, neg_sq]
      rw [pairingVar, NNReal.coe_mul, NNReal.coe_add, hre, him, hnx]
    have hsqrtv : Real.sqrt (pairingVar (-x) q : ℝ) = α * Real.sqrt q := by
      rw [hvar, Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le]
    have hE₁eq : P E₁ = c₁ := by
      have hl := hasLaw_pairing hW (-x) q
      rw [hE₁, ← Measure.map_apply_of_aemeasurable hl.aemeasurable measurableSet_Ioi, hl.map_eq,
        gaussianReal_zero_apply_eq _ measurableSet_Ioi, hsqrtv, hc₁def]
      congr 1
      ext y
      simp only [mem_preimage, mem_Ioi]
      exact lt_mul_iff_one_lt_right (mul_pos hα hsq)
    have htail : ∀ Y : Ω → ℝ, HasLaw Y (gaussianReal 0 q) P →
        P (Y ⁻¹' {y : ℝ | M * Real.sqrt q ≤ |y|}) ≤ c₂ / 2 := by
      intro Y hY
      have hS : MeasurableSet {y : ℝ | M * Real.sqrt q ≤ |y|} :=
        measurableSet_le measurable_const continuous_abs.measurable
      rw [← Measure.map_apply_of_aemeasurable hY.aemeasurable hS, hY.map_eq,
        gaussianReal_zero_apply_eq _ hS]
      refine le_trans (measure_mono fun y hy => ?_) hM
      have hy' : M * Real.sqrt q ≤ |Real.sqrt q * y| := hy
      rw [abs_mul, abs_of_pos hsq, mul_comm M] at hy'
      exact le_of_mul_le_mul_left hy' hsq
    have hE₂le : P E₂ ≤ c₂ := by
      calc P E₂ ≤ c₂ / 2 + c₂ / 2 := (measure_union_le _ _).trans (add_le_add
            (htail _ (hW.re.toIsPreBrownianReal.hasLaw_eval q))
            (htail _ (hW.im.toIsPreBrownianReal.hasLaw_eval q)))
        _ = c₂ := ENNReal.add_halves c₂
    have hsub : E₁ \ E₂ ⊆ (fun ω => annulusExitWitness α R (x, W q ω)) ⁻¹' Ioi 0 := by
      intro ω hω
      obtain ⟨h1, h2⟩ := hω
      have h1' : α * Real.sqrt q < pairing (-x) (W q ω) := h1
      have hre : |(W q ω).re| < M * Real.sqrt q := not_le.1 fun h => h2 (Or.inl h)
      have him : |(W q ω).im| < M * Real.sqrt q := not_le.1 fun h => h2 (Or.inr h)
      have hMsq : (M * Real.sqrt q) ^ 2 = M ^ 2 * q := by
        rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg q)]
      have hre2 := sq_lt_sq' (abs_lt.1 hre).1 (abs_lt.1 hre).2
      have him2 := sq_lt_sq' (abs_lt.1 him).1 (abs_lt.1 him).2
      have hnorm : ‖W q ω‖ ^ 2 = (W q ω).re ^ 2 + (W q ω).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have hpneg : pairing (-x) (W q ω) = -pairing x (W q ω) := by
        simp only [pairing, Complex.neg_re, Complex.neg_im]
        ring
      show 0 < annulusExitWitness α R (x, W q ω)
      simp only [annulusExitWitness, hlt, ↓reduceIte]
      rw [hMsq] at hre2 him2
      linarith
    calc c₁ - c₂ ≤ P E₁ - P E₂ := tsub_le_tsub hE₁eq.ge hE₂le
      _ ≤ P (E₁ \ E₂) := le_measure_sdiff
      _ ≤ _ := measure_mono hsub
  · -- the outer circle
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      linarith
    have hnlt : ¬ ‖x‖ < (α + R) / 2 := by rw [hx]; linarith
    refine ⟨2⁻¹, ENNReal.inv_pos.2 ENNReal.ofNat_ne_top, 1, one_pos, fun q hq _ => le_of_eq ?_⟩
    rw [← measure_pairing_pos hW hx0 hq.ne']
    congr 1
    ext ω
    simp only [mem_preimage, annulusExitWitness, hnlt, ↓reduceIte]

/-- **Regular exit from an annulus.** Planar Brownian motion started at a point of the annulus
`B_R(0) \ closedBall 0 α`, `0 < α < R`, almost surely leaves it at a finite time and exits it regularly. -/
theorem ae_regularExit_annulus_planarBrownian {α R : ℝ} (hα : 0 < α) (hαR : α < R) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) R \ closedBall 0 α) :
    ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion x,
      pathExitTime (ball (0 : ℂ) R \ closedBall 0 α) ⇑b ≠ ⊤ ∧
        MatedCRT.TruncatedLaws.RegularExit (ball (0 : ℂ) R \ closedBall 0 α) ⇑b := by
  set U : Set ℂ := ball (0 : ℂ) R \ closedBall 0 α with hUdef
  have hU : IsOpen U := isOpen_annulus α R
  have hUb : Bornology.IsBounded U := isBounded_ball.subset sdiff_subset
  have hfin : ∀ᵐ b ∂planarBrownianMotion x, ContinuousPath.exitTime U b ≠ ⊤ :=
    (HarmonicBalls.Section6.ae_planarBrownian_exitTime_bounded_lt_top x hUb).mono fun _ hb => hb.ne
  obtain ⟨hW, hind, hBτ⟩ := ExitRestart.exit_restart_planar hU x hfin
  have hBlum := fun A hA =>
    LatticeProb.PlanarBrownian.isTrivialSigma_iInf_pathSigmaTo_planar hW
      (LatticeProb.isTrivialSigma_iInf_bmPast hW.re fun t => Complex.measurable_re.comp (hW.measurable t))
      (LatticeProb.isTrivialSigma_iInf_bmPast hW.im fun t => Complex.measurable_im.comp (hW.measurable t)) A hA
  have hfr : ∀ᵐ b ∂planarBrownianMotion x, b (ExitRestart.exitNN U b) ∈ frontier U := by
    filter_upwards [hfin, ae_planarBrownianMotion_eval_zero x] with b hb hb0
    exact ContinuousPath.coordinate_exitTime_mem_frontier U hU b (hb0 ▸ hx) hb
  have hmarg : ∀ᵐ y ∂(planarBrownianMotion x).map (fun b : ContinuousPath ℂ => b (ExitRestart.exitNN U b)),
      ∃ c : ℝ≥0∞, 0 < c ∧ ∃ q₀ : ℝ≥0, 0 < q₀ ∧ ∀ q : ℝ≥0, 0 < q → q < q₀ →
        c ≤ planarBrownianMotion x ((fun b : ContinuousPath ℂ => annulusExitWitness α R
          (y, b (ExitRestart.exitNN U b + q) - b (ExitRestart.exitNN U b))) ⁻¹' Ioi 0) := by
    have hfr' : ∀ᵐ y ∂(planarBrownianMotion x).map (fun b : ContinuousPath ℂ => b (ExitRestart.exitNN U b)),
        y ∈ frontier U := (ae_map_iff hBτ isClosed_frontier.measurableSet).2 hfr
    filter_upwards [hfr'] with y hy
    exact exists_marginal_annulusExitWitness hW hα hαR (norm_eq_of_mem_frontier_annulus hy)
  have hfreq := ae_frequently_pos_of_indepFun_of_marginal hW hBlum hBτ hind
    (measurable_annulusExitWitness α R) hmarg
  filter_upwards [hfreq, hfin, hfr] with b hb hbfin hbfr
  refine ⟨hbfin, Or.inr ?_⟩
  set τ : ℝ≥0 := ExitRestart.exitNN U b with hτ
  have hT : Tendsto (fun s : ℝ≥0 => τ + s) (𝓝[>] 0) (𝓝[>] τ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ≥0 => τ + s) (𝓝 0) (𝓝 (τ + 0)) :=
        tendsto_const_nhds.add tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact lt_add_of_pos_right _ (show (0 : ℝ≥0) < s from hs)
  have hout : ∃ᶠ s in 𝓝[>] (0 : ℝ≥0), b (τ + s) ∉ closure U := by
    refine hb.mono fun s hs => ?_
    have h := notMem_closure_annulus_of_witness_pos hα hαR (norm_eq_of_mem_frontier_annulus hbfr) hs
    have heq : b τ + (b (τ + s) - b τ) = b (τ + s) := by ring
    rwa [heq] at h
  exact hT.frequently (p := fun t => b t ∉ closure U) hout

end MatedCRT.StopAtExitCmp
