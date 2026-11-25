import MatedCRT.Proofs.Sec2.ConeFamilyFunctional.DenseCircle
import MatedCRT.Proofs.Sec2.ConeFamilyFunctional.Uniqueness
import LatticeProb.Analysis.VagueLimitSequence

/-!
# The LQG measure of a circle average process from its values at rational points

For `y : DenseCircle` let `approx γ y k = lqgApprox γ (extend y) (2^{-k})` be the measures `ε^{γ²/2} e^{γ h_ε(z)} dz`
of the extended process.

* `IsLQGLimit` determines its limit (`IsLQGLimit.unique`: locally finite measures on `ℂ` are regular, and a regular
  measure is determined by its integrals of compactly supported continuous functions).
* `DomR γ`: the Borel set of locally uniformly continuous `y` whose integrals converge on the countable
  convergence-determining family `detFamily` (`LatticeProb.VagueLimit.exists_countable_determining_vague_limit`, the
  Riesz-Markov-Kakutani representation of the limit functional). On it the vague limit exists
  (`exists_isLQGLimit_of_mem_domR`), and `limitMeasure γ y` is that limit.
* `codeOf γ ρ y`: a Borel function of `y` with values in `M_f(B̄_ρ)` which equals `ν|_{B̄_ρ}` whenever the extended
  process has the vague limit `ν` (`codeOf_eq`), for `ρ ≤ 1`. It is the Lusin-Souslin section of the Borel graph of the
  pairs `(y, s)` whose integrals `∫ g χ d(approx γ y k)` converge to `∫ g ds` on the determining family, where `χ` is
  a cutoff equal to `1` on `B̄_1`; this graph has at most one `s` over each `y`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls
open scoped ENNReal

namespace ConeFamilyFunctional

/-- The approximating measures of the extended process at the dyadic scales. -/
noncomputable abbrev approx (γ : ℝ) (y : DenseCircle) (k : ℕ) : Measure ℂ :=
  lqgApprox γ (extend y) (dyadicScale k)

/-! ### Uniqueness of vague limits -/

/-- Two locally finite measures on `ℂ` with the same integrals of compactly supported continuous functions agree. -/
theorem measure_eq_of_integral_eq {ν₁ ν₂ : Measure ℂ} [IsLocallyFiniteMeasure ν₁] [IsLocallyFiniteMeasure ν₂]
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → ∫ z, f z ∂ν₁ = ∫ z, f z ∂ν₂) : ν₁ = ν₂ :=
  Measure.ext_of_integral_eq_on_compactlySupported fun f => h f f.continuous f.hasCompactSupport

/-- The vague limit of `IsLQGLimit` is unique. -/
theorem IsLQGLimit.unique {γ : ℝ} {hε : ℝ → ℂ → ℝ} {ν₁ ν₂ : Measure ℂ} (h₁ : IsLQGLimit γ hε ν₁)
    (h₂ : IsLQGLimit γ hε ν₂) : ν₁ = ν₂ := by
  have := h₁.isLocallyFiniteMeasure
  have := h₂.isLocallyFiniteMeasure
  exact measure_eq_of_integral_eq fun f hf hfc =>
    tendsto_nhds_unique (h₁.tendsto_integral f hf hfc) (h₂.tendsto_integral f hf hfc)

/-- `IsLQGLimit` depends only on the process at positive radii. -/
theorem isLQGLimit_congr {γ : ℝ} {h₁ h₂ : ℝ → ℂ → ℝ} (h : ∀ r z, 0 < r → h₁ r z = h₂ r z) {ν : Measure ℂ} :
    IsLQGLimit γ h₁ ν ↔ IsLQGLimit γ h₂ ν := by
  have heq : ∀ k, lqgApprox γ h₁ (dyadicScale k) = lqgApprox γ h₂ (dyadicScale k) := fun k => by
    unfold lqgApprox
    congr 1
    funext z
    rw [h _ _ (dyadicScale_pos k)]
  constructor
  · exact fun hl => ⟨hl.1, fun f hf hfc => by simpa only [heq] using hl.2 f hf hfc⟩
  · exact fun hl => ⟨hl.1, fun f hf hfc => by simpa only [heq] using hl.2 f hf hfc⟩

/-- The extended process of the values of a continuous process at the rational points has the same vague limit. -/
theorem isLQGLimit_extend_restrictDense {γ : ℝ} {c : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ)) {ν : Measure ℂ} (hν : IsLQGLimit γ c ν) :
    IsLQGLimit γ (extend (restrictDense (circleProcess c))) ν :=
  (isLQGLimit_congr fun _ z hr => extend_restrictDense hc hr z).2 hν

/-! ### Measurability of the approximating integrals -/

/-- `y ↦ ∫ g d(approx γ y k)` is Borel for a bounded continuous `g`. -/
theorem measurable_integral_approx (γ : ℝ) {g : ℂ → ℝ} (hg : Continuous g) (k : ℕ) :
    Measurable fun y : DenseCircle => ∫ z, g z ∂(approx γ y k) := by
  set ε := dyadicScale k with hε
  set a : ℝ := ε ^ (γ ^ 2 / 2) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg (dyadicScale_pos k).le _
  let F : DenseCircle × ℂ → ℝ := fun p => (a * Real.exp (γ * extend p.1 ε p.2)) * g p.2
  have hF : Measurable F := by
    have he : Measurable fun p : DenseCircle × ℂ => extend p.1 ε p.2 :=
      measurable_extend.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    exact (measurable_const.mul ((measurable_const.mul he).exp)).mul (hg.measurable.comp measurable_snd)
  have hI : Measurable fun y => ∫ z, F (y, z) := hF.stronglyMeasurable.integral_prod_right'.measurable
  suffices heq : (fun y : DenseCircle => ∫ z, g z ∂(approx γ y k)) = fun y => ∫ z, F (y, z) by
    rw [heq]
    exact hI
  funext y
  have hden : Measurable fun z => ENNReal.ofReal (a * Real.exp (γ * extend y ε z)) :=
    (measurable_const.mul ((measurable_const.mul (measurable_extend.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))).exp)).ennreal_ofReal
  have htop : ∀ᵐ z : ℂ ∂volume, ENNReal.ofReal (a * Real.exp (γ * extend y ε z)) < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  show ∫ z, g z ∂(lqgApprox γ (extend y) ε) = ∫ z, F (y, z)
  unfold lqgApprox
  rw [integral_withDensity_eq_integral_toReal_smul hden htop]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [F, ENNReal.toReal_ofReal (mul_nonneg ha0 (Real.exp_pos _).le), smul_eq_mul]

/-- On locally uniformly continuous values the approximating measures are finite on compacts. -/
theorem isFiniteMeasureOnCompacts_approx {γ : ℝ} {y : DenseCircle} (hy : y ∈ LocUnifCont) (k : ℕ) :
    IsFiniteMeasureOnCompacts (approx γ y k) := by
  have hc : Continuous fun z : ℂ => dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * extend y (dyadicScale k) z) := by
    refine continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul ?_))
    exact (continuousOn_extend hy).comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨dyadicScale_pos k, mem_univ _⟩)
  have := IsLocallyFiniteMeasure.withDensity_ofReal (μ := (volume : Measure ℂ)) hc
  unfold approx lqgApprox
  infer_instance

/-! ### The domain of the vague limit -/

/-- The countable convergence-determining family of compactly supported continuous functions. -/
noncomputable def detFamily : Set (ℂ → ℝ) :=
  Classical.choose (LatticeProb.VagueLimit.exists_countable_determining_vague_limit (X := ℂ))

theorem detFamily_spec : detFamily.Countable ∧ (∀ g ∈ detFamily, Continuous g ∧ HasCompactSupport g) ∧
    ∀ m : ℕ → Measure ℂ, (∀ k, IsFiniteMeasureOnCompacts (m k)) →
      (∀ g ∈ detFamily, ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, g x ∂(m k)) atTop (𝓝 ℓ)) →
      ∃ μ : Measure ℂ, IsLocallyFiniteMeasure μ ∧ ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
        Tendsto (fun k => ∫ x, f x ∂(m k)) atTop (𝓝 (∫ x, f x ∂μ)) :=
  Classical.choose_spec (LatticeProb.VagueLimit.exists_countable_determining_vague_limit (X := ℂ))

/-- The values with a vague limit: locally uniformly continuous with convergent integrals on `detFamily`. -/
def DomR (γ : ℝ) : Set DenseCircle :=
  LocUnifCont ∩ {y | ∀ g ∈ detFamily, ∃ ℓ : ℝ, Tendsto (fun k => ∫ z, g z ∂(approx γ y k)) atTop (𝓝 ℓ)}

theorem measurableSet_domR (γ : ℝ) : MeasurableSet (DomR γ) := by
  refine measurableSet_locUnifCont.inter ?_
  have : Countable detFamily := detFamily_spec.1.to_subtype
  convert MeasurableSet.iInter fun g : detFamily =>
    measurableSet_exists_tendsto (l := atTop) (f := fun k y => ∫ z, (g : ℂ → ℝ) z ∂(approx γ y k))
      (fun k => measurable_integral_approx γ (detFamily_spec.2.1 g g.2).1 k) using 1
  ext y
  simp only [mem_ofPred_eq, mem_iInter]
  exact ⟨fun h g => h g g.2, fun h g hg => h ⟨g, hg⟩⟩

/-- On `DomR` the extended process has a vague limit. -/
theorem exists_isLQGLimit_of_mem_domR {γ : ℝ} {y : DenseCircle} (hy : y ∈ DomR γ) :
    ∃ ν : Measure ℂ, IsLQGLimit γ (extend y) ν := by
  obtain ⟨ν, hν, hlim⟩ := detFamily_spec.2.2 (approx γ y) (isFiniteMeasureOnCompacts_approx hy.1) hy.2
  exact ⟨ν, hν, hlim⟩

/-- A process with a vague limit and locally uniformly continuous values is in `DomR`. -/
theorem mem_domR_of_isLQGLimit {γ : ℝ} {y : DenseCircle} (hy : y ∈ LocUnifCont) {ν : Measure ℂ}
    (hν : IsLQGLimit γ (extend y) ν) : y ∈ DomR γ :=
  ⟨hy, fun g hg => ⟨_, hν.2 g (detFamily_spec.2.1 g hg).1 (detFamily_spec.2.1 g hg).2⟩⟩

open Classical in
/-- The vague limit of the extended process, and the zero measure when there is none. -/
noncomputable def limitMeasure (γ : ℝ) (y : DenseCircle) : Measure ℂ :=
  if h : ∃ ν : Measure ℂ, IsLQGLimit γ (extend y) ν then Classical.choose h else 0

theorem isLQGLimit_limitMeasure {γ : ℝ} {y : DenseCircle} (h : ∃ ν : Measure ℂ, IsLQGLimit γ (extend y) ν) :
    IsLQGLimit γ (extend y) (limitMeasure γ y) := by
  simp only [limitMeasure, h, ↓reduceDIte]
  exact Classical.choose_spec h

theorem limitMeasure_eq {γ : ℝ} {y : DenseCircle} {ν : Measure ℂ} (hν : IsLQGLimit γ (extend y) ν) :
    limitMeasure γ y = ν :=
  (isLQGLimit_limitMeasure ⟨ν, hν⟩).unique hν

/-! ### The Borel local code -/

/-- The cutoff equal to `1` on `B̄_1` and vanishing off `B̄_2`. -/
noncomputable def cutoff : ℂ → ℝ := LatticeProb.VagueLimit.ballCutoff (0 : ℂ) 1

theorem continuous_cutoff : Continuous cutoff := LatticeProb.VagueLimit.continuous_ballCutoff 0 1

theorem cutoff_nonneg (z : ℂ) : 0 ≤ cutoff z := LatticeProb.VagueLimit.ballCutoff_nonneg 0 1 z

theorem cutoff_eq_one {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : cutoff z = 1 :=
  LatticeProb.VagueLimit.ballCutoff_eq_one (by simpa [mem_closedBall] using hz)

theorem cutoff_eq_zero {z : ℂ} (hz : z ∉ closedBall (0 : ℂ) 2) : cutoff z = 0 :=
  LatticeProb.VagueLimit.ballCutoff_eq_zero (by
    have h2 : (2 : ℝ) < dist z 0 := not_le.1 fun h => hz (mem_closedBall.2 h)
    push_cast
    linarith)

theorem hasCompactSupport_cutoff : HasCompactSupport cutoff :=
  LatticeProb.VagueLimit.hasCompactSupport_ballCutoff 0 1

/-- The graph of the local code: the pairs `(y, s)` whose integrals `∫ g χ d(approx γ y k)` converge to `∫ g ds` on
the determining family. -/
def codeGraph (γ : ℝ) : Set (DenseCircle × FinMeasDisk 2) :=
  {p | ∀ g ∈ detFamily, Tendsto (fun k => ∫ z, g z * cutoff z ∂(approx γ p.1 k)) atTop
    (𝓝 (∫ z, g z ∂(p.2 : Measure ℂ)))}

/-- Real sequences converging to a measurable limit: a measurable condition. -/
theorem measurableSet_tendsto_of_measurable {α : Type*} [MeasurableSpace α] {f : ℕ → α → ℝ} {L : α → ℝ}
    (hf : ∀ k, Measurable (f k)) (hL : Measurable L) :
    MeasurableSet {x | Tendsto (fun k => f k x) atTop (𝓝 (L x))} := by
  have h := MeasurableSet.iInter fun n : ℕ => MeasurableSet.iUnion fun N : ℕ => MeasurableSet.iInter fun k : ℕ =>
    (show MeasurableSet {x | N ≤ k → |f k x - L x| < 1 / ((n : ℝ) + 1)} by
      by_cases hk : N ≤ k
      · simpa [hk] using measurableSet_lt ((hf k).sub hL).abs measurable_const
      · simp [hk])
  convert h using 1
  ext x
  simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
  rw [Metric.tendsto_atTop]
  constructor
  · intro h n
    obtain ⟨N, hN⟩ := h (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨N, fun k hk => by rw [← Real.dist_eq]; exact hN k hk⟩
  · intro h ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := h n
    exact ⟨N, fun k hk => by rw [Real.dist_eq]; exact (hN k hk).trans hn⟩

/-- Integrals of compactly supported continuous functions are Borel on `M_f(B̄_ρ)`. -/
theorem measurable_integral_finMeasDisk_of_cc {ρ : ℝ} {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Measurable fun s : FinMeasDisk ρ => ∫ z, g z ∂(s : Measure ℂ) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  exact measurable_integral_finMeasDisk hg.measurable (C := C) fun x => by simpa [Real.norm_eq_abs] using hC x

theorem measurableSet_codeGraph (γ : ℝ) : MeasurableSet (codeGraph γ) := by
  have : Countable detFamily := detFamily_spec.1.to_subtype
  convert MeasurableSet.iInter fun g : detFamily => measurableSet_tendsto_of_measurable
    (f := fun k (p : DenseCircle × FinMeasDisk 2) => ∫ z, (g : ℂ → ℝ) z * cutoff z ∂(approx γ p.1 k))
    (L := fun p : DenseCircle × FinMeasDisk 2 => ∫ z, (g : ℂ → ℝ) z ∂(p.2 : Measure ℂ))
    (fun k => (measurable_integral_approx γ
      ((detFamily_spec.2.1 g g.2).1.mul continuous_cutoff) k).comp measurable_fst)
    ((measurable_integral_finMeasDisk_of_cc (detFamily_spec.2.1 g g.2).1
      (detFamily_spec.2.1 g g.2).2).comp measurable_snd) using 1
  · ext p
    simp only [codeGraph, mem_ofPred_eq, mem_iInter]
    exact ⟨fun h g => h g g.2, fun h g hg => h ⟨g, hg⟩⟩

theorem cutoff_le_one (z : ℂ) : cutoff z ≤ 1 := by
  unfold cutoff LatticeProb.VagueLimit.ballCutoff
  exact max_le zero_le_one (min_le_left _ _)

/-- The density of the cutoff local measure. -/
noncomputable def cutoffDensity (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (cutoff z)

theorem measurable_cutoffDensity : Measurable cutoffDensity :=
  continuous_cutoff.measurable.ennreal_ofReal

theorem cutoffDensity_le_indicator (z : ℂ) :
    cutoffDensity z ≤ (closedBall (0 : ℂ) 2).indicator 1 z := by
  by_cases hz : z ∈ closedBall (0 : ℂ) 2
  · rw [indicator_of_mem hz, Pi.one_apply, cutoffDensity, ENNReal.ofReal_le_one]
    exact cutoff_le_one z
  · rw [indicator_of_notMem hz, cutoffDensity, cutoff_eq_zero hz, ENNReal.ofReal_zero]

/-- The cutoff local measure `χ ν` of a locally finite measure, in `M_f(B̄_2)`. -/
noncomputable def cutoffMeasure (ν : Measure ℂ) [IsLocallyFiniteMeasure ν] : FinMeasDisk 2 :=
  ⟨ν.withDensity cutoffDensity, by
    refine ⟨⟨?_⟩, ?_⟩
    · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      refine lt_of_le_of_lt (lintegral_mono cutoffDensity_le_indicator) ?_
      rw [lintegral_indicator_one measurableSet_closedBall]
      exact measure_closedBall_lt_top
    · refine Measure.restrict_eq_self_of_ae_mem ?_
      rw [ae_iff]
      show ν.withDensity cutoffDensity (closedBall (0 : ℂ) 2)ᶜ = 0
      rw [withDensity_apply _ measurableSet_closedBall.compl]
      refine (setLIntegral_eq_zero_iff measurableSet_closedBall.compl measurable_cutoffDensity).2
        (Eventually.of_forall fun z hz => ?_)
      simp [cutoffDensity, cutoff_eq_zero hz]⟩

theorem integral_cutoffMeasure {ν : Measure ℂ} [IsLocallyFiniteMeasure ν] (g : ℂ → ℝ) :
    ∫ z, g z ∂((cutoffMeasure ν : FinMeasDisk 2) : Measure ℂ) = ∫ z, g z * cutoff z ∂ν := by
  change ∫ z, g z ∂(ν.withDensity cutoffDensity) = _
  rw [integral_withDensity_eq_integral_toReal_smul measurable_cutoffDensity
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [cutoffDensity, ENNReal.toReal_ofReal (cutoff_nonneg z), smul_eq_mul, mul_comm]

/-- A vague limit gives a point of the code graph. -/
theorem mem_codeGraph_of_isLQGLimit {γ : ℝ} {y : DenseCircle} {ν : Measure ℂ} [IsLocallyFiniteMeasure ν]
    (hν : IsLQGLimit γ (extend y) ν) : (y, cutoffMeasure ν) ∈ codeGraph γ := by
  intro g hg
  show Tendsto _ atTop (𝓝 (∫ z, g z ∂((cutoffMeasure ν : FinMeasDisk 2) : Measure ℂ)))
  rw [integral_cutoffMeasure]
  exact hν.tendsto_integral _ ((detFamily_spec.2.1 g hg).1.mul continuous_cutoff)
    ((detFamily_spec.2.1 g hg).2.mul_right)

/-- Finite measures with the same integrals on the determining family agree. -/
theorem eq_of_integral_eq_detFamily {s s' : Measure ℂ} [IsFiniteMeasure s] [IsFiniteMeasure s']
    (h : ∀ g ∈ detFamily, ∫ z, g z ∂s = ∫ z, g z ∂s') : s = s' := by
  let m : ℕ → Measure ℂ := fun k => if k % 2 = 0 then s else s'
  have hm : ∀ k, IsFiniteMeasureOnCompacts (m k) := fun k => by
    by_cases hk : k % 2 = 0
    · have e : m k = s := by simp only [m, hk, ↓reduceIte]
      rw [e]
      infer_instance
    · have e : m k = s' := by simp only [m, hk, ↓reduceIte]
      rw [e]
      infer_instance
  have hconv : ∀ g ∈ detFamily, ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, g x ∂(m k)) atTop (𝓝 ℓ) := by
    intro g hg
    refine ⟨∫ z, g z ∂s, tendsto_const_nhds.congr fun k => ?_⟩
    by_cases hk : k % 2 = 0
    · have e : m k = s := by simp only [m, hk, ↓reduceIte]
      rw [e]
    · have e : m k = s' := by simp only [m, hk, ↓reduceIte]
      rw [e]
      exact h g hg
  obtain ⟨μ, -, hlim⟩ := detFamily_spec.2.2 m hm hconv
  have e1 : ∀ j : ℕ, m (2 * j) = s := fun j => by
    have : (2 * j) % 2 = 0 := Nat.mul_mod_right 2 j
    simp only [m, this, ↓reduceIte]
  have e2 : ∀ j : ℕ, m (2 * j + 1) = s' := fun j => by
    have : (2 * j + 1) % 2 ≠ 0 := by omega
    simp only [m, this, ↓reduceIte]
  have t1 : Tendsto (fun j : ℕ => 2 * j) atTop atTop := tendsto_atTop_atTop.2 fun b => ⟨b, fun j hj => by omega⟩
  have t2 : Tendsto (fun j : ℕ => 2 * j + 1) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun j hj => by omega⟩
  refine measure_eq_of_integral_eq fun f hf hfc => ?_
  have h1 : Tendsto (fun j : ℕ => ∫ x, f x ∂(m (2 * j))) atTop (𝓝 (∫ x, f x ∂μ)) := (hlim f hf hfc).comp t1
  have h2 : Tendsto (fun j : ℕ => ∫ x, f x ∂(m (2 * j + 1))) atTop (𝓝 (∫ x, f x ∂μ)) := (hlim f hf hfc).comp t2
  simp only [e1, tendsto_const_nhds_iff] at h1
  simp only [e2, tendsto_const_nhds_iff] at h2
  rw [h1, h2]

/-- Over each `y` the code graph has at most one point. -/
theorem codeGraph_unique {γ : ℝ} {y : DenseCircle} {s s' : FinMeasDisk 2} (h : (y, s) ∈ codeGraph γ)
    (h' : (y, s') ∈ codeGraph γ) : s = s' := by
  have := s.2.1
  have := s'.2.1
  exact Subtype.ext (eq_of_integral_eq_detFamily fun g hg => tendsto_nhds_unique (h g hg) (h' g hg))

/-- The zero measure as an element of `M_f(B̄_2)`. -/
noncomputable def zeroDisk : FinMeasDisk 2 := ⟨0, inferInstance, Measure.restrict_zero _⟩

instance : StandardBorelSpace (FinMeasDisk 2) := frozenFiniteMeasureDiskStandardBorel_holds 2 (by norm_num)

/-- The Lusin-Souslin section of the code graph. -/
noncomputable def codeSection (γ : ℝ) : DenseCircle → FinMeasDisk 2 :=
  Classical.choose (exists_measurable_section_of_injective zeroDisk (codeGraph γ) (measurableSet_codeGraph γ)
    fun _ _ _ h h' => codeGraph_unique h h')

theorem measurable_codeSection (γ : ℝ) : Measurable (codeSection γ) :=
  (Classical.choose_spec (exists_measurable_section_of_injective zeroDisk (codeGraph γ) (measurableSet_codeGraph γ)
    fun _ _ _ h h' => codeGraph_unique h h')).1

theorem codeSection_mem {γ : ℝ} {y : DenseCircle} (h : ∃ s, (y, s) ∈ codeGraph γ) :
    (y, codeSection γ y) ∈ codeGraph γ :=
  (Classical.choose_spec (exists_measurable_section_of_injective zeroDisk (codeGraph γ) (measurableSet_codeGraph γ)
    fun _ _ _ h h' => codeGraph_unique h h')).2.1 y h

/-- The Borel local code of `y` on `B̄_ρ`. -/
noncomputable def codeOf (γ ρ : ℝ) (y : DenseCircle) : FinMeasDisk ρ :=
  diskMeasOf ρ ((codeSection γ y : FinMeasDisk 2) : Measure ℂ)

theorem measurable_codeOf (γ ρ : ℝ) : Measurable (codeOf γ ρ) :=
  (measurable_diskMeasOf ρ).comp (measurable_subtype_coe.comp (measurable_codeSection γ))

/-- **The local code is the restricted vague limit.** -/
theorem codeOf_eq {γ ρ : ℝ} (hρ : ρ ≤ 1) {y : DenseCircle} {ν : Measure ℂ} (hν : IsLQGLimit γ (extend y) ν) :
    codeOf γ ρ y = diskMeasOf ρ ν := by
  have := hν.isLocallyFiniteMeasure
  have hmem := mem_codeGraph_of_isLQGLimit (ν := ν) hν
  have hs : codeSection γ y = cutoffMeasure ν := codeGraph_unique (codeSection_mem ⟨_, hmem⟩) hmem
  have hfin : IsFiniteMeasure ((codeSection γ y : FinMeasDisk 2) : Measure ℂ) := (codeSection γ y).2.1
  apply Subtype.ext
  change restrictOrZero ρ _ = restrictOrZero ρ ν
  rw [restrictOrZero_eq_restrict inferInstance, restrictOrZero_eq_restrict inferInstance, hs]
  change (ν.withDensity cutoffDensity).restrict _ = _
  rw [restrict_withDensity measurableSet_closedBall]
  conv_rhs => rw [← withDensity_one (μ := ν.restrict (closedBall (0 : ℂ) ρ))]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
  simp only [cutoffDensity, Pi.one_apply, cutoff_eq_one (closedBall_subset_closedBall hρ hz), ENNReal.ofReal_one]

end ConeFamilyFunctional

end MatedCRT
