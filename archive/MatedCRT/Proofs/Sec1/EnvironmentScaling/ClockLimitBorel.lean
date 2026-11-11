import MatedCRT.Proofs.Sec1.EnvironmentScaling.AllStartsClock

/-!
# Borel clock-limit path map of the all-start selection

The Cauchy convergence set of the selected dyadic clocks
`A_{n_k(a,z)}(a,w,·)` in `𝒯 = C([0,∞),ℝ)` is Borel; its locally uniform limit `J(a,z,w)`, extended by `t ↦ t`
off convergence, is a Borel map into `𝒯`; and `F(a,w,·) = J(a,w(0),w)` is one Borel formula in `(a,w)`
.

Lean names for the paper's objects:
* `ClockPath`: `𝒯 = C([0,∞),ℝ)` as `C(ℝ≥0, ℝ)` with the compact-open topology, which is locally
  uniform convergence on `[0,∞)`. `clockPath_polishSpace` is its Polish structure (same argument as
  CircleProcessSpace.lean, `posCircleFns_polishSpace`).
* `idClockPath`: the default path `t ↦ t`.
* `clockApproxPath`, `selClockPath`: the dyadic clocks `A_n(a,w,·)` and the selected ones
  `A_{n_k(a,z)}(a,w,·)` with `nselFun` (AllStartsClock.lean, `borelSubsequenceSelectionStep_nselFun`).
* `clockConvergenceSet γ`: the set of `((a,z),w)` on which the selected clocks converge in `𝒯`.
* `clockLimitPath`: `J(a,z,w)` as a `𝒯`-valued path; its coercion is `clockLimit`.
* `clockLimitFn`: `F(a,w,·) = J(a,w(0),w)`.

Proved here, with no hypothesis, for the constructed subsequence `nselFun γ`:
* `measurableSet_clockConvergenceSet`: the convergence set is Borel.
* `measurable_clockLimitPath_nselFun`: `((a,z),w) ↦ J(a,z,w) ∈ 𝒯` is Borel.
* `measurable_clockLimitFn`: `(a,w) ↦ J(a,w(0),w) ∈ 𝒯` is Borel.

Not in this module: the universal measurability of `𝒢`, which takes the Preston input
`PrestonAnalyticUniversallyMeasurableStmt` in `allStartsSet_isUniversallyMeasurable` (AllStartsClock.lean).
-/

open MatedCRT.AllStarts
open HarmonicBalls MarkovProcess
open MeasureTheory TopologicalSpace Filter Topology
open scoped NNReal

namespace MatedCRT.ClockLimitBorel

/-- The path space `𝒯 = C([0,∞),ℝ)` with the compact-open topology, which is locally uniform
convergence on `[0,∞)`. -/
abbrev ClockPath : Type := C(ℝ≥0, ℝ)

/-- The identity path `t ↦ t`: the default of `J` off convergence. -/
def idClockPath : ClockPath := ⟨fun t => (t : ℝ), NNReal.continuous_coe⟩

/-- `𝒯` is completely metrizable: its compact-convergence uniformity is countably generated and complete. -/
theorem clockPath_isCompletelyMetrizableSpace : IsCompletelyMetrizableSpace ClockPath :=
  IsCompletelyMetrizableSpace.of_completeSpace_metrizable

/-- The Polish structure on the clock path space `𝒯 = C([0,∞),ℝ)`. -/
instance clockPath_polishSpace : PolishSpace ClockPath where
  toSecondCountableTopology := inferInstance
  toIsCompletelyMetrizableSpace := clockPath_isCompletelyMetrizableSpace

/-- The dyadic clock `A_n(a,w,·)` as a path in `𝒯`. -/
noncomputable def clockApproxPath (γ : ℝ) (a : CircleFns) (n : ℕ) (w : ContinuousPath ℂ) : ClockPath :=
  ⟨clockApprox γ a n w, continuous_clockApprox γ a n w⟩

/-- The selected clock `A_{n_k(a,z)}(a,w,·)` as a function of `x = ((a,z),w)`. -/
noncomputable def selClockPath (γ : ℝ) (k : ℕ) (x : (CircleFns × ℂ) × ContinuousPath ℂ) : ClockPath :=
  clockApproxPath γ x.1.1 (nselFun γ x.1.1 x.1.2 k) x.2

/-- The selected clocks are Borel as `𝒯`-valued maps: every evaluation at a time `t` is Borel
(`measurable_selApprox`), and `ContinuousMap.measurable_iff_eval` assembles them. -/
theorem measurable_selClockPath (γ : ℝ) (k : ℕ) : Measurable (selClockPath γ k) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  exact measurable_selApprox γ k t

/-- Locally uniform convergence of the clocks `A_{n_k}(a,w,·)` to a real function is convergence in `𝒯` to a continuous
path: the compact-open topology of `𝒯` is locally uniform convergence (`ContinuousMap.tendsto_iff_tendstoLocallyUniformly`),
and a locally uniform limit of continuous clocks is continuous. -/
theorem exists_locallyUniform_iff_exists_clockPath (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ)
    (a : CircleFns) (z : ℂ) (w : ContinuousPath ℂ) :
    (∃ f : ℝ≥0 → ℝ, TendstoLocallyUniformly (fun k => clockApprox γ a (nsel a z k) w) f atTop) ↔
      ∃ c : ClockPath, Tendsto (fun k => clockApproxPath γ a (nsel a z k) w) atTop (𝓝 c) := by
  constructor
  · rintro ⟨f, hf⟩
    have hfc : Continuous f :=
      hf.continuous ((Eventually.of_forall fun k => continuous_clockApprox γ a (nsel a z k) w).frequently)
    exact ⟨⟨f, hfc⟩, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.2 hf⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 hc⟩

/-- The convergence set of the selected clocks: the `((a,z),w)` for which
`(A_{n_k(a,z)}(a,w,·))_k` converges in `𝒯`. In the complete space `𝒯` this is the set where the selected sequence is
Cauchy for `d_𝒯`, the sequence whose almost-sure Cauchy property Borel–Cantelli gives, in the sense of `CauchyInProbability`. -/
def clockConvergenceSet (γ : ℝ) : Set ((CircleFns × ℂ) × ContinuousPath ℂ) :=
  {x | ∃ c : ClockPath, Tendsto (fun k => selClockPath γ k x) atTop (𝓝 c)}

/-- **The convergence set is Borel**. It is the set where a sequence of Borel
`𝒯`-valued maps converges, in the Polish space `𝒯` (Mathlib `measurableSet_exists_tendsto`). -/
theorem measurableSet_clockConvergenceSet (γ : ℝ) : MeasurableSet (clockConvergenceSet γ) :=
  measurableSet_exists_tendsto (l := atTop) fun k => measurable_selClockPath γ k

/-- Membership in the convergence set is locally uniform convergence of the selected clocks to a real function. -/
theorem mem_clockConvergenceSet_iff (γ : ℝ) (x : (CircleFns × ℂ) × ContinuousPath ℂ) :
    x ∈ clockConvergenceSet γ ↔
      ∃ f : ℝ≥0 → ℝ, TendstoLocallyUniformly (fun k => clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 k) x.2) f atTop :=
  (exists_locallyUniform_iff_exists_clockPath γ (nselFun γ) x.1.1 x.1.2 x.2).symm

/-- `clockLimit` is continuous: a locally uniform limit of continuous clocks, or the identity `t ↦ t`. -/
theorem continuous_clockLimit (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) (a : CircleFns) (z : ℂ)
    (w : ContinuousPath ℂ) : Continuous (clockLimit γ nsel a z w) := by
  unfold clockLimit
  split_ifs with h
  · exact h.choose_spec.continuous ((Eventually.of_forall fun k => continuous_clockApprox γ a (nsel a z k) w).frequently)
  · exact NNReal.continuous_coe

/-- `J(a,z,w)` as a path in `𝒯`: its coercion to a function is `clockLimit γ nsel a z w`. -/
noncomputable def clockLimitPath (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) (a : CircleFns) (z : ℂ)
    (w : ContinuousPath ℂ) : ClockPath :=
  ⟨clockLimit γ nsel a z w, continuous_clockLimit γ nsel a z w⟩

/-- On the convergence set the selected clocks converge in `𝒯` to `J` (`clockLimit` is the chosen locally uniform
limit). -/
theorem tendsto_clockApproxPath_clockLimitPath {γ : ℝ} {nsel : CircleFns → ℂ → ℕ → ℕ} {a : CircleFns} {z : ℂ}
    {w : ContinuousPath ℂ}
    (h : ∃ f : ℝ≥0 → ℝ, TendstoLocallyUniformly (fun k => clockApprox γ a (nsel a z k) w) f atTop) :
    Tendsto (fun k => clockApproxPath γ a (nsel a z k) w) atTop (𝓝 (clockLimitPath γ nsel a z w)) := by
  refine ContinuousMap.tendsto_iff_tendstoLocallyUniformly.2 ?_
  have hc : clockLimit γ nsel a z w = h.choose := by
    unfold clockLimit
    split_ifs
    rfl
  change TendstoLocallyUniformly (fun k => clockApprox γ a (nsel a z k) w) (clockLimit γ nsel a z w) atTop
  rw [hc]
  exact h.choose_spec

/-- Off the convergence set, `J` is the identity path `t ↦ t`. -/
theorem clockLimitPath_eq_idClockPath {γ : ℝ} {nsel : CircleFns → ℂ → ℕ → ℕ} {a : CircleFns} {z : ℂ}
    {w : ContinuousPath ℂ}
    (h : ¬ ∃ f : ℝ≥0 → ℝ, TendstoLocallyUniformly (fun k => clockApprox γ a (nsel a z k) w) f atTop) :
    clockLimitPath γ nsel a z w = idClockPath := by
  refine ContinuousMap.ext fun t => ?_
  change clockLimit γ nsel a z w t = (t : ℝ)
  unfold clockLimit
  split_ifs
  rfl

/-- **Borel clock-limit component**. The map `((a,z),w) ↦ J(a,z,w) ∈ 𝒯` is Borel for
the constructed subsequence `nselFun γ`. Proof: on the Borel convergence set, `J` is the pointwise limit of the Borel maps
`selClockPath γ k`; off it, `J` is the constant identity path. The glued maps `g_k` are Borel and converge pointwise to `J`
everywhere, so `J` is Borel (`measurable_of_tendsto_metrizable`, `𝒯` being pseudometrizable). -/
theorem measurable_clockLimitPath_nselFun (γ : ℝ) :
    Measurable fun x : (CircleFns × ℂ) × ContinuousPath ℂ => clockLimitPath γ (nselFun γ) x.1.1 x.1.2 x.2 := by
  classical
  have hg : ∀ k : ℕ, Measurable
      ((clockConvergenceSet γ).piecewise (selClockPath γ k) (fun _ => idClockPath)) :=
    fun k => Measurable.piecewise (measurableSet_clockConvergenceSet γ) (measurable_selClockPath γ k) measurable_const
  refine measurable_of_tendsto_metrizable hg ?_
  rw [tendsto_pi_nhds]
  intro x
  by_cases hx : x ∈ clockConvergenceSet γ
  · have hf := (mem_clockConvergenceSet_iff γ x).1 hx
    have hpw : ∀ k : ℕ, (clockConvergenceSet γ).piecewise (selClockPath γ k) (fun _ => idClockPath) x
        = selClockPath γ k x := fun k => Set.piecewise_eq_of_mem _ _ _ hx
    simp only [hpw]
    exact tendsto_clockApproxPath_clockLimitPath (γ := γ) (nsel := nselFun γ) (a := x.1.1) (z := x.1.2)
      (w := x.2) hf
  · have hf : ¬ ∃ f : ℝ≥0 → ℝ,
        TendstoLocallyUniformly (fun k => clockApprox γ x.1.1 (nselFun γ x.1.1 x.1.2 k) x.2) f atTop :=
      fun h => hx ((mem_clockConvergenceSet_iff γ x).2 h)
    have hpw : ∀ k : ℕ, (clockConvergenceSet γ).piecewise (selClockPath γ k) (fun _ => idClockPath) x
        = idClockPath := fun k => Set.piecewise_eq_of_notMem _ _ _ hx
    simp only [hpw]
    rw [clockLimitPath_eq_idClockPath (γ := γ) (nsel := nselFun γ) (a := x.1.1) (z := x.1.2) (w := x.2) hf]
    exact tendsto_const_nhds

/-- `F(a,w,·) = J(a,w(0),w)`: the path-valued all-start map, one formula in `(a,w)` for every
Brownian start `w(0)`. -/
noncomputable def clockLimitFn (γ : ℝ) (p : CircleFns × ContinuousPath ℂ) : ClockPath :=
  clockLimitPath γ (nselFun γ) p.1 (p.2 0) p.2

/-- Evaluation at time `0` is Borel on the path space: the Brownian start `w(0)` is a measurable function of `w`. -/
theorem measurable_clockLimitFn_evalZero : Measurable fun w : ContinuousPath ℂ => w 0 :=
  ContinuousMap.measurable_eval (0 : ℝ≥0)

/-- The start map `(a,w) ↦ (a, w(0), w)` is Borel. -/
theorem measurable_clockLimitFn_start (hev : Measurable fun w : ContinuousPath ℂ => w 0) :
    Measurable fun p : CircleFns × ContinuousPath ℂ => ((p.1, p.2 0), p.2) :=
  (measurable_fst.prodMk (hev.comp measurable_snd)).prodMk measurable_snd

/-- **The all-start path map is Borel**: `(a,w) ↦ J(a,w(0),w) ∈ 𝒯`, for every start `w(0)` at
once. It is the composite of the Borel limit `J` with the Borel start map; the composite is formed without an expected
type and then matched, which avoids higher-order unification against `clockLimitFn`. -/
theorem measurable_clockLimitFn (γ : ℝ) : Measurable (clockLimitFn γ) := by
  have h := (measurable_clockLimitPath_nselFun γ).comp
    (measurable_clockLimitFn_start measurable_clockLimitFn_evalZero)
  exact h

/-- **Named Step `BorelClockLimitPathStep`, proved for `nselFun`**: the path-valued
all-start map `(a,w) ↦ J(a,w(0),w)` is Borel. -/
def BorelClockLimitPathStep (γ : ℝ) : Prop := Measurable (clockLimitFn γ)

/-- The Borel clock-limit path Step holds for the constructed subsequence (no hypothesis). -/
theorem borelClockLimitPathStep (γ : ℝ) : BorelClockLimitPathStep γ := measurable_clockLimitFn γ

end MatedCRT.ClockLimitBorel
