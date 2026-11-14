import MatedCRT.FirstPass.Derived.ExitCdfMedianPos
import LatticeProb.Prob.NonnegInfimum
import LatticeProb.Prob.IndependentDetermination

/-!
# The median of an exit-time distribution function: scaling and measurability

The median `medianOf cdf = inf {m ≥ 0 : cdf m ≥ 1/2}` of a distribution function is divided by `c` when
the argument of the distribution function is multiplied by `c > 0`, and it is a measurable function of
a measurable family of monotone distribution functions.  For the exit time of a continuous path from an
open set this gives: if a path measure `P₀` is the image of `ν` by the time change `f ↦ f (c ·)`, then
`c = median(ν) / median(P₀)`; the ratio of medians is a measurable function of `(ν, P₀)`.
-/

open MeasureTheory MarkovProcess Set LatticeProb
open scoped NNReal ENNReal

namespace MatedCRT

/-- Scaling the argument of a distribution function by `c > 0` divides its median by `c`. -/
theorem medianOf_comp_mul (F : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    medianOf (fun x => F (c * x)) = medianOf F / c :=
  sInf_setOf_nonneg_comp_mul (fun x => (1 / 2 : ℝ≥0∞) ≤ F x) hc

/-- The median of a measurable family of monotone distribution functions is measurable (the
distribution functions need only be measurable at rational arguments). -/
theorem measurable_medianOf {Ω : Type*} [MeasurableSpace Ω] {F : Ω → ℝ → ℝ≥0∞}
    (hmono : ∀ ω, Monotone (F ω)) (hmeas : ∀ q : ℚ, Measurable fun ω => F ω q) :
    Measurable fun ω => medianOf (F ω) :=
  measurable_sInf_setOf_nonneg (P := fun ω m => (1 / 2 : ℝ≥0∞) ≤ F ω m)
    (fun ω _ _ hmm h => h.trans (hmono ω hmm))
    fun q => measurableSet_le measurable_const (hmeas q)

section ExitMedian

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]

/-- **Median of the exit time under a time change.**  Under the image of `ν` by `f ↦ f (c ·)`, the
median of the exit time from the open set `U` is the median under `ν` divided by `c`. -/
theorem medianOf_exitCdf_map_timeScalePath (U : Set α) (hU : IsOpen U) {c : ℝ≥0} (hc : c ≠ 0)
    (ν : Measure (ContinuousPath α)) :
    medianOf (exitCdf U (ν.map (timeScalePath c))) = medianOf (exitCdf U ν) / c := by
  have hfun : exitCdf U (ν.map (timeScalePath c)) = fun x => exitCdf U ν ((c : ℝ) * x) :=
    funext (exitCdf_map_timeScalePath U hU hc ν)
  rw [hfun]
  exact medianOf_comp_mul _ (by positivity)

/-- **The time-change constant is the ratio of the medians.**  If `P₀` is the image of `ν` by
`f ↦ f (c ·)` with `c ≠ 0` and the median of the exit time under `ν` is nonzero, then
`c = median(ν) / median(P₀)`. -/
theorem coe_eq_medianOf_div_of_map_timeScalePath (U : Set α) (hU : IsOpen U) {c : ℝ≥0} (hc : c ≠ 0)
    (ν P₀ : Measure (ContinuousPath α)) (hP₀ : P₀ = ν.map (timeScalePath c))
    (hν : medianOf (exitCdf U ν) ≠ 0) :
    (c : ℝ) = medianOf (exitCdf U ν) / medianOf (exitCdf U P₀) := by
  rw [hP₀, medianOf_exitCdf_map_timeScalePath U hU hc ν]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  field_simp

variable {Ω E : Type*} [MeasurableSpace Ω]

/-- The ratio `median(K g) / median(μ)` of the medians of the exit time from `U` under `K g` and `μ`. -/
noncomputable def exitMedianRatio (U : Set α) (K : E → Measure (ContinuousPath α))
    (p : E × Measure (ContinuousPath α)) : ℝ :=
  medianOf (exitCdf U (K p.1)) / medianOf (exitCdf U p.2)

/-- The median of the exit time under a measurable family of path measures is measurable. -/
theorem measurable_medianOf_exitCdf (U : Set α) (hU : IsOpen U)
    {μ : Ω → Measure (ContinuousPath α)} (hμ : Measurable μ) :
    Measurable fun ω => medianOf (exitCdf U (μ ω)) :=
  measurable_medianOf (fun ω => exitCdf_mono U (μ ω))
    fun q => (measurable_exitCdf U hU q).comp hμ

/-- The ratio of medians is a measurable function of `(g, μ)` when the kernel `K` is measurable. -/
theorem measurable_exitMedianRatio [MeasurableSpace E] (U : Set α) (hU : IsOpen U)
    {K : E → Measure (ContinuousPath α)} (hK : Measurable K) :
    Measurable (exitMedianRatio U K) :=
  (measurable_medianOf_exitCdf U hU (hK.comp measurable_fst)).div
    (measurable_medianOf_exitCdf U hU measurable_snd)

/-- **The time-change constant is a function of the data and the time-changed law.**  Let `P₀ ω` be
the image of `K (h ω)` by the time change `f ↦ f (c ω ·)`, almost surely, with `c ω ≠ 0` and
`K (h ω)` a probability measure for which the exit time from `U` is almost surely positive and finite.
Then `c ω = exitMedianRatio U K (h ω, P₀ ω)` almost surely. -/
theorem ae_coe_eq_exitMedianRatio (U : Set α) (hU : IsOpen U) {P : Measure Ω}
    {K : E → Measure (ContinuousPath α)} {h : Ω → E} {P₀ : Ω → Measure (ContinuousPath α)}
    {c : Ω → ℝ≥0} (hc0 : ∀ᵐ ω ∂P, c ω ≠ 0)
    (hlaw : ∀ᵐ ω ∂P, P₀ ω = (K (h ω)).map (timeScalePath (c ω)))
    (hprob : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h ω)))
    (hpos : ∀ᵐ ω ∂P, K (h ω) {f | ContinuousPath.exitTime U f = 0} = 0)
    (hfin : ∀ᵐ ω ∂P, K (h ω) {f | ContinuousPath.exitTime U f = ⊤} = 0) :
    ∀ᵐ ω ∂P, (c ω : ℝ) = exitMedianRatio U K (h ω, P₀ ω) := by
  filter_upwards [hc0, hlaw, hprob, hpos, hfin] with ω hc0 hlaw hprob hpos hfin
  exact coe_eq_medianOf_div_of_map_timeScalePath U hU hc0 _ _ hlaw
    (medianOf_exitCdf_pos U hU (K (h ω)) hpos hfin).ne'

/-- **The time-change constant is deterministic.**  Suppose `(h, P₀)` and `(h', P₀')` are independent
random elements of `E × Measure (ContinuousPath α)`, `K` is a measurable kernel, and almost surely
`P₀` (resp. `P₀'`) is the image of the probability measure `K h` (resp. `K h'`) by the time change
`f ↦ f (c ·)`, with the same `c ≠ 0` and with exit time from `U` almost surely positive and finite
under `K h` and `K h'`.  Then `c` is almost surely constant: it is almost surely a function of
`(h, P₀)` and a function of `(h', P₀')` (the ratio of the medians of the exit time). -/
theorem exists_ae_eq_const_coe_of_time_change [MeasurableSpace E] (U : Set α) (hU : IsOpen U)
    {P : Measure Ω} [IsProbabilityMeasure P] {K : E → Measure (ContinuousPath α)}
    (hK : Measurable K) {h h' : Ω → E} {P₀ P₀' : Ω → Measure (ContinuousPath α)} {c : Ω → ℝ≥0}
    (hh : Measurable h) (hh' : Measurable h') (hP₀ : Measurable P₀) (hP₀' : Measurable P₀')
    (hind : ProbabilityTheory.IndepFun (fun ω => (h ω, P₀ ω)) (fun ω => (h' ω, P₀' ω)) P)
    (hc0 : ∀ᵐ ω ∂P, c ω ≠ 0)
    (hlaw : ∀ᵐ ω ∂P, P₀ ω = (K (h ω)).map (timeScalePath (c ω)))
    (hlaw' : ∀ᵐ ω ∂P, P₀' ω = (K (h' ω)).map (timeScalePath (c ω)))
    (hprob : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h ω)))
    (hprob' : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h' ω)))
    (hpos : ∀ᵐ ω ∂P, K (h ω) {f | ContinuousPath.exitTime U f = 0} = 0)
    (hpos' : ∀ᵐ ω ∂P, K (h' ω) {f | ContinuousPath.exitTime U f = 0} = 0)
    (hfin : ∀ᵐ ω ∂P, K (h ω) {f | ContinuousPath.exitTime U f = ⊤} = 0)
    (hfin' : ∀ᵐ ω ∂P, K (h' ω) {f | ContinuousPath.exitTime U f = ⊤} = 0) :
    ∃ k : ℝ, ∀ᵐ ω ∂P, (c ω : ℝ) = k := by
  have hmeas := (measurable_exitMedianRatio U hU hK).aemeasurable (μ := P.map fun ω => (h ω, P₀ ω))
  have hmeas' := (measurable_exitMedianRatio U hU hK).aemeasurable
    (μ := P.map fun ω => (h' ω, P₀' ω))
  exact exists_ae_eq_const_of_ae_eq_comp_indep (hh.prodMk hP₀) (hh'.prodMk hP₀') hind
    (c := fun ω => (c ω : ℝ)) hmeas hmeas'
    (ae_coe_eq_exitMedianRatio U hU hc0 hlaw hprob hpos hfin)
    (ae_coe_eq_exitMedianRatio U hU hc0 hlaw' hprob' hpos' hfin')

end ExitMedian

end MatedCRT
