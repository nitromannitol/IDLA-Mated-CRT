import MatedCRT.Defs.KilledGMCClock
import MatedCRT.Proposed.PrestonAnalytic2008
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Clock

/-!
# All-starts clock set `𝒢` (lem:allstarts, env-steps.tex:380-446): definitions, Steps, transfer

Source: `lem:allstarts` (env-steps.tex:380-446) and the proof of `prop:clock` (env-steps.tex:449-487).

Lean names for the paper's objects:
* `posCircleExt a`: the continuous positive-circle field `a ∈ C((0,∞) × ℂ, ℝ)` (env-steps.tex:112), extended by `0`
  to radius `0` so that `lqgClockApprox` can read it; only the dyadic radii `dyadicScale n` are read.
* `clockApprox γ a n w`: the approximating clock `A_n(a,w,·)` of eq:clockapprox (`lqgClockApprox` at `dyadicScale n`).
* `pathDist`: the metric `d_𝒯` of env-steps.tex:398-400. `CauchyInProbability`: the condition eq:cauchy.
* `timeClockSet`: `𝒯_*` of eq:timeclock.
* `AdmitsAllStartClock γ a`, `allStartsSet γ`: `a ∈ 𝒢` iff one `F` satisfies eq:ucp and eq:timeclock for every start.
* `clockLimit γ nsel a z`: `J(a,z,·)` (env-steps.tex:402-407) for a subsequence choice `nsel`.
* `SelectedAllStartsRelation γ nsel a z`: `Q(a,z)`; `selectedAllStartsSet γ nsel`: `{a : ∀ z, Q(a,z)}`.

Proved here:
* `allStartsSet_isUniversallyMeasurable`: `𝒢` is universally measurable, from the Steps below, Polish `C(E,ℝ)`,
  and the staged Preston input (the complement is the projection of a Borel set, hence analytic).
* `ae_allStarts_of_map_eq`: `a₀ ∈ 𝒢` almost surely and equality in law give `aᵦ ∈ 𝒢` almost surely.
* `isLQGClock_congr_dyadic`: fields that agree on the dyadic radii have the same `IsLQGClock` (common-clock step).

Named Steps, NOT proved here (outstanding; each is a Prop hypothesis, never an axiom):
* `BorelSubsequenceSelectionStep`: the Borel recursive choice of `n_k(a,z)` (lem:allstarts proof, env-steps.tex:380-446);
* `BorelAllStartsRelationStep`: Borel measurability of `Q` on `C(E,ℝ) × ℂ`;
* `AllStartsCharacterizationStep`: `𝒢 = {a : ∀ z, Q(a,z)}`, both directions.
-/

open MatedCRT.EnvClock

namespace MatedCRT.AllStarts

open HarmonicBalls MeasureTheory MarkovProcess Filter
open scoped ENNReal NNReal

/-- The positive-circle index set `E = (0,∞) × ℂ` (env-steps.tex:112). -/
abbrev PosCircle : Type := Set.Ioi (0 : ℝ) × ℂ

/-- `H = C(E,ℝ)` with the compact-open topology (env-steps.tex:380). -/
abbrev CircleFns : Type := C(PosCircle, ℝ)

/-- Zero extension of a continuous circle function to all radii; only the dyadic radii are read. -/
noncomputable def posCircleExt (a : CircleFns) : ℝ → ℂ → ℝ :=
  fun r z => if h : 0 < r then a (⟨r, h⟩, z) else 0

/-- `A_n(a,w,·)` of eq:clockapprox: `lqgClockApprox` at the dyadic scale `dyadicScale n`. -/
noncomputable def clockApprox (γ : ℝ) (a : CircleFns) (n : ℕ) (w : ContinuousPath ℂ) : ℝ≥0 → ℝ :=
  lqgClockApprox γ (posCircleExt a) (dyadicScale n) w

/-- The metric `d_𝒯` of env-steps.tex:398-400 on `C([0,∞),ℝ)`: `∑_{j≥1} 2^{-j} min {1, sup_{t≤j} |f(t) - g(t)|}`,
indexed here by `j ↦ j+1`. -/
noncomputable def pathDist (f g : ℝ≥0 → ℝ) : ℝ :=
  ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * min 1 (⨆ t ∈ Set.Icc (0 : ℝ≥0) ((j + 1 : ℕ) : ℝ≥0), |f t - g t|)

/-- The condition eq:cauchy: for every `k ≥ 1` there is `N` with `W_z {d_𝒯(A_n, A_m) > 2^{-k}} < 2^{-k}` for `n, m ≥ N`. -/
def CauchyInProbability (γ : ℝ) (a : CircleFns) (z : ℂ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
    planarBrownianMotion z {w | (1 / 2 : ℝ) ^ k < pathDist (clockApprox γ a n w) (clockApprox γ a m w)}
      < ENNReal.ofReal ((1 / 2 : ℝ) ^ k)

/-- `𝒯_*` of eq:timeclock: `F 0 = 0`, `F` continuous and strictly increasing, `F t → ∞` (`IsTimeChangeClock`). -/
def timeClockSet : Set (ℝ≥0 → ℝ) := {f | IsTimeChangeClock f}

/-- lem:allstarts: `a ∈ 𝒢` iff some single `F (w,t)` satisfies eq:ucp (`IsLQGClock`, with `hε = posCircleExt a`)
and eq:timeclock for every starting point `z`; eq:timeclock holds `W_z`-almost surely. -/
def AdmitsAllStartClock (γ : ℝ) (a : CircleFns) : Prop :=
  ∃ F : ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ z : ℂ,
    IsLQGClock planarBrownianMotion γ (posCircleExt a) z F ∧
      ∀ᵐ B ∂planarBrownianMotion z, IsTimeChangeClock (F B)

/-- The set `𝒢` of lem:allstarts (env-steps.tex:380-446). -/
def allStartsSet (γ : ℝ) : Set CircleFns := {a | AdmitsAllStartClock γ a}

open Classical in
/-- `J(a,z,w)` (env-steps.tex:402-407) for a subsequence choice `nsel a z k = n_k(a,z)`: the locally uniform limit of
`A_{n_k}(a,·,w)` when it exists, and `t ↦ t` otherwise. -/
noncomputable def clockLimit (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) (a : CircleFns) (z : ℂ)
    (w : ContinuousPath ℂ) : ℝ≥0 → ℝ :=
  if h : ∃ f : ℝ≥0 → ℝ, TendstoLocallyUniformly (fun k => clockApprox γ a (nsel a z k) w) f atTop then
    h.choose
  else fun t => (t : ℝ)

/-- `Q(a,z)` (lem:allstarts proof, env-steps.tex:380-446): eq:cauchy holds, and `W_z {J(a,z,w) ∈ 𝒯_*} = 1`. -/
def SelectedAllStartsRelation (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) (a : CircleFns) (z : ℂ) : Prop :=
  CauchyInProbability γ a z ∧ planarBrownianMotion z {w | clockLimit γ nsel a z w ∈ timeClockSet} = 1

/-- `{a : ∀ z, Q(a,z)}` for the subsequence choice `nsel`. -/
def selectedAllStartsSet (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) : Set CircleFns :=
  {a | ∀ z : ℂ, SelectedAllStartsRelation γ nsel a z}

/-- **Named Step `BorelSubsequenceSelectionStep` (outstanding, not proved).** The recursive choice of the
lem:allstarts proof: each `(a,z) ↦ n_k(a,z)` is Borel, `k ↦ n_k(a,z)` is strictly increasing, and when eq:cauchy
holds at `(a,z)` the chosen indices satisfy the displayed tail bound for every `k ≥ 1`. -/
def BorelSubsequenceSelectionStep [MeasurableSpace CircleFns] (γ : ℝ)
    (nsel : CircleFns → ℂ → ℕ → ℕ) : Prop :=
  (∀ k : ℕ, Measurable fun p : CircleFns × ℂ => nsel p.1 p.2 k) ∧
  (∀ (a : CircleFns) (z : ℂ), StrictMono (nsel a z)) ∧
  (∀ (a : CircleFns) (z : ℂ), CauchyInProbability γ a z → ∀ k : ℕ, 1 ≤ k →
    ∀ n m : ℕ, nsel a z k ≤ n → nsel a z k ≤ m →
      planarBrownianMotion z {w | (1 / 2 : ℝ) ^ k < pathDist (clockApprox γ a n w) (clockApprox γ a m w)}
        < ENNReal.ofReal ((1 / 2 : ℝ) ^ k))

/-- **Named Step `BorelAllStartsRelationStep` (outstanding, not proved).** `Q` is a Borel subset of
`C(E,ℝ) × ℂ`: the `W_z`-probabilities of eq:cauchy and of `{J ∈ 𝒯_*}` are Borel in `(a,z)`. -/
def BorelAllStartsRelationStep [MeasurableSpace CircleFns] (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) : Prop :=
  MeasurableSet {p : CircleFns × ℂ | SelectedAllStartsRelation γ nsel p.1 p.2}

/-- **Named Step `AllStartsCharacterizationStep` (outstanding, not proved).** Both directions of lem:allstarts:
`F = J(a, w(0), ·)` witnesses `a ∈ 𝒢` when `Q(a,·)` holds for every start, and conversely any `F` witnessing
`a ∈ 𝒢` forces eq:cauchy and `J = F` `W_z`-a.s. (uniqueness of limits in outer probability, env-steps.tex:380-446). -/
def AllStartsCharacterizationStep (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ) : Prop :=
  allStartsSet γ = selectedAllStartsSet γ nsel

/-- `𝒢` is universally measurable (env-steps.tex:380-446: complement = projection of a Borel subset of `H × ℂ`,
hence analytic; analytic sets are universally measurable, staged as `PrestonAnalyticUniversallyMeasurableStmt`).
Hypotheses: the characterization Step, the Borel Step, Polish `C(E,ℝ)`, and the Preston input. -/
theorem allStartsSet_isUniversallyMeasurable [MeasurableSpace CircleFns] [BorelSpace CircleFns]
    [PolishSpace CircleFns] (hPreston : PrestonAnalyticUniversallyMeasurableStmt) (γ : ℝ)
    (nsel : CircleFns → ℂ → ℕ → ℕ) (hchar : AllStartsCharacterizationStep γ nsel)
    (hBorel : BorelAllStartsRelationStep γ nsel) :
    IsUniversallyMeasurableSet (allStartsSet γ) := by
  have hchar' : allStartsSet γ = selectedAllStartsSet γ nsel := hchar
  have hmeas' : MeasurableSet {p : CircleFns × ℂ | SelectedAllStartsRelation γ nsel p.1 p.2} := hBorel
  have hmeas : MeasurableSet {p : CircleFns × ℂ | ¬ SelectedAllStartsRelation γ nsel p.1 p.2} :=
    hmeas'.compl
  have hcompl : (allStartsSet γ)ᶜ =
      Prod.fst '' {p : CircleFns × ℂ | ¬ SelectedAllStartsRelation γ nsel p.1 p.2} := by
    rw [hchar']
    ext a
    constructor
    · intro h
      have h' : ¬ ∀ z : ℂ, SelectedAllStartsRelation γ nsel a z := h
      obtain ⟨z, hz⟩ := not_forall.mp h'
      exact ⟨(a, z), hz, rfl⟩
    · rintro ⟨p, hp, rfl⟩ hall
      exact hp (hall p.2)
  have hanalytic : AnalyticSet (allStartsSet γ)ᶜ := by
    rw [hcompl]
    exact hmeas.analyticSet.image_of_continuous continuous_fst
  unfold IsUniversallyMeasurableSet
  intro ν hν
  have h := (hPreston CircleFns (allStartsSet γ)ᶜ hanalytic ν hν).compl
  rwa [compl_compl] at h

/-- The almost-sure membership `a₀ ∈ 𝒢` transfers to `aᵦ` under equality in law (proof of `prop:clock`,
env-steps.tex:449-487: the Borel null sandwich of the universally measurable `𝒢`). -/
theorem ae_allStarts_of_map_eq [MeasurableSpace CircleFns] [BorelSpace CircleFns] [PolishSpace CircleFns]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (hPreston : PrestonAnalyticUniversallyMeasurableStmt) (γ : ℝ) (nsel : CircleFns → ℂ → ℕ → ℕ)
    (hchar : AllStartsCharacterizationStep γ nsel) (hBorel : BorelAllStartsRelationStep γ nsel)
    {a₀ aᵦ : Ω → CircleFns} (ha₀ : Measurable a₀) (haᵦ : Measurable aᵦ)
    (hlaw : P.map a₀ = P.map aᵦ) (hall : ∀ᵐ ω ∂P, a₀ ω ∈ allStartsSet γ) :
    ∀ᵐ ω ∂P, aᵦ ω ∈ allStartsSet γ :=
  ae_mem_of_map_eq_of_univMeas ha₀ haᵦ hlaw
    (allStartsSet_isUniversallyMeasurable hPreston γ nsel hchar hBorel) hall

/-- Fields that agree on the dyadic radii `dyadicScale k` (in particular on `E`, env-steps.tex:469-471) have the same
`IsLQGClock`: the approximations `lqgClockApprox` read only these values. -/
theorem isLQGClock_congr_dyadic {Q : ProbabilityTheory.Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {g g' : ℝ → ℂ → ℝ}
    (hg : ∀ k : ℕ, ∀ z : ℂ, g (dyadicScale k) z = g' (dyadicScale k) z) {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} :
    IsLQGClock Q γ g x F ↔ IsLQGClock Q γ g' x F := by
  have happ : ∀ (k : ℕ) (b : ContinuousPath ℂ) (t : ℝ≥0),
      lqgClockApprox γ g (dyadicScale k) b t = lqgClockApprox γ g' (dyadicScale k) b t := by
    intro k b t
    unfold lqgClockApprox
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hg k]
  unfold IsLQGClock
  simp only [happ, iff_self]

end MatedCRT.AllStarts
