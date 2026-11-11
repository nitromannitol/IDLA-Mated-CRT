import Mathlib
import MatedCRT.FirstPass.S6h.Core
import MatedCRT.FirstPass.S6j
import MatedCRT.FirstPass.S6j.FiniteExit
import MatedCRT.FirstPass.S6j.PerState
import MatedCRT.FirstPass.S6h.Successive
import MatedCRT.FirstPass.S6e.RadiusSelect
import MatedCRT.FirstPass.S6e.Cutoff
import MatedCRT.FirstPass.S4S6c.Uniform68Round

/-!
# The concrete test schedule of Lemma 6.8

Write-up C1-C3 and bridge argument §3, Steps B-F: the grid centre `z_j = Q_δ(η(X_{T_j}))`, the first-good radius
`R_j = R_{z_j}` (A5, `Lemma68Radius.firstGoodRadius`, default `δ`), the window `W(y) = I(B_{2R}(z))` at the state `y`, the
successive exit times `T_{j+1} = nextExit W T_j` (`cfgExit`, equal to `Lemma68Successive.exitSchedule` by
`cfgExit_eq_exitSchedule`), the count `N = ⌊r/(100 s)⌋`, `s = √δ`.

Proved here: the structural fields of `TestSchedule.Valid` (monotone σ-algebras `F_{T_j}`, measurability of the test events
`G_j = testHit`, `G_j ∈ F_{T_{j+1}}`, radius bounds, the count bound), the finiteness of the windows from properness of `η`,
and `hstep` from `S6j.hstep_of_schedule`, which discharges the a.s. finiteness of the exits.
Named inputs (NEW steps, not proved here): `OuterTestBound` (write-up C4, per-state outer bound; `S6j/PerState.lean`)
and `ConcreteC12` (write-up C12; `S6m.lean`). Environment inputs: `η` continuous and proper, local finiteness of the
walk law. Cutoff: `r ^ ζ ≤ 1/1000`, from `R ≤ 1000^(-1/ζ)` (write-up D1).
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MatedCRT
namespace Lemma68Concrete

open Lemma68Config Lemma68Successive Lemma68Radius Lemma68Scales S6j WalkPotential

/-! ### σ-algebra facts for the walk history -/

lemma histSigma_mono {k n : ℕ} (h : k ≤ n) : histSigma k ≤ histSigma n := by
  have hg : Measurable (fun w : Fin (n + 1) → ℤ => fun i : Fin (k + 1) => w (Fin.castLE (by omega) i)) := by
    fun_prop
  have hcomp : pathHist k = (fun w : Fin (n + 1) → ℤ => fun i : Fin (k + 1) => w (Fin.castLE (by omega) i)) ∘
      pathHist n := rfl
  unfold histSigma
  rw [hcomp, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

lemma measurableSet_le_histSigma {τ : (ℕ → ℤ) → ℕ∞} (hτ : IsWalkRandomTime τ) (n : ℕ) :
    MeasurableSet[histSigma n] {x | τ x ≤ (n : ℕ∞)} := by
  have hset : {x | τ x ≤ (n : ℕ∞)} = ⋃ l ∈ Finset.range (n + 1), {x | τ x = (l : ℕ∞)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · intro hx
      obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top n) hx)
      refine ⟨l, ?_, hl.symm⟩
      have hle : (l : ℕ∞) ≤ n := by rw [hl]; exact hx
      exact Nat.lt_succ_of_le (ENat.natCast_le_natCast.1 hle)
    · rintro ⟨l, hl, hx⟩
      rw [hx]
      exact ENat.natCast_le_natCast.2 (Nat.lt_succ_iff.1 hl)
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun l hl => ?_
  exact histSigma_mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)) _ (hτ l)

lemma measurableSet_coord_histSigma (n : ℕ) (A : Set ℤ) :
    MeasurableSet[histSigma n] {x : ℕ → ℤ | x n ∈ A} := by
  refine MeasurableSpace.measurableSet_comap.2
    ⟨(fun w : Fin (n + 1) → ℤ => w (Fin.last n)) ⁻¹' A, ?_, rfl⟩
  exact (measurable_pi_apply (Fin.last n)) (Set.to_countable A).measurableSet

/-- The σ-algebra `F_τ` is monotone in the random time (pointwise order `τ ≤ τ'`). -/
lemma stoppedSigma_mono {τ τ' : (ℕ → ℤ) → ℕ∞} (hτ : IsWalkRandomTime τ) (hτ' : IsWalkRandomTime τ')
    (h : ∀ x, τ x ≤ τ' x) : stoppedSigma τ hτ ≤ stoppedSigma τ' hτ' := by
  intro S hS
  obtain ⟨hSm, hSk⟩ := hS
  refine ⟨hSm, fun k => ?_⟩
  have hset : S ∩ {x | τ' x = (k : ℕ∞)} =
      ⋃ l ∈ Finset.range (k + 1), (S ∩ {x | τ x = (l : ℕ∞)}) ∩ {x | τ' x = (k : ℕ∞)} := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨hxS, hx'⟩
      have hle : τ x ≤ (k : ℕ∞) := by rw [← hx']; exact h x
      obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top k) hle)
      refine ⟨l, ?_, ⟨hxS, hl.symm⟩, hx'⟩
      have hlk : (l : ℕ∞) ≤ k := by rw [hl]; exact hle
      exact Nat.lt_succ_of_le (ENat.natCast_le_natCast.1 hlk)
    · rintro ⟨l, _, ⟨hxS, _⟩, hx'⟩
      exact ⟨hxS, hx'⟩
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun l hl => ?_
  refine MeasurableSet.inter ?_ (hτ' k)
  exact histSigma_mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)) _ (hSk l)

/-! ### Measurability of the test events -/

/-- `G_j = testHit A T j` is measurable for the product σ-algebra when the `T j` are walk random times. -/
lemma measurableSet_testHit (T : ℕ → (ℕ → ℤ) → ℕ∞) (hT : ∀ j, IsWalkRandomTime (T j)) (A : Set ℤ) (j : ℕ) :
    MeasurableSet (Lemma68Config.testHit A T j) := by
  have hset : Lemma68Config.testHit A T j =
      ⋃ n : ℕ, ({x | T j x ≤ (n : ℕ∞)} ∩ {x | T (j + 1) x ≤ (n : ℕ∞)}ᶜ) ∩ {x : ℕ → ℤ | x n ∈ Aᶜ} := by
    ext x
    simp only [Lemma68Config.testHit, mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, not_le]
    constructor
    · rintro ⟨n, h1, h2, h3⟩
      exact ⟨n, ⟨h1, h2⟩, h3⟩
    · rintro ⟨n, ⟨h1, h2⟩, h3⟩
      exact ⟨n, h1, h2, h3⟩
  rw [hset]
  refine MeasurableSet.iUnion fun n => MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · exact histSigma_le _ _ (measurableSet_le_histSigma (hT j) n)
  · exact (histSigma_le _ _ (measurableSet_le_histSigma (hT (j + 1)) n)).compl
  · exact histSigma_le _ _ (measurableSet_coord_histSigma n Aᶜ)

/-- `G_j ∩ {T_{j+1} = k}` is `F_k`-measurable: on `{T_{j+1} = k}` the event `G_j` only looks at times `< k`. -/
lemma testHit_inter_histSigma (T : ℕ → (ℕ → ℤ) → ℕ∞) (hT : ∀ j, IsWalkRandomTime (T j)) (A : Set ℤ)
    (j k : ℕ) :
    MeasurableSet[histSigma k] (Lemma68Config.testHit A T j ∩ {x | T (j + 1) x = (k : ℕ∞)}) := by
  have hset : Lemma68Config.testHit A T j ∩ {x | T (j + 1) x = (k : ℕ∞)} =
      (⋃ n ∈ Finset.range k, {x | T j x ≤ (n : ℕ∞)} ∩ {x : ℕ → ℤ | x n ∈ Aᶜ}) ∩
        {x | T (j + 1) x = (k : ℕ∞)} := by
    ext x
    simp only [Lemma68Config.testHit, mem_inter_iff, mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨⟨n, h1, h2, h3⟩, h4⟩
      have hnk : n < k := by
        rw [h4] at h2
        exact ENat.natCast_lt_natCast.1 h2
      exact ⟨⟨n, hnk, h1, h3⟩, h4⟩
    · rintro ⟨⟨n, hnk, h1, h3⟩, h4⟩
      refine ⟨⟨n, h1, ?_, h3⟩, h4⟩
      rw [h4]
      exact ENat.natCast_lt_natCast.2 hnk
  rw [hset]
  refine MeasurableSet.inter ?_ (hT (j + 1) k)
  refine Finset.measurableSet_biUnion _ fun n hn => MeasurableSet.inter ?_ ?_
  · exact histSigma_mono (Nat.le_of_lt (Finset.mem_range.1 hn)) _ (measurableSet_le_histSigma (hT j) n)
  · exact histSigma_mono (Nat.le_of_lt (Finset.mem_range.1 hn)) _ (measurableSet_coord_histSigma n Aᶜ)

/-! ### The test event as a walk test event after `T_j` -/

/-- Arithmetic of the successive exit: `n < k + v` with `k ≤ n` gives `n - k < v` in `ℕ∞`. -/
lemma natCast_sub_lt_of_lt_add {k n : ℕ} {v : ℕ∞} (hkn : k ≤ n) (h : (n : ℕ∞) < (k : ℕ∞) + v) :
    ((n - k : ℕ) : ℕ∞) < v := by
  induction v using ENat.recTopCoe with
  | top => exact ENat.natCast_lt_top _
  | coe l =>
    have h2 : ((n : ℕ) : ℕ∞) < ((k + l : ℕ) : ℕ∞) := by rw [Nat.cast_add]; exact h
    have h3 : n < k + l := ENat.natCast_lt_natCast.1 h2
    exact ENat.natCast_lt_natCast.2 (by omega)

/-- With the successive exit times of a constant window, the test event `G_j` is the walk test event after `T_j`
(bridge argument (4); `nextExit` unfolds to `T_j + vExitTime (W (X_{T_j})) (shift)`). -/
lemma testHit_eq_walkTestEvent (W : ℤ → Set ℤ) (A : Set ℤ) (j : ℕ) :
    walkTestEvent (exitSchedule W j) (fun y => testEvent W A y) =
      Lemma68Config.testHit A (exitSchedule W) j := by
  ext x
  constructor
  · rintro ⟨k, hk, i, hi, hA⟩
    refine ⟨k + i, ?_, ?_, ?_⟩
    · rw [hk]
      exact ENat.natCast_le_natCast.2 (Nat.le_add_right k i)
    · show ((k + i : ℕ) : ℕ∞) < SuccessiveExitStop.nextExit W (exitSchedule W j) x
      unfold SuccessiveExitStop.nextExit
      rw [hk]
      simp only [ENat.recTopCoe_natCast]
      push_cast
      exact (ENat.add_lt_add_iff_left (ENat.natCast_ne_top k)).2 hi
    · exact hA
  · rintro ⟨n, hn1, hn2, hA⟩
    have hne : exitSchedule W j x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hn1
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
    rw [← hk] at hn1
    have hkn : k ≤ n := ENat.natCast_le_natCast.1 hn1
    refine ⟨k, hk.symm, n - k, ?_, ?_⟩
    · have hn2' : (n : ℕ∞) < SuccessiveExitStop.nextExit W (exitSchedule W j) x := hn2
      unfold SuccessiveExitStop.nextExit at hn2'
      rw [← hk] at hn2'
      simp only [ENat.recTopCoe_natCast] at hn2'
      exact natCast_sub_lt_of_lt_add hkn hn2'
    · have hkn' : k + (n - k) = n := by omega
      show x (k + (n - k)) ∉ A
      rw [hkn']
      exact hA

/-! ### The concrete data C1-C3 -/

/-- The grid centre `z_j = Q_δ(η(X_{T_j}))` of write-up C1, with mesh `g_δ = δ/100` and `δ = Δ(p, r)`. -/
noncomputable def cfgCentre (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (y : ℤ) : ℂ :=
  MatedCRT.Uniform68Round.gridRound (Delta p r / 100) (vertexPoint ε η y)

/-- The first-good radius `R_z` of write-up C1 (A5, default `δ`). -/
noncomputable def cfgRadius (p r : ℝ) (good : ℂ → ℕ → Prop) (z : ℂ) : ℝ :=
  firstGoodRadius (Delta p r) (cand (Delta p r)) (numCand (Delta p r)) (good z)

/-- The radius `R_j = R_{z_j}` at the state `y = X_{T_j}`. -/
noncomputable def cfgStateRadius (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (good : ℂ → ℕ → Prop) (y : ℤ) : ℝ :=
  cfgRadius p r good (cfgCentre ε η p r y)

/-- The window `W(y) = I(B_{2R}(z))` of write-up C3, a finite set of cell vertices at the state `y`. -/
noncomputable def cfgWindow (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (good : ℂ → ℕ → Prop) (y : ℤ) : Set ℤ :=
  interiorCellVertices ε η
    (Metric.ball (cfgCentre ε η p r y) (2 * cfgStateRadius ε η p r good y))

/-- The count `N = ⌊r/(100 s)⌋` with `s = √δ` (write-up C1, Step B of the bridge argument). -/
noncomputable def cfgCount (p r : ℝ) : ℕ :=
  ⌊r / (100 * Real.sqrt (Delta p r))⌋₊

/-- The successive exit times `T_j` of write-up C3, `T_{j+1} = nextExit (W) T_j` with the constant window `W = cfgWindow`
(the successive exit schedule `S6j.nextExitSchedule`; `cfgExit_eq_exitSchedule` identifies it with `exitSchedule`). -/
noncomputable def cfgExit (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (good : ℂ → ℕ → Prop) : ℕ → (ℕ → ℤ) → ℕ∞ :=
  S6j.nextExitSchedule (fun _ => cfgWindow ε η p r good)

lemma cfgExit_eq_exitSchedule (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (good : ℂ → ℕ → Prop) :
    cfgExit ε η p r good = exitSchedule (cfgWindow ε η p r good) := by
  have key : ∀ j : ℕ, S6j.nextExitSchedule (fun _ => cfgWindow ε η p r good) j =
      exitSchedule (cfgWindow ε η p r good) j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      show SuccessiveExitStop.nextExit (cfgWindow ε η p r good)
          (S6j.nextExitSchedule (fun _ => cfgWindow ε η p r good) j) =
        SuccessiveExitStop.nextExit (cfgWindow ε η p r good) (exitSchedule (cfgWindow ε η p r good) j)
      rw [ih]
  funext j
  exact key j

lemma cfgExit_isWalkRandomTime (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (good : ℂ → ℕ → Prop) (j : ℕ) :
    IsWalkRandomTime (cfgExit ε η p r good j) :=
  S6j.isWalkRandomTime_nextExitSchedule (fun _ => cfgWindow ε η p r good) j

/-- The windows are finite: `I(B) ⊆ cellVertices B`, the closed ball is compact, and `η` is proper
(`cellVertices_finite_of_isCompact`). -/
lemma cfgWindow_finite {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Filter.Tendsto η (Filter.cocompact ℝ) (Filter.cocompact ℂ)) (hε : 0 < ε) (p r : ℝ)
    (good : ℂ → ℕ → Prop) (y : ℤ) : (cfgWindow ε η p r good y).Finite := by
  refine (cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall (cfgCentre ε η p r y)
    (2 * cfgStateRadius ε η p r good y))).subset ?_
  intro k hk
  obtain ⟨z, hz⟩ := hk.1
  exact ⟨z, hz.1, Metric.ball_subset_closedBall hz.2⟩

/-- The concrete test schedule (C1-C3): `T = cfgExit`, `R_j = cfgStateRadius (X_{T_j})`, `m_j = F_{T_j}`. -/
noncomputable def cfgSchedule (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (good : ℂ → ℕ → Prop) : TestSchedule where
  N := cfgCount p r
  T := cfgExit ε η p r good
  R := fun j x => cfgStateRadius ε η p r good (x ((cfgExit ε η p r good j x).toNat))
  m := fun j => stoppedSigma (cfgExit ε η p r good j) (cfgExit_isWalkRandomTime ε η p r good j)

lemma cfgRadius_bounds {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (good : ℂ → ℕ → Prop) (z : ℂ) :
    0 < cfgRadius p r good z ∧ cfgRadius p r good z ≤ 1 ∧ r ^ p / 2 < cfgRadius p r good z :=
  selectable_delta_bounds hp hr0 hr1 (firstGood_cand_mem (delta_pos p r) (good z))

lemma cfgCount_lower {p r ζ : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (hpζ : p = 2 * ζ + 2)
    (hrζ : r ^ ζ ≤ 1 / 1000) : r ^ (-ζ) / 200 ≤ (cfgCount p r : ℝ) := by
  have hΔ : 0 < Delta p r := delta_pos p r
  have hs : 0 < Real.sqrt (Delta p r) := Real.sqrt_pos.2 hΔ
  have hpow : r ^ p = (r ^ (1 + ζ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    congr 1
    rw [hpζ]
    push_cast
    ring
  have hsζ : Real.sqrt (Delta p r) ≤ r ^ (1 + ζ) := by
    have h1 : Delta p r ≤ r ^ p := Delta_le_rpow hp hr0 hr1
    calc Real.sqrt (Delta p r) ≤ Real.sqrt ((r ^ (1 + ζ)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [← hpow]
          exact h1
      _ = r ^ (1 + ζ) := Real.sqrt_sq (Real.rpow_nonneg hr0.le _)
  have hsr : Real.sqrt (Delta p r) ≤ r / 1000 := by
    have h3 : r ^ (1 + ζ) = r * r ^ ζ := by rw [Real.rpow_add hr0, Real.rpow_one]
    have h2 : r * r ^ ζ ≤ r * (1 / 1000) := mul_le_mul_of_nonneg_left hrζ hr0.le
    linarith
  exact Lemma68Cutoff.N_lower_bound hr0 hs hsr hsζ

/-! ### The concrete `TestSchedule.Valid` -/

/-- The per-state outer test bound of write-up C4 for the concrete schedule, in the form taken by
`S6j.hstep_of_schedule` (input `hpt`): from `X_{T_j}`, the walk stays in `A` until it leaves the window `I(B_{2R}(z))`
with probability at most `1 - q/(1+log(1/R))²`. A NEW step (C4), named input; its proof is in `S6j/PerState.lean`. -/
def OuterTestBound (m : ℤ → ℤ → ℕ) (a : ℤ) (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (good : ℂ → ℕ → Prop) (A : Set ℤ)
    (qStar : ℝ) : Prop :=
  ∀ j, ∀ᵐ x ∂srwLaw m a, x ∈ Lemma68Config.testFail A (cfgExit ε η p r good) j →
    cfgExit ε η p r good j x < ⊤ →
    srwLaw m (x (cfgExit ε η p r good j x).toNat)
        (TestBound68.stayIn (cfgWindow ε η p r good) A (x (cfgExit ε η p r good j x).toNat)) ≤
      ENNReal.ofReal (1 - qStar / (1 + Real.log (1 / cfgStateRadius ε η p r good
        (x (cfgExit ε η p r good j x).toNat))) ^ 2)

/-- The containment of write-up C12 for the concrete schedule, in the form of `TestSchedule.Valid.hC12`: `T_N < τ_U`
almost surely. A NEW step (C12), named input; its proof is in `S6m.lean`. -/
def ConcreteC12 (m : ℤ → ℤ → ℕ) (a : ℤ) (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (good : ℂ → ℕ → Prop) (U : Set ℤ) : Prop :=
  ∀ᵐ x ∂srwLaw m a, cfgExit ε η p r good (cfgCount p r) x < vExitTime U x

/-- The per-state inputs of write-up C4 for the concrete schedule, in the form of `S6j.hpt_of_state` with the centres
`Z = cfgCentre`, the radii `Rs = cfgStateRadius` and a good-state predicate `Good` (NEW inputs, named). `hloc`: the
local printed test bound at the middle sphere of `B_R(z)`; `hdy`, `hdiam`: the cell geometry; `hS2`: the walk from
`X_{T_j}` hits the middle sphere before leaving `I(B_{2R}(z))` (write-up S2); `hgood`: the state `X_{T_j}` is good
almost surely (the first-good radius selection). `Good` is existentially quantified in `configuration_le_pow_concrete`. -/
structure StateTestInputs (m : ℤ → ℤ → ℕ) (a : ℤ) (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (good : ℂ → ℕ → Prop) (A : Set ℤ)
    (qStar c0 : ℝ) (Good : ℤ → Prop) : Prop where
  hloc : ∀ y, Good y → ∀ v ∈ middleVertices ε η (cfgCentre ε η p r y) (cfgStateRadius ε η p r good y),
    srwLaw m v (TestBound68.stayIn
      (fun u => interiorCellVertices ε η (Metric.ball (vertexPoint ε η u) (cfgStateRadius ε η p r good y / 4))) A v)
      ≤ ENNReal.ofReal (1 - min qStar 1 / (1 + Real.log (1 / cfgStateRadius ε η p r good y)) ^ 2)
  hdy : ∀ y, Good y → ∀ v ∈ middleVertices ε η (cfgCentre ε η p r y) (cfgStateRadius ε η p r good y),
    Metric.diam (cell ε η v) ≤ cfgStateRadius ε η p r good y / 100
  hdiam : ∀ y, Good y → ∀ v ∈ middleVertices ε η (cfgCentre ε η p r y) (cfgStateRadius ε η p r good y), ∀ k : ℤ,
    (cell ε η k ∩ Metric.ball (vertexPoint ε η v) (cfgStateRadius ε η p r good y / 4)).Nonempty →
      Metric.diam (cell ε η k) ≤ c0 * cfgStateRadius ε η p r good y
  hS2 : ∀ y, Good y → ∀ᵐ x ∂srwLaw m y,
    vHitTime (middleVertices ε η (cfgCentre ε η p r y) (cfgStateRadius ε η p r good y)) x <
      vExitTime (interiorCellVertices ε η (Metric.ball (cfgCentre ε η p r y) (2 * cfgStateRadius ε η p r good y))) x
  hgood : ∀ j, ∀ᵐ x ∂srwLaw m a, cfgExit ε η p r good j x < ⊤ → Good (x (cfgExit ε η p r good j x).toNat)

/-- The per-state outer bound of write-up C4 for the concrete schedule, from its per-state inputs `StateTestInputs`
(`S6j.hpt_of_state` at `q0 = qStar`; `min qStar 1 = qStar` by `qStar ≤ 1`). The case `qStar = 0` is trivial. -/
theorem outerTestBound_of_state (m : ℤ → ℤ → ℕ) (a : ℤ) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η) {p r : ℝ}
    (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (good : ℂ → ℕ → Prop) (A : Set ℤ) {qStar c0 : ℝ} (hε : 0 < ε)
    (hc0 : c0 < 1 / 8) (hq0 : 0 ≤ qStar) (hq1 : qStar ≤ 1) (Good : ℤ → Prop)
    (h : StateTestInputs m a ε η p r good A qStar c0 Good) :
    OuterTestBound m a ε η p r good A qStar := by
  rcases hq0.eq_or_lt with hz | hpos
  · intro j
    filter_upwards with x
    intro _ _
    subst hz
    simp only [zero_div, sub_zero, ENNReal.ofReal_one]
    exact prob_le_one
  · have hmin : min qStar 1 = qStar := min_eq_left hq1
    intro j
    have key := S6j.hpt_of_state m a η hη A (cfgExit ε η p r good) (cfgCentre ε η p r)
      (cfgStateRadius ε η p r good) Good hε hc0 hpos (fun y => (cfgRadius_bounds hp hr0 hr1 good _).1)
      (fun y => (cfgRadius_bounds hp hr0 hr1 good _).2.1) h.hloc h.hdy h.hdiam h.hS2 h.hgood j
    filter_upwards [key] with x hx
    intro _ hT
    have h2 := hx hT
    rw [hmin] at h2
    exact h2

/-- **Concrete configuration schedule (Lemma 6.8, bridge argument §3 Steps B-F).** `TestSchedule.Valid` holds for the concrete
schedule `cfgSchedule` on `ν = srwLaw m a`, from the environment inputs `hproper` (η continuous and proper), `hlf`, `hcons`
(local finiteness of the walk law), the per-state bound `hpt` (`OuterTestBound`, write-up C4) and the containment `hC12`
(`ConcreteC12`, write-up C12). The almost-sure finiteness of the exits and `hstep` (C15) are proved. -/
theorem cfgSchedule_valid (ε : ℝ) (η : ℝ → ℂ) {p r ζ qStar : ℝ} (good : ℂ → ℕ → Prop) (m : ℤ → ℤ → ℕ) (a : ℤ)
    (A U : Set ℤ) (hε : 0 < ε) (hη : Continuous η)
    (hproper : Filter.Tendsto η (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (hpζ : p = 2 * ζ + 2) (hrζ : r ^ ζ ≤ 1 / 1000)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hq0 : 0 ≤ qStar) (hq1 : qStar ≤ 1)
    (hpt : OuterTestBound m a ε η p r good A qStar)
    (hC12 : ConcreteC12 m a ε η p r good U) :
    TestSchedule.Valid (cfgSchedule ε η p r good) (srwLaw m a) U A r p qStar ζ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hC12, ?_⟩
  · refine monotone_nat_of_le_succ fun j => stoppedSigma_mono (cfgExit_isWalkRandomTime ε η p r good j)
      (cfgExit_isWalkRandomTime ε η p r good (j + 1)) fun x => ?_
    show cfgExit ε η p r good j x ≤ cfgExit ε η p r good (j + 1) x
    rw [cfgExit_eq_exitSchedule]
    exact exitSchedule_le_succ _ j x
  · exact fun j => stoppedSigma_le _ (cfgExit_isWalkRandomTime ε η p r good j)
  · intro x j
    show cfgExit ε η p r good j x ≤ cfgExit ε η p r good (j + 1) x
    rw [cfgExit_eq_exitSchedule]
    exact exitSchedule_le_succ _ j x
  · exact fun j => measurableSet_testHit (cfgExit ε η p r good) (cfgExit_isWalkRandomTime ε η p r good) A j
  · exact fun j => ⟨measurableSet_testHit (cfgExit ε η p r good) (cfgExit_isWalkRandomTime ε η p r good) A j,
      fun k => testHit_inter_histSigma (cfgExit ε η p r good) (cfgExit_isWalkRandomTime ε η p r good) A j k⟩
  · exact fun j => ae_of_all _ fun x => cfgRadius_bounds hp hr0 hr1 good _
  · exact cfgCount_lower hp hr0 hr1 hpζ hrζ
  · intro j
    have hkey := S6j.hstep_of_schedule m a (fun _ => cfgWindow ε η p r good) A
      (Lemma68Config.testFail A (cfgExit ε η p r good))
      (fun j x => cfgStateRadius ε η p r good (x ((cfgExit ε η p r good j x).toNat)))
      hq0 hq1 hlf hcons (fun j y => cfgWindow_finite hη hproper hε p r good y)
      (fun j => ae_of_all _ fun x _ =>
        ⟨(cfgRadius_bounds hp hr0 hr1 good _).1, (cfgRadius_bounds hp hr0 hr1 good _).2.1⟩)
      hpt j
    have e : (Lemma68Config.testHit A (cfgExit ε η p r good) j).indicator (fun _ => (1 : ℝ)) =
        (walkTestEvent (cfgExit ε η p r good j) (fun y => testEvent (cfgWindow ε η p r good) A y)).indicator
          (fun _ => (1 : ℝ)) := by
      rw [cfgExit_eq_exitSchedule, testHit_eq_walkTestEvent]
    filter_upwards [hkey] with x hx
    intro hxH
    show _ ≤ (srwLaw m a)[(Lemma68Config.testHit A (cfgExit ε η p r good) j).indicator (fun _ => (1 : ℝ)) |
      stoppedSigma (cfgExit ε η p r good j) (cfgExit_isWalkRandomTime ε η p r good j)] x
    rw [e]
    exact hx hxH

/-! ### The configuration bound for the concrete schedule -/

/-- **Lemma 6.8 for the concrete schedule (bridge argument §3, assembled).** The configuration bound
`configuration_le_pow` holds with the schedule `cfgSchedule ε (S.η ω) p r (good ε ω)`, on the good event `E ε ∩ G`, for
every configuration with the guard `FullAdm`. Named inputs: `hEnv` (η continuous and proper), `hlf` (local finiteness and
the consecutive-edge condition of the walk law `S.mult ε ω`), `hstate` (the per-state inputs `StateTestInputs` of C4,
with a good-state predicate `Good`, for every admissible configuration), `hC12` (`ConcreteC12`, write-up C12), `hR1000`
(the cutoff `R ≤ 1000^(-1/ζ)`, write-up D1; implied by `R ≤ r0Min` via `Cutoff.r0Min_le_zeta`), `hq1` (the C15 constant
`qStar ≤ 1`), `c0 < 1/8` (the cell-geometry constant of C4). -/
theorem configuration_le_pow_concrete {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ s₀ γ : ℝ)
    (E : ℝ → Set Ω) (G : Set Ω) (α : ℝ → ℝ) (dd : Ω → ℝ) (R : ℝ) (ζ p qStar q0 c0 : ℝ)
    (good : ℝ → Ω → ℂ → ℕ → Prop)
    (hq0 : q0 = qStar / 9) (hq : 0 ≤ qStar) (hq1 : qStar ≤ 1) (hq9 : qStar ≤ 9) (hp : p ≤ 3)
    (hpζ : p = 2 * ζ + 2) (hζ : 0 < ζ) (hα : ∀ ε, 0 < ε → 0 < α ε) (hdd : ∀ ω, dd ω ≤ R)
    (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ) (hR1000 : R ≤ (1000 : ℝ) ^ (-1 / ζ)) (hc0 : c0 < 1 / 8)
    (hEnv : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G,
      Continuous (S.η ω) ∧ Filter.Tendsto (S.η ω) (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (hlf : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0)
    (hstate : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68, FullAdm S ρ s₀ γ ε ω r i →
      ∃ Good : ℤ → Prop, StateTestInputs (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (↑i.A : Set ℤ) qStar c0 Good)
    (hC12 : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68, FullAdm S ρ s₀ γ ε ω r i →
      ConcreteC12 (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) :
    ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68, FullAdm S ρ s₀ γ ε ω r i →
      ∃ N : ℕ, r ^ (-ζ) / 200 ≤ (N : ℝ) ∧
        exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
  have hp0 : 0 < p := by rw [hpζ]; positivity
  refine configuration_le_pow S ρ s₀ γ E G α dd R ζ p qStar q0 hq0 hq hq9 hp hα hdd hR
    (fun ε ω r _ => cfgSchedule ε (S.η ω) p r (good ε ω)) ?_
  intro ε hε ω hω r hαr hrd i hi
  have hr0 : 0 < r := (hα ε hε).trans_le hαr
  have hcut : r ^ ζ ≤ 1 / 1000 := by
    calc r ^ ζ ≤ ((1000 : ℝ) ^ (-1 / ζ)) ^ ζ :=
          Real.rpow_le_rpow hr0.le (hrd.trans ((hdd ω).trans hR1000)) hζ.le
      _ = 1 / 1000 := by
          rw [← Real.rpow_mul (by norm_num)]
          have h1 : -1 / ζ * ζ = -1 := by field_simp
          rw [h1, Real.rpow_neg_one]
          norm_num
  have hr1 : r < 1 := by
    by_contra h
    have h1r : 1 ≤ r := not_lt.1 h
    have h1 : 1 ≤ r ^ ζ := Real.one_le_rpow h1r hζ.le
    linarith
  obtain ⟨hη, hproper⟩ := hEnv ε hε ω hω
  obtain ⟨hlf', hcons⟩ := hlf ε hε ω hω
  obtain ⟨Good, hG⟩ := hstate ε hε ω hω r hαr hrd i hi
  exact cfgSchedule_valid ε (S.η ω) (good ε ω) (S.mult ε ω) i.a (↑i.A) _ hε hη hproper hp0 hr0 hr1 hpζ hcut
    hlf' hcons hq hq1
    (outerTestBound_of_state (S.mult ε ω) i.a ε (S.η ω) hη hp0 hr0 hr1 (good ε ω) (↑i.A) hε hc0 hq hq1 Good hG)
    (hC12 ε hε ω hω r hαr hrd i hi)

end Lemma68Concrete
end MatedCRT
