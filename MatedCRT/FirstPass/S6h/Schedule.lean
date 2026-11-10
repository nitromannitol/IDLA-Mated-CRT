import Mathlib
import MatedCRT.FirstPass.S6h
import MatedCRT.FirstPass.S6j
import MatedCRT.FirstPass.S6h.Successive
import MatedCRT.FirstPass.S6e.RadiusSelect
import MatedCRT.FirstPass.S6e.Cutoff
import MatedCRT.FirstPass.S4S6c.Uniform68Round

/-!
# The concrete test schedule of Lemma 6.8 (fp-S6h, owner z8)

Write-up C1-C3 (`notes/fp-gaps/CHATGPT-lemma68-open-parts.md` lines 659-805) and bridge note §3, Steps B-F
(`notes/fp-gaps/CHATGPT-z9-6-8-bridge.md` lines 218-408): the grid centre `z_j = Q_δ(η(X_{T_j}))`, the first-good radius
`R_j = R_{z_j}` (A5, `Lemma68Radius.firstGoodRadius`, default `δ`), the window `W(y) = I(B_{2R}(z))` at the state `y`, the
successive exit times `T_{j+1} = nextExit W T_j` (`Lemma68Successive.exitSchedule`), the count `N = ⌊r/(100 s)⌋`, `s = √δ`.

Proved here: the structural fields of `TestSchedule.Valid` (monotone σ-algebras `F_{T_j}`, measurability of the test events
`G_j = testHit`, `G_j ∈ F_{T_{j+1}}`, radius bounds, the count bound), and `hstep` from the conditional strong Markov
estimate `S6j.hstep_concrete`. Explicit inputs (not proved here): the stopping property `hstop`, the almost-sure finiteness
`hfin` of the successive exits, the per-state outer test bound `hpt` (write-up C4), the containment `hC12` (write-up C12),
and the cutoff `hrζ : r ^ ζ ≤ 1/1000` (write-up D1, `s ≤ r/1000`).
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

/-- With the successive exit times of a constant window, the test event `G_j` is the walk test event after `T_j`
(bridge note (4); `nextExit` unfolds to `T_j + vExitTime (W (X_{T_j})) (shift)`). -/
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
      generalize vExitTime (W (x k)) (pathShift k x) = v at hn2' ⊢
      induction v using ENat.recTopCoe with
      | top => exact ENat.natCast_lt_top _
      | coe l =>
        have h' : n < k + l := by
          have : (n : ℕ∞) < ((k + l : ℕ) : ℕ∞) := by push_cast; exact hn2'
          exact ENat.natCast_lt_natCast.1 this
        exact ENat.natCast_lt_natCast.2 (by omega)
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

/-- The successive exit times `T_j` of write-up C3 (`T_{j+1} = nextExit W T_j`). -/
noncomputable def cfgExit (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (good : ℂ → ℕ → Prop) : ℕ → (ℕ → ℤ) → ℕ∞ :=
  exitSchedule (cfgWindow ε η p r good)

/-- The count `N = ⌊r/(100 s)⌋` with `s = √δ` (write-up C1, Step B of the bridge note). -/
noncomputable def cfgCount (p r : ℝ) : ℕ :=
  ⌊r / (100 * Real.sqrt (Delta p r))⌋₊

/-- The concrete test schedule (C1-C3): `T = cfgExit`, `R_j = cfgStateRadius (X_{T_j})`, `m_j = F_{T_j}`. -/
noncomputable def cfgSchedule (ε : ℝ) (η : ℝ → ℂ) (p r : ℝ) (good : ℂ → ℕ → Prop)
    (hstop : ∀ j, IsWalkRandomTime (cfgExit ε η p r good j)) : TestSchedule where
  N := cfgCount p r
  T := cfgExit ε η p r good
  R := fun j x => cfgStateRadius ε η p r good (x ((cfgExit ε η p r good j x).toNat))
  m := fun j => stoppedSigma (cfgExit ε η p r good j) (hstop j)

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

/-- **Concrete configuration schedule (Lemma 6.8, bridge note §3 Steps B-F).** For the concrete schedule `cfgSchedule`,
`TestSchedule.Valid` holds on `ν = srwLaw m a`, given the stopping property `hstop`, the almost-sure finiteness `hfin` of
the successive exits, the containment `hC12` (write-up C12) and the per-state outer test bound `hpt` (write-up C4, with
`printed_test_bound` at the local window). The structural fields and `hstep` (via `S6j.hstep_concrete`) are proved. -/
theorem cfgSchedule_valid (ε : ℝ) (η : ℝ → ℂ) {p r ζ qStar : ℝ} (good : ℂ → ℕ → Prop) (m : ℤ → ℤ → ℕ) (a : ℤ)
    (A U : Set ℤ) (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (hpζ : p = 2 * ζ + 2) (hrζ : r ^ ζ ≤ 1 / 1000)
    (hq0 : 0 ≤ qStar) (hq1 : qStar ≤ 1)
    (hstop : ∀ j, IsWalkRandomTime (cfgExit ε η p r good j))
    (hfin : ∀ j, ∀ᵐ x ∂srwLaw m a, cfgExit ε η p r good j x < ⊤)
    (hpt : ∀ j, ∀ᵐ x ∂srwLaw m a, x ∈ Lemma68Config.testFail A (cfgExit ε η p r good) j →
      cfgExit ε η p r good j x < ⊤ →
      srwLaw m (x (cfgExit ε η p r good j x).toNat)
          (TestBound68.stayIn (cfgWindow ε η p r good) A (x (cfgExit ε η p r good j x).toNat)) ≤
        ENNReal.ofReal (1 - qStar / (1 + Real.log (1 / cfgStateRadius ε η p r good
          (x (cfgExit ε η p r good j x).toNat))) ^ 2))
    (hC12 : ∀ᵐ x ∂srwLaw m a, cfgExit ε η p r good (cfgCount p r) x < vExitTime U x) :
    TestSchedule.Valid (cfgSchedule ε η p r good hstop) (srwLaw m a) U A r p qStar ζ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hC12, ?_⟩
  · exact monotone_nat_of_le_succ fun j =>
      stoppedSigma_mono (hstop j) (hstop (j + 1)) fun x => exitSchedule_le_succ _ j x
  · exact fun j => stoppedSigma_le _ (hstop j)
  · exact fun x j => exitSchedule_le_succ _ j x
  · exact fun j => measurableSet_testHit (cfgExit ε η p r good) hstop A j
  · exact fun j => ⟨measurableSet_testHit (cfgExit ε η p r good) hstop A j,
      fun k => testHit_inter_histSigma (cfgExit ε η p r good) hstop A j k⟩
  · exact fun j => ae_of_all _ fun x => cfgRadius_bounds hp hr0 hr1 good _
  · exact cfgCount_lower hp hr0 hr1 hpζ hrζ
  · intro j
    have hkey := S6j.hstep_concrete m a (cfgExit ε η p r good) hstop (fun _ => cfgWindow ε η p r good) A
      (Lemma68Config.testFail A (cfgExit ε η p r good))
      (fun j x => cfgStateRadius ε η p r good (x ((cfgExit ε η p r good j x).toNat)))
      hq0 hq1
      (fun j => ae_of_all _ fun x _ => ⟨(cfgRadius_bounds hp hr0 hr1 good _).1, (cfgRadius_bounds hp hr0 hr1 good _).2.1⟩)
      (fun j => by filter_upwards [hfin j] with x hx _ using hx)
      hpt j
    have e : (Lemma68Config.testHit A (cfgExit ε η p r good) j).indicator (fun _ => (1 : ℝ)) =
        (walkTestEvent (cfgExit ε η p r good j) (fun y => testEvent (cfgWindow ε η p r good) A y)).indicator
          (fun _ => (1 : ℝ)) := by
      unfold cfgExit
      rw [testHit_eq_walkTestEvent]
    filter_upwards [hkey] with x hx
    intro hxH
    show _ ≤ (srwLaw m a)[(Lemma68Config.testHit A (cfgExit ε η p r good) j).indicator (fun _ => (1 : ℝ)) |
      stoppedSigma (cfgExit ε η p r good j) (hstop j)] x
    rw [e]
    exact hx hxH

end Lemma68Concrete
end MatedCRT
