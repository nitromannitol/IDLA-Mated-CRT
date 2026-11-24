import MatedCRT.FirstPass.Derived.GMS21RestartCurveShift
import MatedCRT.FirstPass.Derived.InterpolatedWalkShift
import MatedCRT.FirstPass.S4S6c.StrongMarkovState
import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellIntegral
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Restarting the walk at its first vertex outside a small disc

In the proof of Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, case 1, the comparison of the walk with
Brownian motion is available for starting points away from the origin. For a start inside a small disc `B_δ(0)` the
walk is followed until its first vertex outside `B_δ(0)`, and the strong Markov property restarts it there. Modulo
time parametrization the initial segment moves the stopped curve by at most `2 (δ + 2 L)` when the edges from
`closedBall 0 (δ + L)` have embedded length at most `L`. This file proves the resulting bound: the Lévy–Prokhorov
distance between the law of the walk from the start, stopped at its exit from `U ⊇ closedBall 0 (δ + 2 L)`, and any
measure `ν` is at most `2 (δ + 2 L)` plus the largest distance between `ν` and the laws of the walks restarted at
vertices `y` with `p y ∈ closedBall 0 (δ + 2 L) \ B_δ(0)`.

## Main results

* `exists_pathHist_ballExitIndex_eq`, `measurableSet_ballExitIndex_eq`: the first exit index from `B_δ(0)` is a
  stopping time for the walk.
* `ae_ballExitIndex_ne_top`: on a locally finite graph with the successor edges, the walk leaves `B_δ(0)` almost
  surely when only finitely many vertices lie in `B_δ(0)`.
* `tsum_setLIntegral_const_of_ae_ne_top`: `∑ₖ ∫_{τ = k} c dP = c` for an almost surely finite random time `τ`.
* `restart_edist_le`: the deterministic bound at the restart.
* `levyProkhorovEDist_restart_le`: the Lévy–Prokhorov bound for the walk from a start in `B_δ(0)`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open StopAtExitLevyProkhorov

section StoppingTime

/-- The event that the walk first leaves `B_δ(0)` at the index `k` is determined by the first `k + 1` positions. -/
theorem exists_pathHist_ballExitIndex_eq (p : ℤ → ℂ) (δ : ℝ) (k : ℕ) :
    ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      univ ∩ {w : ℕ → ℤ | ballExitIndex p δ w = k} = {w | pathHist k w ∈ F} := by
  refine ⟨{h | p (h (Fin.last k)) ∉ ball (0 : ℂ) δ ∧ ∀ j : Fin (k + 1), (j : ℕ) < k → p (h j) ∈ ball (0 : ℂ) δ},
    (Set.to_countable _).measurableSet, ?_⟩
  ext w
  simp only [univ_inter, mem_ofPred_eq, ballExitIndex_eq_iff, pathHist, Fin.val_last]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => h2 j hj⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => h2 ⟨j, by omega⟩ hj⟩

theorem measurableSet_ballExitIndex_eq (p : ℤ → ℂ) (δ : ℝ) (k : ℕ) :
    MeasurableSet {w : ℕ → ℤ | ballExitIndex p δ w = k} := by
  obtain ⟨F, hF, hEq⟩ := exists_pathHist_ballExitIndex_eq p δ k
  rw [univ_inter] at hEq
  rw [hEq]
  exact (measurable_pathHist k) hF

/-- **The walk leaves `B_δ(0)`.** If `m` is locally finite with the successor edges and only finitely many vertices
are embedded in `B_δ(0)`, the walk from any vertex leaves `B_δ(0)` almost surely. -/
theorem ae_ballExitIndex_ne_top {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {p : ℤ → ℂ} {δ : ℝ} (hfin : {k | p k ∈ ball (0 : ℂ) δ}.Finite)
    (a : ℤ) : ∀ᵐ w ∂srwLaw m a, ballExitIndex p δ w ≠ ⊤ := by
  have h := ExitNull68.exit_null_of_finite hlf hcons hfin a
  rw [ae_iff]
  refine measure_mono_null (fun w hw => ?_) h
  have hw' : ballExitIndex p δ w = ⊤ := not_not.1 hw
  have hno : ¬ ∃ n, p (w n) ∉ ball (0 : ℂ) δ := by
    intro hex
    unfold ballExitIndex at hw'
    rw [dite_eq_left hex] at hw'
    exact (ENat.top_ne_natCast _) hw'.symm
  have hno' : ¬ ∃ n, w n ∉ {k | p k ∈ ball (0 : ℂ) δ} := fun ⟨n, hn⟩ => hno ⟨n, hn⟩
  show vExitTime _ w = ⊤
  unfold vExitTime
  rw [dite_eq_right hno']

/-- For an almost surely finite random time `τ` with measurable level sets, `∑ₖ ∫_{τ = k} c dP = c`. -/
theorem tsum_setLIntegral_const_of_ae_ne_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : Ω → ℕ∞) (hτm : ∀ k : ℕ, MeasurableSet {ω | τ ω = k})
    (hτ : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (c : ℝ≥0∞) :
    ∑' k : ℕ, ∫⁻ _ in {ω | τ ω = k}, c ∂P = c := by
  have hdisj : Pairwise (Function.onFun Disjoint fun k : ℕ => {ω | τ ω = k}) := by
    intro k k' hkk'
    refine Set.disjoint_left.2 fun ω h h' => hkk' ?_
    have h3 : (k : ℕ∞) = k' := (show τ ω = k from h).symm.trans h'
    exact_mod_cast h3
  have hnull : P {ω | τ ω = ⊤} = 0 := by
    rw [ae_iff] at hτ
    simpa only [ne_eq, not_not] using hτ
  have hU : P (⋃ k : ℕ, {ω | τ ω = k}) = 1 := by
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P ((⋃ k : ℕ, {ω | τ ω = k}) ∪ {ω | τ ω = ⊤}) := by
          refine measure_mono fun ω _ => ?_
          by_cases h : τ ω = ⊤
          · exact Or.inr h
          · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h
            exact Or.inl (mem_iUnion.2 ⟨k, hk.symm⟩)
      _ ≤ P (⋃ k : ℕ, {ω | τ ω = k}) + P {ω | τ ω = ⊤} := measure_union_le _ _
      _ = P (⋃ k : ℕ, {ω | τ ω = k}) := by rw [hnull, add_zero]
  simp only [setLIntegral_const]
  rw [ENNReal.tsum_mul_left, ← measure_iUnion hdisj hτm, hU, mul_one]

end StoppingTime

section Restart

/-- **The restart, deterministically.** Let the walk `w` have consecutive vertices equal or joined by an edge of `m`,
start in `B_δ(0)` and first leave `B_δ(0)` at the index `k`, and let every edge from a vertex of
`closedBall 0 (δ + L)` have embedded length at most `L`. Then the curve classes of the interpolated walk and of the
interpolated walk restarted at the index `k`, both stopped at their exits from `U ⊇ closedBall 0 (δ + 2 L)`, are at
distance at most `2 (δ + 2 L)`, and the restart vertex lies in `closedBall 0 (δ + 2 L) \ B_δ(0)`. -/
theorem restart_edist_le {m : ℤ → ℤ → ℕ} {p : ℤ → ℂ} {δ L : ℝ} (hL : 0 ≤ L)
    (hstep : ∀ x y, p x ∈ closedBall (0 : ℂ) (δ + L) → m x y ≠ 0 → dist (p x) (p y) ≤ L)
    {U : Set ℂ} (hU : closedBall (0 : ℂ) (δ + 2 * L) ⊆ U)
    {w : ℕ → ℤ} (hw : ∀ n, w (n + 1) = w n ∨ m (w n) (w (n + 1)) ≠ 0) (h0 : p (w 0) ∈ ball (0 : ℂ) δ)
    {k : ℕ} (hk : ballExitIndex p δ w = k) :
    edist (stoppedExitCurve U (interpPathCM p zero_le_one w))
        (stoppedExitCurve U (interpPathCM p zero_le_one (WalkPotential.pathShift k w))) ≤
      ENNReal.ofReal (2 * (δ + 2 * L)) ∧
    p (w k) ∉ ball (0 : ℂ) δ ∧ p (w k) ∈ closedBall (0 : ℂ) (δ + 2 * L) := by
  have hball := mem_closedBall_of_ballExitIndex hL hstep hw hk h0
  have hpath : ∀ t ≤ (k : ℝ≥0) + 1, interpPathCM p zero_le_one w t ∈ closedBall (0 : ℂ) (δ + 2 * L) :=
    fun t ht => interpPathCM_mem_closedBall hball ht
  refine ⟨?_, ((ballExitIndex_eq_iff p δ w k).1 hk).1, hball k (Nat.le_succ k)⟩
  refine edist_stoppedExitCurve_shift_le _ _ (T := (k : ℝ≥0)) (fun s => ?_)
    (fun t ht => hU (hpath t (ht.trans le_self_add))) 0 (fun t ht => mem_closedBall.1 (hpath t ht))
  have h := pathShift_interpPathCM p one_pos w k
  have hk' : ((k : ℝ) / 1).toNNReal = (k : ℝ≥0) := by
    rw [div_one]
    exact Real.toNNReal_natCast k
  rw [hk'] at h
  show interpPathCM p zero_le_one (fun j => w (k + j)) s = interpPathCM p zero_le_one w (s + k)
  rw [← h, LatticeProb.pathShift_apply, add_comm]

/-- **The Lévy–Prokhorov bound at the restart** (Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of Theorem 3.4,
case 1, starts near the origin). Let every edge of `m` from a vertex of `closedBall 0 (δ + L)` have embedded length
at most `L`, let `U ⊇ closedBall 0 (δ + 2 L)` be open, and let the walk from `a`, `p a ∈ B_δ(0)`, leave `B_δ(0)`
almost surely. If the law of the curve class of the walk from every vertex `y` with
`p y ∈ closedBall 0 (δ + 2 L) \ B_δ(0)`, stopped at its exit from `U`, is within `κ` of `ν`, then so is the law for
the walk from `a`, up to `2 (δ + 2 L)`. -/
theorem levyProkhorovEDist_restart_le {m : ℤ → ℤ → ℕ} {p : ℤ → ℂ} {δ L : ℝ} (hL : 0 ≤ L)
    (hstep : ∀ x y, p x ∈ closedBall (0 : ℂ) (δ + L) → m x y ≠ 0 → dist (p x) (p y) ≤ L)
    {U : Set ℂ} (hUo : IsOpen U) (hU : closedBall (0 : ℂ) (δ + 2 * L) ⊆ U)
    {a : ℤ} (ha : p a ∈ ball (0 : ℂ) δ) (hτ : ∀ᵐ w ∂srwLaw m a, ballExitIndex p δ w ≠ ⊤)
    (ν : Measure (BouRabeeGwynne.CurveSpace 2)) {κ : ℝ≥0∞}
    (hκ : ∀ y, p y ∉ ball (0 : ℂ) δ → p y ∈ closedBall (0 : ℂ) (δ + 2 * L) →
      levyProkhorovEDist ((srwLaw m y).map fun w => stoppedExitCurve U (interpPathCM p zero_le_one w)) ν ≤ κ) :
    levyProkhorovEDist ((srwLaw m a).map fun w => stoppedExitCurve U (interpPathCM p zero_le_one w)) ν ≤
      κ + ENNReal.ofReal (2 * (δ + 2 * L)) := by
  set Φ : (ℕ → ℤ) → BouRabeeGwynne.CurveSpace 2 := fun w => stoppedExitCurve U (interpPathCM p zero_le_one w)
    with hΦ
  have hΦm : Measurable Φ := (measurable_stoppedExitCurve U hUo).comp (measurable_interpPathCM p zero_le_one)
  set r : ℝ≥0∞ := ENNReal.ofReal (2 * (δ + 2 * L)) with hr
  have hrtop : r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hτm : ∀ k : ℕ, MeasurableSet {w : ℕ → ℤ | ballExitIndex p δ w = k} := measurableSet_ballExitIndex_eq p δ
  have hgood : ∀ᵐ w ∂srwLaw m a, ∀ k : ℕ, ballExitIndex p δ w = k →
      edist (Φ w) (Φ (WalkPotential.pathShift k w)) ≤ r ∧
      p (w k) ∉ ball (0 : ℂ) δ ∧ p (w k) ∈ closedBall (0 : ℂ) (δ + 2 * L) := by
    filter_upwards [srwLaw_ae_start m a, srwLaw_ae_step m a] with w h0 hw k hk
    exact restart_edist_le hL hstep hU hw (by rw [h0]; exact ha) hk
  have hSM : ∀ G : Set (ℕ → ℤ), MeasurableSet G →
      srwLaw m a {w | ∃ k : ℕ, ballExitIndex p δ w = k ∧ WalkPotential.pathShift k w ∈ G} =
        ∑' k : ℕ, ∫⁻ w in {w | ballExitIndex p δ w = k}, srwLaw m (w k) G ∂srwLaw m a := by
    intro G hG
    have h := srwLaw_strong_markov_state m a (ballExitIndex p δ) (fun _ => G) (fun _ => hG) (S := univ)
      (exists_pathHist_ballExitIndex_eq p δ)
    simpa only [univ_inter] using h
  refine levyProkhorovEDist_le_of_forall _ _ _ fun ε B hε hεtop hB => ?_
  have hrε : r ≤ ε := le_add_self.trans hε.le
  set c := ε - r with hc
  have hcancel : c + r = ε := tsub_add_cancel_of_le hrε
  have hκc : κ < c := by
    by_contra h
    have h' := add_le_add (not_lt.1 h) (le_refl r)
    rw [hcancel] at h'
    exact absurd hε (not_lt.2 h')
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top hεtop.ne tsub_le_self
  have hQ : ∀ y, p y ∉ ball (0 : ℂ) δ → p y ∈ closedBall (0 : ℂ) (δ + 2 * L) →
      levyProkhorovEDist ((srwLaw m y).map Φ) ν < c := fun y h1 h2 => (hκ y h1 h2).trans_lt hκc
  constructor
  · set D : Set (BouRabeeGwynne.CurveSpace 2) := {q | infEDist q B ≤ r} with hDdef
    have hD : MeasurableSet D := (isClosed_le continuous_infEDist continuous_const).measurableSet
    calc (srwLaw m a).map Φ B = srwLaw m a (Φ ⁻¹' B) := Measure.map_apply hΦm hB
      _ ≤ srwLaw m a {w | ∃ k : ℕ, ballExitIndex p δ w = k ∧ WalkPotential.pathShift k w ∈ Φ ⁻¹' D} := by
          refine measure_mono_ae ?_
          filter_upwards [hgood, hτ] with w hw hwτ hwB
          obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hwτ
          refine ⟨k, hk.symm, ?_⟩
          have h1 := (hw k hk.symm).1
          show infEDist (Φ (WalkPotential.pathShift k w)) B ≤ r
          calc infEDist (Φ (WalkPotential.pathShift k w)) B
              ≤ infEDist (Φ w) B + edist (Φ (WalkPotential.pathShift k w)) (Φ w) :=
                Metric.infEDist_le_infEDist_add_edist
            _ ≤ 0 + r := add_le_add (Metric.infEDist_zero_of_mem (show Φ w ∈ B from hwB)).le
                (by rw [edist_comm]; exact h1)
            _ = r := zero_add r
      _ = ∑' k : ℕ, ∫⁻ w in {w | ballExitIndex p δ w = k}, srwLaw m (w k) (Φ ⁻¹' D) ∂srwLaw m a :=
          hSM _ (hΦm hD)
      _ ≤ ∑' k : ℕ, ∫⁻ _ in {w | ballExitIndex p δ w = k}, (ν (thickening c.toReal D) + c) ∂srwLaw m a := by
          refine ENNReal.tsum_le_tsum fun k => lintegral_mono_ae ((ae_restrict_iff' (hτm k)).2 ?_)
          filter_upwards [hgood] with w hw hwk
          obtain ⟨-, h1, h2⟩ := hw k hwk
          have h := left_measure_le_of_levyProkhorovEDist_lt (hQ (w k) h1 h2) hD
          rwa [Measure.map_apply hΦm hD] at h
      _ = ν (thickening c.toReal D) + c := tsum_setLIntegral_const_of_ae_ne_top _ _ hτm hτ _
      _ ≤ ν (thickening ε.toReal B) + ε := by
          refine add_le_add (measure_mono fun q hq => ?_) tsub_le_self
          rw [Metric.mem_thickening_iff_infEDist_lt, ENNReal.ofReal_toReal hctop] at hq
          rw [Metric.mem_thickening_iff_infEDist_lt, ENNReal.ofReal_toReal hεtop.ne]
          obtain ⟨q', hq'D, hqq'⟩ := Metric.infEDist_lt_iff.1 hq
          have hq'D' : infEDist q' B ≤ r := hq'D
          calc infEDist q B ≤ infEDist q' B + edist q q' := Metric.infEDist_le_infEDist_add_edist
            _ ≤ r + edist q q' := add_le_add hq'D' le_rfl
            _ < r + c := ENNReal.add_lt_add_left hrtop hqq'
            _ = ε := by rw [add_comm, hcancel]
  · have hDn : MeasurableSet (thickening c.toReal B) := isOpen_thickening.measurableSet
    calc ν B = ∑' k : ℕ, ∫⁻ _ in {w | ballExitIndex p δ w = k}, ν B ∂srwLaw m a :=
          (tsum_setLIntegral_const_of_ae_ne_top _ _ hτm hτ _).symm
      _ ≤ ∑' k : ℕ, ∫⁻ w in {w | ballExitIndex p δ w = k},
            (srwLaw m (w k) (Φ ⁻¹' thickening c.toReal B) + c) ∂srwLaw m a := by
          refine ENNReal.tsum_le_tsum fun k => lintegral_mono_ae ((ae_restrict_iff' (hτm k)).2 ?_)
          filter_upwards [hgood] with w hw hwk
          obtain ⟨-, h1, h2⟩ := hw k hwk
          have h := right_measure_le_of_levyProkhorovEDist_lt (hQ (w k) h1 h2) hB
          rwa [Measure.map_apply hΦm hDn] at h
      _ = ∑' k : ℕ, ∫⁻ w in {w | ballExitIndex p δ w = k},
              srwLaw m (w k) (Φ ⁻¹' thickening c.toReal B) ∂srwLaw m a +
            ∑' k : ℕ, ∫⁻ _ in {w | ballExitIndex p δ w = k}, c ∂srwLaw m a := by
          rw [← ENNReal.tsum_add]
          exact tsum_congr fun k => lintegral_add_right _ measurable_const
      _ = srwLaw m a {w | ∃ k : ℕ, ballExitIndex p δ w = k ∧
              WalkPotential.pathShift k w ∈ Φ ⁻¹' thickening c.toReal B} + c := by
          rw [hSM _ (hΦm hDn), tsum_setLIntegral_const_of_ae_ne_top _ _ hτm hτ]
      _ ≤ (srwLaw m a).map Φ (thickening ε.toReal B) + ε := by
          refine add_le_add ?_ tsub_le_self
          rw [Measure.map_apply hΦm isOpen_thickening.measurableSet]
          refine measure_mono_ae ?_
          filter_upwards [hgood] with w hw hwS
          obtain ⟨k, hk, hkD⟩ := hwS
          have h1 := (hw k hk).1
          have hkD' : Φ (WalkPotential.pathShift k w) ∈ thickening c.toReal B := hkD
          show Φ w ∈ thickening ε.toReal B
          rw [Metric.mem_thickening_iff_infEDist_lt, ENNReal.ofReal_toReal hctop] at hkD'
          rw [Metric.mem_thickening_iff_infEDist_lt, ENNReal.ofReal_toReal hεtop.ne]
          calc infEDist (Φ w) B
              ≤ infEDist (Φ (WalkPotential.pathShift k w)) B + edist (Φ w) (Φ (WalkPotential.pathShift k w)) :=
                Metric.infEDist_le_infEDist_add_edist
            _ ≤ infEDist (Φ (WalkPotential.pathShift k w)) B + r := add_le_add le_rfl h1
            _ < c + r := ENNReal.add_lt_add_right hrtop hkD'
            _ = ε := hcancel

end Restart

end MatedCRT
