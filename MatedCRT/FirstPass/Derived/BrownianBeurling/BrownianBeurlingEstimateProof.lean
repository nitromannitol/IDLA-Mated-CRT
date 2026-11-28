import MatedCRT.FirstPass.Derived.JordanDomainExteriorRegularityProof
import MatedCRT.FirstPass.Derived.BrownianBeurling.AvoidanceMeanValue
import MatedCRT.FirstPass.Derived.BrownianBeurling.MeanValueHarmonic
import MatedCRT.FirstPass.Derived.BrownianBeurling.ThickeningBarrier
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingMain

/-!
# The Beurling estimate for planar Brownian motion

This file proves `MatedCRT.BrownianBeurlingEstimate` (`brownianBeurlingEstimate`): for a curve `γ` from `w = γ 0` to a
point at distance at least `R` from `w`, planar Brownian motion started at `y` with `d = |y - w| < R` leaves `B(w, R)`
before hitting `γ` with probability at most `C (d / R)^{1/2}`.

This is the Beurling estimate of Lawler, *Conformally Invariant Processes in the Plane*, Section 3.8, Theorem 3.76. The
probability is reduced to the analytic Beurling estimate for harmonic majorants proved in Lattice-Probability by
Carleman's method (`QuantumZipper.Thm18Asm.LWFar.beurlingHarmStmt_holds`), applied to the probability of leaving
`B(y, ρ)`, `ρ = R - d`, before hitting the closed `δ`-thickening `K_δ` of the trace `K = γ([0, 1])`:

* this probability is harmonic in `B(y, ρ) \ K_δ`, by the mean value property at disc exits
  (`circleAverage_avoidanceProb`, `harmonicOnNhd_of_forall_circleAverage_eq`), and it tends to `0` at every frontier
  point of `K_δ`, where `K_δ` contains a disc of radius `δ` touching the point
  (`exists_avoidanceProb_le_of_exterior_disc`);
* the trace `K` is connected, disjoint from the complement of `K_δ`, meets `closedBall y d` at `w` and leaves `B(y, ρ)`
  at `γ 1`, so the analytic estimate bounds the probability by `C₀ (d / ρ)^{1/2}`;
* a path that leaves `B(w, R) ⊇ B(y, ρ)` before hitting `K` avoids `K_δ` until it leaves `B(y, ρ)` once `δ` is smaller
  than the distance from `K` to the compact piece of the path before that exit (`exitTime_lt_subset_iUnion_avoidEvent`),
  and the union over `δ = e / (n + 2)` is increasing.

For `d > R / 2` the bound holds because the probability is at most `1`; for `d ≤ R / 2` one has `ρ ≥ R / 2`, and the
constant is `C = √2 · max C₀ 1`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.BrownianBeurling

/-- The probability of leaving `O` before hitting a compact `K` is harmonic in `O \ K`. -/
theorem harmonicOnNhd_avoidanceProb {O K : Set ℂ} (hO : IsOpen O) (hK : IsCompact K) :
    InnerProductSpace.HarmonicOnNhd (avoidanceProb O K) (O \ K) :=
  harmonicOnNhd_of_forall_circleAverage_eq (hO.sdiff hK.isClosed) (measurable_avoidanceProb hO hK)
    (M := 1) (fun z => by
      rw [abs_of_nonneg (avoidanceProb_nonneg O K z)]
      exact avoidanceProb_le_one O K z)
    (fun _ _ _ hr hxr => circleAverage_avoidanceProb hO hK hr hxr)

/-- At a frontier point of the closed `δ`-thickening of a compact set, inside `O`, the probability of leaving `O` before
hitting the thickening tends to `0`. -/
theorem exists_avoidanceProb_cthickening_le {O K : Set ℂ} (hO : IsOpen O) (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) {x₀ : ℂ} (hx₀O : x₀ ∈ O) (hx₀ : x₀ ∈ frontier (cthickening δ K))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : ℂ, dist x x₀ < η → avoidanceProb O (cthickening δ K) x ≤ ε := by
  have hKne : K.Nonempty := by
    rcases K.eq_empty_or_nonempty with rfl | h
    · simp [cthickening_empty] at hx₀
    · exact h
  have hinf : infEDist x₀ K = ENNReal.ofReal δ := frontier_cthickening_subset K hx₀
  obtain ⟨z, hzK, hz⟩ := hK.exists_infDist_eq_dist hKne x₀
  have hdist : dist x₀ z = δ := by
    rw [← hz, infDist, hinf, ENNReal.toReal_ofReal hδ.le]
  exact exists_avoidanceProb_le_of_exterior_disc hO hK.cthickening hδ hx₀O hdist
    (closedBall_subset_cthickening hzK δ) hε

/-- A path that leaves `O' ⊇ O` before hitting a compact `K` leaves `O` before hitting the closed `δ n`-thickening of
`K` for some `n`, when `δ n → 0`. -/
theorem exitTime_lt_subset_iUnion_avoidEvent {K : Set ℂ} (hK : IsCompact K) {O O' : Set ℂ}
    (hOO' : O ⊆ O') {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) :
    {b : ContinuousPath ℂ | ContinuousPath.exitTime O' b < ContinuousPath.exitTime Kᶜ b} ⊆
      ⋃ n, avoidEvent O (cthickening (δ n) K) := by
  intro b hb
  simp only [mem_ofPred_eq] at hb
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine mem_iUnion.2 ⟨0, ?_⟩
    simp only [avoidEvent, cthickening_empty, compl_empty, mem_ofPred_eq]
    rw [show ContinuousPath.exitTime univ b = ⊤ from ?_]
    · exact le_top
    · rw [ContinuousPath.exitTime_eq_top_iff]
      intro t
      exact mem_univ _
  set t := ContinuousPath.exitTime O b with ht
  have htO : t ≤ ContinuousPath.exitTime O' b := ContinuousPath.exitTime_mono hOO' b
  have htK : t < ContinuousPath.exitTime Kᶜ b := htO.trans_lt hb
  have htop : t ≠ ⊤ := ne_top_of_lt htK
  set t₀ : ℝ≥0 := t.toNNReal
  have ht₀ : (t₀ : ℝ≥0∞) = t := ENNReal.coe_toNNReal htop
  -- the compact piece of the path before the exit from `O` misses `K`
  have hS : IsCompact (b '' Icc 0 t₀) := isCompact_Icc.image b.continuous
  have hSK : ∀ p ∈ b '' Icc 0 t₀, p ∉ K := by
    rintro p ⟨s, hs, rfl⟩
    have : (s : ℝ≥0∞) < ContinuousPath.exitTime Kᶜ b :=
      lt_of_le_of_lt (by rw [← ht₀]; exact_mod_cast hs.2) htK
    exact ContinuousPath.mem_of_lt_exitTime Kᶜ b s this
  have hSne : (b '' Icc 0 t₀).Nonempty := ⟨b 0, mem_image_of_mem b ⟨le_rfl, zero_le⟩⟩
  obtain ⟨p₀, hp₀, hmin⟩ := hS.exists_isMinOn hSne (continuous_infDist_pt K).continuousOn
  have hm : 0 < infDist p₀ K :=
    (infDist_pos_iff_notMem_closure hKne).1 (by rw [hK.isClosed.closure_eq]; exact hSK p₀ hp₀)
  obtain ⟨n, hn⟩ := (hδ.eventually (gt_mem_nhds hm)).exists
  refine mem_iUnion.2 ⟨n, ?_⟩
  simp only [avoidEvent, mem_ofPred_eq]
  rw [ContinuousPath.le_exitTime_iff]
  intro v hv
  rw [mem_compl_iff, not_not] at hv
  by_contra hlt
  push Not at hlt
  have hvt : v ≤ t₀ := by
    have : (v : ℝ≥0∞) ≤ t₀ := by rw [ht₀]; exact hlt.le
    exact_mod_cast this
  have hpS : b v ∈ b '' Icc 0 t₀ := mem_image_of_mem b ⟨zero_le, hvt⟩
  have h1 : infDist p₀ K ≤ infDist (b v) K := hmin hpS
  rw [mem_cthickening_iff, ← ENNReal.ofReal_toReal (infEDist_ne_top hKne)] at hv
  have h2 : (infEDist (b v) K).toReal = infDist (b v) K := rfl
  rw [h2] at hv
  have h3 : infDist (b v) K ≤ max (δ n) 0 := by
    by_cases h0 : δ n ≤ 0
    · rw [ENNReal.ofReal_of_nonpos h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hv
      exact hv.trans (le_max_right _ _)
    · exact ((ENNReal.ofReal_le_ofReal_iff (le_of_not_ge h0)).1 hv).trans (le_max_left _ _)
  have h4 := max_lt hn hm
  linarith

/-- **The Beurling estimate for planar Brownian motion** (Lawler, *Conformally Invariant Processes in the Plane*,
Theorem 3.76; Lawler–Limic, arXiv:math/0403309, Section 1), from the analytic Beurling estimate for harmonic
majorants. -/
theorem brownianBeurlingEstimate : BrownianBeurlingEstimate := by
  obtain ⟨C₀, hC₀, hB⟩ := QuantumZipper.Thm18Asm.LWFar.beurlingHarmStmt_holds
  refine ⟨Real.sqrt 2 * max C₀ 1, by positivity, ?_⟩
  intro γ y R hR hy
  set w := γ 0 with hw
  set d := dist y w with hd
  set K : Set ℂ := range γ with hKdef
  have hR0 : 0 < R := lt_of_le_of_lt dist_nonneg hy
  have hKc : IsCompact K := isCompact_range γ.continuous
  have hwK : w ∈ K := mem_range_self 0
  -- a start on the trace hits it at time zero
  by_cases hyK : y ∈ K
  · have h0 : planarBrownianMotion y
        {b | ContinuousPath.exitTime (ball w R) b < ContinuousPath.exitTime Kᶜ b} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [ae_planarBrownianMotion_eval_zero y] with b hb
      simp only [not_lt]
      have : ContinuousPath.exitTime Kᶜ b ≤ ((0 : ℝ≥0) : ℝ≥0∞) :=
        ContinuousPath.exitTime_le_of_notMem Kᶜ b 0 (by simpa [hb] using hyK)
      exact this.trans zero_le
    rw [h0]
    exact zero_le
  -- far starts: the probability is at most one
  by_cases hd2 : R / 2 < d
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdR : 1 / 2 ≤ d / R := by
      rw [div_le_div_iff₀ (by norm_num) hR0]
      linarith
    have hs : 1 ≤ Real.sqrt 2 * Real.sqrt (d / R) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.one_le_sqrt.2 (by linarith)
    calc (1 : ℝ) ≤ Real.sqrt 2 * Real.sqrt (d / R) := hs
      _ ≤ Real.sqrt 2 * max C₀ 1 * Real.sqrt (d / R) := by
          rw [mul_right_comm]
          exact le_mul_of_one_le_right (by positivity) (le_max_right _ _)
  push Not at hd2
  have hd0 : 0 < d := dist_pos.2 (fun h => hyK (h ▸ hwK))
  set ρ := R - d with hρdef
  have hdρ : d ≤ ρ := by linarith
  have hρ0 : 0 < ρ := hd0.trans_le hdρ
  have hball : ball y ρ ⊆ ball w R := ball_subset_ball' (by rw [← hd, hρdef]; linarith)
  -- the thickenings
  set e := infDist y K with he
  have he0 : 0 < e :=
    (infDist_pos_iff_notMem_closure ⟨w, hwK⟩).1 (by rw [hKc.isClosed.closure_eq]; exact hyK)
  set δ : ℕ → ℝ := fun n => e / ((n : ℝ) + 2) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos he0 (by positivity)
  have hδlt : ∀ n, δ n < e := fun n =>
    div_lt_self he0 (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
  have hδanti : Antitone δ := fun m n hmn =>
    div_le_div_of_nonneg_left he0.le (by positivity) (by exact_mod_cast (by omega : m + 2 ≤ n + 2))
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa using this.const_div_atTop e
  set A : ℕ → Set (ContinuousPath ℂ) := fun n => avoidEvent (ball y ρ) (cthickening (δ n) K) with hA
  have hAmono : Monotone A := by
    intro m n hmn b hb
    simp only [hA, avoidEvent, mem_ofPred_eq] at hb ⊢
    exact hb.trans (ContinuousPath.exitTime_mono
      (compl_subset_compl.2 (cthickening_mono (hδanti hmn) K)) b)
  -- the analytic Beurling estimate for each thickening
  have hAn : ∀ n, planarBrownianMotion y (A n) ≤ ENNReal.ofReal (C₀ * (d / ρ) ^ (1 / 2 : ℝ)) := by
    intro n
    set Kn := cthickening (δ n) K with hKn
    have hKnc : IsCompact Kn := hKc.cthickening
    have hyKn : y ∉ Kn := by
      rw [hKn, mem_cthickening_iff, not_le, ← ENNReal.ofReal_toReal (infEDist_ne_top ⟨w, hwK⟩)]
      exact (ENNReal.ofReal_lt_ofReal_iff he0).2 (hδlt n)
    have hcomp : connectedComponentIn (Knᶜ ∩ ball y ρ) y ⊆ ball y ρ \ Kn := by
      refine (connectedComponentIn_subset _ _).trans ?_
      rw [inter_comm, diff_eq]
    have hh := hB Knᶜ K y d ρ (avoidanceProb (ball y ρ) Kn) isClosed_cthickening.isOpen_compl hyKn hd0
      hdρ (isConnected_range γ.continuous)
      (disjoint_compl_right.mono_left (self_subset_cthickening K))
      ⟨w, hwK, by rw [mem_closedBall, dist_comm]⟩
      ⟨γ 1, mem_range_self 1, by
        rw [mem_ball, not_lt]
        have h1 := dist_triangle (γ 1) y w
        linarith⟩
      ((harmonicOnNhd_avoidanceProb isOpen_ball hKnc).mono hcomp)
      (fun x _ => ⟨avoidanceProb_nonneg _ _ x, avoidanceProb_le_one _ _ x⟩)
      (fun x₀ hx₀ ε hε => by
        rw [frontier_compl] at hx₀
        obtain ⟨η, hη, hle⟩ :=
          exists_avoidanceProb_cthickening_le isOpen_ball hKc (hδpos n) hx₀.2 hx₀.1 hε
        exact ⟨η, hη, fun x _ hx => hle x hx⟩)
    rw [← ofReal_avoidanceProb]
    exact ENNReal.ofReal_le_ofReal hh
  -- the union over the thickenings
  have hsubU : {b : ContinuousPath ℂ |
      ContinuousPath.exitTime (ball w R) b < ContinuousPath.exitTime Kᶜ b} ⊆ ⋃ n, A n :=
    exitTime_lt_subset_iUnion_avoidEvent hKc hball hδlim
  calc planarBrownianMotion y
        {b | ContinuousPath.exitTime (ball (γ 0) R) b < ContinuousPath.exitTime (range γ)ᶜ b}
      ≤ planarBrownianMotion y (⋃ n, A n) := measure_mono hsubU
    _ ≤ ENNReal.ofReal (C₀ * (d / ρ) ^ (1 / 2 : ℝ)) :=
        le_of_tendsto' (tendsto_measure_iUnion_atTop hAmono) hAn
    _ ≤ ENNReal.ofReal (Real.sqrt 2 * max C₀ 1 * Real.sqrt (dist y (γ 0) / R)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.sqrt_eq_rpow, ← hd]
        have hdρR : d / ρ ≤ 2 * (d / R) := by
          rw [div_le_iff₀ hρ0]
          have : 2 * (d / R) * ρ = d * (2 * ρ / R) := by ring
          rw [this]
          refine le_mul_of_one_le_right hd0.le ?_
          rw [le_div_iff₀ hR0]
          linarith
        have hsq : Real.sqrt (d / ρ) ≤ Real.sqrt 2 * Real.sqrt (d / R) := by
          rw [← Real.sqrt_mul (by norm_num)]
          exact Real.sqrt_le_sqrt hdρR
        calc C₀ * Real.sqrt (d / ρ) ≤ max C₀ 1 * (Real.sqrt 2 * Real.sqrt (d / R)) :=
              mul_le_mul (le_max_left _ _) hsq (Real.sqrt_nonneg _) (by positivity)
          _ = Real.sqrt 2 * max C₀ 1 * Real.sqrt (d / R) := by ring

end MatedCRT.BrownianBeurling
