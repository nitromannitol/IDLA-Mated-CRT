import MatedCRT.FirstPass.Derived.GMS21AnnulusHoleBound
import MatedCRT.FirstPass.Derived.GMS21RestartStrongMarkov
import MatedCRT.FirstPass.Derived.BrownianClassLawContinuity

/-!
# From the annulus to the ball, for every starting point

In the proof of Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, case 1, the comparison of the embedded walk
with Brownian motion is transferred from the `0`-quantum cone to the `γ`-quantum cone on annuli
`B_R(0) \ closedBall 0 α` that avoid the origin. This file proves the deterministic step from the annulus to the
ball `B_R(0)`, for every starting point `z ∈ closedBall 0 ρ`:

* for `z` away from the origin, Brownian motion from `z` rarely hits the small hole `closedBall 0 α` before it leaves
  `B_R(0)`, so the curve classes stopped at the exits from the annulus and from the ball are close
  (`GMS21AnnulusHoleBound`);
* for `z` near the origin, the walk is restarted at its first vertex outside `B_b(0)` by the strong Markov property
  (`GMS21RestartStrongMarkov`), and the law of the stopped Brownian class is continuous in the starting point
  (`BrownianClassLawContinuity`).

The walk is given by edge multiplicities `m`, embedded positions `p` and cells `cell x ∋ p x`; the hypotheses are the
annulus comparison, edges of length at most `L` from `closedBall 0 (b + L)`, cells meeting `B_b(0)` within distance
`L` of their points, and the almost sure exit of the walk from `B_b(0)`.

## Main results

* `annulusHoleError`: the error term of the passage from the annulus to the ball.
* `levyProkhorovEDist_walk_ball_le_of_annulus`: starts outside `B_b(0)`.
* `levyProkhorovEDist_walk_ball_le_of_shell`: walks from vertices of the shell `closedBall 0 (b + 2 L) \ B_b(0)`,
  against Brownian motion from a point of `closedBall 0 (b + 2 L)`.
* `levyProkhorovEDist_walk_ball_le_of_annulus_restart`: every start `z ∈ closedBall 0 ρ`.
* `exists_ballOfAnnulus_parameters`: a choice of the parameters making the total error less than `κ`.
* `exists_forall_levyProkhorovEDist_walk_ball_lt`: for all `R, κ > 0` there are `α, b, L, c > 0` such that the
  annulus comparison at precision `c` and the mesh conditions at scale `(b, L)` give the comparison on the ball at
  precision `κ` for every start.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open StopAtExitLevyProkhorov

/-- The error of the passage from the annulus `B_R(0) \ closedBall 0 α` to the ball `B_R(0)` for starts outside
`B_b(0)`, at annulus precision `c`, with the auxiliary radius `r` (`α + c ≤ r < b`):
`c + (L r + c) + L α`, where `L x = log (R / b) / log (R / x)` bounds the probability that Brownian motion from a
point outside `B_b(0)` hits `closedBall 0 x` before it leaves `B_R(0)`. -/
noncomputable def annulusHoleError (α r b R : ℝ) (c : ℝ≥0∞) : ℝ≥0∞ :=
  c + (ENNReal.ofReal (Real.log R - Real.log b) / ENNReal.ofReal (Real.log R - Real.log r) + c) +
    ENNReal.ofReal (Real.log R - Real.log b) / ENNReal.ofReal (Real.log R - Real.log α)

section Ball

variable {m : ℤ → ℤ → ℕ} {p : ℤ → ℂ}

/-- **Starts outside `B_b(0)`.** If the laws of the curve classes of the walk from `x` and of Brownian motion from
`z ∉ B_b(0)`, stopped at their exits from the annulus `B_R(0) \ closedBall 0 α`, are at Lévy–Prokhorov distance less
than `c`, then the laws stopped at their exits from `B_R(0)` are at distance at most `annulusHoleError α r b R c`. -/
theorem levyProkhorovEDist_walk_ball_le_of_annulus {α r b R : ℝ} (hα : 0 < α) (hr : 0 < r) (hrb : r < b)
    (hbR : b < R) {c : ℝ≥0∞} (hαc : α + c.toReal ≤ r) {x : ℤ} {z : ℂ} (hz : z ∉ ball (0 : ℂ) b)
    (hc : levyProkhorovEDist ((srwLaw m x).map fun w =>
        stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (interpPathCM p zero_le_one w))
      ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α))) < c) :
    levyProkhorovEDist ((srwLaw m x).map fun w =>
        stoppedExitCurve (ball (0 : ℂ) R) (interpPathCM p zero_le_one w))
      ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R))) ≤ annulusHoleError α r b R c :=
  levyProkhorovEDist_stoppedExitCurve_le_of_annulus (srwLaw m x)
    (measurable_interpPathCM p zero_le_one).aemeasurable isOpen_ball hα hr hrb hbR subset_rfl
    (closedBall_subset_ball (hrb.trans hbR)) hz hαc hc

/-- **Walks from the shell.** Under the annulus comparison at precision `c` for all starts
`z ∈ closedBall 0 ρ \ B_b(0)` and all cells containing them, and with `β` bounding the distance between the stopped
Brownian class laws from the points of `closedBall 0 (b + 2 L)` and from `0`, the walk from a vertex `y` with
`p y ∈ closedBall 0 (b + 2 L) \ B_b(0)` is within `annulusHoleError α r b R c + 2 β` of Brownian motion from any
`z ∈ closedBall 0 (b + 2 L)`. -/
theorem levyProkhorovEDist_walk_ball_le_of_shell {cell : ℤ → Set ℂ} (hpc : ∀ x, p x ∈ cell x)
    {α r b R L ρ : ℝ} (hα : 0 < α) (hr : 0 < r) (hrb : r < b) (hbR : b < R) {c β : ℝ≥0∞}
    (hαc : α + c.toReal ≤ r) (hρ : b + 2 * L ≤ ρ)
    (hann : ∀ z, z ∉ ball (0 : ℂ) b → z ∈ closedBall (0 : ℂ) ρ → ∀ x, z ∈ cell x →
      levyProkhorovEDist ((srwLaw m x).map fun w =>
          stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (interpPathCM p zero_le_one w))
        ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α))) < c)
    (hβ : ∀ u ∈ closedBall (0 : ℂ) (b + 2 * L),
      levyProkhorovEDist ((planarBrownianMotion u).map (stoppedExitCurve (ball (0 : ℂ) R)))
        ((planarBrownianMotion 0).map (stoppedExitCurve (ball (0 : ℂ) R))) ≤ β)
    {y : ℤ} (hy : p y ∉ ball (0 : ℂ) b) (hy' : p y ∈ closedBall (0 : ℂ) (b + 2 * L))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) (b + 2 * L)) :
    levyProkhorovEDist ((srwLaw m y).map fun w =>
        stoppedExitCurve (ball (0 : ℂ) R) (interpPathCM p zero_le_one w))
      ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R))) ≤
      annulusHoleError α r b R c + 2 * β := by
  have h1 := levyProkhorovEDist_walk_ball_le_of_annulus hα hr hrb hbR hαc hy
    (hann (p y) hy (closedBall_subset_closedBall hρ hy') y (hpc y))
  have h2 := hβ (p y) hy'
  have h3 : levyProkhorovEDist ((planarBrownianMotion 0).map (stoppedExitCurve (ball (0 : ℂ) R)))
      ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R))) ≤ β := by
    rw [levyProkhorovEDist_comm]
    exact hβ z hz
  refine (levyProkhorovEDist_triangle _
    ((planarBrownianMotion (p y)).map (stoppedExitCurve (ball (0 : ℂ) R))) _).trans ?_
  refine (add_le_add h1 (levyProkhorovEDist_triangle _
    ((planarBrownianMotion 0).map (stoppedExitCurve (ball (0 : ℂ) R))) _)).trans ?_
  rw [two_mul]
  exact add_le_add le_rfl (add_le_add h2 h3)

/-- **Every start in `closedBall 0 ρ`** (Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of Theorem 3.4, case 1).
Let the cells `cell x ∋ p x` meeting `B_b(0)` lie within distance `L` of their points, let the edges of `m` from
`closedBall 0 (b + L)` have embedded length at most `L`, let the walk from every vertex of `B_b(0)` leave `B_b(0)`
almost surely, and let the annulus comparison hold at precision `c` for all starts
`z ∈ closedBall 0 ρ \ B_b(0)`, `ρ ≥ b + 2 L`, and all cells containing them. Then for every `z ∈ closedBall 0 ρ` and
every cell `cell x ∋ z`, the laws of the curve classes of the walk from `x` and of Brownian motion from `z`, stopped
at their exits from `B_R(0)`, are at Lévy–Prokhorov distance at most
`annulusHoleError α r b R c + 2 β + 2 (b + 2 L)`. -/
theorem levyProkhorovEDist_walk_ball_le_of_annulus_restart {cell : ℤ → Set ℂ} (hpc : ∀ x, p x ∈ cell x)
    {α r b R L ρ : ℝ} (hα : 0 < α) (hr : 0 < r) (hrb : r < b) (hL : 0 ≤ L) (hbLR : b + 2 * L < R)
    (hstep : ∀ x y, p x ∈ closedBall (0 : ℂ) (b + L) → m x y ≠ 0 → dist (p x) (p y) ≤ L)
    (hdiam : ∀ x z, z ∈ cell x → z ∈ ball (0 : ℂ) b → dist (p x) z ≤ L)
    (hτ : ∀ a, p a ∈ ball (0 : ℂ) b → ∀ᵐ w ∂srwLaw m a, ballExitIndex p b w ≠ ⊤)
    {c β : ℝ≥0∞} (hαc : α + c.toReal ≤ r) (hρ : b + 2 * L ≤ ρ)
    (hann : ∀ z, z ∉ ball (0 : ℂ) b → z ∈ closedBall (0 : ℂ) ρ → ∀ x, z ∈ cell x →
      levyProkhorovEDist ((srwLaw m x).map fun w =>
          stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (interpPathCM p zero_le_one w))
        ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α))) < c)
    (hβ : ∀ u ∈ closedBall (0 : ℂ) (b + 2 * L),
      levyProkhorovEDist ((planarBrownianMotion u).map (stoppedExitCurve (ball (0 : ℂ) R)))
        ((planarBrownianMotion 0).map (stoppedExitCurve (ball (0 : ℂ) R))) ≤ β)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) ρ) {x : ℤ} (hx : z ∈ cell x) :
    levyProkhorovEDist ((srwLaw m x).map fun w =>
        stoppedExitCurve (ball (0 : ℂ) R) (interpPathCM p zero_le_one w))
      ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R))) ≤
      annulusHoleError α r b R c + 2 * β + ENNReal.ofReal (2 * (b + 2 * L)) := by
  have hbR : b < R := by linarith
  by_cases hzb : z ∈ ball (0 : ℂ) b
  · have hz0 : ‖z‖ < b := mem_ball_zero_iff.1 hzb
    have hzc : z ∈ closedBall (0 : ℂ) (b + 2 * L) := mem_closedBall_zero_iff.2 (by linarith)
    by_cases hpb : p x ∈ ball (0 : ℂ) b
    · exact levyProkhorovEDist_restart_le hL hstep isOpen_ball (closedBall_subset_ball hbLR) hpb (hτ x hpb)
        ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R)))
        (fun y hy hy' => levyProkhorovEDist_walk_ball_le_of_shell hpc hα hr hrb hbR hαc hρ hann hβ hy hy' hzc)
    · have hxz : ‖p x - z‖ ≤ L := by
        rw [← dist_eq_norm]
        exact hdiam x z hx hzb
      have hpx : p x ∈ closedBall (0 : ℂ) (b + 2 * L) := by
        rw [mem_closedBall_zero_iff]
        have := norm_sub_norm_le (p x) z
        linarith
      exact (levyProkhorovEDist_walk_ball_le_of_shell hpc hα hr hrb hbR hαc hρ hann hβ hpb hpx hzc).trans
        le_self_add
  · exact (levyProkhorovEDist_walk_ball_le_of_annulus hα hr hrb hbR hαc hzb (hann z hzb hz x hx)).trans
      (le_self_add.trans le_self_add)

end Ball

/-- **Choice of the parameters.** For `R, κ > 0` there are radii `0 < α < r < b`, a mesh `L > 0` with
`b + 2 L < R`, an annulus precision `c > 0` with `α + c ≤ r`, and a bound `β` for the distance between the stopped
Brownian class laws from the points of `closedBall 0 (b + 2 L)` and from `0`, such that
`annulusHoleError α r b R c + 2 β + 2 (b + 2 L) < κ`. -/
theorem exists_ballOfAnnulus_parameters {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ) :
    ∃ α r b L c : ℝ, 0 < α ∧ 0 < r ∧ r < b ∧ 0 < L ∧ b + 2 * L < R ∧ 0 < c ∧ α + c ≤ r ∧
      ∃ β : ℝ≥0∞, (∀ u ∈ closedBall (0 : ℂ) (b + 2 * L),
          levyProkhorovEDist ((planarBrownianMotion u).map (stoppedExitCurve (ball (0 : ℂ) R)))
            ((planarBrownianMotion 0).map (stoppedExitCurve (ball (0 : ℂ) R))) ≤ β) ∧
        annulusHoleError α r b R (ENNReal.ofReal c) + 2 * β + ENNReal.ofReal (2 * (b + 2 * L)) <
          ENNReal.ofReal κ := by
  set q : ℝ := κ / 16 with hq
  have hq0 : 0 < q := by positivity
  obtain ⟨s, hs, hsB⟩ :=
    BrownianClassLawContinuity.exists_levyProkhorovDist_planarBrownianMotion_stoppedExitCurve_lt
      (R := R) (z := 0) (mem_ball_self hR) hq0
  set t : ℝ := min s (min R q) / 4 with ht
  have ht0 : 0 < t := div_pos (lt_min hs (lt_min hR hq0)) (by norm_num)
  have h1 : min s (min R q) ≤ s := min_le_left _ _
  have h2 : min s (min R q) ≤ R := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : min s (min R q) ≤ q := (min_le_right _ _).trans (min_le_right _ _)
  have htR : t < R := by linarith
  set D : ℝ := Real.log R - Real.log t with hD
  have hD0 : 0 < D := by
    have := Real.log_lt_log ht0 htR
    linarith
  set K : ℝ := 1 / q + 1 with hK
  have hK1 : 1 < K := by
    have : 0 < 1 / q := by positivity
    linarith
  have hK0 : 0 < K := by linarith
  set r : ℝ := R * Real.exp (-(K * D)) with hr
  have hr0 : 0 < r := mul_pos hR (Real.exp_pos _)
  have hlogr : Real.log r = Real.log R - K * D := by
    rw [hr, Real.log_mul hR.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hrt : r < t := by
    rw [← Real.log_lt_log_iff hr0 ht0, hlogr]
    have : (K - 1) * D = K * D - D := by ring
    have := mul_pos (sub_pos.2 hK1) hD0
    linarith
  have hα0 : 0 < r / 2 := by positivity
  have hαr : r / 2 ≤ r := by linarith
  set Q : ℝ≥0∞ := ENNReal.ofReal q with hQ
  have hc : ENNReal.ofReal (r / 2) ≤ Q := ENNReal.ofReal_le_ofReal (by linarith)
  have hAr : ENNReal.ofReal (Real.log R - Real.log t) / ENNReal.ofReal (Real.log R - Real.log r) ≤ Q := by
    have hRr : Real.log R - Real.log r = K * D := by rw [hlogr]; ring
    rw [hRr, ← hD, ← ENNReal.ofReal_div_of_pos (mul_pos hK0 hD0)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hKD : D / (K * D) = 1 / K := by field_simp
    rw [hKD]
    have hqK : 1 / q ≤ K := by linarith
    calc 1 / K ≤ 1 / (1 / q) := one_div_le_one_div_of_le (by positivity) hqK
      _ = q := one_div_one_div q
  have hAα : ENNReal.ofReal (Real.log R - Real.log t) / ENNReal.ofReal (Real.log R - Real.log (r / 2)) ≤ Q := by
    refine le_trans (ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal ?_) _) hAr
    have := Real.log_le_log hα0 hαr
    linarith
  refine ⟨r / 2, r, t, t, r / 2, hα0, hr0, hrt, ht0, by linarith, hα0, by linarith, Q, ?_, ?_⟩
  · intro u hu
    have hu' : dist u 0 < s := by
      rw [dist_zero_right]
      have := mem_closedBall_zero_iff.1 hu
      linarith
    have h := hsB u hu'
    rw [← ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h.le
  · have hE : annulusHoleError (r / 2) r t R (ENNReal.ofReal (r / 2)) ≤ Q + (Q + Q) + Q :=
      add_le_add (add_le_add hc (add_le_add hAr hc)) hAα
    have hlast : ENNReal.ofReal (2 * (t + 2 * t)) ≤ 2 * Q := by
      rw [hQ, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hsum : Q + (Q + Q) + Q + 2 * Q + 2 * Q = ENNReal.ofReal (8 * q) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← hQ]
      ring
    calc annulusHoleError (r / 2) r t R (ENNReal.ofReal (r / 2)) + 2 * Q + ENNReal.ofReal (2 * (t + 2 * t))
        ≤ Q + (Q + Q) + Q + 2 * Q + 2 * Q := add_le_add (add_le_add hE le_rfl) hlast
      _ = ENNReal.ofReal (8 * q) := hsum
      _ < ENNReal.ofReal κ := (ENNReal.ofReal_lt_ofReal_iff hκ).2 (by linarith)

/-- **From the annulus to the ball, with explicit parameters.** For `R, κ > 0` there are `α, b, L, c > 0` with
`α < b` and `b + 2 L < R` such that, for every walk (edge multiplicities `m`, embedded positions `p`, cells `cell x ∋ p x`) and
every `ρ ≥ b + 2 L`: if the edges from `closedBall 0 (b + L)` have embedded length at most `L`, the cells meeting
`B_b(0)` lie within distance `L` of their points, the walk from every vertex of `B_b(0)` leaves `B_b(0)` almost
surely, and the laws of the curve classes of the walk and of Brownian motion stopped at their exits from the annulus
`B_R(0) \ closedBall 0 α` are at Lévy–Prokhorov distance less than `c` for all starts `z ∈ closedBall 0 ρ \ B_b(0)`
and all cells containing them, then the laws stopped at their exits from `B_R(0)` are at distance less than `κ` for
all starts `z ∈ closedBall 0 ρ` and all cells containing them. -/
theorem exists_forall_levyProkhorovEDist_walk_ball_lt {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ) :
    ∃ α b L c : ℝ, 0 < α ∧ α < b ∧ 0 < L ∧ b + 2 * L < R ∧ 0 < c ∧
      ∀ (m : ℤ → ℤ → ℕ) (p : ℤ → ℂ) (cell : ℤ → Set ℂ) (ρ : ℝ), (∀ x, p x ∈ cell x) →
        (∀ x y, p x ∈ closedBall (0 : ℂ) (b + L) → m x y ≠ 0 → dist (p x) (p y) ≤ L) →
        (∀ x z, z ∈ cell x → z ∈ ball (0 : ℂ) b → dist (p x) z ≤ L) →
        (∀ a, p a ∈ ball (0 : ℂ) b → ∀ᵐ w ∂srwLaw m a, ballExitIndex p b w ≠ ⊤) →
        b + 2 * L ≤ ρ →
        (∀ z, z ∉ ball (0 : ℂ) b → z ∈ closedBall (0 : ℂ) ρ → ∀ x, z ∈ cell x →
          levyProkhorovEDist ((srwLaw m x).map fun w =>
              stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (interpPathCM p zero_le_one w))
            ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α))) <
            ENNReal.ofReal c) →
        ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ x, z ∈ cell x →
          levyProkhorovEDist ((srwLaw m x).map fun w =>
              stoppedExitCurve (ball (0 : ℂ) R) (interpPathCM p zero_le_one w))
            ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R))) < ENNReal.ofReal κ := by
  obtain ⟨α, r, b, L, c, hα, hr, hrb, hL, hbLR, hc, hαc, β, hβ, hlt⟩ := exists_ballOfAnnulus_parameters hR hκ
  refine ⟨α, b, L, c, hα, by linarith, hL, hbLR, hc, ?_⟩
  intro m p cell ρ hpc hstep hdiam hτ hρ hann z hz x hx
  have hαc' : α + (ENNReal.ofReal c).toReal ≤ r := by rw [ENNReal.toReal_ofReal hc.le]; exact hαc
  exact (levyProkhorovEDist_walk_ball_le_of_annulus_restart hpc hα hr hrb hL.le hbLR hstep hdiam hτ hαc' hρ hann
    hβ hz hx).trans_lt hlt

end MatedCRT
