import HarmonicBalls.Defs.Obstacle

/-!
# The cluster identity behind `FixedTimeRadiusStep` (Lemma 1, eqs. (5)-(6))

Pure topology plus the obstacle definitions of `HarmonicBalls.Defs.Obstacle`. For a set `K ⊆ ℂ` with `K \ {0}` open
and `Λ = int cl K`, the containment `Λ ⊆ B̄_n` (integer `n ≥ 0`) is decided by the Gaussian rational points of `K`
outside `B̄_n`. Applied to the cluster `Λ_{B_ρ;0}(u)` of Armitage-Gardiner's obstacle problem (HarmonicBalls.cluster), this
is the deterministic step of the containment event; no measure theory and no paper-specific input enter here.
-/

namespace MatedCRT

open Set Metric Complex Topology HarmonicBalls MeasureTheory

/-- The Gaussian rationals `ℚ(i) = {a + b i : a, b ∈ ℚ}`, a countable dense subset of `ℂ`. -/
def ratComplex : Set ℂ := Set.range fun q : ℚ × ℚ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

/-- Every nonempty open subset of `ℂ` contains a Gaussian rational point. -/
theorem ratComplex_meets_open {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ p ∈ ratComplex, p ∈ U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x.re - ε / 2 < x.re + ε / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x.im - ε / 2 < x.im + ε / 2 by linarith)
  refine ⟨(a : ℂ) + (b : ℂ) * Complex.I, ⟨(a, b), rfl⟩, hball (mem_ball.2 ?_)⟩
  rw [dist_eq_norm]
  have hre : ((a : ℂ) + (b : ℂ) * Complex.I - x).re = (a : ℝ) - x.re := by simp
  have him : ((a : ℂ) + (b : ℂ) * Complex.I - x).im = (b : ℝ) - x.im := by simp
  calc ‖(a : ℂ) + (b : ℂ) * Complex.I - x‖
      ≤ |((a : ℂ) + (b : ℂ) * Complex.I - x).re| + |((a : ℂ) + (b : ℂ) * Complex.I - x).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |(a : ℝ) - x.re| + |(b : ℝ) - x.im| := by rw [hre, him]
    _ < ε := by
        have h1 : |(a : ℝ) - x.re| < ε / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
        have h2 : |(b : ℝ) - x.im| < ε / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
        linarith

/-- Containment of the interior of a closure in a closed ball, decided on the Gaussian rational points of `K` outside
the ball: `int cl K ⊆ B̄_n` iff no rational point of `K` has modulus `> n`, when `K \ {0}` is open. -/
theorem interior_closure_subset_closedBall_iff {K : Set ℂ} {n : ℕ} (hK : IsOpen (K \ {0})) :
    interior (closure K) ⊆ closedBall (0 : ℂ) n ↔ ∀ p ∈ ratComplex, (n : ℝ) < ‖p‖ → p ∉ K := by
  constructor
  · intro hsub p hp hn hpK
    have hp0 : p ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact absurd hn (not_lt.2 (Nat.cast_nonneg n))
    have h1 : p ∈ interior (K \ {0}) := by
      rw [hK.interior_eq]
      exact ⟨hpK, hp0⟩
    have hint : p ∈ interior K := interior_mono sdiff_subset h1
    have hmem : p ∈ interior (closure K) := interior_mono subset_closure hint
    have hle := hsub hmem
    rw [mem_closedBall_zero_iff] at hle
    linarith
  · intro hpts
    have hKsub : K ⊆ closedBall (0 : ℂ) n := by
      intro x hxK
      by_contra hx
      rw [mem_closedBall_zero_iff, not_le] at hx
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hx
        exact absurd hx (not_lt.2 (Nat.cast_nonneg n))
      have hO : IsOpen ((K \ {0}) ∩ {y : ℂ | (n : ℝ) < ‖y‖}) :=
        hK.inter (isOpen_lt continuous_const continuous_norm)
      obtain ⟨p, hpR, hpO⟩ := ratComplex_meets_open hO ⟨x, ⟨hxK, hx0⟩, hx⟩
      exact hpts p hpR hpO.2 hpO.1.1
    intro y hy
    exact closure_minimal hKsub isClosed_closedBall (interior_subset hy)

/-- The cluster `Λ_{B_ρ;0}(u)` of the obstacle problem, minus the pole, is open when the least supersolution is
continuous on the closed disc and the disc Green function `G_{B_ρ}(0,·)` is continuous off the pole
(Armitage-Gardiner, Green functions of a disc; the cluster is the set where `v > -uG`). -/
theorem isOpen_cluster_diff_pole (μ : Measure ℂ) {ρ u : ℝ}
    (hv : ContinuousOn (leastSupersolution μ ρ 0 u) (closedBall 0 ρ))
    (hG : ContinuousOn (greenFunction (ball 0 ρ) 0) (ball 0 ρ \ {0})) :
    IsOpen (cluster μ ρ 0 u \ {0}) := by
  have hv' : ContinuousOn (leastSupersolution μ ρ 0 u) (ball 0 ρ \ {0}) :=
    hv.mono fun x hx => ball_subset_closedBall hx.1
  have hcont : ContinuousOn (fun x => leastSupersolution μ ρ 0 u x + u * greenFunction (ball 0 ρ) 0 x)
      (ball 0 ρ \ {0}) :=
    hv'.add (continuousOn_const.mul hG)
  have hset : cluster μ ρ 0 u \ {0} =
      (ball 0 ρ \ {0}) ∩ (fun x => leastSupersolution μ ρ 0 u x + u * greenFunction (ball 0 ρ) 0 x) ⁻¹' Ioi 0 := by
    ext x
    constructor
    · rintro ⟨⟨hb, hcase⟩, hne⟩
      rcases hcase with hx | hlt
      · exact absurd hx hne
      · refine ⟨⟨hb, hne⟩, ?_⟩
        show (0 : ℝ) < leastSupersolution μ ρ 0 u x + u * greenFunction (ball 0 ρ) 0 x
        linarith
    · rintro ⟨⟨hb, hne⟩, hpos⟩
      refine ⟨⟨hb, Or.inr ?_⟩, hne⟩
      have hpos' : (0 : ℝ) < leastSupersolution μ ρ 0 u x + u * greenFunction (ball 0 ρ) 0 x := hpos
      linarith
  rw [hset]
  exact hcont.isOpen_inter_preimage (isOpen_ball.sdiff isClosed_singleton) isOpen_Ioi

/-- Deterministic containment for the obstacle cluster at radius `ρ`: its interior closure lies in `B̄_n` iff no
Gaussian rational point of the cluster has modulus `> n`. -/
theorem interior_cluster_subset_closedBall_iff (μ : Measure ℂ) {ρ u : ℝ} (n : ℕ)
    (hv : ContinuousOn (leastSupersolution μ ρ 0 u) (closedBall 0 ρ))
    (hG : ContinuousOn (greenFunction (ball 0 ρ) 0) (ball 0 ρ \ {0})) :
    interior (closure (cluster μ ρ 0 u)) ⊆ closedBall (0 : ℂ) n ↔
      ∀ p ∈ ratComplex, (n : ℝ) < ‖p‖ → p ∉ cluster μ ρ 0 u :=
  interior_closure_subset_closedBall_iff (isOpen_cluster_diff_pole μ hv hG)

end MatedCRT
