import HarmonicBalls.Defs.Obstacle

/-!
# FIRST PASS, Lemma 5.3: pointwise limit of the rescaled obstacle (G-5-3 note, Section 1, eq. (4))

For a fixed point `x ≠ 0` of the disk, the least supersolution at mass `s` equals the obstacle `-s G_{B_r}(0, ·)`
at `x` as soon as `x` lies outside the open cluster at mass `s` (the least supersolution is `≥` the obstacle,
and `≤` it off the cluster). Since the harmonic balls `Λ_s` decrease to `{0}` as `s ↓ 0`, the rescaled
`R_n(x) = -w_{s_n}(x)/s_n` equals `G_{B_ρ}(0, x)` for all large `n` (G-5-3 eq. (4)). Potential theory of the
harmonic-balls package only (Armitage-Gardiner obstacle problem; Armstrong-Kuusi-Mourrat least supersolutions).
Inputs are hypotheses about the realized family: openness of the cluster (Harmonic-Balls Draft `ClusterOpenLaplacianStmt`),
the regular-open identity `Λ_s = interior (closure (cluster μ ρ 0 s))`, monotonicity in `s`, and `⋂ Λ_s = {0}`
(`SatisfiesHarmonicBallConditions`, Harmonic-Balls Draft Section 1).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open _root_.HarmonicBalls

/-- Off the open cluster, at a point `x ≠ z` of the disk, the least supersolution equals the obstacle
`-s G_{B_r}(z, x)` (G-5-3 Section 1; Harmonic-Balls Defs/Obstacle.lean `supersolutions`, `cluster`). -/
lemma leastSupersolution_eq_obstacle_of_not_mem_cluster {μ : Measure ℂ} {r s : ℝ} (hs : 0 ≤ s)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) r) (hx0 : x ≠ 0) (hnot : x ∉ cluster μ r 0 s) :
    leastSupersolution μ r 0 s x = -s * greenFunction (ball 0 r) 0 x := by
  apply le_antisymm
  · have hnot' : ¬ (-s * greenFunction (ball 0 r) 0 x < leastSupersolution μ r 0 s x) :=
      fun h => hnot ⟨hx, Or.inr h⟩
    exact not_lt.1 hnot'
  · have hne : ((fun w : ℂ → ℝ => w x) '' supersolutions μ r 0 s).Nonempty :=
      ⟨(fun w : ℂ → ℝ => w x) 0, Set.mem_image_of_mem _ (zero_mem_supersolutions μ r 0 hs)⟩
    show -s * greenFunction (ball 0 r) 0 x ≤ sInf ((fun w : ℂ → ℝ => w x) '' supersolutions μ r 0 s)
    refine le_csInf hne ?_
    rintro _ ⟨w, ⟨_, _, hob⟩, rfl⟩
    exact hob x (ball_subset_closedBall hx) hx0

/-- **Eq. (4), pointwise** (G-5-3 Section 1): for `x ≠ 0` in the disk `B_ρ` with `x` outside the cluster of some
mass `s₀ > 0`, the rescaled obstacle `R_n(x) = -w_{s_n}(x) / s_n` with `s_n = t (1/2)^n` equals `G_{B_ρ}(0, x)` for
all large `n`. Hypotheses: the cluster is open at each positive mass (`ClusterOpenLaplacianStmt`), `Λ_s` is its
regular open interior for `0 < s ≤ t`, and `Λ` is monotone in the mass. -/
theorem eventually_leastSupersolution_eq_neg_green {μ : Measure ℂ} {ρ t : ℝ} (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hopen : ∀ s : ℝ, 0 < s → IsOpen (cluster μ ρ 0 s))
    (hΛ : ∀ s : ℝ, 0 < s → s ≤ t → Λ s = interior (closure (cluster μ ρ 0 s)))
    (hmono : ∀ s u : ℝ, 0 < s → s ≤ u → Λ s ⊆ Λ u)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) ρ) (hx0 : x ≠ 0) (s₀ : ℝ) (hs₀ : 0 < s₀) (hxs₀ : x ∉ Λ s₀) :
    ∀ᶠ n : ℕ in atTop,
      leastSupersolution μ ρ 0 (t * (1 / 2) ^ n) x = -(t * (1 / 2) ^ n) * greenFunction (ball 0 ρ) 0 x := by
  have hlim : Tendsto (fun n : ℕ => t * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul t
    simpa using h
  filter_upwards [hlim.eventually (Iio_mem_nhds hs₀)] with n hn
  have hpos : 0 < t * (1 / 2 : ℝ) ^ n := by positivity
  have hle : t * (1 / 2 : ℝ) ^ n ≤ t :=
    mul_le_of_le_one_right ht.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hxnot : x ∉ Λ (t * (1 / 2) ^ n) := fun h => hxs₀ (hmono _ _ hpos hn.le h)
  have hsub : cluster μ ρ 0 (t * (1 / 2) ^ n) ⊆ Λ (t * (1 / 2) ^ n) := by
    rw [hΛ _ hpos hle]
    exact interior_maximal subset_closure (hopen _ hpos)
  exact leastSupersolution_eq_obstacle_of_not_mem_cluster hpos.le hx hx0 fun h => hxnot (hsub h)

/-- **Strict surplus at `x ∈ Λ_t \ {0}`** (G-5-3 Section 1, eq. (5) pointwise): if `x ≠ 0` lies in the unregularized
cluster at mass `t` (the strict obstacle gap, the harmonic ball `Λ_t` is contained in `cluster μ ρ 0 t`), then
`A_n(x) = w_t(x) + t R_n(x)` is eventually equal to `w_t(x) + t G(0, x) > 0`. -/
theorem eventually_pos_surplus_of_mem_cluster {μ : Measure ℂ} {ρ t : ℝ} (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hopen : ∀ s : ℝ, 0 < s → IsOpen (cluster μ ρ 0 s))
    (hΛ : ∀ s : ℝ, 0 < s → s ≤ t → Λ s = interior (closure (cluster μ ρ 0 s)))
    (hmono : ∀ s u : ℝ, 0 < s → s ≤ u → Λ s ⊆ Λ u)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) ρ) (hx0 : x ≠ 0) (hgap : x ∈ cluster μ ρ 0 t)
    (s₀ : ℝ) (hs₀ : 0 < s₀) (hxs₀ : x ∉ Λ s₀) :
    ∀ᶠ n : ℕ in atTop, 0 < leastSupersolution μ ρ 0 t x +
      t * (-(leastSupersolution μ ρ 0 (t * (1 / 2) ^ n) x) / (t * (1 / 2) ^ n)) := by
  have hpos : ∀ n : ℕ, 0 < t * (1 / 2 : ℝ) ^ n := fun n => by positivity
  filter_upwards [eventually_leastSupersolution_eq_neg_green ht hopen hΛ hmono hx hx0 s₀ hs₀ hxs₀] with n hn
  rw [hn]
  have hgap' : -t * greenFunction (ball 0 ρ) 0 x < leastSupersolution μ ρ 0 t x := by
    rcases hgap with ⟨_, h | h⟩
    · exact absurd h hx0
    · exact h
  have hne : (t * (1 / 2 : ℝ) ^ n) ≠ 0 := (hpos n).ne'
  have hcalc : t * (-(-(t * (1 / 2 : ℝ) ^ n) * greenFunction (ball 0 ρ) 0 x) / (t * (1 / 2 : ℝ) ^ n))
      = t * greenFunction (ball 0 ρ) 0 x := by
    field_simp
  rw [hcalc]
  linarith

end MatedCRT.S5c
