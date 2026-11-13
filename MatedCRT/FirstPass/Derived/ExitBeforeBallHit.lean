import MatedCRT.FirstPass.Derived.SrwWalkLawBridge
import MatedCRT.FirstPass.S4S6c.TraceFrom68
import MatedCRT.FirstPass.S4S6c.WindowStop68
import MatedCRT.FirstPass.S6d.Core68
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15CTheorem39
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.WaypointWalk
import LatticeProb.Bonanno.MatedCRTHarmonic.WalkSteps.WalkPath

/-!
# The walk exits the ball before it hits the small circle (Berestycki–Gwynne (2020), Lemma 6.13, last assertion)

For `x ∈ V^ε(B_ρ \ B_{ρ-δ})` the walk on the mated-CRT map started at `x` exits `G^ε(B_ρ)` before hitting
`V^ε(∂B_{√δ}(η(x)))` with probability at least `1 - A δ^{ξ/2}`.

Proof (the argument of Gwynne–Miller–Sheffield (3.38), the good-event form of Lemma 3.11, in place of the printed
topological step): take `D = B_{ρ+δ}(0) ∩ B_{√δ}(z)` with `z = η(x)`, `t = √δ/2`.  The complement of `D` is connected,
`dist(z, ∂D) ≤ 3δ`, and `∂D ∩ B_t(z) ⊆ ∂B_{ρ+δ}(0)`.  Cells have diameter `≤ δ`, so a vertex whose cell meets
`∂D ∩ B_t(z)` has a cell outside `B_ρ` and inside `B_{√δ}(z)`, and every vertex visited before the first hit of
`V(∂D)` has its cell inside `D ⊆ B_{√δ}(z)`.  The first hit of `V(∂D)` therefore happens in `V(D) ∩ V(∂D ∩ B_t(z))`
with probability at least `1 - κ^ξ (t / max(dist(z, ∂D), ε^β))^{-ξ}`, and then the walk has exited `B_ρ` and has not hit
`V(∂B_{√δ}(z))`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitBeforeBallHit

open MeasureTheory Set Metric
open scoped ENNReal
open WindowStop68
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.GMSMain MatedCRTHarmonic.GMSMain.T15A

/-- A walk that stays in `Vd` until its first visit to `F` and whose first `F`-visit (at time `τ`) is outside `A` and
`B` exits `A` strictly before it hits `B`. -/
theorem vExitTime_lt_vHitTime_of_firstHit {X : ℕ → ℤ} {Vd F A B : Set ℤ} {τ : ℕ}
    (hX0 : X 0 ∈ Vd) (hstep : ∀ n, X n ∈ Vd → X n ∉ F → X (n + 1) ∈ Vd)
    (hB : ∀ v ∈ Vd, v ∉ F → v ∉ B) (hτ : ∀ j < τ, X j ∉ F)
    (hτA : X τ ∉ A) (hτB : X τ ∉ B) :
    vExitTime A X < vHitTime B X := by
  have hinv : ∀ n ≤ τ, X n ∈ Vd := by
    intro n
    induction n with
    | zero => intro _; exact hX0
    | succ k ih =>
      intro hk
      exact hstep k (ih (Nat.le_of_succ_le hk)) (hτ k (Nat.lt_of_succ_le hk))
  have h1 : (τ : ℕ∞) < vHitTime B X := by
    refine lt_vExitTime_of_forall (fun m hm => ?_)
    rcases hm.lt_or_eq with hlt | rfl
    · exact hB _ (hinv m hm) (hτ m hlt)
    · exact hτB
  have h2 : vExitTime A X ≤ τ := by
    by_contra h
    exact hτA (mem_of_lt_vExitTime (not_le.1 h))
  exact lt_of_le_of_lt h2 h1

/-- A connected set that meets an open set `D` but not its frontier lies in `D`. -/
theorem subset_of_preconnected_of_inter_frontier_eq_empty {c D : Set ℂ} (hDo : IsOpen D) (hc : IsPreconnected c)
    (h1 : (c ∩ D).Nonempty) (h2 : c ∩ frontier D = ∅) : c ⊆ D := by
  have hdisj : Disjoint D (closure D)ᶜ := disjoint_compl_right.mono_left subset_closure
  have hsub : c ⊆ D ∪ (closure D)ᶜ := by
    intro y hy
    by_cases hyc : y ∈ closure D
    · left
      by_contra hyD
      have : y ∈ c ∩ frontier D := ⟨hy, by rw [frontier, hDo.interior_eq]; exact ⟨hyc, hyD⟩⟩
      rw [h2] at this
      exact this
    · right; exact hyc
  rcases hc.subset_or_subset hDo isClosed_closure.isOpen_compl hdisj hsub with h | h
  · exact h
  · obtain ⟨y, hyc, hyD⟩ := h1
    exact absurd (subset_closure hyD) (h hyc)

/-- The complement of an open disc in the plane is preconnected. -/
theorem isPreconnected_compl_ball (a : ℂ) {r : ℝ} (hr : 0 < r) : IsPreconnected (ball a r)ᶜ := by
  have himg : (ball a r)ᶜ = (fun p : ℂ × ℝ => a + p.2 • (p.1 - a)) '' (sphere a r ×ˢ Ici (1 : ℝ)) := by
    ext y
    constructor
    · intro hy
      have hyr : r ≤ ‖y - a‖ := by
        rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] at hy
        exact hy
      have hd : 0 < ‖y - a‖ := lt_of_lt_of_le hr hyr
      refine ⟨(a + (r / ‖y - a‖) • (y - a), ‖y - a‖ / r), ⟨?_, ?_⟩, ?_⟩
      · rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos hr hd)]
        field_simp
      · exact (one_le_div hr).2 hyr
      · show a + (‖y - a‖ / r) • (a + (r / ‖y - a‖) • (y - a) - a) = y
        rw [add_sub_cancel_left, smul_smul, div_mul_div_comm, mul_comm r, div_self (by positivity), one_smul]
        abel
    · rintro ⟨⟨u, s⟩, ⟨hu, hs⟩, rfl⟩
      rw [mem_sphere, dist_eq_norm] at hu
      simp only [mem_Ici] at hs
      rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by linarith), hu]
      nlinarith
  rw [himg]
  have hconn : IsPreconnected (sphere a r) :=
    (isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) a hr.le).isPreconnected
  exact (hconn.prod isPreconnected_Ici).image _ (by fun_prop)

/-- The complement of the intersection of two discs of the plane is preconnected. -/
theorem isPreconnected_compl_ball_inter (a b : ℂ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    IsPreconnected (ball a r ∩ ball b s)ᶜ := by
  rw [compl_inter]
  refine IsPreconnected.union ((‖a‖ + ‖b‖ + r + s + 1 : ℝ) : ℂ) ?_ ?_ (isPreconnected_compl_ball a hr)
    (isPreconnected_compl_ball b hs)
  · rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt]
    have h1 := norm_sub_norm_le ((‖a‖ + ‖b‖ + r + s + 1 : ℝ) : ℂ) a
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
    linarith [norm_nonneg a, norm_nonneg b]
  · rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt]
    have h1 := norm_sub_norm_le ((‖a‖ + ‖b‖ + r + s + 1 : ℝ) : ℂ) b
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
    linarith [norm_nonneg a, norm_nonneg b]

/-- A point of the frontier of `B_R(0) ∩ B_s(z)` that is strictly inside `B_s(z)` has norm `R`. -/
theorem norm_eq_of_mem_frontier_inter_ball {R s : ℝ} (hs : 0 < s) {z q : ℂ}
    (hq : q ∈ frontier (ball (0 : ℂ) R ∩ ball z s)) (hqz : dist q z < s) : ‖q‖ = R := by
  rcases frontier_inter_subset (ball (0 : ℂ) R) (ball z s) hq with ⟨h1, _⟩ | ⟨_, h2⟩
  · by_cases hR : R = 0
    · subst hR
      simp only [ball_zero, frontier_empty] at h1
      exact h1.elim
    · rw [frontier_ball _ hR, mem_sphere_zero_iff_norm] at h1
      exact h1
  · rw [frontier_ball _ hs.ne', mem_sphere] at h2
    exact absurd h2 hqz.ne

/-- The radial projection of `z` to the sphere of radius `R` lies on the frontier of `B_R(0) ∩ B_s(z)`
when `0 < ‖z‖ < R` and `R - ‖z‖ < s`. -/
theorem exists_frontier_point_radial {R s : ℝ} {z : ℂ} (hz0 : z ≠ 0) (hzR : ‖z‖ < R)
    (hd : R - ‖z‖ < s) : ∃ q ∈ frontier (ball (0 : ℂ) R ∩ ball z s), dist z q ≤ R - ‖z‖ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hR : 0 < R := hzn.trans hzR
  set q : ℂ := ((R / ‖z‖ : ℝ) : ℂ) * z with hq
  have hqn : ‖q‖ = R := by
    rw [hq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hR hzn)]
    field_simp
  have hdq : dist q z = R - ‖z‖ := by
    have h1 : q - z = (((R - ‖z‖) / ‖z‖ : ℝ) : ℂ) * z := by
      have hzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hzn.ne'
      rw [hq]
      push_cast
      field_simp
    rw [dist_eq_norm, h1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (sub_pos.2 hzR) hzn)]
    field_simp
  have hcl : q ∈ closure (ball (0 : ℂ) R) := by
    rw [closure_ball _ hR.ne', mem_closedBall_zero_iff]
    exact hqn.le
  have hin : q ∈ ball z s := by
    rw [mem_ball, hdq]; exact hd
  have hq_cl : q ∈ closure (ball (0 : ℂ) R ∩ ball z s) := by
    have h1 : q ∈ closure (ball z s ∩ ball (0 : ℂ) R) :=
      (Metric.isOpen_ball : IsOpen (ball z s)).inter_closure ⟨hin, hcl⟩
    rwa [inter_comm] at h1
  refine ⟨q, ⟨hq_cl, ?_⟩, by rw [dist_comm]; exact hdq.le⟩
  rw [(Metric.isOpen_ball.inter Metric.isOpen_ball).interior_eq, mem_inter_iff, mem_ball_zero_iff, hqn]
  exact fun h => lt_irrefl _ h.1


/-- **Berestycki–Gwynne (2020), Lemma 6.13, last assertion, for the edge-end walk** (deterministic form).
On an environment where the disconnection events of Lemma 3.11 hold at ambient radius `ρ'` with floor `ε^β` and
success probability `p`, the cells of the vertices meeting `B_{ρ'}` have diameter `≤ δ ≤ min(1/16, ρ/4, (ρ'-ρ)/2)`
and `ε^β ≤ δ`: from every `x ∈ V^ε(B_ρ \ B_{ρ-δ})` the walk exits `V^ε(B_ρ)` before it hits
`V^ε(∂B_{√δ}(η(x)))` with probability at least `1 - A δ^{ξ/2}`, where `ξ = t15cXi p` and
`A = (6 · 8 (3ρ + 3 + ρ')/(ρ' - ρ))^ξ`. -/
theorem walkLaw_exit_before_ballHit
    {ε : ℝ} {η : ℝ → ℂ} {E : Type*} {G : LFMultigraph ℤ E} [Countable G.State]
    (hloop : ∀ e : E, G.src e ≠ G.tgt e)
    (H : CellularEmbedding G (0 : ℤ)) (hHc : H.cell = cell ε η)
    (hconn : G.adj.Connected) (hLC : H.PointConnected)
    {β p ρ ρ' δ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hp0 : 0 < p) (hp1 : p < 1)
    (h311 : Lemma311Holds H ε ρ' β p) (hδ0 : 0 < δ)
    (hδ : δ ≤ min (1 / 16) (min (ρ / 4) ((ρ' - ρ) / 2))) (hεβ : ε ^ β ≤ δ)
    (hdiam : ∀ k, (cell ε η k ∩ ball (0 : ℂ) ρ').Nonempty →
      ∀ a ∈ cell ε η k, ∀ b ∈ cell ε η k, dist a b ≤ δ)
    {x : ℤ} (hx : x ∈ cellVertices ε η (ball (0 : ℂ) ρ \ ball (0 : ℂ) (ρ - δ))) :
    ENNReal.ofReal (1 - (6 * (8 * (3 * ρ + 3 + ρ') / (ρ' - ρ))) ^ t15cXi p * δ ^ (t15cXi p / 2)) ≤
      G.walkLaw x
        (G.vertexPath ⁻¹'
          {X | vExitTime (cellVertices ε η (ball (0 : ℂ) ρ)) X <
            vHitTime (cellVertices ε η (frontier (ball (vertexPoint ε η x) (Real.sqrt δ)))) X}) := by
  classical
  have hδ1 : δ ≤ 1 / 16 := hδ.trans (min_le_left _ _)
  have hδρ : δ ≤ ρ / 4 := (hδ.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδρ' : δ ≤ (ρ' - ρ) / 2 := (hδ.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hρ'0 : 0 < ρ' := hρ.trans hρρ'
  have hcell : ∀ k, H.cell k = cell ε η k := fun k => congrFun hHc k
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt δ := ⟨_, rfl⟩
  rw [← hsdef]
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hδ0
  have hss : s * s = δ := by rw [hsdef]; exact Real.mul_self_sqrt hδ0.le
  have hs14 : s ≤ 1 / 4 := by nlinarith
  have hsδ : 4 * δ ≤ s := by nlinarith
  obtain ⟨z, hzdef⟩ : ∃ z : ℂ, z = vertexPoint ε η x := ⟨_, rfl⟩
  rw [← hzdef]
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ρ + δ := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hRdef]; linarith
  have hRρ' : R < ρ' := by rw [hRdef]; linarith
  obtain ⟨y₀, hy₀c, hy₀1, hy₀2⟩ := hx
  have hy₀n : ‖y₀‖ < ρ := by simpa using hy₀1
  have hy₀n2 : ρ - δ ≤ ‖y₀‖ := by
    by_contra h
    exact hy₀2 (by simpa using not_le.1 h)
  have hzc : z ∈ cell ε η x := hzdef ▸ vertexPoint_mem_cell_of_nonneg hε.le η x
  have hy₀z : dist y₀ z ≤ δ :=
    hdiam x ⟨y₀, hy₀c, mem_ball_zero_iff.2 (hy₀n.trans hρρ')⟩ y₀ hy₀c z hzc
  have hzn1 : ‖z‖ < R := by
    have h1 := norm_sub_norm_le z y₀
    have h2 : ‖z - y₀‖ ≤ δ := by rw [← dist_eq_norm, dist_comm]; exact hy₀z
    rw [hRdef]; linarith
  have hzn2 : R - 3 * δ ≤ ‖z‖ := by
    have h1 := norm_sub_norm_le y₀ z
    have h2 : ‖y₀ - z‖ ≤ δ := by rw [← dist_eq_norm]; exact hy₀z
    rw [hRdef]; linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzn2
    rw [hRdef] at hzn2
    linarith
  set D : Set ℂ := ball (0 : ℂ) R ∩ ball z s with hD
  have hDo : IsOpen D := isOpen_ball.inter isOpen_ball
  have hDR : D ⊆ ball (0 : ℂ) R := inter_subset_left
  have hDc : IsPreconnected Dᶜ := isPreconnected_compl_ball_inter 0 z hR0 hs0
  have hy₀D : y₀ ∈ D :=
    ⟨mem_ball_zero_iff.2 (by rw [hRdef]; linarith), by rw [mem_ball]; linarith⟩
  have hxD : (H.cell x ∩ D).Nonempty := ⟨y₀, by rw [hcell]; exact hy₀c, hy₀D⟩
  have hzx : z ∈ H.cell x := by rw [hcell]; exact hzc
  have ht : 0 < s / 2 := by positivity
  have key := t15c_hitDist_ge_of_lemma311Holds hconn hLC hε hR0 hRρ' hp0 hp1 h311 hDo hDR hDc hxD hzx ht
  -- the real-number bound
  have hξ : 0 < t15cXi p := t15cXi_pos hp0 hp1
  have hinf : infDist z (frontier D) ≤ 3 * δ := by
    obtain ⟨q, hq, hdq⟩ := exists_frontier_point_radial hz0 hzn1 (by linarith : R - ‖z‖ < s)
    exact (infDist_le_dist_of_mem hq).trans (hdq.trans (by linarith))
  have hm0 : 0 < max (infDist z (frontier D)) (ε ^ β) := lt_max_of_lt_right (Real.rpow_pos_of_pos hε β)
  have hm : max (infDist z (frontier D)) (ε ^ β) ≤ 3 * δ := max_le hinf (by linarith)
  have hratio : s / (6 * δ) ≤ (s / 2) / max (infDist z (frontier D)) (ε ^ β) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hs0.le (by positivity) (by linarith)
  have hne : ρ' - ρ ≠ 0 := ne_of_gt (sub_pos.2 hρρ')
  have hK0 : 0 ≤ 8 * (3 * ρ + 3 + ρ') / (ρ' - ρ) := div_nonneg (by positivity) (sub_pos.2 hρρ').le
  have hq_le : t15cKappa R ρ' ^ t15cXi p *
      ((s / 2) / max (infDist z (frontier D)) (ε ^ β)) ^ (-t15cXi p) ≤
      (6 * (8 * (3 * ρ + 3 + ρ') / (ρ' - ρ))) ^ t15cXi p * δ ^ (t15cXi p / 2) := by
    have hκ0 : 0 ≤ t15cKappa R ρ' := (t15cKappa_pos hR0 hRρ').le
    have hκK : t15cKappa R ρ' ≤ 8 * (3 * ρ + 3 + ρ') / (ρ' - ρ) := by
      unfold t15cKappa
      have h1 : 0 < ρ' - R := by linarith
      have h2 : (ρ' - ρ) / 2 ≤ ρ' - R := by rw [hRdef]; linarith
      have h3 : 3 * R + ρ' ≤ 3 * ρ + 3 + ρ' := by rw [hRdef]; linarith
      calc 4 * (3 * R + ρ') / (ρ' - R) ≤ 4 * (3 * ρ + 3 + ρ') / ((ρ' - ρ) / 2) :=
            div_le_div₀ (by positivity) (by linarith) (by linarith) h2
        _ = 8 * (3 * ρ + 3 + ρ') / (ρ' - ρ) := by field_simp; ring
    have h6 : ((s / 2) / max (infDist z (frontier D)) (ε ^ β)) ^ (-t15cXi p) ≤ (6 * s) ^ t15cXi p := by
      calc ((s / 2) / max (infDist z (frontier D)) (ε ^ β)) ^ (-t15cXi p)
          ≤ (s / (6 * δ)) ^ (-t15cXi p) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hratio (by linarith)
        _ = (6 * s) ^ t15cXi p := by
            rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
            congr 1
            rw [div_eq_iff hs0.ne', ← hss]
            ring
    have hsξ : s ^ t15cXi p = δ ^ (t15cXi p / 2) := by
      rw [hsdef, Real.sqrt_eq_rpow, ← Real.rpow_mul hδ0.le]
      congr 1
      ring
    calc t15cKappa R ρ' ^ t15cXi p * ((s / 2) / max (infDist z (frontier D)) (ε ^ β)) ^ (-t15cXi p)
        ≤ (8 * (3 * ρ + 3 + ρ') / (ρ' - ρ)) ^ t15cXi p * (6 * s) ^ t15cXi p :=
          mul_le_mul (Real.rpow_le_rpow hκ0 hκK hξ.le) h6
            (Real.rpow_nonneg (div_nonneg (by positivity) hm0.le) _) (Real.rpow_nonneg hK0 _)
      _ = (6 * (8 * (3 * ρ + 3 + ρ') / (ρ' - ρ))) ^ t15cXi p * δ ^ (t15cXi p / 2) := by
          rw [Real.mul_rpow (by norm_num) hK0, Real.mul_rpow (by norm_num) hs0.le, hsξ]
          ring
  have hmono : ENNReal.ofReal (1 - (6 * (8 * (3 * ρ + 3 + ρ') / (ρ' - ρ))) ^ t15cXi p * δ ^ (t15cXi p / 2)) ≤
      ENNReal.ofReal (1 - t15cKappa R ρ' ^ t15cXi p *
        ((s / 2) / max (infDist z (frontier D)) (ε ^ β)) ^ (-t15cXi p)) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  refine hmono.trans (key.trans ?_)
  -- the event inclusion
  set I : Set ℤ := verticesMeeting H.cell (frontier D) with hI
  set W : Set ℤ := verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z (s / 2)) with hW
  have hhit : hitDist G I x W = G.walkLaw x {ξ | Markov.hitTime I (G.vertexPath ξ) ≠ ⊤ ∧
      G.vertexPath ξ (Markov.hitTime I (G.vertexPath ξ)).toNat ∈ W} := rfl
  rw [hhit]
  have hint : ∀ v, v ∈ verticesMeeting H.cell D → v ∉ I → H.cell v ⊆ D := fun v hv hvI =>
    subset_of_preconnected_of_inter_frontier_eq_empty hDo (H.isConnected_cell v).isPreconnected hv
      (Set.not_nonempty_iff_eq_empty.1 hvI)
  refine measure_mono_ae ?_
  filter_upwards [WalkSteps.ae_start (G := G) x, CellFamily.waypoint_walkLaw_ae_adj hloop x] with ξ h0 hadj hξ
  obtain ⟨hne', hmem⟩ := hξ
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne'
  obtain ⟨hk1, hk2⟩ := Markov.hitTime_eq_coe_iff.1 hk.symm
  rw [← hk, ENat.toNat_natCast] at hmem
  have hX0 : G.vertexPath ξ 0 = x := by
    show G.stateVertex (ξ 0) = x
    rw [h0]; rfl
  obtain ⟨hmemD, q, hq1, hq2⟩ := hmem
  have hqz : dist q z < s / 2 := mem_ball.1 hq2.2
  have hqn : ‖q‖ = R := norm_eq_of_mem_frontier_inter_ball hs0 hq2.1 (by linarith)
  have hqcell : q ∈ cell ε η (G.vertexPath ξ k) := by rw [← hcell]; exact hq1
  have hdq : ∀ y ∈ cell ε η (G.vertexPath ξ k), dist y q ≤ δ := fun y hy =>
    hdiam _ ⟨q, hqcell, mem_ball_zero_iff.2 (hqn ▸ hRρ')⟩ y hy q hqcell
  refine vExitTime_lt_vHitTime_of_firstHit (Vd := verticesMeeting H.cell D) (F := I) (τ := k)
    (by rw [hX0]; exact hxD) ?_ ?_ (fun j hj => hk2 j hj) ?_ ?_
  · intro n hn hnI
    obtain ⟨w, hw1, hw2⟩ := H.inter_of_adj _ _ (hadj n)
    exact ⟨w, hw2, hint _ hn hnI hw1⟩
  · intro v hv hvI hvB
    obtain ⟨y, hy1, hy2⟩ := hvB
    have hyD := hint v hv hvI (by rw [hcell]; exact hy1)
    rw [frontier_ball _ hs0.ne', mem_sphere] at hy2
    exact absurd hy2 (mem_ball.1 hyD.2).ne
  · rintro ⟨y, hy1, hy2⟩
    have h1 := hdq y hy1
    have h2 := norm_sub_norm_le q y
    rw [← dist_eq_norm] at h2
    have h3 : dist q y ≤ δ := by rw [dist_comm]; exact h1
    rw [mem_ball_zero_iff] at hy2
    rw [hRdef] at hqn
    linarith
  · rintro ⟨y, hy1, hy2⟩
    have h1 := hdq y hy1
    rw [frontier_ball _ hs0.ne', mem_sphere] at hy2
    have h2 := dist_triangle y q z
    linarith

/-- **Berestycki–Gwynne (2020), Lemma 6.13, last assertion, for simple random walk on the edge count** of the
Brownian pair `ω`: the transfer of `walkLaw_exit_before_ballHit` through the vertex path
(`walkLaw_vertexPath_preimage_le_srwLaw`). -/
theorem srwLaw_exit_before_ballHit
    {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} {η : ℝ → ℂ}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ)) (hHc : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected) (hLC : H.PointConnected)
    {β p ρ ρ' δ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hp0 : 0 < p) (hp1 : p < 1)
    (h311 : Lemma311Holds H ε ρ' β p) (hδ0 : 0 < δ)
    (hδ : δ ≤ min (1 / 16) (min (ρ / 4) ((ρ' - ρ) / 2))) (hεβ : ε ^ β ≤ δ)
    (hdiam : ∀ k, (cell ε η k ∩ ball (0 : ℂ) ρ').Nonempty →
      ∀ a ∈ cell ε η k, ∀ b ∈ cell ε η k, dist a b ≤ δ)
    {x : ℤ} (hx : x ∈ cellVertices ε η (ball (0 : ℂ) ρ \ ball (0 : ℂ) (ρ - δ))) :
    ENNReal.ofReal (1 - (6 * (8 * (3 * ρ + 3 + ρ') / (ρ' - ρ))) ^ t15cXi p * δ ^ (t15cXi p / 2)) ≤
      srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x
        {X | vExitTime (cellVertices ε η (ball (0 : ℂ) ρ)) X <
          vHitTime (cellVertices ε η (frontier (ball (vertexPoint ε η x) (Real.sqrt δ)))) X} :=
  have : Countable (MatedCRTHarmonic.MatedCRT.Edge ε ω) := by
    unfold MatedCRTHarmonic.MatedCRT.Edge
    infer_instance
  (walkLaw_exit_before_ballHit (fun e => ne_of_lt e.2.1) H hHc hconn hLC hε hρ hρρ' hp0 hp1 h311 hδ0 hδ hεβ
    hdiam hx).trans (walkLaw_vertexPath_preimage_le_srwLaw hlf hε.le x _)

end ExitBeforeBallHit
end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.ExitBeforeBallHit.srwLaw_exit_before_ballHit
