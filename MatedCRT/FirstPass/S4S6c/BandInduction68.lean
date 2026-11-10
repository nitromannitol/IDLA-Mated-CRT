import MatedCRT.FirstPass.S4S6c.ConfigBound68
import MatedCRT.FirstPass.S4S6c.ConfigGeometry68
import MatedCRT.FirstPass.S4S6c.ExitPath68
import MatedCRT.FirstPass.S4S6c.NextExitStop

/-!
# Band induction of the printed Lemma 6.8 (q2, task fp-S4S6c-envscaling-6-7-6-8; LEMMA68 C3)

Deterministic core of the test sequence of LEMMA68 (C1)-(C3) (write-up `CHATGPT-lemma68-open-parts.md`, section C3).
For a legal walk `x` started at a frontier vertex `b`: `P v` is the vertex point of the cell `H v`, `ctr v` the test
centre (`z_j = Q_δ(x_j)`, within `g` of `P v`), `rad v` the test radius (`R_j`), `Wt v = I(B_{2 rad v}(ctr v))` the inner
test window, and `T_{j+1} = T_j + (first exit time of Wt (x_{T_j}) from the shifted path)`.

The induction (C6): `dist(P(x_{T_j}), P b) ≤ 3 j s` for `j ≤ N`, with `N s ≤ r/100`. It uses the finiteness of each window
exit (the path input `hfinW`, an almost sure property of the Good event) and gives the three hypotheses of
`ConfigBound68.frontier_half` which are deterministic:

* `band_facts`: `T_j < ∞` and `x_{T_j} ∈ Y` for `j < N` (`hfin`, `hYvis`), with `Y = band P F r d`;
* `window_sub`: `Wt y ⊆ V(U₂) \ Θ` for `y ∈ Y` (`hWU`); the constant `Aof` gives `hAof` trivially.

Terminology: inner vertices `I(D)` (Armitage-Gardiner), infimal distance to the cluster `F` (`Metric.infDist`). No
probability input is used here.
-/

open Set Metric

namespace MatedCRT

namespace BandInduction68

/-- The band `Y` of LEMMA68 (C7), (C11): the vertices whose vertex point lies within `3r/100 + 2d` of the sphere
`{dist(·, F) = r/2}`. -/
def band (P : ℤ → ℂ) (F : Set ℂ) (r d : ℝ) : Set ℤ :=
  {v | |infDist (P v) F - r / 2| ≤ 3 * r / 100 + 2 * d}

theorem mem_band_iff {P : ℤ → ℂ} {F : Set ℂ} {r d : ℝ} {v : ℤ} :
    v ∈ band P F r d ↔ |infDist (P v) F - r / 2| ≤ 3 * r / 100 + 2 * d :=
  Iff.rfl

/-- A point at infimal distance less than `t` from a cluster `F ⊆ B_{ρ/2}` has norm less than `ρ/2 + t`. -/
theorem norm_lt_of_infDist {F : Set ℂ} {ρ t : ℝ} {p : ℂ} (hFball : F ⊆ ball (0 : ℂ) (ρ / 2))
    (hFne : F.Nonempty) (h : infDist p F < t) : ‖p‖ < ρ / 2 + t := by
  obtain ⟨f, hf, hdist⟩ := (Metric.infDist_lt_iff hFne).1 h
  have hfn : ‖f‖ < ρ / 2 := mem_ball_zero_iff.1 (hFball hf)
  have htri : ‖p‖ ≤ ‖p - f‖ + ‖f‖ := by
    calc ‖p‖ = ‖(p - f) + f‖ := by rw [sub_add_cancel]
      _ ≤ ‖p - f‖ + ‖f‖ := norm_add_le _ _
  have hpf : ‖p - f‖ = dist p f := (dist_eq_norm p f).symm
  linarith

/-- Norm change under a distance: `‖q‖ ≤ ‖p‖ + dist q p`. -/
theorem norm_le_add_dist (p q : ℂ) : ‖q‖ ≤ ‖p‖ + dist q p := by
  rw [dist_eq_norm]
  calc ‖q‖ = ‖p + (q - p)‖ := by congr 1; ring
    _ ≤ ‖p‖ + ‖q - p‖ := norm_add_le _ _

/-- Lipschitz bound of the distance to a cluster. -/
theorem abs_infDist_sub_le (F : Set ℂ) (p q : ℂ) :
    |infDist p F - infDist q F| ≤ dist p q := by
  rw [abs_le]
  have h1 := Metric.infDist_le_infDist_add_dist (x := p) (y := q) (s := F)
  have h2 := Metric.infDist_le_infDist_add_dist (x := q) (y := p) (s := F)
  have h3 := dist_comm q p
  constructor <;> linarith

/-- The band-scale bound `3 j s ≤ 3r/100` for `j ≤ N` (from `N s ≤ r/100`). -/
theorem js_bound {j N : ℕ} {s r : ℝ} (hs : 0 < s) (hj : j ≤ N) (hNs : (N : ℝ) * s ≤ r / 100) :
    3 * (j : ℝ) * s ≤ 3 * r / 100 := by
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
  have := mul_le_mul_of_nonneg_right hjN hs.le
  linarith

/-- Band membership from the distance of a vertex point to the start point (LEMMA68 (C5), (C7)). -/
theorem mem_band_of_dist {P : ℤ → ℂ} {F : Set ℂ} {r d : ℝ} {v b : ℤ} (hd : 0 ≤ d)
    (hstart : |infDist (P b) F - r / 2| ≤ d) (hv : dist (P v) (P b) ≤ 3 * r / 100) :
    v ∈ band P F r d := by
  rw [mem_band_iff]
  have h1 := abs_le.1 (abs_infDist_sub_le F (P v) (P b))
  have h2 := abs_le.1 hstart
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- One test of the walk (LEMMA68 C3, one window). Let `w` be a legal path (`hlegal`) whose vertex `w 0` has cell point
within `g` of the centre `c`, and let the inner window `I(B_{2R}(c))` have exit time `e` (`hE`). Then the position of the
exit vertex lies within `2R + d + g` of `P (w 0)`. The exit cell has closure meeting the sphere `∂B_{2R}(c)`
(`ExitPath68.exit_closure_meets_sphere`), and that sphere lies in `B_ρ`, so the cell-size bound `hsm` applies to it. -/
theorem test_step {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {P : ℤ → ℂ} {c : ℂ} {R d g ρ : ℝ} {w : ℕ → ℤ} {e : ℕ}
    (hconn : ∀ v, IsPreconnected (H v))
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    (hPmem : ∀ v, P v ∈ H v)
    (hsm : ∀ v, (H v ∩ ball (0 : ℂ) ρ).Nonempty → ∀ u ∈ closure (H v), ∀ u' ∈ closure (H v), dist u u' ≤ d)
    (hρ : ‖c‖ + 2 * R < ρ) (hnn : 0 ≤ 2 * R + d + g)
    (hlegal : ∀ n, w (n + 1) = w n ∨ m (w n) (w (n + 1)) ≠ 0)
    (hPc : dist (P (w 0)) c ≤ g)
    (hE : vExitTime (innerVertices H (ball c (2 * R))) w = (e : ℕ∞)) :
    dist (P (w e)) (P (w 0)) ≤ 2 * R + d + g := by
  obtain ⟨hin, hout⟩ := (NextExitStop.vExitTime_eq_coe_iff _ w e).1 hE
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · rw [he0, dist_self]
    exact hnn
  · have hk'in : w (e - 1) ∈ innerVertices H (ball c (2 * R)) := hin (e - 1) (by omega)
    have hmk : m (w (e - 1)) (w e) ≠ 0 := by
      have h := hlegal (e - 1)
      rw [show e - 1 + 1 = e by omega] at h
      rcases h with h | h
      · exact (hout (by rw [h]; exact hk'in)).elim
      · exact h
    obtain ⟨q, hqcl, hqs⟩ := ExitPath68.exit_closure_meets_sphere hconn hadj hk'in hmk hout
    have hqn : dist q c = 2 * R := mem_sphere.1 hqs
    have hqball : q ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff]
      have h1 := norm_le_add_dist c q
      linarith
    have hkH : (H (w e) ∩ ball (0 : ℂ) ρ).Nonempty := by
      have h := (_root_.mem_closure_iff.1 hqcl) (ball (0 : ℂ) ρ) isOpen_ball hqball
      rwa [inter_comm] at h
    have hPq : dist (P (w e)) q ≤ d :=
      hsm (w e) hkH (P (w e)) (subset_closure (hPmem (w e))) q hqcl
    have h1 := dist_triangle (P (w e)) q c
    have h2 := dist_triangle (P (w e)) c (P (w 0))
    have h3 := dist_comm c (P (w 0))
    linarith

/-- **Band induction (LEMMA68 C3, C6).** On a legal path `x` from the frontier vertex `b`, with the window exits finite
on the band (`hfinW`), the test times satisfy `dist(P(x_{T_j}), P b) ≤ 3 j s` for `j ≤ N`, and `T_j` is finite. -/
theorem band_induction {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {F : Set ℂ} {P ctr : ℤ → ℂ} {rad : ℤ → ℝ}
    {Wt : ℤ → Set ℤ} {r ρ s d g : ℝ} {N : ℕ} {b : ℤ} {x : ℕ → ℤ} {τ : ℕ → (ℕ → ℤ) → ℕ∞}
    (hconn : ∀ v, IsPreconnected (H v))
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    (hPmem : ∀ v, P v ∈ H v)
    (hsm : ∀ v, (H v ∩ ball (0 : ℂ) ρ).Nonempty → ∀ u ∈ closure (H v), ∀ u' ∈ closure (H v), dist u u' ≤ d)
    (hFne : F.Nonempty) (hFball : F ⊆ ball (0 : ℂ) (ρ / 2))
    (hctr : ∀ v, dist (ctr v) (P v) ≤ g)
    (hWt : ∀ v, dist (P v) (P b) ≤ 3 * r / 100 → Wt v = innerVertices H (ball (ctr v) (2 * rad v)))
    (hrad0 : ∀ v ∈ band P F r d, 0 ≤ rad v) (hrad : ∀ v ∈ band P F r d, rad v ≤ s)
    (_hr : 0 < r) (hrρ : r ≤ ρ / 100) (hs : 0 < s) (hsr : s ≤ r / 1000) (hd : 0 ≤ d) (hdr : d ≤ r / 1000)
    (hg : 0 ≤ g) (hgd : g + d < s) (hNs : (N : ℝ) * s ≤ r / 100)
    (hstart : |infDist (P b) F - r / 2| ≤ d)
    (hτ0 : ∀ y : ℕ → ℤ, τ 0 y = 0)
    (hτsucc : ∀ (M : ℕ) (y : ℕ → ℤ) (i : ℕ), τ M y = (i : ℕ∞) →
      τ (M + 1) y = (i : ℕ∞) + vExitTime (Wt (y i)) (WalkPotential.pathShift i y))
    (hx0 : x 0 = b)
    (hlegal : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (hfinW : ∀ i, dist (P (x i)) (P b) ≤ 3 * r / 100 → vExitTime (Wt (x i)) (WalkPotential.pathShift i x) ≠ ⊤) :
    ∀ j ≤ N, ∃ i : ℕ, τ j x = (i : ℕ∞) ∧ dist (P (x i)) (P b) ≤ 3 * (j : ℝ) * s := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨0, ?_, ?_⟩
    · simp [hτ0]
    · simp [hx0]
  | succ j ih =>
    intro hj
    obtain ⟨i, hi, hdist⟩ := ih (by omega)
    have hxi3 : dist (P (x i)) (P b) ≤ 3 * r / 100 := le_trans hdist (js_bound hs (by omega) hNs)
    have hbi : x i ∈ band P F r d := mem_band_of_dist hd hstart hxi3
    have hrad_i := hrad (x i) hbi
    have hrad0_i := hrad0 (x i) hbi
    have hρpos : 0 < ρ := by linarith
    have hinf : infDist (P (x i)) F < ρ / 4 + (r / 2 + 3 * r / 100 + 2 * d) := by
      have h := (abs_le.1 (mem_band_iff.1 hbi)).2
      linarith
    have hnP := norm_lt_of_infDist hFball hFne hinf
    have hcn := norm_le_add_dist (P (x i)) (ctr (x i))
    have hcP := hctr (x i)
    have hnorm : ‖ctr (x i)‖ + 2 * rad (x i) < ρ := by linarith
    have hlegal' : ∀ n, WalkPotential.pathShift i x (n + 1) = WalkPotential.pathShift i x n ∨
        m (WalkPotential.pathShift i x n) (WalkPotential.pathShift i x (n + 1)) ≠ 0 := by
      intro n
      have h := hlegal (i + n)
      show x (i + (n + 1)) = x (i + n) ∨ m (x (i + n)) (x (i + (n + 1))) ≠ 0
      rw [show i + (n + 1) = i + n + 1 by omega]
      exact h
    have hPc : dist (P (WalkPotential.pathShift i x 0)) (ctr (x i)) ≤ g := by
      show dist (P (x i)) (ctr (x i)) ≤ g
      rw [dist_comm]
      exact hctr (x i)
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 (hfinW i hxi3)
    have hE : vExitTime (innerVertices H (ball (ctr (x i)) (2 * rad (x i))))
        (WalkPotential.pathShift i x) = (e : ℕ∞) := by
      rw [← hWt (x i) hxi3]
      exact he.symm
    have hbd : dist (P (x (i + e))) (P (x i)) ≤ 2 * rad (x i) + d + g :=
      test_step hconn hadj hPmem hsm hnorm (by linarith) hlegal' hPc hE
    have hstep : dist (P (x (i + e))) (P (x i)) ≤ 3 * s := by linarith
    refine ⟨i + e, ?_, ?_⟩
    · rw [hτsucc j x i hi, ← he, Nat.cast_add]
    · have h1 := dist_triangle (P (x (i + e))) (P (x i)) (P b)
      have hfinal : 3 * ((j + 1 : ℕ) : ℝ) * s = 3 * (j : ℝ) * s + 3 * s := by
        push_cast
        ring
      rw [hfinal]
      linarith

/-- **C3 facts for `ConfigBound68`.** Under the hypotheses of `band_induction`: every test time `T_j`, `j < N`, is finite,
and `x_{T_j} ∈ Y` (`ConfigBound68.frontier_half`, `hfin` and `hYvis`). -/
theorem band_facts {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {F : Set ℂ} {P ctr : ℤ → ℂ} {rad : ℤ → ℝ}
    {Wt : ℤ → Set ℤ} {r ρ s d g : ℝ} {N : ℕ} {b : ℤ} {x : ℕ → ℤ} {τ : ℕ → (ℕ → ℤ) → ℕ∞}
    (hconn : ∀ v, IsPreconnected (H v))
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    (hPmem : ∀ v, P v ∈ H v)
    (hsm : ∀ v, (H v ∩ ball (0 : ℂ) ρ).Nonempty → ∀ u ∈ closure (H v), ∀ u' ∈ closure (H v), dist u u' ≤ d)
    (hFne : F.Nonempty) (hFball : F ⊆ ball (0 : ℂ) (ρ / 2))
    (hctr : ∀ v, dist (ctr v) (P v) ≤ g)
    (hWt : ∀ v, dist (P v) (P b) ≤ 3 * r / 100 → Wt v = innerVertices H (ball (ctr v) (2 * rad v)))
    (hrad0 : ∀ v ∈ band P F r d, 0 ≤ rad v) (hrad : ∀ v ∈ band P F r d, rad v ≤ s)
    (_hr : 0 < r) (hrρ : r ≤ ρ / 100) (hs : 0 < s) (hsr : s ≤ r / 1000) (hd : 0 ≤ d) (hdr : d ≤ r / 1000)
    (hg : 0 ≤ g) (hgd : g + d < s) (hNs : (N : ℝ) * s ≤ r / 100)
    (hstart : |infDist (P b) F - r / 2| ≤ d)
    (hτ0 : ∀ y : ℕ → ℤ, τ 0 y = 0)
    (hτsucc : ∀ (M : ℕ) (y : ℕ → ℤ) (i : ℕ), τ M y = (i : ℕ∞) →
      τ (M + 1) y = (i : ℕ∞) + vExitTime (Wt (y i)) (WalkPotential.pathShift i y))
    (hx0 : x 0 = b)
    (hlegal : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (hfinW : ∀ i, dist (P (x i)) (P b) ≤ 3 * r / 100 → vExitTime (Wt (x i)) (WalkPotential.pathShift i x) ≠ ⊤) :
    (∀ j < N, τ j x ≠ ⊤) ∧ (∀ j < N, ∀ k : ℕ, τ j x = (k : ℕ∞) → x k ∈ band P F r d) := by
  have key := band_induction hconn hadj hPmem hsm hFne hFball hctr hWt hrad0 hrad _hr hrρ hs hsr hd hdr hg hgd hNs
    hstart hτ0 hτsucc hx0 hlegal hfinW
  refine ⟨fun j hj => ?_, fun j hj k hk => ?_⟩
  · obtain ⟨i, hi, -⟩ := key j (by omega)
    rw [hi]
    exact ENat.natCast_ne_top i
  · obtain ⟨i, hi, hdist⟩ := key j (by omega)
    rw [hi] at hk
    have hik : i = k := by exact_mod_cast hk
    subst hik
    exact mem_band_of_dist hd hstart (le_trans hdist (js_bound hs (by omega) hNs))

/-- **Window containment (LEMMA68 `Wt y ⊆ V(U₂) \ Θ`, `hWU`).** For a vertex `y` of the band, the inner test window
`I(B_{2R_y}(z_y))` lies in `V(U₂) \ Θ`, `U₂ = thickening r F`: the centre is at infimal distance `r/2 ± (3r/100 + 2d + g)`
from `F`, which places the disk strictly between `2R` and `r - 2R` from `F` (`ConfigGeometry68.innerWindow_subset_meetVerts`). -/
theorem window_sub {H : ℤ → Set ℂ} {F : Set ℂ} {Θ : Set ℤ} {P ctr : ℤ → ℂ} {rad : ℤ → ℝ} {Wt : ℤ → Set ℤ}
    {r s d g : ℝ}
    (hconn : ∀ v, IsPreconnected (H v)) (hne : ∀ v, (H v).Nonempty) (hF : ∀ k ∈ Θ, H k ⊆ F) (hFne : F.Nonempty)
    (hctr : ∀ v, dist (ctr v) (P v) ≤ g)
    (hWt : ∀ v, Wt v = innerVertices H (ball (ctr v) (2 * rad v)))
    (hrad : ∀ v ∈ band P F r d, rad v ≤ s) (_hr : 0 < r) (hsr : s ≤ r / 1000) (hd : 0 ≤ d) (_hdr : d ≤ r / 1000)
    (hg : 0 ≤ g) (hgd : g + d < s) :
    ∀ y ∈ band P F r d, Wt y ⊆ FrontierSeparation.meetVerts H (Metric.thickening r F) \ Θ := by
  intro y hy
  rw [hWt y]
  have hy' := abs_le.1 (mem_band_iff.1 hy)
  have hz := abs_le.1 (abs_infDist_sub_le F (ctr y) (P y))
  have hcd := hctr y
  have hR := hrad y hy
  have hlow : r / 2 - (3 * r / 100 + 2 * d + g) ≤ infDist (ctr y) F := by
    linarith [hz.1, hz.2, hy'.1, hy'.2]
  have hup : infDist (ctr y) F ≤ r / 2 + (3 * r / 100 + 2 * d + g) := by
    linarith [hz.1, hz.2, hy'.1, hy'.2]
  have h2R : 2 * rad y ≤ infDist (ctr y) F := by linarith
  have hnear : ∃ f ∈ F, dist (ctr y) f < r - 2 * rad y :=
    (Metric.infDist_lt_iff hFne).1 (by linarith)
  have hfar : ∀ f ∈ F, 2 * rad y ≤ dist (ctr y) f := fun f hf =>
    le_trans h2R (Metric.infDist_le_dist_of_mem hf)
  exact ConfigGeometry68.innerWindow_subset_meetVerts hconn hne hF hnear hfar

end BandInduction68

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.BandInduction68.test_step
#print axioms MatedCRT.BandInduction68.band_induction
#print axioms MatedCRT.BandInduction68.band_facts
#print axioms MatedCRT.BandInduction68.window_sub
