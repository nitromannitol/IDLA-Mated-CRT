import Mathlib
import MatedCRT.FirstPass.S6h.Schedule
import MatedCRT.FirstPass.S6e.Admissible
import MatedCRT.FirstPass.S4S6c.Uniform68Round

/-!
# Lemma 6.8: the deterministic geometry behind C12 (write-up (C1)–(C11))

Source: `notes/fp-gaps/CHATGPT-lemma68-open-parts.md`, lines 660–805 (tags (C1)–(C11)).
The deterministic statements are proved here, as statements about real numbers, points of `ℂ`,
the grid rounding `Q_δ` (`Uniform68Round.gridRound`) and the schedule's centres and radii
(`Lemma68Concrete.cfgCentre`, `cfgRadius`).

* (C1) enters as the explicit cutoff bundle `hC1 : r ≤ ρ/100 ∧ s ≤ r/1000 ∧ 10 s < s₀/4 ∧ d ≤ δ/100`
  with `s = √δ`, `δ > 0`; the write-up says these follow from the final cutoffs.
* (C6), (C10), (C12) and the good event of A5 (existence of a good radius) are not proved here.
* The cell-size bound `d` (write-up (C5), (C11)) enters as the hypothesis `∀ u ∈ H, ∀ v ∈ H, dist u v ≤ d`
  on the cell `H`; the caller supplies it from the cell-size estimate on the good event.
-/

open Set Metric Filter
open scoped Topology ENNReal

namespace MatedCRT

namespace Lemma68C12Geom

/-! ### (C2) Borel rounding moves a point strictly less than the mesh -/

/-- (C2) `|Q_δ(x) − x| ≤ g/√2 < g`: the Borel rounding `Q_δ` with mesh `g > 0` moves `x` by less than `g`. -/
theorem gridRound_dist_lt {g : ℝ} (hg : 0 < g) (x : ℂ) :
    dist (Uniform68Round.gridRound g x) x < g := by
  have h1 := Uniform68Round.abs_gridRound1_sub_le hg x.re
  have h2 := Uniform68Round.abs_gridRound1_sub_le hg x.im
  have hre : (Uniform68Round.gridRound g x - x).re = Uniform68Round.gridRound1 g x.re - x.re := rfl
  have him : (Uniform68Round.gridRound g x - x).im = Uniform68Round.gridRound1 g x.im - x.im := rfl
  have hsq : ‖Uniform68Round.gridRound g x - x‖ ^ 2 < g ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have a1 := mul_self_le_mul_self (abs_nonneg _) h1
    have a2 := mul_self_le_mul_self (abs_nonneg _) h2
    rw [abs_mul_abs_self] at a1 a2
    nlinarith
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hg.le hsq

/-- The grid point `Q_δ(x)` of the schedule lies on the lattice `(δ/100)ℤ²`. -/
theorem gridRound_mem_lattice (g : ℝ) (x : ℂ) :
    ∃ m n : ℤ, Uniform68Round.gridRound g x = ⟨g * m, g * n⟩ :=
  ⟨⌊x.re / g + 1 / 2⌋, ⌊x.im / g + 1 / 2⌋, rfl⟩

/-! ### (C4) The boundary of `K + B_t` -/

/-- (C4) For nonempty compact `K` and `t > 0`: `∂(K + B_t) = {x : dist(x,K) = t}`.
Here `K + B_t` is `Metric.thickening t K`. -/
theorem frontier_thickening_eq {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) {t : ℝ} (ht : 0 < t) :
    frontier (thickening t K) = {x | infDist x K = t} := by
  ext x
  have hop : interior (thickening t K) = thickening t K := isOpen_thickening.interior_eq
  simp only [Set.mem_ofPred_eq, frontier, Set.mem_sdiff, hop]
  constructor
  · rintro ⟨hcl, hnot⟩
    have h1 : t ≤ infDist x K :=
      not_lt.1 fun h => hnot (mem_thickening_iff.2 ((infDist_lt_iff hne).1 h))
    have h2 : infDist x K ≤ t := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨b, hb, hxb⟩ := Metric.mem_closure_iff.1 hcl ε hε
      have hb' : infDist b K < t := (infDist_lt_iff hne).2 (mem_thickening_iff.1 hb)
      have := infDist_le_infDist_add_dist (x := x) (y := b) (s := K)
      linarith
    exact le_antisymm h2 h1
  · intro hx
    refine ⟨?_, fun hmem => ?_⟩
    · rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨k, hk, hkd⟩ := hK.exists_infDist_eq_dist hne x
      have hl0 : 0 < min (1 / 2 : ℝ) (ε / (2 * t)) := lt_min one_half_pos (div_pos hε (by linarith))
      have hl1 : min (1 / 2 : ℝ) (ε / (2 * t)) ≤ 1 / 2 := min_le_left _ _
      have hl2 : min (1 / 2 : ℝ) (ε / (2 * t)) * t ≤ ε / 2 := by
        have h3 : min (1 / 2 : ℝ) (ε / (2 * t)) ≤ ε / (2 * t) := min_le_right _ _
        have h4 : ε / (2 * t) * t = ε / 2 := by
          rw [div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero two_ne_zero ht.ne') two_ne_zero]
          ring
        have h5 := mul_le_mul_of_nonneg_right h3 ht.le
        linarith
      set l := min (1 / 2 : ℝ) (ε / (2 * t)) with hl
      refine ⟨x + (l : ℂ) * (k - x), ?_, ?_⟩
      · rw [mem_thickening_iff]
        refine ⟨k, hk, ?_⟩
        have e : x + (l : ℂ) * (k - x) - k = ((1 - l : ℝ) : ℂ) * (x - k) := by push_cast; ring
        have hl1' : 0 ≤ 1 - l := by linarith
        rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl1',
          ← dist_eq_norm, ← hkd, hx]
        nlinarith [mul_pos hl0 ht]
      · have e : x - (x + (l : ℂ) * (k - x)) = -((l : ℂ) * (k - x)) := by ring
        rw [dist_eq_norm, e, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0.le,
          norm_sub_rev, ← dist_eq_norm, ← hkd, hx]
        linarith
    · obtain ⟨z, hz, hzd⟩ := mem_thickening_iff.1 hmem
      have : infDist x K < t := (infDist_lt_iff hne).2 ⟨z, hz, hzd⟩
      linarith

/-! ### (C5) The distance to `K` is 1-Lipschitz; the level set lies in `B_ρ` -/

/-- `|dist(x,K) − dist(y,K)| ≤ |x − y|`. -/
theorem abs_infDist_sub_infDist_le (K : Set ℂ) (x y : ℂ) :
    |infDist x K - infDist y K| ≤ dist x y := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [infDist_le_infDist_add_dist (x := x) (y := y) (s := K), dist_comm x y]
  · linarith [infDist_le_infDist_add_dist (x := y) (y := x) (s := K), dist_comm x y]

/-- (C5) If a cell `H` has diameter at most `d` and meets the level set `{dist(·,K) = t}` at `y`,
then every point `x₀` of `H` satisfies `|dist(x₀,K) − t| ≤ d`. -/
theorem abs_infDist_sub_le_of_mem_level {K H : Set ℂ} {d t : ℝ} {x0 y : ℂ}
    (hH : ∀ u ∈ H, ∀ v ∈ H, dist u v ≤ d) (hx0 : x0 ∈ H) (hy : y ∈ H) (hyt : infDist y K = t) :
    |infDist x0 K - t| ≤ d := by
  have h := abs_infDist_sub_infDist_le K x0 y
  rw [hyt] at h
  exact h.trans (hH x0 hx0 y hy)

/-- The level set `{dist(·,K) = t}` with `t < ρ/2` lies in `B_ρ` when `K ⊂ B_{ρ/2}` is compact. -/
theorem norm_lt_of_infDist_eq {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) {ρ t : ℝ}
    (hKρ : K ⊆ ball 0 (ρ / 2)) {y : ℂ} (hy : infDist y K = t) (ht : t < ρ / 2) :
    ‖y‖ < ρ := by
  obtain ⟨k, hk, hkd⟩ := hK.exists_infDist_eq_dist hne y
  have hkn : ‖k‖ < ρ / 2 := by simpa using hKρ hk
  have h := norm_sub_norm_le y k
  have hyk : ‖y - k‖ = t := by rw [← dist_eq_norm, ← hkd, hy]
  linarith

/-! ### (C7), (C8): the centres `z_j` and the window -/

/-- (C7) From `|dist(x₀,K) − r/2| ≤ d`, `dist(x_j, x₀) ≤ 3js` and `Ns ≤ r/100` with `j ≤ N`:
`|dist(x_j,K) − r/2| ≤ d + 3r/100`, that is `r/2 − d − 3r/100 ≤ dist(x_j,K) ≤ r/2 + d + 3r/100`. -/
theorem infDist_xj_bound {K : Set ℂ} {x0 xj : ℂ} {r d s : ℝ} {j N : ℕ}
    (hx0 : |infDist x0 K - r / 2| ≤ d) (hs : 0 ≤ s) (hjN : j ≤ N) (hN : (N : ℝ) * s ≤ r / 100)
    (hxj : dist xj x0 ≤ 3 * j * s) :
    |infDist xj K - r / 2| ≤ d + 3 * r / 100 := by
  have h1 := abs_infDist_sub_infDist_le K xj x0
  have hjN' : (j : ℝ) * s ≤ N * s := mul_le_mul_of_nonneg_right (by exact_mod_cast hjN) hs
  have h2 : |infDist xj K - infDist x0 K| ≤ 3 * r / 100 := by linarith
  rw [abs_le] at h1 h2 hx0 ⊢
  constructor <;> linarith [h2.1, h2.2, hx0.1, hx0.2]

/-- (C8, first part) Under (C1) and (C7), `x_j ∉ K`, `|x_j| ≥ s₀` and `|x_j| < ρ/2 + r`. -/
theorem xj_norm_bounds {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) {ρ s0 r d δ s : ℝ}
    (hδ : 0 < δ) (hs : s = Real.sqrt δ) (hρ1 : ρ < 1)
    (hKρ : K ⊆ ball 0 (ρ / 2)) (hBs : ball 0 s0 ⊆ K)
    (hC1 : r ≤ ρ / 100 ∧ s ≤ r / 1000 ∧ 10 * s < s0 / 4 ∧ d ≤ δ / 100)
    {x : ℂ} (hx : |infDist x K - r / 2| ≤ d + 3 * r / 100) :
    s0 ≤ ‖x‖ ∧ ‖x‖ < ρ / 2 + r := by
  obtain ⟨h1, h2, h3, h4⟩ := hC1
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg δ
  have hsp : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hδ
  have hsq : s ^ 2 = δ := by rw [hs]; exact Real.sq_sqrt hδ.le
  have hr1 : r < 1 := by linarith
  have hs1 : s < 1 := by linarith
  have hδs : δ < s := by rw [← hsq]; nlinarith
  have hdr : d ≤ r / 100000 := by linarith
  obtain ⟨hxa, hxb⟩ := abs_le.1 hx
  have hpos : 0 < infDist x K := by linarith
  have hxK : x ∉ K := fun h => (ne_of_gt hpos) (infDist_zero_of_mem h)
  have hs0x : s0 ≤ ‖x‖ := by
    by_contra h
    exact hxK (hBs (mem_ball_zero_iff.2 (not_le.1 h)))
  obtain ⟨k, hk, hkd⟩ := hK.exists_infDist_eq_dist hne x
  have hkn : ‖k‖ < ρ / 2 := by simpa using hKρ hk
  have hxk : ‖x - k‖ = infDist x K := by rw [hkd, dist_eq_norm]
  have hn := norm_sub_norm_le x k
  exact ⟨hs0x, by linarith⟩

/-- The membership predicate of the write-up's grid set `Z_δ = (δ/100)ℤ² ∩ (B_{ρ−3√δ} \ B_{10√δ})`
(write-up A5, line 306). -/
def zDeltaSet (δ ρ : ℝ) : Set ℂ :=
  {z | (∃ m n : ℤ, z = ⟨δ / 100 * m, δ / 100 * n⟩) ∧ ‖z‖ < ρ - 3 * Real.sqrt δ ∧
    10 * Real.sqrt δ ≤ ‖z‖}

/-- (C8, second part) Under (C1) and `s₀ ≤ |x| < ρ/2 + r`, the rounded centre `z = Q_δ(x)` satisfies
`10 s < |z|`, `|z| + 3s < ρ`, `|z − x| < δ/100`, and `z` lies on the lattice `(δ/100)ℤ²`;
in particular `z ∈ Z_δ`. -/
theorem zcentre_bounds {ρ s0 r d δ s : ℝ} {x z : ℂ}
    (hδ : 0 < δ) (hs : s = Real.sqrt δ) (hρ1 : ρ < 1)
    (hC1 : r ≤ ρ / 100 ∧ s ≤ r / 1000 ∧ 10 * s < s0 / 4 ∧ d ≤ δ / 100)
    (hx : s0 ≤ ‖x‖ ∧ ‖x‖ < ρ / 2 + r) (hz : z = Uniform68Round.gridRound (δ / 100) x) :
    10 * s < ‖z‖ ∧ ‖z‖ + 3 * s < ρ ∧ ‖z - x‖ < δ / 100 ∧ z ∈ zDeltaSet δ ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := hC1
  obtain ⟨hx1, hx2⟩ := hx
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg δ
  have hsp : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hδ
  have hsq : s ^ 2 = δ := by rw [hs]; exact Real.sq_sqrt hδ.le
  have hr1 : r < 1 := by linarith
  have hs1 : s < 1 := by linarith
  have hδs : δ < s := by rw [← hsq]; nlinarith
  have hzx : ‖z - x‖ < δ / 100 := by
    rw [← dist_eq_norm, hz]
    exact gridRound_dist_lt (by linarith) x
  have hA := norm_sub_norm_le x z
  rw [norm_sub_rev] at hA
  have hB := norm_sub_norm_le z x
  have hlat : ∃ m n : ℤ, z = ⟨δ / 100 * m, δ / 100 * n⟩ := by
    rw [hz]
    exact gridRound_mem_lattice (δ / 100) x
  have hzn1 : 10 * s < ‖z‖ := by linarith
  have hzn2 : ‖z‖ + 3 * s < ρ := by linarith
  have hZ : z ∈ zDeltaSet δ ρ := by
    simp only [zDeltaSet, Set.mem_ofPred_eq]
    refine ⟨hlat, ?_, ?_⟩
    · rw [← hs]; linarith
    · rw [← hs]; linarith
  exact ⟨hzn1, hzn2, hzx, hZ⟩

/-! ### (C9): the enlarged disk stays in the interior region -/

/-- (C9) If `|z| < ρ/2 + r + δ/100` and `R ≤ s` then `|z| + 2R < 3ρ/4`. -/
theorem norm_add_two_radius_lt {ρ r δ s R : ℝ} {z : ℂ} (hρ0 : 0 < ρ)
    (hC : r ≤ ρ / 100 ∧ s ≤ r / 1000) (hδ : δ < s) (hz : ‖z‖ < ρ / 2 + r + δ / 100) (hR : R ≤ s) :
    ‖z‖ + 2 * R < 3 * ρ / 4 := by
  obtain ⟨h1, h2⟩ := hC
  linarith

/-! ### The radii `R_j = R_{z_j}` of the schedule (A5) -/

/-- The first-good radius of the schedule lies in `[δ, √δ]` (write-up A5: `R ∈ [δ, √δ]`), so `R ≤ s` and
`4R/3 ≥ δ/50`. This holds for every centre, the default `δ` included. -/
theorem cfgRadius_mem_Icc {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1)
    (good : ℂ → ℕ → Prop) (z : ℂ) :
    Lemma68Scales.Delta p r ≤ Lemma68Concrete.cfgRadius p r good z ∧
      Lemma68Concrete.cfgRadius p r good z ≤ Real.sqrt (Lemma68Scales.Delta p r) := by
  have hδ0 : 0 < Lemma68Scales.Delta p r := Lemma68Radius.delta_pos p r
  have hδ1 : Lemma68Scales.Delta p r ≤ 1 :=
    (Lemma68Scales.Delta_le_rpow hp hr0 hr1).trans (Real.rpow_le_one hr0.le hr1.le hp.le)
  have hmem := Lemma68Radius.firstGood_cand_mem hδ0 (good z)
  exact Lemma68Radius.selectable_bounds hδ0 hδ1 hmem

/-! ### (C3) Test disks -/

/-- (C3) If `H` has diameter at most `d ≤ δ/100`, `x ∈ H`, `|z − x| < δ/100` and `R ≥ δ`, then
every `u ∈ H` satisfies `|u − z| < 4R/3`; that is `H ⊂ B_{δ/50}(z) ⊂ B_{4R/3}(z)`. -/
theorem cell_sub_testDisk {H : Set ℂ} {d δ R : ℝ} {x z u : ℂ} (hδ : 0 ≤ δ) (hd : d ≤ δ / 100)
    (hR : δ ≤ R) (hH : ∀ u ∈ H, ∀ v ∈ H, dist u v ≤ d) (hx : x ∈ H) (hu : u ∈ H)
    (hzx : dist z x < δ / 100) :
    dist u z < 4 * R / 3 := by
  have h1 := hH u hu x hx
  have h2 := dist_triangle u x z
  rw [dist_comm x z] at h2
  linarith

/-! ### (C11): the deterministic implication behind the strict bound -/

/-- (C11), deterministic part. Let `y` be the state point `η(X_n)` (in the cell `H` of `X_n`, of
diameter at most `d`) with `|y − x_j| < 3s` (window inclusion (C10), a hypothesis here), `|x_j − x₀| ≤ 3js`,
`j + 1 ≤ N`, `Ns ≤ r/100`, `s ≤ r/1000` and `d ≤ s/100`, and `|dist(x₀,K) − r/2| ≤ d` (C5).
Then every `u ∈ H` satisfies `2r/5 < dist(u,K) < 3r/5`. -/
theorem infDist_mem_Ioo_of_window {K H : Set ℂ} {x0 xj y u : ℂ} {r d s : ℝ} {j N : ℕ}
    (hx0 : |infDist x0 K - r / 2| ≤ d) (hs : 0 ≤ s) (hd : d ≤ s / 100) (hs' : s ≤ r / 1000)
    (hjN : j + 1 ≤ N) (hNs : (N : ℝ) * s ≤ r / 100) (hxj : dist xj x0 ≤ 3 * j * s)
    (hyj : dist y xj < 3 * s)
    (hH : ∀ u ∈ H, ∀ v ∈ H, dist u v ≤ d) (hy : y ∈ H) (hu : u ∈ H) :
    2 * r / 5 < infDist u K ∧ infDist u K < 3 * r / 5 := by
  have hjN' : ((j : ℝ) + 1) * s ≤ N * s :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hjN) hs
  have hyx : dist y x0 < 3 * r / 100 := by
    have := dist_triangle y xj x0
    nlinarith
  have hux : dist u x0 < d + 3 * r / 100 := by
    have := dist_triangle u y x0
    have := hH u hu y hy
    linarith
  have h := abs_infDist_sub_infDist_le K u x0
  have hx' := abs_le.1 hx0
  have h' := abs_le.1 h
  constructor <;> linarith [h'.1, h'.2, hx'.1, hx'.2]

end Lemma68C12Geom

end MatedCRT
