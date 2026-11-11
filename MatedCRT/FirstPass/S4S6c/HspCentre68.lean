import MatedCRT.FirstPass.S6r.LocalBudget

/-!
# FIRST PASS S4S6c, HspCentre68: the mass-relative sparsity at the walk centre

Lemma 6.8 (Draft/Section6.lean:115-116) gives the sparsity `|A ∩ V^ε(B_r(z))| < s₁ r^{2β⁻} ε⁻¹` for every centre
`z ∈ ℂ` at the single radius `r`. The chain needs the mass-relative form
`ε #(A ∩ V^ε(B_{c₀R}(w))) ≤ (1/16) μ(B_{c₀R}(w))` at the walk centre `w` only, where the
lower bound `(c₀R)^{β⁻} ≤ μ(B_{c₀R}(w))` is the consumer's `hVolC`.

* Case `c₀R ≤ r`: the ball `B_{c₀R}(w)` lies in `B_r(w)` (Lemma 6.8 at the centre `w`), and `16 s₁ ≤ c₀^{β⁻}`.
* Case `r ≤ c₀R` (the case the bridge `hsp_massRel_of_lemma68` of HspRepair68.lean cannot treat, since it needs
  `c₀R ≤ r`): cover `B_{c₀R}(w)` by a grid of `N ≤ 49 (c₀R/r)²` balls of radius `r` (`ball_grid_cover`). Lemma 6.8 at
  each grid centre (valid for every `z ∈ ℂ`) gives `ε #(A ∩ V(B_{c₀R}(w))) ≤ N s₁ r^{2β⁻}`, and
  `784 s₁ r^{2β⁻-2} ≤ (c₀R)^{β⁻-2}` finishes, using `44 s₁ ≤ c₀^{β⁻} ≤ c₀ ≤ 1/24`, `r ≤ 1`, `r ≤ c₀R`, `β⁻ ≥ 2`.

The covering step needs no volume bound at other centres: only the walk centre `w` carries `hVolC`.
-/
namespace MatedCRT
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace Lemma68Centre

/-- **Grid covering of a disc by `r`-balls.** For `0 < r ≤ ρ`, the ball `B(w, ρ)` is covered by the `r`-balls around
the points `w + (i r/2 + j r/2 i)` with `|i|, |j| ≤ ⌈2ρ/r⌉`; there are at most `49 (ρ/r)²` of them. -/
theorem ball_grid_cover (w : ℂ) {ρ r : ℝ} (hr : 0 < r) (hρ : r ≤ ρ) :
    ∃ S : Finset ℂ, (S.card : ℝ) ≤ 49 * (ρ / r) ^ 2 ∧ ∀ u ∈ ball w ρ, ∃ z ∈ S, u ∈ ball z r := by
  set a : ℝ := r / 2 with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  set M : ℕ := ⌈2 * ρ / r⌉₊ with hM
  set G : Finset (ℤ × ℤ) := Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M with hG
  set g : ℤ × ℤ → ℂ := fun p => w + ⟨(p.1 : ℝ) * a, (p.2 : ℝ) * a⟩ with hg
  have ht : 1 ≤ ρ / r := by rw [le_div_iff₀ hr]; linarith
  have hMle : (M : ℝ) ≤ 2 * ρ / r + 1 := by
    have := Nat.ceil_lt_add_one (div_nonneg (by linarith : (0:ℝ) ≤ 2 * ρ) hr.le)
    linarith
  have hMge : 2 * ρ / r ≤ (M : ℝ) := Nat.le_ceil _
  refine ⟨G.image g, ?_, ?_⟩
  · have hc : (G.image g).card ≤ G.card := Finset.card_image_le
    have hG' : G.card = (2 * M + 1) ^ 2 := by
      rw [hG, Finset.card_product, Int.card_Icc]
      have h2 : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
      rw [h2]; ring
    have hcR : ((G.image g).card : ℝ) ≤ (2 * (M : ℝ) + 1) ^ 2 := by
      have h := (hc.trans (le_of_eq hG'))
      have h' : ((G.image g).card : ℝ) ≤ (((2 * M + 1 : ℕ)) : ℝ) ^ 2 := by exact_mod_cast h
      push_cast at h'
      linarith
    have hkey : 2 * (M : ℝ) + 1 ≤ 7 * (ρ / r) := by
      have h2ρ : 2 * ρ / r = 2 * (ρ / r) := by ring
      linarith
    calc ((G.image g).card : ℝ) ≤ (2 * (M : ℝ) + 1) ^ 2 := hcR
      _ ≤ (7 * (ρ / r)) ^ 2 := pow_le_pow_left₀ (by positivity) hkey 2
      _ = 49 * (ρ / r) ^ 2 := by ring
  · intro u hu
    have hu' : ‖u - w‖ < ρ := by simpa [dist_eq_norm] using hu
    set v : ℂ := u - w with hv
    set i : ℤ := round (v.re / a) with hi
    set j : ℤ := round (v.im / a) with hj
    have hri : |v.re / a - (i : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have hrj : |v.im / a - (j : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have hre : |v.re| < ρ := lt_of_le_of_lt (Complex.abs_re_le_norm v) hu'
    have him : |v.im| < ρ := lt_of_le_of_lt (Complex.abs_im_le_norm v) hu'
    have h2a : 2 * ρ / r * a = ρ := by rw [ha]; field_simp
    have hxa : |v.re / a| < 2 * ρ / r := by
      rw [abs_div, abs_of_pos ha0, div_lt_iff₀ ha0]
      linarith
    have hya : |v.im / a| < 2 * ρ / r := by
      rw [abs_div, abs_of_pos ha0, div_lt_iff₀ ha0]
      linarith
    -- the integer indices lie in `[-M, M]`
    have hiM : i ∈ Finset.Icc (-(M : ℤ)) M := by
      have h1 : |(i : ℝ)| ≤ |v.re / a| + |(i : ℝ) - v.re / a| := by
        have := abs_sub_abs_le_abs_sub (i : ℝ) (v.re / a)
        linarith
      rw [abs_sub_comm] at h1
      have h2 : |(i : ℝ)| < (M : ℝ) + 1 := by linarith
      have h3 := abs_lt.mp h2
      have h4 : i < (M : ℤ) + 1 := by exact_mod_cast h3.2
      have h5 : -((M : ℤ) + 1) < i := by exact_mod_cast h3.1
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hjM : j ∈ Finset.Icc (-(M : ℤ)) M := by
      have h1 : |(j : ℝ)| ≤ |v.im / a| + |(j : ℝ) - v.im / a| := by
        have := abs_sub_abs_le_abs_sub (j : ℝ) (v.im / a)
        linarith
      rw [abs_sub_comm] at h1
      have h2 : |(j : ℝ)| < (M : ℝ) + 1 := by linarith
      have h3 := abs_lt.mp h2
      have h4 : j < (M : ℤ) + 1 := by exact_mod_cast h3.2
      have h5 : -((M : ℤ) + 1) < j := by exact_mod_cast h3.1
      rw [Finset.mem_Icc]
      constructor <;> omega
    refine ⟨g (i, j), Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr ⟨hiM, hjM⟩, rfl⟩, ?_⟩
    rw [mem_ball, dist_eq_norm]
    have hre' : (u - g (i, j)).re = v.re - (i : ℝ) * a := by
      simp [hg, hv]
      ring
    have him' : (u - g (i, j)).im = v.im - (j : ℝ) * a := by
      simp [hg, hv]
      ring
    have hbi : |v.re - (i : ℝ) * a| ≤ a / 2 := by
      have e : v.re - (i : ℝ) * a = a * (v.re / a - (i : ℝ)) := by field_simp
      rw [e, abs_mul, abs_of_pos ha0]
      nlinarith
    have hbj : |v.im - (j : ℝ) * a| ≤ a / 2 := by
      have e : v.im - (j : ℝ) * a = a * (v.im / a - (j : ℝ)) := by field_simp
      rw [e, abs_mul, abs_of_pos ha0]
      nlinarith
    calc ‖u - g (i, j)‖ ≤ |(u - g (i, j)).re| + |(u - g (i, j)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ a / 2 + a / 2 := by rw [hre', him']; linarith
      _ < r := by rw [ha]; linarith

/-- **The mass-relative sparsity at the walk centre (Lemma 6.8 with the covering of `B_{c₀R}(w)`).** Let `w` be a
centre with the volume lower bound `hvol` (the walk-centre part of `hVolC`). Lemma 6.8 at radius `r` at every centre
(`hL68`) gives `ε #(A ∩ V^ε(B_{c₀R}(w))) ≤ (1/16) μ(B_{c₀R}(w))`. Case `c₀R ≤ r` is the bridge
`hsp_massRel_of_lemma68` at the single centre `w`; case `r ≤ c₀R` covers by `ball_grid_cover`. -/
theorem hsp_centre_of_lemma68 {μ : Measure ℂ} {η : ℝ → ℂ} {A : Set ℤ} {ε s1 β c0 r R : ℝ} {w : ℂ}
    (hη : Continuous η) (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hs0 : 0 < s1) (hβ1 : 1 ≤ β) (hβ2 : 2 ≤ β) (hc0 : 0 < c0) (hc1 : c0 ≤ 1 / 24) (hR : 0 < R)
    (hr : 0 < r) (hr1 : r ≤ 1) (hs1 : 44 * s1 ≤ c0 ^ β) (hr2 : r ^ 2 ≤ R)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε)
    (hvol : (c0 * R) ^ β ≤ (μ (ball w (c0 * R))).toReal) :
    ε * ((A ∩ cellVertices ε η (ball w (c0 * R))).ncard : ℝ)
      ≤ (1 / 16 : ℝ) * (μ (ball w (c0 * R))).toReal := by
  have hρ : 0 < c0 * R := mul_pos hc0 hR
  have hcb : c0 ^ β ≤ c0 := by
    have h := Real.rpow_le_rpow_of_exponent_ge hc0 (by linarith) hβ1
    rwa [Real.rpow_one] at h
  have hs1' : 16 * s1 ≤ c0 ^ β := by linarith
  have hs784 : 784 * s1 ≤ 1 := by linarith
  rcases le_total (c0 * R) r with hcR | hcR
  · have hfin : (cellVertices ε η (ball w r)).Finite :=
      S6j.perState_cellVertices_ball_finite hη hprop hε w r
    have hsub1 : cellVertices ε η (ball w (c0 * R)) ⊆ cellVertices ε η (ball w r) :=
      Lemma68Window.cellVertices_mono_win (Metric.ball_subset_ball hcR)
    have hncard : ((A ∩ cellVertices ε η (ball w (c0 * R))).ncard : ℝ)
        ≤ ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard (inter_subset_inter_right _ hsub1)
        (hfin.subset inter_subset_right)
    have h1 : ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ) * ε ≤ s1 * r ^ (2 * β) :=
      ((lt_div_iff₀ hε).mp (hL68 w)).le
    have hpow : r ^ (2 * β) ≤ R ^ β := by
      have e : r ^ (2 * β) = (r ^ 2) ^ β := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
        congr 1
      rw [e]
      exact Real.rpow_le_rpow (by positivity) hr2 (by linarith)
    have hRβ : 0 ≤ R ^ β := Real.rpow_nonneg hR.le β
    have hmain : s1 * r ^ (2 * β) ≤ s1 * R ^ β := mul_le_mul_of_nonneg_left hpow hs0.le
    have h44 : 16 * s1 * R ^ β ≤ c0 ^ β * R ^ β := mul_le_mul_of_nonneg_right hs1' hRβ
    have hv := hvol
    rw [Real.mul_rpow hc0.le hR.le] at hv
    have h6 : ε * ((A ∩ cellVertices ε η (ball w (c0 * R))).ncard : ℝ)
        ≤ ε * ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ) :=
      mul_le_mul_of_nonneg_left hncard hε.le
    linarith [h6, h1, hmain, h44, hv]
  · obtain ⟨S, hS, hcov⟩ := ball_grid_cover w hr hcR
    have hfinz : ∀ z : ℂ, (cellVertices ε η (ball z r)).Finite := fun z =>
      S6j.perState_cellVertices_ball_finite hη hprop hε z r
    have hsub : A ∩ cellVertices ε η (ball w (c0 * R)) ⊆ ⋃ z ∈ S, (A ∩ cellVertices ε η (ball z r)) := by
      rintro k ⟨hkA, x, hxc, hxb⟩
      obtain ⟨z, hz, hxz⟩ := hcov x hxb
      exact mem_iUnion₂.mpr ⟨z, hz, hkA, x, hxc, hxz⟩
    have hfinU : (⋃ z ∈ S, (A ∩ cellVertices ε η (ball z r))).Finite :=
      Set.Finite.biUnion S.finite_toSet (fun z _ => (hfinz z).subset inter_subset_right)
    have hN1 : ((A ∩ cellVertices ε η (ball w (c0 * R))).ncard : ℝ)
        ≤ ((⋃ z ∈ S, (A ∩ cellVertices ε η (ball z r))).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hfinU
    have hN2 : ((⋃ z ∈ S, (A ∩ cellVertices ε η (ball z r))).ncard : ℝ)
        ≤ ∑ z ∈ S, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) := by
      have := Finset.set_ncard_biUnion_le S (fun z => A ∩ cellVertices ε η (ball z r))
      exact_mod_cast this
    have hterm : ∀ z ∈ S, ε * ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) ≤ s1 * r ^ (2 * β) := by
      intro z _
      have := (lt_div_iff₀ hε).mp (hL68 z)
      linarith
    have hsumle : ε * ∑ z ∈ S, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ)
        ≤ (S.card : ℝ) * (s1 * r ^ (2 * β)) := by
      rw [Finset.mul_sum]
      calc ∑ z ∈ S, ε * ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ)
          ≤ ∑ z ∈ S, s1 * r ^ (2 * β) := Finset.sum_le_sum hterm
        _ = (S.card : ℝ) * (s1 * r ^ (2 * β)) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hS2 : (S.card : ℝ) * (s1 * r ^ (2 * β)) ≤ 49 * (c0 * R / r) ^ 2 * (s1 * r ^ (2 * β)) :=
      mul_le_mul_of_nonneg_right hS (mul_nonneg hs0.le (Real.rpow_nonneg hr.le _))
    -- exponent bookkeeping: `r^{2β} = r² r^{2β-2}`, `ρ^β = ρ² ρ^{β-2}`, `r^{2β-2} = r^{β-2} r^β`
    have hr0 : r ≠ 0 := hr.ne'
    have h_r2 : r ^ (2 * β) = r ^ 2 * r ^ (2 * β - 2) := by
      rw [← Real.rpow_two r, ← Real.rpow_add hr]
      congr 1
      ring
    have h_ρ : (c0 * R) ^ β = (c0 * R) ^ 2 * (c0 * R) ^ (β - 2) := by
      rw [← Real.rpow_two (c0 * R), ← Real.rpow_add hρ]
      congr 1
      ring
    have hK : 784 * s1 * r ^ (2 * β - 2) ≤ (c0 * R) ^ (β - 2) := by
      have hX0 : 0 ≤ r ^ (β - 2) := Real.rpow_nonneg hr.le _
      have hXr : r ^ β ≤ 1 := Real.rpow_le_one hr.le hr1 (by linarith)
      have hX : r ^ (β - 2) ≤ (c0 * R) ^ (β - 2) := Real.rpow_le_rpow hr.le hcR (by linarith)
      have hrr : r ^ (2 * β - 2) = r ^ (β - 2) * r ^ β := by
        rw [← Real.rpow_add hr]
        congr 1
        ring
      rw [hrr]
      calc 784 * s1 * (r ^ (β - 2) * r ^ β) = (784 * s1 * r ^ (β - 2)) * r ^ β := by ring
        _ ≤ 784 * s1 * r ^ (β - 2) := mul_le_of_le_one_right (mul_nonneg (mul_nonneg (by norm_num) hs0.le) hX0) hXr
        _ ≤ 1 * r ^ (β - 2) := mul_le_mul_of_nonneg_right hs784 hX0
        _ ≤ (c0 * R) ^ (β - 2) := by linarith
    have hkey : 49 * (c0 * R / r) ^ 2 * (s1 * r ^ (2 * β)) * 16 ≤ (c0 * R) ^ β := by
      have e1 : 49 * (c0 * R / r) ^ 2 * (s1 * r ^ (2 * β))
          = (49 * s1 * r ^ (2 * β - 2)) * (c0 * R) ^ 2 := by
        rw [h_r2]
        field_simp
      rw [e1, h_ρ]
      have := mul_le_mul_of_nonneg_right hK (sq_nonneg (c0 * R))
      linarith
    have hN12 : ((A ∩ cellVertices ε η (ball w (c0 * R))).ncard : ℝ)
        ≤ ∑ z ∈ S, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) := hN1.trans hN2
    have h6 : ε * ((A ∩ cellVertices ε η (ball w (c0 * R))).ncard : ℝ)
        ≤ ε * ∑ z ∈ S, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) :=
      mul_le_mul_of_nonneg_left hN12 hε.le
    linarith [h6, hsumle, hS2, hkey, hvol]

end Lemma68Centre
end MatedCRT

#print axioms MatedCRT.Lemma68Centre.ball_grid_cover
#print axioms MatedCRT.Lemma68Centre.hsp_centre_of_lemma68
