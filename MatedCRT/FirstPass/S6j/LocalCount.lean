import MatedCRT.Defs.Map

/-!
# Local count of the `A`-vertices in a `c₀R`-ball (fp-S6j; `hA_local` of `printed_test_bound`)

Write-up [C22] (Lemma 6.8, Step 3, corrected). The printed count of `A ∩ V^ε(B_{c₀R}(x))` by the sparsity of one
radius-`r` ball needs `c₀R ≤ r`, which the radius selection does not give (`CHATGPT-idla-6-8-hRr.md`). The corrected
count covers `B_{c₀R}(x)` by at most `(3 + 2c₀R/r)²` balls of radius `r` (`exists_grid_cover`), sums the global
sparsity `|A ∩ V^ε(B_r(z))| < s₁ r^{2β} ε⁻¹` over the cover (`ncard_cellVertices_ball_le`), and uses `r² ≤ R ≤ 1`
(`cover_mul_rpow_le`) to bound the count by `11 s₁ R^β ε⁻¹`. The volume growth `μ(B_δ(z)) ≥ δ^β` (paper Lemma
`volume-growth`, exponent `β = β⁻`) and `44 s₁ ≤ c₀^β` give the local estimate (`hA_local_of_sparse`).
-/

open MeasureTheory Set Metric

namespace MatedCRT
namespace S6j

/-- A grid cover of the ball `B_ρ(x)` by balls of radius `r`, with at most `(3 + 2ρ/r)²` centres
(the grid `x + r(a + b i)`, `|a|, |b| ≤ ⌈ρ/r⌉`). -/
lemma exists_grid_cover (x : ℂ) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : 0 < r) :
    ∃ Y : Finset ℂ, (Y.card : ℝ) ≤ (3 + 2 * ρ / r) ^ 2 ∧
      ∀ p ∈ ball x ρ, ∃ y ∈ Y, p ∈ ball y r := by
  classical
  have hρr : 0 ≤ ρ / r := div_nonneg hρ hr.le
  set M : ℤ := (⌈ρ / r⌉₊ : ℤ) with hM
  have hM0 : 0 ≤ M := by omega
  have hMle : ρ / r ≤ (M : ℝ) := by
    rw [hM]; exact_mod_cast Nat.le_ceil (ρ / r)
  have hMlt : (M : ℝ) < ρ / r + 1 := by
    rw [hM]; exact_mod_cast Nat.ceil_lt_add_one hρr
  set G : Finset (ℤ × ℤ) := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M with hG
  refine ⟨G.image (fun ab : ℤ × ℤ => x + (r : ℂ) * ((ab.1 : ℂ) + (ab.2 : ℂ) * Complex.I)), ?_, ?_⟩
  · have hN : (((M + 1 - -M).toNat : ℕ) : ℝ) = 2 * (M : ℝ) + 1 := by
      have h1 : (((M + 1 - -M).toNat : ℕ) : ℤ) = M + 1 - -M := Int.toNat_of_nonneg (by omega)
      have h2 : ((((M + 1 - -M).toNat : ℕ) : ℤ) : ℝ) = ((M + 1 - -M : ℤ) : ℝ) := by rw [h1]
      rw [Int.cast_natCast] at h2
      rw [h2]; push_cast; ring
    have hcardG : (G.card : ℝ) = (2 * (M : ℝ) + 1) ^ 2 := by
      rw [hG, Finset.card_product, Int.card_Icc]
      rw [← hN]; push_cast; ring
    have h2ρ : 2 * ρ / r = 2 * (ρ / r) := by ring
    calc ((G.image (fun ab : ℤ × ℤ => x + (r : ℂ) * ((ab.1 : ℂ) + (ab.2 : ℂ) * Complex.I))).card : ℝ)
        ≤ (G.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = (2 * (M : ℝ) + 1) ^ 2 := hcardG
      _ ≤ (3 + 2 * ρ / r) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          rw [h2ρ]; linarith
  · intro p hp
    have hpρ : dist p x < ρ := hp
    rw [Complex.dist_eq_re_im] at hpρ
    have hρpos : 0 < ρ := lt_of_le_of_lt (Real.sqrt_nonneg _) hpρ
    have hS : (p.re - x.re) ^ 2 + (p.im - x.im) ^ 2 < ρ ^ 2 := (Real.sqrt_lt' hρpos).1 hpρ
    have hre : |p.re - x.re| < ρ :=
      abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (p.im - x.im)]) hρpos.le
    have him : |p.im - x.im| < ρ :=
      abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (p.re - x.re)]) hρpos.le
    set u : ℝ := (p.re - x.re) / r with hu
    set v : ℝ := (p.im - x.im) / r with hv
    have hu' : |u| < (M : ℝ) := by
      rw [hu, abs_div, abs_of_pos hr]
      have : |p.re - x.re| / r < ρ / r := by gcongr
      linarith
    have hv' : |v| < (M : ℝ) := by
      rw [hv, abs_div, abs_of_pos hr]
      have : |p.im - x.im| / r < ρ / r := by gcongr
      linarith
    obtain ⟨hu_lo, hu_hi⟩ := abs_lt.1 hu'
    obtain ⟨hv_lo, hv_hi⟩ := abs_lt.1 hv'
    set a : ℤ := ⌊u + 1 / 2⌋ with ha
    set b : ℤ := ⌊v + 1 / 2⌋ with hb
    have ha1 : (a : ℝ) ≤ u + 1 / 2 := Int.floor_le _
    have ha2 : u + 1 / 2 < (a : ℝ) + 1 := Int.lt_floor_add_one _
    have hb1 : (b : ℝ) ≤ v + 1 / 2 := Int.floor_le _
    have hb2 : v + 1 / 2 < (b : ℝ) + 1 := Int.lt_floor_add_one _
    have haM : a ∈ Finset.Icc (-M) M := by
      rw [Finset.mem_Icc]
      constructor
      · have h : (-M - 1 : ℝ) < a := by linarith
        have h' : (-M - 1 : ℤ) < a := by exact_mod_cast h
        omega
      · have h : (a : ℝ) < M + 1 := by linarith
        have h' : a < M + 1 := by exact_mod_cast h
        omega
    have hbM : b ∈ Finset.Icc (-M) M := by
      rw [Finset.mem_Icc]
      constructor
      · have h : (-M - 1 : ℝ) < b := by linarith
        have h' : (-M - 1 : ℤ) < b := by exact_mod_cast h
        omega
      · have h : (b : ℝ) < M + 1 := by linarith
        have h' : b < M + 1 := by exact_mod_cast h
        omega
    refine ⟨x + (r : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I),
      Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨haM, hbM⟩, rfl⟩, ?_⟩
    rw [mem_ball, Complex.dist_eq_re_im]
    have hyre : (x + (r : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I)).re = x.re + r * a := by simp
    have hyim : (x + (r : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I)).im = x.im + r * b := by simp
    rw [hyre, hyim]
    apply (Real.sqrt_lt' hr).2
    have e1 : p.re - (x.re + r * a) = r * (u - a) := by
      rw [hu]; field_simp; ring
    have e2 : p.im - (x.im + r * b) = r * (v - b) := by
      rw [hv]; field_simp; ring
    rw [e1, e2]
    have f1 : (u - a) ^ 2 ≤ 1 / 4 := by nlinarith
    have f2 : (v - b) ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left f1 (sq_nonneg r), mul_le_mul_of_nonneg_left f2 (sq_nonneg r),
      pow_pos hr 2]

/-- Products of finite-index unions: the count of a union is at most the sum of the counts. -/
lemma ncard_biUnion_le_sum {α β : Type*} [DecidableEq α] (Y : Finset α) (T : α → Set β) :
    (⋃ y ∈ Y, T y).ncard ≤ ∑ y ∈ Y, (T y).ncard := by
  induction Y using Finset.induction_on with
  | empty => simp
  | insert a Y ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- Covering count (write-up [C22] Step 3): if every radius-`r` ball has at most `b` vertices of `A`, then
`B_ρ(x)` has at most `(3 + 2ρ/r)² b` of them. -/
lemma ncard_cellVertices_ball_le {ε : ℝ} {η : ℝ → ℂ} {A : Set ℤ} {x : ℂ} {ρ r b : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hb : 0 ≤ b)
    (hfin : ∀ z : ℂ, (cellVertices ε η (ball z r)).Finite)
    (hglob : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) ≤ b) :
    ((A ∩ cellVertices ε η (ball x ρ)).ncard : ℝ) ≤ (3 + 2 * ρ / r) ^ 2 * b := by
  classical
  obtain ⟨Y, hY, hcov⟩ := exists_grid_cover x hρ hr
  have hsub : A ∩ cellVertices ε η (ball x ρ) ⊆ ⋃ y ∈ Y, (A ∩ cellVertices ε η (ball y r)) := by
    rintro k ⟨hkA, q, hqc, hqb⟩
    obtain ⟨y, hy, hqy⟩ := hcov q hqb
    exact Set.mem_iUnion₂.2 ⟨y, hy, hkA, q, hqc, hqy⟩
  have hU : (⋃ y ∈ Y, (A ∩ cellVertices ε η (ball y r))).Finite :=
    Set.Finite.biUnion (Y.finite_toSet) fun y _ => (hfin y).subset Set.inter_subset_right
  have h3 : (∑ y ∈ Y, ((A ∩ cellVertices ε η (ball y r)).ncard : ℝ)) ≤ ∑ _y ∈ Y, b :=
    Finset.sum_le_sum fun y _ => hglob y
  rw [Finset.sum_const, nsmul_eq_mul] at h3
  calc ((A ∩ cellVertices ε η (ball x ρ)).ncard : ℝ)
      ≤ ((⋃ y ∈ Y, (A ∩ cellVertices ε η (ball y r))).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hU
    _ ≤ ((∑ y ∈ Y, (A ∩ cellVertices ε η (ball y r)).ncard : ℕ) : ℝ) := by
        exact_mod_cast ncard_biUnion_le_sum Y (fun y => A ∩ cellVertices ε η (ball y r))
    _ = ∑ y ∈ Y, ((A ∩ cellVertices ε η (ball y r)).ncard : ℝ) := Nat.cast_sum _ _
    _ ≤ (Y.card : ℝ) * b := h3
    _ ≤ (3 + 2 * ρ / r) ^ 2 * b := mul_le_mul_of_nonneg_right hY hb

/-- The radius arithmetic of [C22] Step 3: for `r² ≤ R ≤ 1`, `c₀ ≤ 1/8` and `β ≥ 1`,
`(3 + 2c₀R/r)² r^{2β} ≤ 11 R^β`. -/
lemma cover_mul_rpow_le {r R c0 β : ℝ} (hr : 0 < r) (hR : 0 < R) (hR1 : R ≤ 1) (hc0 : 0 ≤ c0)
    (hc0' : c0 ≤ 1 / 8) (hβ : 1 ≤ β) (hr2 : r ^ 2 ≤ R) :
    (3 + 2 * (c0 * R) / r) ^ 2 * r ^ (2 * β) ≤ 11 * R ^ β := by
  have hρ : (3 + 2 * (c0 * R) / r) ^ 2 * r ^ 2 = (3 * r + 2 * (c0 * R)) ^ 2 := by
    field_simp
  have hs : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hs0 : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  have hs1 : Real.sqrt R ≤ 1 := by nlinarith
  have hrs : r ≤ Real.sqrt R := by
    rw [← Real.sqrt_sq hr.le]; exact Real.sqrt_le_sqrt hr2
  have hRs : R ≤ Real.sqrt R := by nlinarith
  have hc0R : c0 * R ≤ R / 8 := by nlinarith
  have hX : 3 * r + 2 * (c0 * R) ≤ 13 / 4 * Real.sqrt R := by linarith
  have hX0 : 0 ≤ 3 * r + 2 * (c0 * R) := by positivity
  have hsq : (3 * r + 2 * (c0 * R)) ^ 2 ≤ 11 * R := by
    have h := pow_le_pow_left₀ hX0 hX 2
    nlinarith
  have e1 : r ^ (2 * β) = r ^ (2 : ℝ) * r ^ (2 * β - 2) := by
    rw [← Real.rpow_add hr]; ring_nf
  have e2 : r ^ (2 * β - 2) = (r ^ 2) ^ (β - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1; push_cast; ring
  have e3 : (r ^ 2) ^ (β - 1) ≤ R ^ (β - 1) :=
    Real.rpow_le_rpow (by positivity) hr2 (by linarith)
  have hPos : 0 ≤ r ^ (2 * β - 2) := by positivity
  have hRβ : R * R ^ (β - 1) = R ^ β := by
    rw [Real.rpow_sub_one hR.ne']; field_simp
  calc (3 + 2 * (c0 * R) / r) ^ 2 * r ^ (2 * β)
      = (3 + 2 * (c0 * R) / r) ^ 2 * r ^ 2 * r ^ (2 * β - 2) := by
        rw [e1, Real.rpow_two]; ring
    _ = (3 * r + 2 * (c0 * R)) ^ 2 * r ^ (2 * β - 2) := by rw [hρ]
    _ ≤ (11 * R) * R ^ (β - 1) := by
        apply mul_le_mul hsq (by rw [e2]; exact e3) hPos (by positivity)
    _ = 11 * R ^ β := by rw [← hRβ]; ring

/-- **Local count of `A`-vertices (`hA_local` of `printed_test_bound`)**: from the global sparsity
`|A ∩ V^ε(B_r(z))| < s₁ r^{2β} ε⁻¹` (all centres `z`), the radius bound `r² ≤ R ≤ 1`, the volume growth
`(c₀R)^β ≤ μ(B_{c₀R}(x))` and `44 s₁ ≤ c₀^β`, the count of `A`-vertices in `B_{c₀R}(x)` is at most
`μ(B_{c₀R}(x)) / (4ε)`. -/
theorem hA_local_of_sparse {μ : Measure ℂ} {ε : ℝ} {η : ℝ → ℂ} {A : Set ℤ} {x : ℂ}
    {R r s1 β c0 : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hR : 0 < R) (hR1 : R ≤ 1) (hc0 : 0 < c0) (hc0' : c0 ≤ 1 / 8)
    (hs0 : 0 ≤ s1) (hβ : 1 ≤ β) (hr2 : r ^ 2 ≤ R) (hs1 : 44 * s1 ≤ c0 ^ β)
    (hfin : ∀ z : ℂ, (cellVertices ε η (ball z r)).Finite)
    (hglob : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε)
    (hvol : (c0 * R) ^ β ≤ (μ (ball x (c0 * R))).toReal) :
    ((A ∩ cellVertices ε η (ball x (c0 * R))).ncard : ℝ)
      ≤ (μ (ball x (c0 * R))).toReal / (4 * ε) := by
  have hb : 0 ≤ s1 * r ^ (2 * β) / ε := by positivity
  have hc := ncard_cellVertices_ball_le (A := A) (x := x) (ρ := c0 * R) (b := s1 * r ^ (2 * β) / ε)
    hr (by positivity) hb hfin (fun z => (hglob z).le)
  have hcov := cover_mul_rpow_le hr hR hR1 hc0.le hc0' hβ hr2
  have h1 : (3 + 2 * (c0 * R) / r) ^ 2 * (s1 * r ^ (2 * β) / ε) ≤ s1 / ε * (11 * R ^ β) := by
    rw [show (3 + 2 * (c0 * R) / r) ^ 2 * (s1 * r ^ (2 * β) / ε)
        = s1 / ε * ((3 + 2 * (c0 * R) / r) ^ 2 * r ^ (2 * β)) by ring]
    exact mul_le_mul_of_nonneg_left hcov (by positivity)
  have h2 : s1 / ε * (11 * R ^ β) ≤ (c0 * R) ^ β / (4 * ε) := by
    rw [Real.mul_rpow hc0.le hR.le]
    have hRβ : 0 ≤ R ^ β := by positivity
    have h44 : 44 * s1 * R ^ β ≤ c0 ^ β * R ^ β := mul_le_mul_of_nonneg_right hs1 hRβ
    rw [show s1 / ε * (11 * R ^ β) = (11 * s1 * R ^ β) / ε by ring]
    rw [show c0 ^ β * R ^ β / (4 * ε) = (c0 ^ β * R ^ β / 4) / ε by ring]
    apply div_le_div_of_nonneg_right _ hε.le
    linarith
  have h3 : (c0 * R) ^ β / (4 * ε) ≤ (μ (ball x (c0 * R))).toReal / (4 * ε) :=
    div_le_div_of_nonneg_right hvol (by positivity)
  linarith [hc, h1, h2, h3]

end S6j
end MatedCRT
