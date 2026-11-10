import MatedCRT.FirstPass.S5d.FloorProof.Pathwise

/-!
# The floor on one cell, pathwise (task fp-S5d-5-1, floor note Part I, Sections 8.1-8.3)

`floor_cell_bound`: for one outcome and one mesh `ε`, if the cell `H_k` meets `B⁻_{δ/2}(Λ_t)` and the localized good events
of Section 7 hold (`hEw`, `hEg`, `hM`, `hsmall`, `hpole`, the obstacle bound `hS` of the floor constant `s`), then
`s/2 ≤ m_ε⁻¹ u^ε_t(k)`. Case 8.1 (the cell misses `B_r`) uses one exclusive point of the cell; case 8.2 (the cell meets `B_r`)
uses the minimum principle of `MinPrinciple.lean` on the finite set `A^ε = {a : H_a ∩ B_{2r} ≠ ∅, H_a ∩ ∂B_{2r} = ∅}`, whose outer
boundary cells are small and lie in the annulus `{r < |x| < 3r}` (equation (22)).
-/

open MeasureTheory Set Metric Filter Topology

namespace MatedCRT

namespace FloorProof

/-- Cells are compact images of intervals under the continuous `η`, hence bounded. -/
theorem cell_isBounded {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    Bornology.IsBounded (cell ε η k) :=
  (isCompact_Icc.image hη).isBounded

/-- Rescaling the deterministic affine relation: `ε m_ε ⁻¹`-normalized pole values. -/
theorem le_mul_iff_pole {ε mε t c g : ℝ} (hε : 0 < ε) (hmε : 0 < mε) (ht : 0 < t) :
    c ≤ t * (mε⁻¹ * (ε⁻¹ * g)) ↔ (ε * mε / t) * c ≤ g := by
  have e1 : t * (mε⁻¹ * (ε⁻¹ * g)) = t / (ε * mε) * g := by
    field_simp
  have hp : 0 < ε * mε / t := by positivity
  have e2 : t / (ε * mε) * g = g / (ε * mε / t) := by
    field_simp
  rw [e1, e2, le_div_iff₀ hp]
  constructor <;> intro h <;> linarith [mul_comm c (ε * mε / t)]

/-- The set `A^ε` of floor note Step 8.2: vertices whose cells meet `B_{2r}` but not `∂B_{2r}`. -/
def nearVertices (ε : ℝ) (η : ℝ → ℂ) (r : ℝ) : Set ℤ :=
  {j | (cell ε η j ∩ ball (0 : ℂ) (2 * r)).Nonempty ∧ ¬ (cell ε η j ∩ sphere (0 : ℂ) (2 * r)).Nonempty}

/-- Floor note (14)-(21): the floor `s/2 ≤ m_ε⁻¹ u^ε_t(k)` on every cell `H_k` meeting `B⁻_{δ/2}(Λ_t)`, for one outcome
and one mesh (all inputs deterministic). -/
theorem floor_cell_bound {m : ℤ → ℤ → ℕ} {ε ρ t mε α δ d r e n s : ℝ} {η : ℝ → ℂ}
    {W G : ℂ → ℝ} {Λt : Set ℂ} {k : ℤ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m) (hcons : ∀ j : ℤ, m j (j + 1) ≠ 0)
    (hη : Continuous η) (hε : 0 < ε) (ht : 0 < t) (hmε : 0 < mε) (hδ : 0 < δ) (hδρ : δ < ρ)
    (hr : 0 < r) (hr3 : 3 * r < ρ) (hfin : (ballInterior ε η ρ).Finite)
    (hadj : ∀ j l : ℤ, m j l ≠ 0 → (cell ε η j ∩ cell ε η l).Nonempty)
    (hexcl : ∀ j : ℤ, ∃ x ∈ cell ε η j, ∀ b : ℤ, x ∈ cell ε η b → b = j)
    (hd8 : d ≤ δ / 8) (hd4 : d ≤ r / 4)
    (hsmall : ∀ j : ℤ, (cell ε η j ∩ ball (0 : ℂ) ρ).Nonempty → diam (cell ε η j) < d)
    (hΛ : Λt ⊆ ball (0 : ℂ) (ρ / 3))
    (hEw : ∀ x ∈ ball (0 : ℂ) ρ,
      |rescale mε ε η (matedLeastSupersolution m ε η ρ t) x - α * W x| ≤ e)
    (hEg : ∀ x : ℂ, r ≤ ‖x‖ → ‖x‖ ≤ ρ →
      |rescale mε ε η (fun a => ε⁻¹ * greenKernel m (ballInterior ε η ρ) 0 a) x - α * G x| ≤ e)
    (hM : ∀ x ∈ closedBall (0 : ℂ) ρ, |α * W x| ≤ n)
    (hpole : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ ≤ 3 * r → n + 4 ≤ α * t * G x)
    (hS : ∀ x ∈ innerNbhd (δ / 4) Λt, x ≠ 0 → s ≤ α * (W x + t * G x))
    (hsn : 1 / n ≤ s) (hs1 : s ≤ 1) (hn1 : 1 ≤ n) (hen : (1 + t) * e ≤ 1 / (4 * n))
    (hK : (cell ε η k ∩ innerNbhd (δ / 2) Λt).Nonempty) :
    s / 2 ≤ mε⁻¹ * stoppedOdometer m ε η ρ t k := by
  obtain ⟨y, hyK, hyI⟩ := hK
  have hb : Bornology.IsBounded (cell ε η k) := cell_isBounded hη k
  have hyB : y ∈ ball (0 : ℂ) ρ := ball_subset_ball (by linarith) (hΛ hyI.1)
  have hdiam : diam (cell ε η k) < d := hsmall k ⟨y, hyK, hyB⟩
  have hdiam8 : diam (cell ε η k) < δ / 8 := lt_of_lt_of_le hdiam hd8
  have hdiam4 : diam (cell ε η k) < δ / 4 := by linarith
  have hKq : cell ε η k ⊆ innerNbhd (δ / 4) Λt :=
    cell_subset_innerNbhd_quarter hδ hb hdiam4 ⟨y, hyK, hyI⟩
  have hKball : cell ε η k ⊆ ball (0 : ℂ) (ρ / 2) :=
    cell_subset_ball_half hδ hδρ hΛ hb hdiam8 ⟨y, hyK, hyI⟩
  have hKρ : cell ε η k ⊆ ball (0 : ℂ) ρ := fun x hx => ball_subset_ball (by linarith) (hKball hx)
  have hk_mem : k ∈ cellVertices ε η (closedBall (0 : ℂ) ρ) :=
    ⟨y, hyK, ball_subset_closedBall hyB⟩
  -- the identity (1) at an exclusive point of the cell `H_k`
  have hkey : ∀ x : ℂ, x ∈ cell ε η k → (∀ b : ℤ, x ∈ cell ε η b → b = k) →
      mε⁻¹ * stoppedOdometer m ε η ρ t k =
        rescale mε ε η (matedLeastSupersolution m ε η ρ t) x +
          t * rescale mε ε η (fun a => ε⁻¹ * greenKernel m (ballInterior ε η ρ) 0 a) x := by
    intro x hx hex
    rw [stoppedOdometer_eq_of_mem hk_mem, rescale_exclusive_eq _ hx hex,
      rescale_exclusive_eq _ hx hex]
    ring
  by_cases hA : (cell ε η k ∩ ball (0 : ℂ) r).Nonempty
  · -- Case 8.2: the cell meets `B_r`; minimum principle on `A^ε`
    have hKsub : cell ε η k ⊆ ball (0 : ℂ) (2 * r) := cell_subset_ball_two hb (by linarith) hA
    have hAcell : ∀ j ∈ nearVertices ε η r, cell ε η j ⊆ ball (0 : ℂ) (2 * r) := by
      intro j hj
      refine cell_subset_ball_of_not_sphere ((isPreconnected_Icc).image η hη.continuousOn) hj.1 ?_
      intro x hx hxn
      exact hj.2 ⟨x, hx, by rw [mem_sphere_zero_iff_norm]; exact hxn⟩
    have hAsub : nearVertices ε η r ⊆ ballInterior ε η ρ :=
      cellVertices_sub_interior hη (by linarith) (by linarith)
    have hAfin : (nearVertices ε η r).Finite := hfin.subset hAsub
    have hkA : k ∈ nearVertices ε η r := by
      refine ⟨?_, ?_⟩
      · obtain ⟨z, hzK, hzB⟩ := hA
        exact ⟨z, hzK, ball_subset_ball (by linarith) hzB⟩
      · rintro ⟨z, hzK, hzS⟩
        have h1 := hKsub hzK
        rw [mem_ball_zero_iff] at h1
        rw [mem_sphere_zero_iff_norm] at hzS
        linarith
    -- the superharmonicity of the killed Green kernel on `A^ε`, and the boundary bound (22)
    have hsup : ∀ a ∈ nearVertices ε η r,
        lapSum hlf (fun b => greenKernel m (ballInterior ε η ρ) 0 b - (ε * mε / t) * (n + 4 - t * e)) a ≤ 0 := by
      intro a ha
      have h1 := lapSum_sub_const hlf (fun b => greenKernel m (ballInterior ε η ρ) 0 b)
        ((ε * mε / t) * (n + 4 - t * e)) a
      have h2 := lapSum_greenKernel_source_nonpos hsymm hlf hcons hfin (hAsub ha)
      rw [h1]
      exact h2
    have hbd : ∀ b ∈ vBoundary m (nearVertices ε η r),
        0 ≤ greenKernel m (ballInterior ε η ρ) 0 b - (ε * mε / t) * (n + 4 - t * e) := by
      rintro b ⟨hbA, a', ha', hmb⟩
      obtain ⟨z, hzA, hzb⟩ := hadj a' b hmb
      have hzB : z ∈ ball (0 : ℂ) (2 * r) := hAcell a' ha' hzA
      have hbB : (cell ε η b ∩ ball (0 : ℂ) (2 * r)).Nonempty := ⟨z, hzb, hzB⟩
      have hbS : (cell ε η b ∩ sphere (0 : ℂ) (2 * r)).Nonempty := by
        by_contra hnS
        exact hbA ⟨hbB, hnS⟩
      have hbmeet : (cell ε η b ∩ ball (0 : ℂ) ρ).Nonempty :=
        ⟨z, hzb, ball_subset_ball (by linarith) hzB⟩
      have hdb : diam (cell ε η b) < r / 4 := lt_of_lt_of_le (hsmall b hbmeet) hd4
      have hann := cell_norm_annulus (cell_isBounded hη b) hdb hbS
      obtain ⟨xb, hxbK, hexb⟩ := hexcl b
      obtain ⟨hxb1, hxb2⟩ := hann xb hxbK
      have hpole' := hpole xb (by linarith) (le_of_lt hxb2)
      have hg := hEg xb (le_of_lt hxb1) (le_of_lt (lt_trans hxb2 hr3))
      have hgb := floor_pole_value ht hg hpole'
      rw [rescale_exclusive_eq _ hxbK hexb] at hgb
      have h3 := (le_mul_iff_pole hε hmε ht).1 hgb
      linarith
    have hmain := nonneg_of_lapSum_nonpos_consecutive hlf hcons hAfin hsup hbd
    have hka := hmain k hkA
    have hgk : n + 4 - t * e ≤ t * (mε⁻¹ * (ε⁻¹ * greenKernel m (ballInterior ε η ρ) 0 k)) :=
      (le_mul_iff_pole hε hmε ht).2 (by linarith)
    -- the near value at an exclusive point of `H_k`
    obtain ⟨x, hxK, hex⟩ := hexcl k
    have hxρ : x ∈ ball (0 : ℂ) ρ := hKρ hxK
    have hxW : x ∈ closedBall (0 : ℂ) ρ := ball_subset_closedBall hxρ
    have hw := hEw x hxρ
    have hW := hM x hxW
    have hgx : n + 4 - t * e ≤
        t * rescale mε ε η (fun a => ε⁻¹ * greenKernel m (ballInterior ε η ρ) 0 a) x := by
      rw [rescale_exclusive_eq _ hxK hex]
      exact hgk
    have hnear := floor_near_value hn1 hs1 hen hw hW hgx
    rw [hkey x hxK hex]
    exact hnear
  · -- Case 8.1: the cell misses `B_r`; one exclusive point of the cell
    obtain ⟨x, hxK, hex⟩ := hexcl k
    have hxr : r ≤ ‖x‖ := by
      by_contra h
      exact hA ⟨x, hxK, by rw [mem_ball_zero_iff]; exact lt_of_not_ge h⟩
    have hxρ : ‖x‖ ≤ ρ := by
      have := hKball hxK
      rw [mem_ball_zero_iff] at this
      linarith
    have hxball : x ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff]
      have := hKball hxK
      rw [mem_ball_zero_iff] at this
      linarith
    have hxI := hKq hxK
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hxr
      linarith
    have hw := hEw x hxball
    have hg := hEg x hxr hxρ
    have hs := hS x hxI hx0
    have hspos : 0 < s := lt_of_lt_of_le (div_pos one_pos (by linarith)) hsn
    have hfar := floor_far_value ht hsn hen hw hg hs
    rw [hkey x hxK hex]
    linarith
end FloorProof

end MatedCRT
