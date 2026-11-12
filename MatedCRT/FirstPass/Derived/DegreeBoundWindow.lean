import MatedCRT.Defs.Setting

/-!
# The vertices whose cells meet a ball lie in a deterministic window

For a curve `η` parametrized by an area measure `μ` (`MatedCRT.IsAreaParametrized`: `η` is continuous and
`μ(η([a, b])) = b - a`), if the unit disk is covered by `η([-M, M])`, then `η` does not visit the unit disk at any
time `t` with `|t| > M`: otherwise a short segment `η([t, t + δ])` (or `η([t - δ, t])`) would lie in the disk, hence
in `η([-M, M])`, and adding it to `η([-M, t])` would not change the set while increasing its area by `δ`.

Consequently every vertex `k` of the mated-CRT map whose cell `H^ε_k = η([ε(k-1), εk])` meets `B_ρ` (`ρ ≤ 1`)
satisfies `|k| ≤ M/ε + 1`. This is the deterministic part of the proof of GMS19 Lemma 2.6 (the degree bound): the
covering `𝔻 ⊂ η([-M, M])` holds outside an event of probability `O(M^{-c})` (HS18 Proposition 6.2; GMS19 Lemma A.4
for the `γ`-cone), and on it the maximal degree over `V^ε(B_ρ)` is a maximum over the deterministic window
`[-M/ε - 1, M/ε + 1]`, to which the union bound with the exponential degree tail (GMS19 Lemma 2.5) applies.

## Main statements

* `MatedCRT.IsAreaParametrized.abs_le_of_mem_ball`
* `MatedCRT.IsAreaParametrized.abs_le_of_mem_cellVertices_ball`
* `MatedCRT.IsAreaParametrized.cellVertices_ball_subset_Icc`
-/

namespace MatedCRT

open MeasureTheory Set Metric

variable {μ : Measure ℂ} {η : ℝ → ℂ}

/-- An area-parametrized curve whose segment `η([-M, M])` covers the unit disk does not visit the unit disk at any time
`t` with `|t| > M`. -/
theorem IsAreaParametrized.abs_le_of_mem_ball (hη : IsAreaParametrized μ η) {M : ℝ}
    (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-M) M) {t : ℝ} (ht : η t ∈ ball (0 : ℂ) 1) : |t| ≤ M := by
  obtain ⟨hcont, -, -, harea⟩ := hη
  have hM : -M ≤ M := by
    obtain ⟨s, hs, -⟩ := hcov (mem_ball_self one_pos)
    exact hs.1.trans hs.2
  -- a neighbourhood of `t` is mapped into the unit disk
  have hopen : IsOpen (η ⁻¹' ball (0 : ℂ) 1) := isOpen_ball.preimage hcont
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hopen t ht
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hseg : ∀ s, |s - t| ≤ δ / 2 → η s ∈ η '' Icc (-M) M := by
    intro s hs
    refine hcov (hδsub ?_)
    rw [mem_ball, Real.dist_eq]
    linarith
  by_contra hlt
  rcases lt_abs.mp (not_le.mp hlt) with htM | htM
  · -- `t > M`: `η([-M, t + δ/2]) = η([-M, t])`
    have hEq : η '' Icc (-M) (t + δ / 2) = η '' Icc (-M) t := by
      apply Subset.antisymm
      · rintro _ ⟨s, hs, rfl⟩
        by_cases hst : s ≤ t
        · exact ⟨s, ⟨hs.1, hst⟩, rfl⟩
        · obtain ⟨u, hu, hu'⟩ := hseg s (by rw [abs_le]; constructor <;> linarith [hs.2])
          exact ⟨u, ⟨hu.1, hu.2.trans htM.le⟩, hu'⟩
      · exact image_mono (Icc_subset_Icc le_rfl (by linarith))
    have h1 := harea (-M) (t + δ / 2) (by linarith)
    have h2 := harea (-M) t (by linarith)
    rw [hEq, h2, ENNReal.ofReal_eq_ofReal_iff (by linarith) (by linarith)] at h1
    linarith
  · -- `t < -M`: `η([t - δ/2, M]) = η([t, M])`
    have htM' : t < -M := by linarith
    have hEq : η '' Icc (t - δ / 2) M = η '' Icc t M := by
      apply Subset.antisymm
      · rintro _ ⟨s, hs, rfl⟩
        by_cases hst : t ≤ s
        · exact ⟨s, ⟨hst, hs.2⟩, rfl⟩
        · obtain ⟨u, hu, hu'⟩ := hseg s (by rw [abs_le]; constructor <;> linarith [hs.1])
          exact ⟨u, ⟨htM'.le.trans hu.1, hu.2⟩, hu'⟩
      · exact image_mono (Icc_subset_Icc (by linarith) le_rfl)
    have h1 := harea (t - δ / 2) M (by linarith)
    have h2 := harea t M (by linarith)
    rw [hEq, h2, ENNReal.ofReal_eq_ofReal_iff (by linarith) (by linarith)] at h1
    linarith

/-- **The window of the vertices meeting `B_ρ`**: if `η([-M, M])` covers the unit disk and `ρ ≤ 1`, every vertex `k`
whose cell `η([ε(k-1), εk])` meets `B_ρ` has `|k| ≤ M/ε + 1`. -/
theorem IsAreaParametrized.abs_le_of_mem_cellVertices_ball (hη : IsAreaParametrized μ η) {M ε ρ : ℝ}
    (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-M) M) (hε : 0 < ε) (hρ : ρ ≤ 1) {k : ℤ}
    (hk : k ∈ cellVertices ε η (ball 0 ρ)) : |(k : ℝ)| ≤ M / ε + 1 := by
  obtain ⟨_, ⟨s, hs, rfl⟩, hsρ⟩ := hk
  have hs1 : η s ∈ ball (0 : ℂ) 1 := ball_subset_ball hρ hsρ
  have hsM := abs_le.mp (hη.abs_le_of_mem_ball hcov hs1)
  have hlo : ε * ((k : ℝ) - 1) ≤ M := hs.1.trans hsM.2
  have hhi : -M ≤ ε * (k : ℝ) := hsM.1.trans hs.2
  have hdiv : M / ε * ε = M := div_mul_cancel₀ M hε.ne'
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- The window in `Finset` form: the vertices whose cells meet `B_ρ` (`ρ ≤ 1`) lie in `[-N, N]` with
`N = ⌈M/ε⌉₊ + 1`. -/
theorem IsAreaParametrized.cellVertices_ball_subset_Icc (hη : IsAreaParametrized μ η) {M ε ρ : ℝ}
    (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-M) M) (hε : 0 < ε) (hρ : ρ ≤ 1) :
    cellVertices ε η (ball 0 ρ) ⊆
      (Finset.Icc (-((⌈M / ε⌉₊ : ℤ) + 1)) ((⌈M / ε⌉₊ : ℤ) + 1) : Set ℤ) := by
  intro k hk
  have h := abs_le.mp (hη.abs_le_of_mem_cellVertices_ball hcov hε hρ hk)
  have hc : M / ε ≤ (⌈M / ε⌉₊ : ℝ) := Nat.le_ceil _
  rw [Finset.coe_Icc, mem_Icc]
  constructor
  · have : (-(((⌈M / ε⌉₊ : ℤ) : ℝ) + 1)) ≤ (k : ℝ) := by push_cast; linarith [h.1]
    exact_mod_cast this
  · have : (k : ℝ) ≤ ((⌈M / ε⌉₊ : ℤ) : ℝ) + 1 := by push_cast; linarith [h.2]
    exact_mod_cast this

end MatedCRT
