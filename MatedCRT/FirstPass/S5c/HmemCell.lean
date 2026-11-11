import MatedCRT.Defs.Sandpile
import MatedCRT.Defs.Map

/-!
# FIRST PASS, 5.3 (MeanValueSurplusLowerStep), hmemcell: local first-hit cell membership

The deterministic helper:
if every cell meeting `B_ρ` has diameter at most `ρ/2`, then every point `x ∈ B_{ρ/3}` lies in the cell of its
smallest-label vertex `vertexOf ε η x` (the paper's `eq:plane-to-embedding` convention), and that vertex lies in
`ballInterior ε η ρ`. The proof: the set of labels whose cell contains `x` is nonempty (the cell of `⌈u/ε⌉` contains `η(u)`
for any `u` with `η(u) = x`), lies in the finite set `ballInterior` (each such cell lies in `B_ρ` and misses its
boundary), and has a least element.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology

/-- **Local first-hit cell membership**: under the finiteness of `ballInterior` and the
small-cell bound on `B_ρ`, each `x ∈ B_{ρ/3}` lies in the cell of `vertexOf ε η x`, and that label is in `ballInterior`. -/
theorem mem_cell_vertexOf_of_small_cells {ε ρ : ℝ} {η : ℝ → ℂ}
    (hε : 0 < ε) (hρ : 0 < ρ) (hη : Continuous η) (hsurj : Function.Surjective η)
    (hfin : (ballInterior ε η ρ).Finite)
    (hsmall : ∀ a ∈ cellVertices ε η (ball (0 : ℂ) ρ), diam (cell ε η a) ≤ ρ / 2) :
    ∀ x ∈ ball (0 : ℂ) (ρ / 3),
      x ∈ cell ε η (vertexOf ε η x) ∧ vertexOf ε η x ∈ ballInterior ε η ρ := by
  intro x hx
  have hx' : ‖x‖ < ρ / 3 := mem_ball_zero_iff.mp hx
  -- Step 1: the label set of `x` is nonempty: the cell of `⌈u/ε⌉` contains `x = η u`.
  obtain ⟨u, hu⟩ := hsurj x
  have hcell_a : x ∈ cell ε η ⌈u / ε⌉ := by
    have h1 : ((⌈u / ε⌉ : ℤ) : ℝ) - 1 < u / ε := by
      have := Int.ceil_lt_add_one (u / ε)
      linarith
    have h2 : u / ε ≤ ((⌈u / ε⌉ : ℤ) : ℝ) := Int.le_ceil _
    have e1 : ε * (((⌈u / ε⌉ : ℤ) : ℝ) - 1) ≤ u := by
      rw [mul_comm]
      exact ((lt_div_iff₀ hε).mp h1).le
    have e2 : u ≤ ε * ((⌈u / ε⌉ : ℤ) : ℝ) := by
      rw [div_le_iff₀ hε] at h2
      linarith [mul_comm ((⌈u / ε⌉ : ℤ) : ℝ) ε]
    exact ⟨u, ⟨e1, e2⟩, hu⟩
  have hIne : ({k : ℤ | x ∈ cell ε η k}).Nonempty := ⟨_, hcell_a⟩
  -- Step 2: every label of `x` lies in `ballInterior ε η ρ`.
  have hsub : {k : ℤ | x ∈ cell ε η k} ⊆ ballInterior ε η ρ := by
    intro k hk
    have hxk : x ∈ cell ε η k := hk
    have hxball : x ∈ ball (0 : ℂ) ρ := mem_ball_zero_iff.mpr (by linarith)
    have hmeet : (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty := ⟨x, hxk, hxball⟩
    have hdiam := hsmall k hmeet
    have hbdd : Bornology.IsBounded (cell ε η k) := (isCompact_Icc.image hη).isBounded
    -- the cell lies in the open ball `B_ρ`
    have hcellball : cell ε η k ⊆ ball (0 : ℂ) ρ := by
      intro y hy
      have h1 : dist y x ≤ diam (cell ε η k) := dist_le_diam_of_mem hbdd hy hxk
      have h2 : dist y 0 ≤ dist y x + dist x 0 := dist_triangle y x 0
      simp only [dist_zero_right] at h2
      rw [mem_ball_zero_iff]
      linarith
    show k ∈ cellVertices ε η (ball (0 : ℂ) ρ) \ cellVertices ε η (frontier (ball (0 : ℂ) ρ))
    refine ⟨hmeet, ?_⟩
    rintro ⟨y, hy, hyfr⟩
    rw [frontier_ball (0 : ℂ) hρ.ne'] at hyfr
    have hyn : ‖y‖ = ρ := mem_sphere_zero_iff_norm.mp hyfr
    have hyball : y ∈ ball (0 : ℂ) ρ := hcellball hy
    have hyl : ‖y‖ < ρ := mem_ball_zero_iff.mp hyball
    linarith
  -- Step 3: the least label exists (finite set) and realises the cell of `x`.
  have hmem : sInf {k : ℤ | x ∈ cell ε η k} ∈ {k : ℤ | x ∈ cell ε η k} :=
    hIne.csInf_mem (hfin.subset hsub)
  have hv : vertexOf ε η x = sInf {k : ℤ | x ∈ cell ε η k} := rfl
  rw [hv]
  exact ⟨hmem, hsub hmem⟩

end MatedCRT.S5c
