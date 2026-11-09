import MatedCRT.Defs.Map

/-!
# FIRST PASS, Lemma 5.3: the smallest vertex of a point has the point in its cell (hmemcell, deterministic)

For a surjective curve `η` on which each point `x` is visited only at times bounded below (the frozen first-hit property
`FPFirstHitVisits`, Frozen/S5c.lean), the smallest vertex `a^ε_x = sInf {k | x ∈ H^ε_k}` (paper line 637, Defs/Map.lean
`vertexOf`) satisfies `x ∈ H^ε_{a^ε_x}`. This is the hypothesis `hmemcell` of `core_subset_fillCells_eventually`
(CoverEventually.lean). Pure arithmetic on the cells `η '' [ε(k-1), εk]`.
-/

namespace MatedCRT.S5c

open Set

/-- **The smallest vertex's cell contains the point** (hmemcell): see the module docstring. -/
theorem mem_cell_vertexOf_of_first_hit {η : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hsurj : Function.Surjective η) (hfirst : ∀ x : ℂ, BddBelow {s : ℝ | η s = x}) (x : ℂ) :
    x ∈ cell ε η (vertexOf ε η x) := by
  have hne : {k : ℤ | x ∈ cell ε η k}.Nonempty := by
    obtain ⟨s, hs⟩ := hsurj x
    have h1 := Int.le_ceil (s / ε)
    have h2 := Int.ceil_lt_add_one (s / ε)
    have hA : (s : ℝ) ≤ ε * ((⌈s / ε⌉ : ℤ) : ℝ) := by
      rw [mul_comm]
      exact (div_le_iff₀ hε).1 h1
    have hB : (((⌈s / ε⌉ : ℤ) : ℝ) - 1) * ε < s := (lt_div_iff₀ hε).1 (by linarith)
    exact ⟨⌈s / ε⌉, ⟨s, ⟨by linarith, hA⟩, hs⟩⟩
  have hbdd : BddBelow {k : ℤ | x ∈ cell ε η k} := by
    obtain ⟨s₀, hs₀⟩ := hfirst x
    refine ⟨⌈s₀ / ε⌉, fun k hk => ?_⟩
    obtain ⟨s', ⟨_, h2⟩, hs'⟩ := hk
    have hlow : s₀ ≤ s' := hs₀ (show s' ∈ {s : ℝ | η s = x} from hs')
    have hle : s₀ / ε ≤ (k : ℝ) := (div_le_iff₀ hε).2 (by nlinarith)
    exact Int.ceil_le.2 hle
  show x ∈ cell ε η (sInf {k : ℤ | x ∈ cell ε η k})
  exact Int.csInf_mem hne hbdd

end MatedCRT.S5c
