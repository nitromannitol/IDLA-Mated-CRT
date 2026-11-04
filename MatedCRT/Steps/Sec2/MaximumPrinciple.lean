import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple

/-!
# Lemma 2.13 (maximum principle, as corrected [C2]) from `AdjacentCellsMeetAeStep`

Almost surely, for every `ε > 0`, the map `𝒢^ε` is locally finite (`MatedCRTEnv.IsValid.ae_isLocallyFiniteMult`, from
`AdjacentCellsMeetAeStep` and the properness and continuity of `η`) and consecutive vertices are adjacent
(`MatedCRTEnv.mult_succ_ne_zero`), so an edge leaves every nonempty finite set (`escape_of_adjacent_succ`). For a
nonempty finite `A`, the boundary `∂A` is then finite and nonempty; with `b ∈ ∂A` maximizing `u` on `∂A`, the
maximum principle on a finite set with the escape property (`nonpos_of_lapSum_nonneg`,
MatedCRT/Proofs/WalkPotential/MaximumPrinciple.lean) applied to `u - u(b)` gives `u ≤ u(b)` on `A`.
-/

namespace MatedCRT

open MeasureTheory Set

/-- **Lemma 2.13** (as corrected [C2]) from `AdjacentCellsMeetAeStep` (a.s. adjacent vertices have intersecting
cells, used here only for the local finiteness of `𝒢^ε`). -/
theorem maximumPrinciple_of_steps {𝒮 : SpaceFillingSLEModel} (hcell : AdjacentCellsMeetAeStep 𝒮) :
    MaximumPrincipleStmt 𝒮 := by
  intro γ hγ0 hγ2 Ω _ S hS
  filter_upwards [hS.ae_isLocallyFiniteMult hγ0 hγ2 hcell] with ω hlf
  intro ε hε A hAne hA u hu a ha
  have hlf' := hlf ε hε
  have hesc := escape_of_adjacent_succ (S.mult_succ_ne_zero hε.le ω) hA
  have hbfin : (vBoundary (S.mult ε ω) A).Finite := by
    refine (hA.biUnion fun x _ => hlf' x).subset ?_
    rintro y ⟨-, x, hx, hxy⟩
    exact mem_biUnion hx hxy
  obtain ⟨x₀, hx₀, y₀, hy₀, hx₀y₀⟩ := hesc A Subset.rfl hAne
  have hbne : (vBoundary (S.mult ε ω) A).Nonempty := ⟨y₀, hy₀, x₀, hx₀, hx₀y₀⟩
  obtain ⟨b, hb, hbmax⟩ := exists_max_image _ u hbfin hbne
  refine ⟨b, hb, ?_⟩
  have key : u a - u b ≤ 0 := by
    refine nonpos_of_lapSum_nonneg hlf' hA hesc (w := fun x => u x - u b) ?_ ?_ a ha
    · intro x hx
      have hshift : lapSum hlf' (fun y => u y - u b) x = lapSum hlf' u x := by
        simp only [lapSum, sub_sub_sub_cancel_right]
      rw [hshift, ← mLaplacian_mul_mdeg hlf' u x]
      exact mul_nonneg (hu x hx) (Nat.cast_nonneg _)
    · intro x hx y hxy hy
      show u y - u b ≤ 0
      linarith [hbmax y ⟨hy, x, hx, hxy⟩]
  linarith

end MatedCRT
