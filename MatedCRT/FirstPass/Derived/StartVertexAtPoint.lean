import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellMeasurable
import MatedCRT.FirstPass.S3t.CellGeometry
import MatedCRT.FirstPass.S5c.CellFirstHit

/-!
# The starting vertices of the embedded walks of Theorem 2.11 are measurable

The embedded walk of Theorem 2.11 started at the vertex of a cell of `H^{ε_n}` containing a fixed point `z₀ ∈ ℂ`
needs a start vertex `k_n : Ω → ℤ` that is a measurable function of the environment, with `z₀ ∈ H^{ε_n}_{k_n(ω)}`
almost surely.  The vertex `vertexOf ε_n (η ω) z₀` of the first cell containing `z₀` is almost surely such a
vertex, and the jointly measurable version `V (ω, x)` of `MatedCRTEnv.IsValid.exists_measurable_vertexOf` evaluated
at `x = z₀` is measurable for the ambient σ-algebra of `Ω`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Measurable starting vertices.**  For a valid environment, a curve `η'` that agrees almost surely with
`S.η`, meshes `ε_n > 0` and a point `z₀`, there are vertices `k_n : Ω → ℤ`, measurable for the ambient σ-algebra,
that are almost surely the first vertices of the cells `H^{ε_n}` containing `z₀`; in particular
`z₀ ∈ H^{ε_n}_{k_n(ω)}` for all `n` almost surely. -/
theorem MatedCRTEnv.IsValid.exists_measurable_startVertex_mem_cell {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (z₀ : ℂ) :
    ∃ k : ℕ → Ω → ℤ, (∀ n, Measurable (k n)) ∧
      (∀ᵐ ω ∂S.P, ∀ n, k n ω = vertexOf (ε n) (S.η ω) z₀) ∧
      ∀ᵐ ω ∂S.P, ∀ n, z₀ ∈ cell (ε n) (⇑(η' ω)) (k n ω) := by
  choose V hVm hV using fun n => hS.exists_measurable_vertexOf (hε0 n)
  have hV' : ∀ᵐ ω ∂S.P, ∀ n, ∀ x : ℂ, V n (ω, x) = vertexOf (ε n) (S.η ω) x := ae_all_iff.2 hV
  refine ⟨fun n ω => V n (ω, z₀), fun n => (hVm n).comp (measurable_id.prodMk measurable_const),
    ?_, ?_⟩
  · filter_upwards [hV'] with ω h1 n using h1 n z₀
  · filter_upwards [hV', hae, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω h1 h2 hap hp n
    rw [h1 n z₀, h2]
    exact MatedCRT.S5c.mem_cell_vertexOf_of_first_hit (hε0 n) hap.2.2.1
      (MatedCRT.TruncatedLaws.cellGeom_bddBelow_preimage hp) z₀

end MatedCRT.FirstPass.Derived
