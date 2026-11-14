import MatedCRT.FirstPass.Derived.NoStickingEvent
import MatedCRT.FirstPass.Derived.StickyWindowWalk
import MatedCRT.FirstPass.Derived.InterpKernelVertex
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import LatticeProb.Prob.InterpolatedLawMeasureBound

/-!
# Sticky windows of the interpolated quenched walk laws

For `ρ, δ > 0` and `a, T ≥ 0`, `stickyWindowSet ρ δ a T` is the set of continuous paths `f` for which some
`s ≤ T` has `f u ∈ B(0, ρ)` for all `u ≤ s + a` and `dist (f u) (f s) < δ` for all `u ∈ [s, s + a]`: the path
stays in the ball up to the end of a window of length `a` that starts before time `T`, and it nearly stands
still during the window.

* `interpWalkLaw_apply_le_of_start`: the interpolated law `P̃^ε(ω)(z)` is a mixture of the walk path laws from
  vertices whose cells come within `ε` of `z`; a measurable set of paths all starting in `B(0, ρ)` has
  `P̃^ε(ω)(z)`-mass at most `b` as soon as the walk path laws from the vertices with cells meeting `B(0, ρ)`
  give it mass at most `b` (the other vertices do not charge it, as the walk starts at its vertex).
* `walkPathLaw_stickyWindowSet_le`: the walk path law from a vertex charges `stickyWindowSet ρ δ a T` at most as
  much as the simple random walk violates the conclusion of the event of Proposition 6.14 of Berestycki-Gwynne
  at threshold `2 δ` (windows of `2 b` steps before the exit time from the vertices of cells meeting `B(0, ρ)`),
  provided `2 b ≤ m_ε a` (`StickyWindowWalk.exists_stepWindow`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal
open MatedCRT.FirstPass.Derived

namespace MatedCRT
namespace StickyWindowKernel

variable {Ω : Type} [MeasurableSpace Ω]

/-- Paths that, for some `s ≤ T`, stay in `B(0, ρ)` up to time `s + a` and move less than `δ` away from their
position at time `s` during `[s, s + a]`. -/
def stickyWindowSet (ρ δ : ℝ) (a T : ℝ≥0) : Set (ContinuousPath ℂ) :=
  {f | ∃ s : ℝ≥0, s ≤ T ∧ (∀ u, u ≤ s + a → f u ∈ ball (0 : ℂ) ρ) ∧
    ∀ u, s ≤ u → u ≤ s + a → dist (f u) (f s) < δ}

theorem stickyWindowSet_start (ρ δ : ℝ) (a T : ℝ≥0) :
    ∀ f ∈ stickyWindowSet ρ δ a T, f 0 ∈ ball (0 : ℂ) ρ := by
  rintro f ⟨s, -, hin, -⟩
  exact hin 0 zero_le

/-- **The interpolated law is a mixture over nearby vertices.**  See the module docstring. -/
theorem interpWalkLaw_apply_le_of_start (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε)
    {ω : Ω}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z,
      {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0) (z : ℂ) {ρ : ℝ}
    {s : Set (ContinuousPath ℂ)} (hs : MeasurableSet s) (hstart : ∀ f ∈ s, f 0 ∈ ball (0 : ℂ) ρ)
    {b : ℝ≥0∞}
    (h : ∀ k ∈ cellVertices ε (⇑(η' ω)) (ball (0 : ℂ) ρ),
      ((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω :
        ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) s ≤ b) :
    ((interpWalkLaw S η' ε ω z : ProbabilityMeasure (ContinuousPath ℂ)) :
      Measure (ContinuousPath ℂ)) s ≤ b := by
  rw [interpWalkLaw_eq_of_good S η' hloc hpos z]
  refine interpLaw_apply_le hloc hpos _ z hs fun k _ => ?_
  by_cases hv : vertexPoint ε (⇑(η' ω)) k ∈ ball (0 : ℂ) ρ
  · exact h k ⟨vertexPoint ε (⇑(η' ω)) k, NoStickingEvent.vertexPoint_mem_cell hε _ k, hv⟩
  · have hnull := walkPathLaw_start_null S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω
      (z := vertexPoint ε (⇑(η' ω)) k) (r := 0) (by simp)
    refine le_trans (measure_mono ?_) (hnull.le.trans zero_le)
    intro f hf
    have h0 := hstart f hf
    show 0 < dist (f 0) (vertexPoint ε (⇑(η' ω)) k)
    refine dist_pos.2 fun heq => hv ?_
    rw [← heq]
    exact h0

/-- **A walk that sticks violates the event of Proposition 6.14.**  See the module docstring. -/
theorem walkPathLaw_stickyWindowSet_le (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε)
    (ω : Ω) {ρ δ : ℝ} {a T : ℝ≥0} {b : ℕ} (hm : 0 < S.mε ε) (hb : 2 * (b : ℝ) ≤ S.mε ε * a)
    (hs : MeasurableSet (stickyWindowSet ρ δ a T)) (k : ℤ) :
    ((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω :
      ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) (stickyWindowSet ρ δ a T) ≤
      srwLaw (S.mult ε ω) k {X | ¬ ∀ j : ℕ,
        ((j + b : ℕ) : ℕ∞) ≤ vExitTime (cellVertices ε (⇑(η' ω)) (ball (0 : ℂ) ρ)) X →
          ∃ i₁ i₂ : ℕ, j ≤ i₁ ∧ i₁ ≤ i₂ ∧ i₂ < j + 2 * b ∧
            2 * δ ≤ ‖vertexPoint ε (⇑(η' ω)) (X i₂) - vertexPoint ε (⇑(η' ω)) (X i₁)‖} := by
  have hcoe : ((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω :
      ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) =
      Measure.map (interpPathCM (vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε)) (srwLaw (S.mult ε ω) k) := rfl
  rw [hcoe, Measure.map_apply (measurable_interpPathCM _ _) hs]
  refine measure_mono ?_
  intro X hX hall
  obtain ⟨s, -, hin, hstill⟩ := hX
  obtain ⟨j, hj1, hj2⟩ := StickyWindowWalk.exists_stepWindow (vertexPoint ε (⇑(η' ω))) hm X hb
    (cellVertices ε (⇑(η' ω)) (ball (0 : ℂ) ρ))
    (fun w hw => ⟨_, NoStickingEvent.vertexPoint_mem_cell hε _ w, hw⟩) hin hstill
  obtain ⟨i₁, i₂, h1, h12, h2, hge⟩ := hall j hj1
  exact absurd (hj2 i₁ i₂ h1 h12 h2) (not_lt.2 hge)

end StickyWindowKernel
end MatedCRT
