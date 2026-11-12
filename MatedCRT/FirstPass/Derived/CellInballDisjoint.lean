import MatedCRT.Defs.Map
import MatedCRT.Defs.Setting
import LatticeProb.Analysis.AreaParametrizedCurveCells

/-!
# Disjoint inballs of the cells of the mated-CRT map

The space-filling curve `η` is parametrized by `μ_h`-area (`IsAreaParametrized`, line 193), and
`μ_h` may be singular with respect to Lebesgue measure, so the cells `H^ε_k = η([ε (k - 1), ε k])`
need not meet in Lebesgue-null sets. What the parametrization gives is that two distinct cells
contain no common nonempty open set (`LatticeProb.pairwiseDisjoint_of_isOpen_subset_cell`): in
particular discs inscribed in distinct cells (inballs) are pairwise disjoint. This is the
disjointness hypothesis of the inball form of the flow-energy bound for the diagonal Green
function (BG20 Lemma 5.6, the cells of `lem-eff-res-diag`).

## Main results

* `MatedCRT.pairwiseDisjoint_of_isOpen_subset_cell_of_isAreaParametrized`
* `MatedCRT.pairwiseDisjoint_inball_cell`
* `MatedCRT.MatedCRTEnv.IsValid.ae_pairwiseDisjoint_inball_cell`
* `MatedCRT.isBounded_cell`
-/

open MeasureTheory Set Metric

namespace MatedCRT

/-- Open sets contained in distinct cells `H^ε_k` (`k ∈ s`, `ε > 0`) of a curve parametrized by
area are pairwise disjoint. -/
theorem pairwiseDisjoint_of_isOpen_subset_cell_of_isAreaParametrized {μ : Measure ℂ}
    {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) {s : Set ℤ}
    {O : ℤ → Set ℂ} (hO : ∀ k ∈ s, IsOpen (O k)) (hsub : ∀ k ∈ s, O k ⊆ cell ε η k) :
    s.PairwiseDisjoint O :=
  LatticeProb.pairwiseDisjoint_of_isOpen_subset_cell hap.1 hap.2.2.1 hap.2.2.2 hε hO hsub

/-- **Inballs of distinct cells are disjoint.** Discs `ball (c k) (r k)` inscribed in the cells
`H^ε_k` (`k ∈ s`, `ε > 0`) of a curve parametrized by area are pairwise disjoint. -/
theorem pairwiseDisjoint_inball_cell {μ : Measure ℂ} {η : ℝ → ℂ}
    (hap : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) {s : Set ℤ} {c : ℤ → ℂ} {r : ℤ → ℝ}
    (hball : ∀ k ∈ s, ball (c k) (r k) ⊆ cell ε η k) :
    s.PairwiseDisjoint fun k => ball (c k) (r k) :=
  pairwiseDisjoint_of_isOpen_subset_cell_of_isAreaParametrized hap hε
    (fun _ _ => isOpen_ball) hball

/-- For a valid environment, almost surely, for every `ε > 0`, discs inscribed in distinct cells
`H^ε_k` of `η` are pairwise disjoint. -/
theorem MatedCRTEnv.IsValid.ae_pairwiseDisjoint_inball_cell {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ (s : Set ℤ) (c : ℤ → ℂ) (r : ℤ → ℝ),
      (∀ k ∈ s, ball (c k) (r k) ⊆ cell ε (S.η ω) k) →
        s.PairwiseDisjoint fun k => ball (c k) (r k) := by
  filter_upwards [hS.isAreaParametrized] with ω hap ε hε s c r hball
  exact pairwiseDisjoint_inball_cell hap hε hball

/-- The cells of a continuous curve are bounded. -/
theorem isBounded_cell {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    Bornology.IsBounded (cell ε η k) :=
  (isCompact_Icc.image hη).isBounded

end MatedCRT
