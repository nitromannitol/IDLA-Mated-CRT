import MatedCRT.FirstPass.S6m.State
import MatedCRT.FirstPass.S6j.StateGood

/-!
# The per-state inputs of the concrete bridge, assembled (Lemma 6.8, write-up C4)

`Lemma68Concrete.StateTestInputs` (S6h/Schedule.lean) has three geometric fields and one walk-level field:
* `hloc`: the printed vertex bound at every middle vertex, from the good-event fields `S6j.GoodVertexInputs`
  (`S6j.hloc_of_goodState`, S6j/StateGood.lean);
* `hdy`, `hdiam`, `hS2`: the cell-diameter bounds and the hitting-before-exit property at the concrete centres and
  radii (`Lemma68C12.stateHdy`, `stateHdiam`, `stateHS2`, S6m/State.lean);
* `hgood`: the walk-level good event at the exit states, a named input (`StateGoodData.hgood`).

`StateGoodData` collects the named inputs; `stateTestInputs_of_data` assembles the structure. The scale hypotheses
of `hloc_of_goodState` are derived for every state: `Δ(p,r) ≤ R ≤ √Δ(p,r) ≤ r ≤ 1` for the selected radius `R`
(`cfgStateRadius_bounds`), using `2 ≤ p` (so `r^p ≤ r²`), and the logarithmic constant is `KL = 1`.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal

namespace MatedCRT

namespace Lemma68StateInputs

open Lemma68Concrete Lemma68C12 Lemma68Scales S6j WalkPotential

/-- The named good-event inputs of one configuration (write-up C4, C12-C14). On the good states `Good y`:
the good-event fields `GoodVertexInputs` at every middle vertex (sparsity scale `Δ(p,r)/100`), the region
`|z| + 2R < ρ` of the centres (the region hypothesis of `stateHS2`, `stateHdy`, `stateHdiam`), and the
walk-level good event at the exit states `X_{T_j}` (`hgood`, the event of the good states at the exit times). -/
structure StateGoodData (μ : Measure ℂ) (η : ℝ → ℂ) (m : ℤ → ℤ → ℕ) (a : ℤ) (ε ρ c0 C Cd Cg s1 β p r : ℝ)
    (good : ℂ → ℕ → Prop) (A : Set ℤ) (Good : ℤ → Prop) : Prop where
  hGood : ∀ y, Good y → ∀ v ∈ middleVertices ε η (cfgCentre ε η p r y) (cfgStateRadius ε η p r good y),
    GoodVertexInputs μ η m A ε c0 C Cd Cg s1 β (Delta p r / 100) r (cfgCentre ε η p r y)
      (cfgStateRadius ε η p r good y) v
  hreg : ∀ y, Good y → dist (cfgCentre ε η p r y) 0 + 2 * cfgStateRadius ε η p r good y < ρ
  hgood : ∀ j, ∀ᵐ x ∂srwLaw m a, cfgExit ε η p r good j x < ⊤ → Good (x (cfgExit ε η p r good j x).toNat)

/-- The scale bounds of the selected radius at every state: `0 < R`, `R ≤ r`, `r^p / 2 < R` and `Δ/100 ≤ R/100`,
from `Δ ≤ R ≤ √Δ`, `Δ ∈ (r^p/2, r^p]` and `r^p ≤ r²` (`2 ≤ p`, `0 < r < 1`). -/
lemma radius_scale_bounds {ε : ℝ} {η : ℝ → ℂ} {p r : ℝ} {good : ℂ → ℕ → Prop} (hp2 : 2 ≤ p)
    (hr0 : 0 < r) (hr1 : r < 1) (y : ℤ) :
    0 < cfgStateRadius ε η p r good y ∧ cfgStateRadius ε η p r good y ≤ r ∧
      r ^ p / 2 < cfgStateRadius ε η p r good y ∧ Delta p r / 100 ≤ cfgStateRadius ε η p r good y / 100 := by
  have hp : 0 < p := by linarith
  obtain ⟨hlo, hhi⟩ := cfgStateRadius_bounds ε η hp hr0 hr1 good y
  have hΔ : 0 < Delta p r := Lemma68Radius.delta_pos p r
  have hD := Delta_le_rpow hp hr0 hr1
  have h2 : r ^ p ≤ r ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hp2
  rw [Real.rpow_two, sq] at h2
  have hsq : Real.sqrt (Delta p r) ≤ r := by
    calc Real.sqrt (Delta p r) ≤ Real.sqrt (r * r) := Real.sqrt_le_sqrt (by linarith)
      _ = r := Real.sqrt_mul_self hr0.le
  exact ⟨lt_of_lt_of_le hΔ hlo, hhi.trans hsq, (half_rpow_lt_Delta hp hr0 hr1).trans_le hlo, by linarith⟩

/-- **Assembly of `StateTestInputs` (write-up C4).** For one configuration `(m, a, ε, η, p, r, good, A)`, the
per-state inputs of the concrete schedule follow from the named data `D : StateGoodData` and the cell-size input
`hsize` at the scale `d ≤ min (Δ/100) (c0 Δ)`. The constant `KL = 1` of `hloc_of_goodState` and the scale bounds are
derived (`radius_scale_bounds`); the remaining hypotheses are the constants (`hC`, `hCd`, `hCg`, `hc0`, `hc0'`, `hc0C`,
`hεc : ε ≤ 16 c0`, `hs1`), the environment (`hap`, `hη`, `hproper`), the local finiteness and cell adjacency of the
multiplicity, and `hqS : qStar ≤ 1/(288 Cd² K²)` with `K = Cg(1+(log 4-1))/(1-log 2)`. -/
theorem stateTestInputs_of_data {μ : Measure ℂ} [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    {m : ℤ → ℤ → ℕ} {a : ℤ} {A : Set ℤ} {ε ρ d c0 C Cd Cg s1 β p r qStar : ℝ} {η : ℝ → ℂ}
    {good : ℂ → ℕ → Prop} {Good : ℤ → Prop}
    (hap : IsAreaParametrized μ η) (hη : Continuous η) (hproper : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (hεc : ε ≤ 16 * c0) (hs1 : 0 < s1) (hC : 0 < C) (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hc0 : 0 < c0) (hc0' : c0 < 1 / 8) (hc0C : c0 ≤ Real.exp (-(2 * C)) / 16)
    (hp2 : 2 ≤ p) (hp3 : p ≤ 3) (hr0 : 0 < r) (hr1 : r < 1)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ u v : ℤ, m u v ≠ 0 → (cell ε η u ∩ cell ε η v).Nonempty)
    (hdc : d ≤ c0 * Delta p r) (hd : d ≤ Delta p r / 100)
    (hsize : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty → diam (cell ε η k) ≤ d)
    (hqS : qStar ≤ 1 / (288 * Cd ^ 2 * (Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2))
    (D : StateGoodData μ η m a ε ρ c0 C Cd Cg s1 β p r good A Good) :
    StateTestInputs m a ε η p r good A qStar c0 Good := by
  have hp : 0 < p := by linarith
  have hB := fun y => radius_scale_bounds (ε := ε) (η := η) (good := good) hp2 hr0 hr1 y
  have hRs : ∀ y, Good y → 0 < cfgStateRadius ε η p r good y ∧ cfgStateRadius ε η p r good y ≤ 1 ∧
      r ^ p / 2 < cfgStateRadius ε η p r good y ∧ c0 * cfgStateRadius ε η p r good y ≤ r ∧
      Delta p r / 100 ≤ cfgStateRadius ε η p r good y / 100 := by
    intro y _
    obtain ⟨h1, h2, h3, h4⟩ := hB y
    refine ⟨h1, by linarith, h3, ?_, h4⟩
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - c0) h1.le]
  have hLR : ∀ y, Good y → 1 + Real.log (1 / r) ≤ 1 * (1 + Real.log (1 / cfgStateRadius ε η p r good y)) := by
    intro y _
    obtain ⟨h1, h2, -, -⟩ := hB y
    have hinv : 1 / r ≤ 1 / cfgStateRadius ε η p r good y := one_div_le_one_div_of_le h1 h2
    have hlog := Real.log_le_log (one_div_pos.mpr hr0) hinv
    linarith
  have hloc := hloc_of_goodState (μ := μ) (η := η) (m := m) (A := A) (ε := ε) (c0 := c0) (C := C) (Cd := Cd)
    (Cg := Cg) (s1 := s1) (β := β) (p := p) (r := r) (qStar := qStar) (KL := 1)
    (Z := cfgCentre ε η p r) (Rs := fun y => cfgStateRadius ε η p r good y)
    (δs := fun _ => Delta p r / 100) (Good := Good) hap hη hproper hε hs1 hr0 hr1.le hC hCd hCg hc0 hc0' hc0C
    hεc hp3 hRs D.hGood zero_lt_one hLR (by rw [one_pow, div_one]; exact hqS)
  exact
    { hloc := hloc
      hdy := stateHdy good hp hr0 hr1 hd hsize D.hreg
      hdiam := stateHdiam good hε hη hp hr0 hr1 hc0.le hdc hd hsize D.hreg
      hS2 := stateHS2 good hε hη hproper hp hr0 hr1 hlf hcons hadj hd hsize D.hreg
      hgood := D.hgood }

end Lemma68StateInputs

end MatedCRT
