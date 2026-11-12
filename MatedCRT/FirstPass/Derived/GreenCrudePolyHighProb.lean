import MatedCRT.FirstPass.Derived.GreenCellCrudeEventually
import MatedCRT.Draft.Section2
import MatedCRT.External.SLE
import MatedCRT.Proofs.Sec7.MassBoundOdometer.PolyHighProb
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# The crude Green function bound with polynomially high probability

BG20 Lemma 5.6 (Lemma 2.15 of the paper, `GreenFunctionCrudeBoundStmt`), reduction to the cell
events. The cell size estimate (Lemma 2.8, `CellSizeEstimateStmt`) gives the diameters of the
cells meeting `B_ρ` between two powers of `ε`, and the degree bound (`DegreeBoundInput`) gives
`deg^ε(a) ≤ (log ε⁻¹)² ≤ ε^{-δ}` for small `ε`. Together with the inradius event (each cell
meeting `B_ρ` contains a Euclidean disc of radius `ε^{δ/4} diam`) and the segment-path event
(every vertex of `V^ε(B_ρ) \ V^ε(∂B_ρ)` has a family of segment paths in `V^ε(B_ρ)` leaving it),
both with polynomially high probability, the event of Lemma 2.15 holds with polynomially high
probability whenever `5δ/2 < ζ`. The pathwise bound is
`MatedCRTEnv.IsValid.exists_ae_greenFn_le_rpow_of_cellBounds`.

## Main statements

* `MatedCRT.eventually_log_inv_sq_le_rpow_neg`: `(log ε⁻¹)² ≤ ε^{-δ}` for small `ε > 0`.
* `MatedCRT.MatedCRTEnv.IsValid.polyHighProb_greenFn_le_of_inball_of_segmentPaths`
* `MatedCRT.greenFunctionCrudeBoundStmt_of_inball_of_segmentPaths`
-/

open Set Metric MeasureTheory Filter Topology Asymptotics HarmonicBalls

namespace MatedCRT

/-- A power of the logarithm is small against any negative power: `(log ε⁻¹)² ≤ ε^{-δ}` for all
small `ε > 0`, for every `δ > 0`. -/
theorem eventually_log_inv_sq_le_rpow_neg {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.log ε⁻¹ ^ 2 ≤ ε ^ (-δ) := by
  have h := (isLittleO_log_rpow_atTop (half_pos hδ)).bound one_pos
  have h1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  filter_upwards [tendsto_inv_nhdsGT_zero.eventually (h.and h1), self_mem_nhdsWithin]
    with ε hb hε
  obtain ⟨hb, hx⟩ := hb
  have hε0 : 0 < ε := hε
  have hl : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg hx
  have hp : 0 ≤ ε⁻¹ ^ (δ / 2) := Real.rpow_nonneg (inv_nonneg.2 hε0.le) _
  rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg hp, one_mul] at hb
  calc Real.log ε⁻¹ ^ 2 ≤ (ε⁻¹ ^ (δ / 2)) ^ 2 := pow_le_pow_left₀ hl hb 2
    _ = ε ^ (-δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hε0.le), Real.inv_rpow hε0.le,
        ← Real.rpow_neg hε0.le]
      congr 1
      push_cast
      ring

/-- The inradius event of the cells meeting `B_ρ`: each of them contains a Euclidean disc of
radius `ε^{δ/4}` times its diameter. -/
def MatedCRTEnv.cellInballEvent {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (δ ρ ε : ℝ) : Set Ω :=
  {ω | ∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∃ c : ℂ,
    ball c (ε ^ (δ / 4) * diam (cell ε (S.η ω) k)) ⊆ cell ε (S.η ω) k}

/-- The segment-path event: every vertex `x` of `V^ε(B_ρ) \ V^ε(∂B_ρ)` has a family of segment
paths (from a point `u` with `‖u‖ ≤ U`, indexed by the angle) which are nodup chains of the
mated-CRT map starting at `x`, stay in `V^ε(B_ρ)` and end outside `V^ε(B_ρ) \ V^ε(∂B_ρ)`. -/
def MatedCRTEnv.segmentPathEvent {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ρ U ε : ℝ) : Set Ω :=
  {ω | ∀ x ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ), ∃ (u : ℂ) (ℓ : ℝ) (Y : Finset ℤ)
    (F : Finset ℤ → List ℤ), ‖u‖ ≤ U ∧ (∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) ∧
    (∀ θ, (LatticeProb.segmentPath u ℓ (cell ε (S.η ω)) Y F θ).Nodup) ∧
    (∀ θ, (LatticeProb.segmentPath u ℓ (cell ε (S.η ω)) Y F θ).IsChain
      fun a b => S.mult ε ω a b ≠ 0) ∧
    (∀ θ, ∃ l, LatticeProb.segmentPath u ℓ (cell ε (S.η ω)) Y F θ = x :: l ∧
      (∀ v ∈ x :: l, v ∈ cellVertices ε (S.η ω) (ball 0 ρ)) ∧
      (x :: l).getLast (List.cons_ne_nil x l) ∉ interiorCellVertices ε (S.η ω) (ball 0 ρ))}

/-- **Crude Green function bound with polynomially high probability (BG20 Lemma 5.6),
reduction to the cell events.** For a valid environment, `0 < ρ < 1` and `0 < δ` with
`5δ/2 < ζ`: the cell size estimate, the degree bound, and the inradius and segment-path events
with polynomially high probability give `G_{B_ρ}(a, b) ≤ ε^{-ζ}` for all `a, b ∈ V^ε(B_ρ)` with
polynomially high probability. -/
theorem MatedCRTEnv.IsValid.polyHighProb_greenFn_le_of_inball_of_segmentPaths
    {𝒮 : SpaceFillingSLEModel} (hcell : CellSizeEstimateStmt 𝒮) (hdeg : DegreeBoundInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {δ ζ ρ U : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hδ : 0 < δ)
    (hζ : 5 * δ / 2 < ζ) (hU : 0 ≤ U) (hE2 : PolyHighProb S.P (S.cellInballEvent δ ρ))
    (hP : PolyHighProb S.P (S.segmentPathEvent ρ U)) :
    PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
        greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a b ≤ ε ^ (-ζ)} := by
  have h2γ : 0 < (2 + γ) ^ 2 := by positivity
  have hζ'0 : 0 < 1 / (2 + γ) ^ 2 := by positivity
  have hζ'1 : 1 / (2 + γ) ^ 2 < 1 := by rw [div_lt_one h2γ]; nlinarith
  have hq : 0 ≤ 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 := by
    have e : 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 := by ring
    rw [e]
    exact hζ'0.le
  obtain ⟨ε₀, hε₀, hae⟩ := hS.exists_ae_greenFn_le_rpow_of_cellBounds hγ hγ2
    (p := 2 / (2 - γ) ^ 2 + 1 / (2 + γ) ^ 2) hq hρ.le hU hζ
  obtain ⟨ε₁, hε₁, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.1 (eventually_log_inv_sq_le_rpow_neg hδ)
  refine Sec7.polyHighProb_of_inter_ae
    ((hcell γ hγ hγ2 _ ρ hζ'0 hζ'1 hρ hρ1 Ω S hS).inter hE2)
    ((hdeg γ hγ hγ2 ρ hρ hρ1 Ω S hS).inter hP) hae (lt_min hε₀ hε₁) ?_
  rintro ε hε hεr ω ⟨h1, h2⟩ ⟨h3, h4⟩ hω a - b -
  have hlog : Real.log ε⁻¹ ^ 2 ≤ ε ^ (-δ) := hsub ⟨hε, hεr.trans_le (min_le_right _ _)⟩
  exact hω ε ⟨hε, hεr.trans_le (min_le_left _ _)⟩ (fun k hk => h1 k hk) h2
    (fun k hk => (h3 k hk).trans hlog) h4 a b

/-- **Lemma 2.15 from the cell events.** The cell size estimate, the degree bound, the inradius
event at every exponent and the segment-path event (at some radius `U`) with polynomially high
probability give `GreenFunctionCrudeBoundStmt`. -/
theorem greenFunctionCrudeBoundStmt_of_inball_of_segmentPaths {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (hE2 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ δ ρ : ℝ, 0 < δ → 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        PolyHighProb S.P (S.cellInballEvent δ ρ))
    (hP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ U : ℝ, 0 ≤ U ∧ PolyHighProb S.P (S.segmentPathEvent ρ U)) :
    GreenFunctionCrudeBoundStmt 𝒮 := by
  intro γ hγ hγ2 ρ ζ hρ hρ1 hζ _ Ω _ S hS
  obtain ⟨U, hU, hPU⟩ := hP γ hγ hγ2 ρ hρ hρ1 Ω S hS
  have hδ : 0 < ζ / 5 := by positivity
  exact hS.polyHighProb_greenFn_le_of_inball_of_segmentPaths hcell hdeg hγ hγ2 hρ hρ1 hδ
    (by linarith) hU (hE2 γ hγ hγ2 _ ρ hδ hρ hρ1 Ω S hS) hPU

end MatedCRT
