import MatedCRT.FirstPass.Derived.HarnackPairFromCoupling
import MatedCRT.FirstPass.Derived.HarnackPairBall
import MatedCRT.FirstPass.Derived.ResistanceBoundGridEvent
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd
import MatedCRT.FirstPass.Derived.GreenUpperBoundOfInputs
import MatedCRT.FirstPass.S3c.ExitTimeBridge
import MatedCRT.FirstPass.S3i.GoodEvent
import LatticeProb.LQG.AnnulusEnergyBoundGrid

/-!
# The resistance bound (4.15) in every valid environment, from a reference environment

Berestycki–Gwynne (2020), proof of Lemma 4.3.  For a valid environment `S'` on the standard Borel space `ℝ`, the
library theorem `LatticeProb.LQG.polyHighProb_grid_annulus_energyOn_le` gives the energy bound (4.7) on every
admissible annulus of the polynomial grid of ratio `6/5`, mesh `ε^{α/4}` and radii at least `ε^β`, with polynomially
high probability; the cell size estimate (Lemma 2.8) bounds the diameters of the cells meeting `B_{(1+ρ)/2}` by
`ε^{1/(2+γ)²}`; and almost surely adjacent vertices have intersecting cells.  At a fixed sample these give the
resistance bound (4.15) (`resistanceEvent_of_gridEvent`).  The event depends on the Brownian pair only through the
edge counts, so it transfers to every valid environment of a model with the same normalized space-filling SLE law
(`measure_not_of_multEq_le_of_valid`).

* `hres_polyHighProb_reference`: the resistance bound (4.15) with polynomially high probability in `S'`;
* `hres_of_reference`: the hypothesis `hres` of `greenKernelLowerBoundStmt_of_pair`;
* `greenKernelLowerBoundStmt_of_reference`: Lemma 2.16 (Berestycki–Gwynne Lemma 4.4) from the reference environments
  and a one-sided mating-rigid set.
-/

set_option autoImplicit false

open MeasureTheory Metric Set Filter Topology _root_.HarmonicBalls
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- For `u < v` and `c > 0`, `ε^v ≤ c ε^u` for all small `ε > 0`. -/
theorem exists_rpow_le_mul_rpow_of_lt {u v c : ℝ} (huv : u < v) (hc : 0 < c) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ ε : ℝ, 0 < ε → ε < r₁ → ε ^ v ≤ c * ε ^ u := by
  obtain ⟨r₁, hr₁, h⟩ := MatedCRT.exists_rpow_le_of_small (sub_pos.mpr huv) hc
  refine ⟨r₁, hr₁, fun ε hε hεr => ?_⟩
  rw [show ε ^ v = ε ^ (v - u) * ε ^ u by rw [← Real.rpow_add hε, sub_add_cancel]]
  exact mul_le_mul_of_nonneg_right (h ε hε hεr) (Real.rpow_nonneg hε.le _)

/-- The library form of polynomially high probability is the paper's. -/
theorem polyHighProb_of_gauss {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    (h : LatticeProb.Gauss.PolyHighProb P E) : PolyHighProb P E := by
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := h
  exact ⟨p, hp, C, r₀, hr₀, hb⟩

/-- **Transfer of polynomially high probability** for events that depend on the Brownian pair only through its edge
counts, from a valid environment `S'` on a standard Borel space to every valid environment `S` of a model with the
same normalized space-filling SLE law. -/
theorem polyHighProb_of_multEq_of_valid {𝒮 𝒮' : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ) {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) {Q : ℝ → MatedCRTHarmonic.MatedCRT.Path2 → (ℝ → ℂ) → Prop}
    (hQ : ∀ (ε : ℝ) (ω ω' : MatedCRTHarmonic.MatedCRT.Path2) (η : ℝ → ℂ),
      bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) =
        bmEdgeCount ε (fun t => (ω' t).1) (fun t => (ω' t).2) → (Q ε ω η ↔ Q ε ω' η))
    (h' : PolyHighProb S'.P fun ε => {w | Q ε (S'.bm w) (S'.η w)}) :
    PolyHighProb S.P fun ε => {w | Q ε (S.bm w) (S.η w)} := by
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := h'
  exact ⟨p, hp, C, r₀, hr₀, fun r hr hrr =>
    (measure_not_of_multEq_le_of_valid hν hν' hγ0 hγ2 hS hS' hGnull hG r (Q := Q r) (hQ r)).trans
      (hb r hr hrr)⟩

/-- For every valid environment, almost surely, for every `ε > 0`, adjacent vertices of `𝒢^ε` have intersecting
cells (the mating-of-trees merge rule and the distinct values of the Brownian local minima). -/
private theorem ae_cellsMeet_of_isValid' {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  have hdist := ae_of_ae_map hC.measurable_curves.2.2.2.aemeasurable
    (MatedCRTHarmonic.MatedCRT.ae_locMinDistinct hC.boundaryLawBM)
  filter_upwards [hdist, hC.merge, htie] with ω hdist hmerge htie
  intro ε hε j k hedge
  have hLd : ∀ x y, x ≠ y → IsLocalMin (fun t => (S.bm ω t).1) x →
      IsLocalMin (fun t => (S.bm ω t).1) y → (S.bm ω x).1 ≠ (S.bm ω y).1 := by
    simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using hdist 0
  have hRd : ∀ x y, x ≠ y → IsLocalMin (fun t => (S.bm ω t).2) x →
      IsLocalMin (fun t => (S.bm ω t).2) y → (S.bm ω x).2 ≠ (S.bm ω y).2 := by
    simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using hdist 1
  have hLm : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel (fun u => (S.bm ω u).1) s t →
      S.η ω s = S.η ω t := by
    intro s t h
    rw [← htie.1]
    exact hmerge s t (Or.inl h)
  have hRm : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel (fun u => (S.bm ω u).2) s t →
      S.η ω s = S.η ω t := by
    intro s t h
    rw [← htie.1]
    exact hmerge s t (Or.inr h)
  exact cells_meet_of_bmEdgeCount hε.le (S.bm ω).continuous.fst (S.bm ω).continuous.snd
    hLd hRd hLm hRm hedge

/-- **The resistance bound (4.15) in a reference environment** (Berestycki–Gwynne (2020), proof of Lemma 4.3): for
a valid environment on `ℝ` there is `β > 0` such that for every `ρ ∈ (0, 1)`, with polynomially high probability as
`ε → 0`, every annulus `B_{3r/4}(η(a)) \ B̄_s(η(a))` with `a ∈ V(B_ρ)`, `r ≤ dist(η(a), ∂B_ρ)` and
`ε^β ≤ s ≤ r/4` carries a test function of ordered-pair energy at most `C₂ / log(3r/(4s))`. -/
theorem hres_polyHighProb_reference {𝒮ref : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {S' : MatedCRTEnv ℝ} (hS' : S'.IsValid 𝒮ref γ) :
    ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C₂ : ℝ, 1 ≤ C₂ ∧
      PolyHighProb S'.P fun ε => {ω | ∀ a ∈ cellVertices ε (S'.η ω) (ball 0 ρ), ∀ r : ℝ,
        r ≤ infDist (vertexPoint ε (S'.η ω) a) (sphere 0 ρ) → ∀ s : ℝ, ε ^ β ≤ s → s ≤ r / 4 →
        ∃ h : ℤ → ℝ, (∀ k ∈ cellVertices ε (S'.η ω) (closedBall (vertexPoint ε (S'.η ω) a) s), h k = 1) ∧
          (∀ k, k ∉ cellVertices ε (S'.η ω) (ball (vertexPoint ε (S'.η ω) a) (3 * r / 4)) → h k = 0) ∧
          ∀ T : Finset ℤ, Real.log (3 * r / 4 / s) *
            ((1 / 2) * ∑ k ∈ T, ∑ l ∈ T, (S'.mult ε ω k l : ℝ) * (h k - h l) ^ 2) ≤ C₂} := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η'', η₀, D, hae⟩ := hS'.matingOfTrees
  obtain ⟨α, hα, βT, hβT, hLP⟩ := LatticeProb.LQG.polyHighProb_grid_annulus_energyOn_le γ hγ0 hγ2 ℝ S'.P
    X X₀ hIG₀ B B' B₀ B₀' U ηL η'' η₀ S'.bm D
  have hγsq : 0 < (2 + γ) ^ 2 := by positivity
  set e : ℝ := 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 with he_def
  have he : 0 < e := by
    rw [he_def, div_sub_div_same]
    exact div_pos (by norm_num) hγsq
  set a : ℝ := α / 4 with ha_def
  have ha : 0 < a := by positivity
  set β : ℝ := min a (min βT e) / 4 with hβ_def
  have hmin_a : min a (min βT e) ≤ a := min_le_left _ _
  have hmin_T : min a (min βT e) ≤ βT := (min_le_right _ _).trans (min_le_left _ _)
  have hmin_e : min a (min βT e) ≤ e := (min_le_right _ _).trans (min_le_right _ _)
  have hβ : 0 < β := div_pos (lt_min ha (lt_min hβT he)) (by norm_num)
  have hβa : β < a := by linarith
  have hβe : β < e := by linarith
  have hβT2 : 2 * β < βT := by linarith
  have hβα : β ≤ α := by linarith
  refine ⟨β, hβ, fun ρ hρ0 hρ1 => ?_⟩
  set ρT : ℝ := (1 + ρ) / 2 with hρT_def
  have hρT0 : 0 < ρT := by linarith
  have hρT1 : ρT < 1 := by linarith
  obtain ⟨A, hA, hLPρ⟩ := hLP ρT hρT0 hρT1
  have hgrid := hLPρ (6 / 5) a 1 1 β 1 1 β 1 (by norm_num) zero_le_one ha.le (by linarith) one_pos hβ.le le_rfl
    one_pos hβ.le le_rfl
  have hζ1 : 1 / (2 + γ) ^ 2 < 1 := (div_lt_one hγsq).mpr (by nlinarith)
  have hcs := cellSizeEstimateStmt_holds 𝒮ref γ hγ0 hγ2 (1 / (2 + γ) ^ 2) ρT (div_pos one_pos hγsq) hζ1 hρT0
    hρT1 ℝ S' hS'
  have hboth := FirstPass36.polyHighProb_inter (polyHighProb_of_gauss hgrid) hcs
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨r₁, hr₁, h1⟩ := exists_rpow_le_mul_rpow_of_lt hβa (by norm_num : (0 : ℝ) < 1 / 100)
  obtain ⟨r₂, hr₂, h2⟩ := exists_rpow_le_mul_rpow_of_lt he (by linarith : (0 : ℝ) < (1 - ρ) / 4)
  obtain ⟨r₃, hr₃, h3⟩ := exists_rpow_le_mul_rpow_of_lt (by linarith : -βT < -β) hl
  obtain ⟨r₄, hr₄, h4⟩ := exists_rpow_le_mul_rpow_of_lt (by linarith : -βT < -(2 * β)) hl
  refine ⟨max 1 (2 * (A * (2 * Real.pi) + 1)), le_max_left _ _, ?_⟩
  refine S3cBridge.polyHighProb_mono_ae_small (r₁ := min (min r₁ r₂) (min (min r₃ r₄) 1))
    (lt_min (lt_min hr₁ hr₂) (lt_min (lt_min hr₃ hr₄) one_pos)) hboth (hae.and (ae_cellsMeet_of_isValid' hS')) ?_
  intro ε hε hεr ω hω hq
  have hε1 : ε < r₁ := hεr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε2 : ε < r₂ := hεr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε3 : ε < r₃ := hεr.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hε4 : ε < r₄ := hεr.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hεlt : ε < 1 := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hgω, hcsω⟩ := hω
  obtain ⟨⟨hη, -⟩, hadjω⟩ := hq
  have hx0 : 0 < 1 * ε ^ β := by positivity
  have hmx : ε ^ a ≤ 1 * ε ^ β / 100 := by
    have := h1 ε hε hε1
    rw [one_mul]
    linarith
  have hdx : ε ^ e < 1 * ε ^ β := by
    rw [one_mul]
    exact Real.rpow_lt_rpow_of_exponent_gt hε hεlt hβe
  have hρTd : ρ + 2 * ε ^ e ≤ ρT := by
    have := h2 ε hε hε2
    rw [Real.rpow_zero, mul_one] at this
    linarith
  have hreg1 : (1 * ε ^ β * Real.log 2)⁻¹ ≤ ε ^ (-βT) := by
    have := h3 ε hε hε3
    rw [one_mul, mul_inv, ← Real.rpow_neg hε.le, ← div_eq_mul_inv, div_le_iff₀ hl]
    linarith
  have hreg2 : ((1 * ε ^ β) ^ 2 * Real.log 2)⁻¹ ≤ ε ^ (-βT) := by
    have := h4 ε hε hε4
    have hsq : (1 * ε ^ β) ^ 2 = ε ^ (2 * β) := by
      rw [one_mul, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
      congr 1
      push_cast
      ring
    rw [hsq, mul_inv, ← Real.rpow_neg hε.le, ← div_eq_mul_inv, div_le_iff₀ hl]
    linarith
  have henergy : Real.log (1 / (1 * ε ^ β)) * ε ^ α ≤ 1 := by
    have hlog : Real.log (1 / (1 * ε ^ β)) ≤ 1 / (1 * ε ^ β) :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    calc Real.log (1 / (1 * ε ^ β)) * ε ^ α ≤ 1 / (1 * ε ^ β) * ε ^ α :=
          mul_le_mul_of_nonneg_right hlog (by positivity)
      _ = ε ^ (α - β) := by rw [one_mul, Real.rpow_sub hε]; ring
      _ ≤ 1 := Real.rpow_le_one hε.le hεlt.le (by linarith)
  have hdiam : ∀ k : ℤ, (MatedCRTHarmonic.MatedCRT.cell ε (η'' ω) k ∩ ball (0 : ℂ) ρT).Nonempty →
      diam (MatedCRTHarmonic.MatedCRT.cell ε (η'' ω) k) ≤ ε ^ e := by
    intro k hk
    have h' := hcsω k (by rw [← hη]; exact hk)
    rw [← hη] at h'
    exact h'.2
  have hadj : ∀ j k : ℤ, bmEdgeCount ε (fun t => (S'.bm ω t).1) (fun t => (S'.bm ω t).2) j k ≠ 0 →
      (MatedCRTHarmonic.MatedCRT.cell ε (η'' ω) j ∩ MatedCRTHarmonic.MatedCRT.cell ε (η'' ω) k).Nonempty := by
    intro j k hjk
    have h' := hadjω ε hε j k hjk
    rw [← hη] at h'
    exact h'
  have key := resistanceEvent_of_gridEvent (ε := ε) (ω := S'.bm ω)
    (H := MatedCRTHarmonic.MatedCRT.cell ε (η'' ω)) (p := vertexPoint ε ⇑(η'' ω)) (q := 6 / 5) (m := ε ^ a)
    (x := 1 * ε ^ β) (d := ε ^ e) (ρ := ρ) (ρT := ρT) (A := A) (α := α) (βT := βT)
    hε (by norm_num) (by norm_num) (by positivity) hx0 hmx hdx (by positivity) hρ0 hρTd hρT1.le hA.le hreg1 hreg2
    henergy (fun k => isPreconnected_Icc.image _ (η'' ω).continuous.continuousOn)
    (fun k => (isCompact_Icc.image (η'' ω).continuous).isBounded) hdiam
    (fun k => ⟨ε * (k : ℝ), ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩) hadj hgω
  intro a ha r hr s hs1 hs2
  rw [← hη] at ha hr ⊢
  exact key a ha r hr s ((one_mul _).trans_le hs1) hs2

/-- **The resistance bound (4.15) in every valid environment** (Berestycki–Gwynne (2020), Lemma 4.3), from the
reference environments of a model with the same normalized space-filling SLE law and a one-sided mating-rigid set
`G` (full for every `γ`-correlated Brownian law). The conclusion is the hypothesis `hres` of
`greenKernelLowerBoundStmt_of_pair`. -/
theorem hres_of_reference {𝒮 𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref) {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
      MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ r : ℝ,
        r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) → ∀ s : ℝ, ε ^ β ≤ s → s ≤ r / 4 →
        ∃ h : ℤ → ℝ, (∀ k ∈ cellVertices ε (S.η ω) (closedBall (vertexPoint ε (S.η ω) a) s), h k = 1) ∧
          (∀ k, k ∉ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (3 * r / 4)) → h k = 0) ∧
          ∀ T : Finset ℤ, Real.log (3 * r / 4 / s) *
            ((1 / 2) * ∑ k ∈ T, ∑ l ∈ T, (S.mult ε ω k l : ℝ) * (h k - h l) ^ 2) ≤ C₂} := by
  intro γ hγ0 hγ2
  obtain ⟨S', hS'⟩ := href γ hγ0 hγ2
  obtain ⟨β, hβ, hρ⟩ := hres_polyHighProb_reference hγ0 hγ2 hS'
  refine ⟨β, hβ, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨C₂, hC₂, hP⟩ := hρ ρ hρ0 hρ1
  refine ⟨C₂, hC₂, fun Ω _ S hS => ?_⟩
  exact polyHighProb_of_multEq_of_valid hν hνref hγ0 hγ2 hS hS' (hGnull γ hγ0 hγ2) hG
    (Q := fun ε ω η => ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ r : ℝ,
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρ) → ∀ s : ℝ, ε ^ β ≤ s → s ≤ r / 4 →
      ∃ h : ℤ → ℝ, (∀ k ∈ cellVertices ε η (closedBall (vertexPoint ε η a) s), h k = 1) ∧
        (∀ k, k ∉ cellVertices ε η (ball (vertexPoint ε η a) (3 * r / 4)) → h k = 0) ∧
        ∀ T : Finset ℤ, Real.log (3 * r / 4 / s) *
          ((1 / 2) * ∑ k ∈ T, ∑ l ∈ T,
            (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k l : ℝ) * (h k - h l) ^ 2) ≤ C₂)
    (fun ε ω ω' η hm => by rw [hm]) hP

/-- **Lemma 2.16** (Berestycki–Gwynne (2020), Lemma 4.4) for every model with a normalized space-filling SLE law
`ν`, from the reference environments of a model with law `ν` and a one-sided mating-rigid set `G` (full for every
`γ`-correlated Brownian law): the cell size estimate is a theorem, the pair events are `hPair_of_reference` and the
resistance bound (4.15) is `hres_of_reference`. -/
theorem greenKernelLowerBoundStmt_of_reference {𝒮 𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref) {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
      MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) : GreenKernelLowerBoundStmt 𝒮 :=
  greenKernelLowerBoundStmt_of_pair (cellSizeEstimateStmt_holds 𝒮)
    (hPair_of_reference hν hνref href hGnull hG) (hres_of_reference hν hνref href hGnull hG)

end MatedCRT.FirstPass.Derived
