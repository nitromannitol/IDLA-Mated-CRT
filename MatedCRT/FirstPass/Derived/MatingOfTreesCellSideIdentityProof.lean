import MatedCRT.FirstPass.Derived.WindowChartBGDiscreteLawIntrinsic
import MatedCRT.FirstPass.Derived.ValidPeanosphere
import MatedCRT.FirstPass.Derived.BlockCellMinInjective
import LatticeProb.LQG.PeanosphereContactContinuity

/-!
# The multiplicities of the mated-CRT map are the frontier-side multiplicities of the cells

This file proves `MatingOfTreesCellSideIdentity` (`WindowChartBGDiscreteLawIntrinsic.lean`): in a valid environment,
for every cell size `ε > 0`, almost surely the edge multiplicities `S.mult ε` of Definition 1.1 (read off the
boundary-length pair `(L, R)`) are the frontier-side multiplicities `cellSideMult ε (S.η ω)` of the cells (read off
the curve, `CellSideMult.lean`). The argument is the written answer MQ-sbl-31, section "Why the count is the Brownian
count" (lines 26-40).

Validity supplies, on the same probability space, the boundary-length pair `S.bm` with the law of a correlated
two-sided Brownian motion and the curve `S.η` forming a Peanosphere (`ValidPeanosphere.lean`): the times identified
by the curve are exactly those identified by the contour functions (Duplantier–Miller–Sheffield, arXiv:1409.7055,
Lemmas 8.8 and 8.14, the coupling fields `merge` and `onlyMerge`), and the fibres of the curve are finite (Lemma 8.13,
the coupling field `visitBound`). For a coordinate `X = L` or `R`, write a *weak level pair* `v ≤ w` when
`X v = X w ≤ X` on `[v, w]`.

* **Contacts are weak level pairs** (`isWeakLevelPair_of_cellSideContact`, MQ-sbl-31 lines 28-32): if `D_η(v, w)`,
  every common continuum of `η(P) ∩ η(Q)` contains a point visited at most twice (named hypothesis
  `SpaceFillingSLETriplePointsNoContinuum`), so its two visits are directly identified by `L` or `R`; shrinking `P`,
  `Q` and using that the weak level pairs form a closed set gives `v ∼_L w` or `v ∼_R w`.
* **A branch time is a centred minimum** (`isCenteredMin_of_mem_cellSideBranchTimes`, line 34): two of the three
  pairs of a witness `(s, u, t)` use the same coordinate, and then `X s = X u = X t = min_{[s, t]} X`; hence the
  adjacency condition (1.1) holds for `X` (`IsCenteredMin.intervalAdjacent`) and `u` minimizes `X` on the intervening
  interval.
* **Strict windows give branch times** (`LevelContactData.exists_mem_cellSideBranchTimes`, lines 36-38): at a strict
  window the minimum `g` of `X` on the intervening interval is attained at a unique time `u`, the last visit `s` to
  `g` in the first cell and the first visit `t` in the second are witnesses, and the three contacts come from the
  levels just above `g` (`cellSideContact_of_excursion`) and just below `g` (`cellSideContact_of_dips`): the last and
  first visits to these levels are identified by the curve, and their image is a continuum of positive diameter
  (`LevelContactData.containsNondegenerateContinuum`: it varies continuously with the level by
  `Peanosphere.continuousOn_eta_ellMinus`, and is not a point since the fibres are finite).
* The adjacency condition is a.s. strict (distinct heights of local minima and descent at the cell endpoints), the
  minimizers of `L` and `R` on the intervening interval differ (`CorrelatedBMNoCommonLocalMin`, proved by
  `correlatedBMNoCommonLocalMin_holds`), and
  consecutive cells carry one edge.

Hypotheses (literature, on general objects):
* `SpaceFillingSLETriplePointsNoContinuum 𝒮` (named hypothesis): for whole-plane space-filling SLE_κ, `κ > 4`, almost
  surely the points visited at least three times contain no continuum of positive diameter (Gwynne–Holden–Miller,
  arXiv:1512.01223, Corollary 6.5; DMS (8.9) and Lemmas 8.12-8.13).
* `CorrelatedBMNoCommonLocalMin`: a correlated planar Brownian motion almost surely has no time which is a local
  minimum of both coordinates (Le Gall, two-sided cone points, Chapter III, Theorem 3(i)). Proved:
  `correlatedBMNoCommonLocalMin_holds` (`PlanarBMConePoints/Holds.lean`).
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open MatedCRTHarmonic.MatedCRT (Path2 lrCoord IsCorrelatedBM2)
open MatedCRTHarmonic.RouteM (Peanosphere lCoord rCoord ellMinus ellPlus rhoMinus rhoPlus directRel)
open scoped NNReal

namespace MatedCRT

/-! ### The named hypotheses -/

/-- The points visited at least three times by a curve `η : ℝ → ℂ`: the points `z = η t₁ = η t₂ = η t₃` for times
`t₁ < t₂ < t₃`. -/
def curveTriplePoints (η : ℝ → ℂ) : Set ℂ :=
  {z | ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧ η t₁ = z ∧ η t₂ = z ∧ η t₃ = z}

/-- **Named hypothesis: the multiple points of whole-plane space-filling SLE contain no continuum.** It holds for the
genuine whole-plane space-filling SLE_κ, `κ > 4` (Gwynne–Holden–Miller, arXiv:1512.01223, Corollary 6.5; DMS (8.9) and
Lemmas 8.12-8.13), and so for a model whose curves agree with it up to increasing time homeomorphisms, such as the
canonical model. What the cell-side identity in a valid environment uses is `ValidEnvTriplePointsNoContinuum`
(`MatingOfTreesCellSideIdentityValid.lean`, `matingOfTreesCellSideIdentity_of_valid`), which is derived from
`CorrelatedBMPeanosphereTriplePointsNoContinuum` (`validEnvTriplePointsNoContinuum_of_peanosphere`).

For `κ > 4` and a whole-plane space-filling SLE_κ `η` (independent of `𝓕`, in the model `𝒮`), almost surely the set
of points visited at least three times (`curveTriplePoints`) contains no continuum of positive diameter. The set is
invariant under increasing reparametrization of the curve. Sources: for `κ ≥ 8` the set is countable
(Duplantier–Miller–Sheffield, arXiv:1409.7055, (8.9) and Lemmas 8.12-8.13); for `4 < κ < 8` Gwynne–Holden–Miller,
arXiv:1512.01223, Corollary 6.5 (p. 40), `dim_H ≤ 3(8 - κ)/8`, applied on the countably many simple frontier subarcs
of dimension `1 + 2/κ` (written answer MQ-sbl-29, line 23; MQ-sbl-31, line 30). -/
def SpaceFillingSLETriplePointsNoContinuum (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ) (𝓕 : MeasurableSpace Ω) (κ : ℝ)
    (η : Ω → ℝ → ℂ), 4 < κ → @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 κ η →
      ∀ᵐ ω ∂P, ¬ ContainsNondegenerateContinuum (curveTriplePoints (η ω))

/-- **A correlated planar Brownian motion has no common local minimum of its coordinates.** Proved:
`correlatedBMNoCommonLocalMin_holds` (`PlanarBMConePoints/Holds.lean`), from Le Gall's theorem
(`planarBMNoTwoSidedConePoints`, proved from `PlanarBMConePoints.noTwoSidedConePoints`).

For `0 < γ < 2` and the law `μ` of a `γ`-correlated two-sided planar Brownian motion `(L, R)` (`IsCorrelatedBM2 γ μ`,
correlation `-cos(πγ²/4)`), almost surely no time `u` is a local minimum of both `L` and `R`. Writing `(L, R) = A W`
with `W` a standard planar Brownian motion, a common local minimum is a two-sided cone time of `W` for the cone
`A⁻¹[0, ∞)²`, of angle `πγ²/4 < π`. Source: Le Gall, *Some properties of planar Brownian motion* (École d'été de
Probabilités de Saint-Flour XX, 1990), Chapter III, Theorem 3(i), p. 136 (no two-sided cone points of angle less than
`π`), localized at rational times; written answer MQ-sbl-31, line 38. -/
def CorrelatedBMNoCommonLocalMin : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
    ∀ᵐ p ∂μ, ∀ u : ℝ, ¬ (IsLocalMin (fun t => lrCoord 0 t p) u ∧ IsLocalMin (fun t => lrCoord 1 t p) u)

/-! ### Last and first visits of a coordinate -/

/-- **Last and first visits of a contour coordinate.** For a continuous coordinate `X` with distinct values at
distinct local minima, `σ m ℓ` is the last time before `m` and `τ m ℓ` the first time after `m` at which `X ≤ ℓ`;
for `ℓ < X m` the curve `η` identifies them, and the image `η (σ m ℓ)` varies continuously with the level. -/
structure LevelContactData (η : ℝ → ℂ) (X : ℝ → ℝ) (σ τ : ℝ → ℝ → ℝ) : Prop where
  continuous : Continuous X
  locMin_ne : ∀ a b, a ≠ b → IsLocalMin X a → IsLocalMin X b → X a ≠ X b
  σ_le : ∀ m ℓ, σ m ℓ ≤ m
  σ_level : ∀ m ℓ, ℓ < X m → X (σ m ℓ) = ℓ
  le_σ : ∀ m ℓ r, r ≤ m → X r ≤ ℓ → r ≤ σ m ℓ
  le_τ : ∀ m ℓ, m ≤ τ m ℓ
  τ_level : ∀ m ℓ, X (τ m ℓ) ≤ ℓ
  τ_le : ∀ m ℓ r, m ≤ r → X r ≤ ℓ → τ m ℓ ≤ r
  continuousOn : ∀ m, ContinuousOn (fun ℓ => η (σ m ℓ)) (Iio (X m))
  eta_eq : ∀ m ℓ, ℓ < X m → η (σ m ℓ) = η (τ m ℓ)

/-- The last and first visits of the left contour function of a Peanosphere. -/
theorem levelContactData_lCoord {ω : Path2} {η : ℝ → ℂ} (P : Peanosphere ω η) :
    LevelContactData η (lCoord ω) (ellMinus ω) (ellPlus ω) where
  continuous := ω.continuous.fst
  locMin_ne a b hab ha hb := P.locMinDistinct 0 a b hab ha hb
  σ_le m ℓ := (MatedCRTHarmonic.RouteM.ellMinus_mem P m ℓ).1
  σ_level _ _ h := MatedCRTHarmonic.RouteM.ellMinus_level P h
  le_σ m ℓ r hr hX := by
    show r ≤ sSup {s | s ≤ m ∧ lCoord ω s ≤ ℓ}
    exact le_csSup ⟨m, fun _ hx => hx.1⟩ ⟨hr, hX⟩
  le_τ m ℓ := (MatedCRTHarmonic.RouteM.ellPlus_mem P m ℓ).1
  τ_level m ℓ := (MatedCRTHarmonic.RouteM.ellPlus_mem P m ℓ).2
  τ_le m ℓ r hr hX := by
    show sInf {s | m ≤ s ∧ lCoord ω s ≤ ℓ} ≤ r
    exact csInf_le ⟨m, fun _ hx => hx.1⟩ ⟨hr, hX⟩
  continuousOn m := P.continuousOn_eta_ellMinus m
  eta_eq _ _ h := MatedCRTHarmonic.RouteM.eta_eq_of_L_last_first P h

/-- The last and first visits of the right contour function of a Peanosphere. -/
theorem levelContactData_rCoord {ω : Path2} {η : ℝ → ℂ} (P : Peanosphere ω η) :
    LevelContactData η (rCoord ω) (rhoMinus ω) (rhoPlus ω) where
  continuous := ω.continuous.snd
  locMin_ne a b hab ha hb := P.locMinDistinct 1 a b hab ha hb
  σ_le m ℓ := (MatedCRTHarmonic.RouteM.rhoMinus_mem P m ℓ).1
  σ_level _ _ h := MatedCRTHarmonic.RouteM.rhoMinus_level P h
  le_σ m ℓ r hr hX := by
    show r ≤ sSup {s | s ≤ m ∧ rCoord ω s ≤ ℓ}
    exact le_csSup ⟨m, fun _ hx => hx.1⟩ ⟨hr, hX⟩
  le_τ m ℓ := (MatedCRTHarmonic.RouteM.rhoPlus_mem P m ℓ).1
  τ_level m ℓ := (MatedCRTHarmonic.RouteM.rhoPlus_mem P m ℓ).2
  τ_le m ℓ r hr hX := by
    show sInf {s | m ≤ s ∧ rCoord ω s ≤ ℓ} ≤ r
    exact csInf_le ⟨m, fun _ hx => hx.1⟩ ⟨hr, hX⟩
  continuousOn m := P.continuousOn_eta_rhoMinus m
  eta_eq _ _ h := MatedCRTHarmonic.RouteM.eta_eq_of_R_last_first P h

/-! ### Contacts from levels -/

/-- **The images of the visits to an interval of levels form a continuum of positive diameter.** Let
`r₁ ≤ m₁ ≤ m₂ ≤ r₂` and `ℓ₁ < ℓ₂` with `X r₁, X r₂ ≤ ℓ₁` and `X > ℓ₂` on `[m₁, m₂]`. For each level
`ℓ ∈ [ℓ₁, ℓ₂]` the last visit `σ m₁ ℓ ∈ [r₁, m₁]` and the first visit `τ m₁ ℓ ∈ [m₂, r₂]` have the same image, which
varies continuously with `ℓ`; since the fibres of `η` are finite it is not constant. -/
theorem LevelContactData.containsNondegenerateContinuum {η : ℝ → ℂ} {X : ℝ → ℝ} {σ τ : ℝ → ℝ → ℝ}
    (C : LevelContactData η X σ τ) (hfin : ∀ z, (η ⁻¹' {z}).Finite) {r₁ m₁ m₂ r₂ ℓ₁ ℓ₂ : ℝ}
    {A B : Set ℝ} (hr₁ : r₁ ≤ m₁) (hm : m₁ ≤ m₂) (hr₂ : m₂ ≤ r₂) (hℓ : ℓ₁ < ℓ₂) (hX₁ : X r₁ ≤ ℓ₁)
    (hX₂ : X r₂ ≤ ℓ₁) (habove : ∀ r ∈ Icc m₁ m₂, ℓ₂ < X r) (hA : Icc r₁ m₁ ⊆ A) (hB : Icc m₂ r₂ ⊆ B) :
    ContainsNondegenerateContinuum (η '' A ∩ η '' B) := by
  have hsub : Icc ℓ₁ ℓ₂ ⊆ Iio (X m₁) := fun ℓ hℓ' => hℓ'.2.trans_lt (habove m₁ ⟨le_rfl, hm⟩)
  have hcont : ContinuousOn (fun ℓ => η (σ m₁ ℓ)) (Icc ℓ₁ ℓ₂) := (C.continuousOn m₁).mono hsub
  have hKc : IsCompact ((fun ℓ => η (σ m₁ ℓ)) '' Icc ℓ₁ ℓ₂) := isCompact_Icc.image_of_continuousOn hcont
  refine ⟨_, ?_, hKc, (isConnected_Icc hℓ.le).image _ hcont, ?_⟩
  · rintro _ ⟨ℓ, hℓ', rfl⟩
    refine ⟨⟨σ m₁ ℓ, hA ⟨C.le_σ m₁ ℓ r₁ hr₁ (hX₁.trans hℓ'.1), C.σ_le m₁ ℓ⟩, rfl⟩,
      ⟨τ m₁ ℓ, hB ⟨?_, C.τ_le m₁ ℓ r₂ (hm.trans hr₂) (hX₂.trans hℓ'.1)⟩, (C.eta_eq m₁ ℓ (hsub hℓ')).symm⟩⟩
    refine not_lt.1 fun hlt => ?_
    have hτ : ℓ₂ < X (τ m₁ ℓ) := habove _ ⟨C.le_τ m₁ ℓ, hlt.le⟩
    exact absurd ((C.τ_level m₁ ℓ).trans hℓ'.2) (not_le.2 hτ)
  · have hinj : InjOn (σ m₁) (Icc ℓ₁ ℓ₂) := fun x hx y hy hxy =>
      calc x = X (σ m₁ x) := (C.σ_level m₁ x (hsub hx)).symm
        _ = X (σ m₁ y) := by rw [hxy]
        _ = y := C.σ_level m₁ y (hsub hy)
    have hnt : ((fun ℓ => η (σ m₁ ℓ)) '' Icc ℓ₁ ℓ₂).Nontrivial := by
      by_contra hnt
      rw [Set.not_nontrivial_iff] at hnt
      have hsubset : σ m₁ '' Icc ℓ₁ ℓ₂ ⊆ η ⁻¹' {η (σ m₁ ℓ₁)} := by
        rintro _ ⟨ℓ, hℓ', rfl⟩
        exact hnt ⟨ℓ, hℓ', rfl⟩ ⟨ℓ₁, left_mem_Icc.2 hℓ.le, rfl⟩
      exact (Set.infinite_image_iff hinj).2 (Set.Icc_infinite hℓ) ((hfin _).subset hsubset)
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    exact (dist_pos.2 hxy).trans_le (dist_le_diam_of_mem hKc.isBounded hx hy)

/-- **Contact across an excursion above a level** (written answer MQ-sbl-31, lines 36-37): if `X v = X w = g` and
`X > g` on `(v, w)`, then `D_η(v, w)`. The levels just above `g` are visited last near `v` and first near `w`. -/
theorem LevelContactData.cellSideContact_of_excursion {η : ℝ → ℂ} {X : ℝ → ℝ} {σ τ : ℝ → ℝ → ℝ}
    (C : LevelContactData η X σ τ) (hfin : ∀ z, (η ⁻¹' {z}).Finite) {a d v w g : ℝ} (hvw : v < w)
    (hv : X v = g) (hw : X w = g) (habove : ∀ r ∈ Ioo v w, g < X r) : cellSideContact a d η v w := by
  intro p₁ p₂ q₁ q₂ hvp hwq _ _ _
  obtain ⟨m₁, hm₁v, hm₁'⟩ := exists_between (lt_min hvp.2 hvw)
  have hm₁p : m₁ < p₂ := hm₁'.trans_le (min_le_left _ _)
  have hm₁w : m₁ < w := hm₁'.trans_le (min_le_right _ _)
  obtain ⟨m₂, hm₂a, hm₂w⟩ := exists_between (max_lt hwq.1 hm₁w)
  have hm₂q : (q₁ : ℝ) < m₂ := (le_max_left _ _).trans_lt hm₂a
  have hm₁₂ : m₁ < m₂ := (le_max_right _ _).trans_lt hm₂a
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hm₁₂.le) C.continuous.continuousOn
  have hgr : g < X r := habove r ⟨hm₁v.trans_le hr.1, hr.2.trans_lt hm₂w⟩
  exact C.containsNondegenerateContinuum hfin (r₁ := v) (m₁ := m₁) (m₂ := m₂) (r₂ := w)
    (ℓ₁ := (3 * g + X r) / 4) (ℓ₂ := (g + X r) / 2) (A := Icc (p₁ : ℝ) p₂) (B := Icc (q₁ : ℝ) q₂)
    hm₁v.le hm₁₂.le hm₂w.le (by linarith) (by linarith) (by linarith)
    (fun r' hr' => by
      have h' : X r ≤ X r' := hmin hr'
      linarith)
    (fun x hx => ⟨by linarith [hvp.1, hx.1], by linarith [hx.2]⟩)
    (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, hwq.2]⟩)

/-- **Contact across a level from below** (written answer MQ-sbl-31, line 37): if `X ≥ g` on `[v, w]` and `X` dips
below `g` immediately before `v` and immediately after `w`, then `D_η(v, w)`. The levels just below `g` are visited
last before `v` and first after `w`. -/
theorem LevelContactData.cellSideContact_of_dips {η : ℝ → ℂ} {X : ℝ → ℝ} {σ τ : ℝ → ℝ → ℝ}
    (C : LevelContactData η X σ τ) (hfin : ∀ z, (η ⁻¹' {z}).Finite) {a d v w g : ℝ} (hvw : v ≤ w)
    (hge : ∀ r ∈ Icc v w, g ≤ X r) (hdv : ∀ δ > 0, ∃ r, v - δ < r ∧ r < v ∧ X r < g)
    (hdw : ∀ δ > 0, ∃ r, w < r ∧ r < w + δ ∧ X r < g) : cellSideContact a d η v w := by
  intro p₁ p₂ q₁ q₂ hvp hwq _ _ _
  obtain ⟨r₁, hr₁a, hr₁b, hr₁g⟩ := hdv (v - p₁) (by linarith [hvp.1])
  obtain ⟨r₂, hr₂a, hr₂b, hr₂g⟩ := hdw (q₂ - w) (by linarith [hwq.2])
  have hμ : max (X r₁) (X r₂) < g := max_lt hr₁g hr₂g
  have h₁ := le_max_left (X r₁) (X r₂)
  have h₂ := le_max_right (X r₁) (X r₂)
  exact C.containsNondegenerateContinuum hfin (r₁ := r₁) (m₁ := v) (m₂ := w) (r₂ := r₂)
    (ℓ₁ := (2 * max (X r₁) (X r₂) + g) / 3) (ℓ₂ := (max (X r₁) (X r₂) + 2 * g) / 3)
    (A := Icc (p₁ : ℝ) p₂) (B := Icc (q₁ : ℝ) q₂) hr₁b.le hvw hr₂a.le (by linarith) (by linarith)
    (by linarith)
    (fun r hr => by
      have := hge r hr
      linarith)
    (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, hvp.2]⟩)
    (fun x hx => ⟨by linarith [hx.1, hwq.1], by linarith [hx.2]⟩)

/-! ### Contacts are weak level pairs -/

/-- `v, w` is a **weak level pair** of `X`: `X v = X w` is the minimum of `X` over `[v, w]`. -/
def IsWeakLevelPair (X : ℝ → ℝ) (v w : ℝ) : Prop :=
  X v = X w ∧ ∀ r ∈ Icc v w, X v ≤ X r

/-- The weak level pairs `(v, w)`, `v ≤ w`, of `X`, with the times of `[v, w]` written as convex combinations. -/
def weakLevelPairSet (X : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ≤ q.2} ∩ {q | X q.1 = X q.2} ∩ ⋂ l ∈ Icc (0 : ℝ) 1, {q | X q.1 ≤ X (q.1 + l * (q.2 - q.1))}

/-- The weak level pairs of a continuous function form a closed set. -/
theorem isClosed_weakLevelPairSet {X : ℝ → ℝ} (hX : Continuous X) : IsClosed (weakLevelPairSet X) :=
  ((isClosed_le continuous_fst continuous_snd).inter
    (isClosed_eq (hX.comp continuous_fst) (hX.comp continuous_snd))).inter
    (isClosed_biInter fun _ _ => isClosed_le (hX.comp continuous_fst)
      (hX.comp (continuous_fst.add (continuous_const.mul (continuous_snd.sub continuous_fst)))))

/-- A direct identification is a weak level pair. -/
theorem mem_weakLevelPairSet_of_directRel {X : ℝ → ℝ} {s t : ℝ} (h : directRel X s t) :
    (s, t) ∈ weakLevelPairSet X := by
  obtain ⟨hst, heq, habove⟩ := h
  refine ⟨⟨hst.le, heq⟩, mem_iInter₂.2 fun l hl => ?_⟩
  show X s ≤ X (s + l * (t - s))
  rcases eq_or_lt_of_le hl.1 with h0 | h0
  · have e : s + l * (t - s) = s := by rw [← h0]; ring
    exact le_of_eq (by rw [e])
  rcases eq_or_lt_of_le hl.2 with h1 | h1
  · have e : s + l * (t - s) = t := by rw [h1]; ring
    rw [e]
    exact heq.le
  exact (habove _ ⟨by nlinarith [mul_pos h0 (sub_pos.2 hst)],
    by nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 hst)]⟩).le

/-- A member of `weakLevelPairSet X` is a weak level pair. -/
theorem isWeakLevelPair_of_mem_weakLevelPairSet {X : ℝ → ℝ} {v w : ℝ} (h : (v, w) ∈ weakLevelPairSet X) :
    IsWeakLevelPair X v w := by
  have hvw : v ≤ w := h.1.1
  have heq : X v = X w := h.1.2
  have hall : ∀ l ∈ Icc (0 : ℝ) 1, X v ≤ X (v + l * (w - v)) := fun l hl => mem_iInter₂.1 h.2 l hl
  refine ⟨heq, fun r hr => ?_⟩
  rcases eq_or_lt_of_le hvw with h' | h'
  · have hrv : r = v := by linarith [hr.1, hr.2]
    exact le_of_eq (by rw [hrv])
  · have hl : (r - v) / (w - v) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.2 hr.1) (sub_pos.2 h').le, (div_le_one (sub_pos.2 h')).2 (by linarith [hr.2])⟩
    have h1 := hall _ hl
    have e : v + (r - v) / (w - v) * (w - v) = r := by
      rw [div_mul_cancel₀ _ (sub_pos.2 h').ne']
      ring
    rwa [e] at h1

/-- **An equivalence class with two elements is joined directly.** If `R` relates only points with the same image
under `f`, and the fibre of `f` over `z` is contained in `{s, t}`, then two points of that fibre related by the
equivalence relation generated by `R` are equal or related by `R` in some order. -/
theorem eq_or_rel_of_eqvGen_of_fiber {α β : Type*} {R : α → α → Prop} {f : α → β} {s t : α} {z : β}
    (hR : ∀ a b, R a b → f a = f b) (hfib : ∀ x, f x = z → x = s ∨ x = t) {x y : α}
    (h : Relation.EqvGen R x y) (hx : f x = z) : x = y ∨ R x y ∨ R y x := by
  have heq : ∀ a b, Relation.EqvGen R a b → f a = f b := by
    intro a b hab
    induction hab with
    | rel a b h => exact hR a b h
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  revert hx
  induction h with
  | rel a b hab => exact fun _ => Or.inr (Or.inl hab)
  | refl a => exact fun _ => Or.inl rfl
  | symm a b hab ih =>
    intro hb
    rcases ih ((heq a b hab).trans hb) with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  | trans a b c hab hbc ih₁ ih₂ =>
    intro ha
    have hb : f b = z := (heq a b hab).symm.trans ha
    have hc : f c = z := (heq b c hbc).symm.trans hb
    by_cases hac : a = c
    · exact Or.inl hac
    · have hbac : b = a ∨ b = c := by
        rcases hfib a ha with h1 | h1 <;> rcases hfib c hc with h2 | h2 <;>
          rcases hfib b hb with h3 | h3 <;>
          first
            | exact Or.inl (h3.trans h1.symm)
            | exact Or.inr (h3.trans h2.symm)
            | exact absurd (h1.trans h2.symm) hac
      rcases hbac with h | h
      · rw [h] at ih₂
        rcases ih₂ ha with h' | h' | h'
        · exact absurd h' hac
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      · rw [h] at ih₁
        exact ih₁ ha

/-- **Contacts are weak level pairs** (written answer MQ-sbl-31, lines 28-32). For a Peanosphere whose points
visited at least three times contain no continuum of positive diameter, if `D_η(v, w)` for times `v < w` of `(a, d)`
then `v, w` is a weak level pair of `L` or of `R`: otherwise a neighbourhood of `(v, w)` contains no weak level pair,
a common continuum of the images of two small time intervals about `v` and `w` contains a point visited exactly
twice, and its two visits are directly identified by `L` or `R` (DMS Lemmas 8.8 and 8.14). -/
theorem isWeakLevelPair_of_cellSideContact {ω : Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    (htriple : ¬ ContainsNondegenerateContinuum (curveTriplePoints η)) {a d v w : ℝ} (hvw : v < w)
    (hv : v ∈ Ioo a d) (hw : w ∈ Ioo a d) (hD : cellSideContact a d η v w) :
    IsWeakLevelPair (lCoord ω) v w ∨ IsWeakLevelPair (rCoord ω) v w := by
  by_contra hno
  rw [not_or] at hno
  have hL : (v, w) ∉ weakLevelPairSet (lCoord ω) := fun h =>
    hno.1 (isWeakLevelPair_of_mem_weakLevelPairSet h)
  have hR : (v, w) ∉ weakLevelPairSet (rCoord ω) := fun h =>
    hno.2 (isWeakLevelPair_of_mem_weakLevelPairSet h)
  have hopen : IsOpen (weakLevelPairSet (lCoord ω) ∪ weakLevelPairSet (rCoord ω))ᶜ :=
    ((isClosed_weakLevelPairSet (levelContactData_lCoord P).continuous).union
      (isClosed_weakLevelPairSet (levelContactData_rCoord P).continuous)).isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen (v, w) fun h => h.elim hL hR
  have hδ' : 0 < min δ ((w - v) / 2) := lt_min hδ (by linarith)
  have hδ1 := min_le_left δ ((w - v) / 2)
  have hδ2 := min_le_right δ ((w - v) / 2)
  obtain ⟨p₁, p₂, hvp, hP, hPδ⟩ := exists_rat_Ioo_subset hv hδ'
  obtain ⟨q₁, q₂, hwq, hQ, hQδ⟩ := exists_rat_Ioo_subset hw hδ'
  have hp₂ := hPδ (right_mem_Icc.2 (hvp.1.trans hvp.2).le)
  have hq₁ := hQδ (left_mem_Icc.2 (hwq.1.trans hwq.2).le)
  have hpq : (p₂ : ℝ) < q₁ := by linarith [hp₂.2, hq₁.1]
  have hdisj : Disjoint (Ioo (p₁ : ℝ) p₂) (Ioo (q₁ : ℝ) q₂) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    linarith [hx.2, hx'.1]
  obtain ⟨K, hK, hKc, hKconn, hKd⟩ := hD p₁ p₂ q₁ q₂ hvp hwq hdisj hP hQ
  obtain ⟨z, hzK, hz⟩ : ∃ z ∈ K, z ∉ curveTriplePoints η := by
    by_contra hall
    exact htriple ⟨K, fun z hz => Classical.byContradiction fun hz' => hall ⟨z, hz, hz'⟩, hKc, hKconn, hKd⟩
  obtain ⟨⟨s', hs', hs'z⟩, ⟨t', ht', ht'z⟩⟩ := hK hzK
  have hst' : s' < t' := hs'.2.trans_lt (hpq.trans_le ht'.1)
  have hfib : ∀ x, η x = z → x = s' ∨ x = t' := by
    intro x hx
    by_contra hne
    rw [not_or] at hne
    apply hz
    rcases lt_trichotomy x s' with h | h | h
    · exact ⟨x, s', t', h, hst', hx, hs'z, ht'z⟩
    · exact absurd h hne.1
    · rcases lt_trichotomy x t' with h' | h' | h'
      · exact ⟨s', x, t', h, h', hs'z, hx, ht'z⟩
      · exact absurd h' hne.2
      · exact ⟨s', t', x, hst', h', hs'z, ht'z, hx⟩
  have hdir : directRel (lCoord ω) s' t' ∨ directRel (rCoord ω) s' t' := by
    rcases eq_or_rel_of_eqvGen_of_fiber (fun a b h => P.merge a b h) hfib
        (P.onlyMerge s' t' (hs'z.trans ht'z.symm)) hs'z with h | h | h
    · exact absurd h hst'.ne
    · exact h
    · rcases h with h | h <;> exact absurd h.1 (not_lt.2 hst'.le)
  have hmem : (s', t') ∈ weakLevelPairSet (lCoord ω) ∪ weakLevelPairSet (rCoord ω) :=
    hdir.elim (fun h => Or.inl (mem_weakLevelPairSet_of_directRel h))
      fun h => Or.inr (mem_weakLevelPairSet_of_directRel h)
  have h1 := hPδ hs'
  have h2 := hQδ ht'
  have hb : (s', t') ∈ ball (v, w) δ := by
    rw [mem_ball]
    simp only [Prod.dist_eq, Real.dist_eq]
    exact max_lt (abs_sub_lt_iff.2 ⟨by linarith [h1.2], by linarith [h1.1]⟩)
      (abs_sub_lt_iff.2 ⟨by linarith [h2.2], by linarith [h2.1]⟩)
  exact hball hb hmem

/-! ### Branch times are centred minima -/

/-- `X s = X u = X t` is the minimum of `X` over `[s, t]`. -/
def IsCenteredMin (X : ℝ → ℝ) (s u t : ℝ) : Prop :=
  X s = X u ∧ X t = X u ∧ ∀ r ∈ Icc s t, X u ≤ X r

/-- **Two weak level pairs of the same coordinate among `s, u, t` make `u` a centred minimum** (written answer
MQ-sbl-31, line 34: transitivity puts all three times in the same tree). -/
theorem isCenteredMin_of_two {X : ℝ → ℝ} {s u t : ℝ}
    (h : (IsWeakLevelPair X s u ∧ IsWeakLevelPair X u t) ∨ (IsWeakLevelPair X s u ∧ IsWeakLevelPair X s t) ∨
      (IsWeakLevelPair X u t ∧ IsWeakLevelPair X s t)) : IsCenteredMin X s u t := by
  rcases h with ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ | ⟨⟨h1, _⟩, ⟨h2, h2'⟩⟩ | ⟨⟨h1, _⟩, ⟨h2, h2'⟩⟩
  · refine ⟨h1, h2.symm, fun r hr => ?_⟩
    rcases le_total r u with hru | hru
    · have := h1' r ⟨hr.1, hru⟩
      linarith
    · exact h2' r ⟨hru, hr.2⟩
  · refine ⟨h1, by linarith, fun r hr => ?_⟩
    have := h2' r hr
    linarith
  · refine ⟨by linarith, h1.symm, fun r hr => ?_⟩
    have := h2' r hr
    linarith

/-- **A branch time is a centred minimum of `L` or of `R`** (written answer MQ-sbl-31, lines 28-34). -/
theorem isCenteredMin_of_mem_cellSideBranchTimes {ω : Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    (htriple : ¬ ContainsNondegenerateContinuum (curveTriplePoints η)) {a b c d u : ℝ}
    (hu : u ∈ cellSideBranchTimes a b c d η) :
    ∃ s ∈ Ioo a b, ∃ t ∈ Ioo c d, IsCenteredMin (lCoord ω) s u t ∨ IsCenteredMin (rCoord ω) s u t := by
  obtain ⟨⟨hub, huc⟩, s, hs, t, ht, hsu, hut, hst⟩ := hu
  have hsu' : s < u := hs.2.trans hub
  have hut' : u < t := huc.trans ht.1
  have hsd : s ∈ Ioo a d := ⟨hs.1, hsu'.trans (hut'.trans ht.2)⟩
  have hud : u ∈ Ioo a d := ⟨hs.1.trans hsu', hut'.trans ht.2⟩
  have htd : t ∈ Ioo a d := ⟨hs.1.trans (hsu'.trans hut'), ht.2⟩
  have w1 := isWeakLevelPair_of_cellSideContact P htriple hsu' hsd hud hsu
  have w2 := isWeakLevelPair_of_cellSideContact P htriple hut' hud htd hut
  have w3 := isWeakLevelPair_of_cellSideContact P htriple (hsu'.trans hut') hsd htd hst
  refine ⟨s, hs, t, ht, ?_⟩
  rcases w1 with h1 | h1 <;> rcases w2 with h2 | h2 <;> rcases w3 with h3 | h3 <;>
    first
      | exact Or.inl (isCenteredMin_of_two (Or.inl ⟨h1, h2⟩))
      | exact Or.inl (isCenteredMin_of_two (Or.inr (Or.inl ⟨h1, h3⟩)))
      | exact Or.inl (isCenteredMin_of_two (Or.inr (Or.inr ⟨h2, h3⟩)))
      | exact Or.inr (isCenteredMin_of_two (Or.inl ⟨h1, h2⟩))
      | exact Or.inr (isCenteredMin_of_two (Or.inr (Or.inl ⟨h1, h3⟩)))
      | exact Or.inr (isCenteredMin_of_two (Or.inr (Or.inr ⟨h2, h3⟩)))

/-- The adjacency condition (eq:edge-map, line 175) for the cell intervals `[a, b]`, `[c, d]` and the intervening
interval `[b, c]`: `(inf_{[a, b]} X) ∨ (inf_{[c, d]} X) ≤ inf_{[b, c]} X`. -/
def IntervalAdjacent (X : ℝ → ℝ) (a b c d : ℝ) : Prop :=
  max (sInf (X '' Icc a b)) (sInf (X '' Icc c d)) ≤ sInf (X '' Icc b c)

/-- **A centred minimum straddling the intervening interval gives the adjacency condition.** -/
theorem IsCenteredMin.intervalAdjacent {X : ℝ → ℝ} (hX : Continuous X) {a b c d s u t : ℝ}
    (h : IsCenteredMin X s u t) (hs : s ∈ Icc a b) (hu : u ∈ Icc b c) (ht : t ∈ Icc c d) :
    IntervalAdjacent X a b c d := by
  have hbc : b ≤ c := hu.1.trans hu.2
  have hmid : X u ≤ sInf (X '' Icc b c) :=
    le_csInf ((nonempty_Icc.2 hbc).image X) (by
      rintro _ ⟨r, hr, rfl⟩
      exact h.2.2 r ⟨hs.2.trans hr.1, hr.2.trans ht.1⟩)
  unfold IntervalAdjacent
  refine max_le ?_ ?_
  · calc sInf (X '' Icc a b) ≤ X s := csInf_le (isCompact_Icc.image hX).bddBelow (mem_image_of_mem X hs)
      _ = X u := h.1
      _ ≤ _ := hmid
  · calc sInf (X '' Icc c d) ≤ X t := csInf_le (isCompact_Icc.image hX).bddBelow (mem_image_of_mem X ht)
      _ = X u := h.2.1
      _ ≤ _ := hmid

/-! ### Strict windows give branch times -/

/-- The coordinate takes smaller values immediately to the right and immediately to the left of `x`. -/
def IsTwoSidedDescent (X : ℝ → ℝ) (x : ℝ) : Prop :=
  (∀ δ > 0, ∃ t, x < t ∧ t < x + δ ∧ X t < X x) ∧ (∀ δ > 0, ∃ t, x - δ < t ∧ t < x ∧ X t < X x)

/-- A minimum over `[b, c]` attained in `(b, c)` is a local minimum. -/
theorem isLocalMin_of_mem_Ioo {X : ℝ → ℝ} {b c u : ℝ} (hu : u ∈ Ioo b c) (hmin : ∀ r ∈ Icc b c, X u ≤ X r) :
    IsLocalMin X u :=
  (isMinOn_iff.2 hmin).isLocalMin (Icc_mem_nhds hu.1 hu.2)

/-- With distinct values at distinct local minima, the minimum over `[b, c]` is attained at most once in `(b, c)`. -/
theorem eq_of_forall_le_of_mem_Ioo {X : ℝ → ℝ}
    (hlm : ∀ x y, x ≠ y → IsLocalMin X x → IsLocalMin X y → X x ≠ X y) {b c u v : ℝ} (hu : u ∈ Ioo b c)
    (hv : v ∈ Ioo b c) (hum : ∀ r ∈ Icc b c, X u ≤ X r) (hvm : ∀ r ∈ Icc b c, X v ≤ X r) : u = v := by
  by_contra hne
  exact hlm u v hne (isLocalMin_of_mem_Ioo hu hum) (isLocalMin_of_mem_Ioo hv hvm)
    (le_antisymm (hum v (Ioo_subset_Icc_self hv)) (hvm u (Ioo_subset_Icc_self hu)))

/-- **The adjacency condition is strict** (written answer MQ-sbl-31, line 34): if `X` descends on both sides of
`a, b, c, d` and takes distinct values at distinct local minima, the three minima over `[a, b]`, `[b, c]`, `[c, d]`
are attained at interior local minima, hence have distinct values. -/
theorem IntervalAdjacent.strict {X : ℝ → ℝ} {a b c d : ℝ} (h : IntervalAdjacent X a b c d) (hX : Continuous X)
    (hlm : ∀ x y, x ≠ y → IsLocalMin X x → IsLocalMin X y → X x ≠ X y) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (ha : IsTwoSidedDescent X a) (hb : IsTwoSidedDescent X b) (hc : IsTwoSidedDescent X c)
    (hd : IsTwoSidedDescent X d) : max (sInf (X '' Icc a b)) (sInf (X '' Icc c d)) < sInf (X '' Icc b c) := by
  obtain ⟨c₁, -, hc₁b, hc₁m, hc₁⟩ := exists_interior_localMin hX hab ha.1 hb.2
  obtain ⟨c₂, hc₂a, hc₂b, hc₂m, hc₂⟩ := exists_interior_localMin hX hbc hb.1 hc.2
  obtain ⟨c₃, hc₃a, -, hc₃m, hc₃⟩ := exists_interior_localMin hX hcd hc.1 hd.2
  have h12 : X c₁ ≠ X c₂ := hlm c₁ c₂ (hc₁b.trans hc₂a).ne hc₁m hc₂m
  have h32 : X c₃ ≠ X c₂ := hlm c₃ c₂ (hc₂b.trans hc₃a).ne' hc₃m hc₂m
  unfold IntervalAdjacent at h
  rw [hc₁, hc₂, hc₃] at h ⊢
  exact max_lt (lt_of_le_of_ne ((le_max_left _ _).trans h) h12)
    (lt_of_le_of_ne ((le_max_right _ _).trans h) h32)

/-- **The left witness of a strict window** (written answer MQ-sbl-31, line 36). Let `u ∈ (b, c)` be a local minimum
of `X` attaining its minimum `g` over `[b, c]`, let `X` descend immediately after `b`, and let the minimum of `X`
over `[a, b]` be below `g`. The last time `s` of `[a, b]` at which `X < g` is approached satisfies `s ∈ (a, b)`,
`X s = g`, `X > g` on `(s, u)`, and `X` dips below `g` immediately before `s`. -/
theorem exists_left_level_witness {X : ℝ → ℝ} (hX : Continuous X)
    (hlm : ∀ x y, x ≠ y → IsLocalMin X x → IsLocalMin X y → X x ≠ X y) {a b c u : ℝ} (hab : a < b)
    (hbc : b < c) (huc : u < c) (hulm : IsLocalMin X u) (hmin : ∀ r ∈ Icc b c, X u ≤ X r)
    (hob : ∀ δ > 0, ∃ t, b < t ∧ t < b + δ ∧ X t < X b) (hlt : sInf (X '' Icc a b) < X u) :
    ∃ s ∈ Ioo a b, X s = X u ∧ (∀ r ∈ Ioo s u, X u < X r) ∧
      ∀ δ > 0, ∃ r, s - δ < r ∧ r < s ∧ X r < X u := by
  have hIne : (Icc a b).Nonempty := nonempty_Icc.2 hab.le
  obtain ⟨_, ⟨r₀, hr₀, rfl⟩, hr₀lt⟩ := exists_lt_of_csInf_lt (hIne.image X) hlt
  obtain ⟨SL, hSL⟩ : ∃ SL : Set ℝ, ∀ r, r ∈ SL ↔ r ∈ Icc a b ∧ X r < X u :=
    ⟨{r | r ∈ Icc a b ∧ X r < X u}, fun _ => Iff.rfl⟩
  have hr₀SL : r₀ ∈ SL := (hSL r₀).2 ⟨hr₀, hr₀lt⟩
  have hSLne : SL.Nonempty := ⟨r₀, hr₀SL⟩
  have hSLbdd : BddAbove SL := ⟨b, fun r hr => ((hSL r).1 hr).1.2⟩
  obtain ⟨s, hs⟩ : ∃ s, sSup SL = s := ⟨_, rfl⟩
  have hs_ub : ∀ r ∈ SL, r ≤ s := fun r hr => hs ▸ le_csSup hSLbdd hr
  have hsb : s ≤ b := hs ▸ csSup_le hSLne fun r hr => ((hSL r).1 hr).1.2
  have has : a ≤ s := hr₀.1.trans (hs_ub r₀ hr₀SL)
  have habove : ∀ r, s < r → r ≤ b → X u ≤ X r := fun r hsr hrb =>
    not_lt.1 fun hlt' => absurd (hs_ub r ((hSL r).2 ⟨⟨has.trans hsr.le, hrb⟩, hlt'⟩)) (not_le.2 hsr)
  have hXs_le : X s ≤ X u := by
    have hcl : closure SL ⊆ {r | X r ≤ X u} :=
      closure_minimal (fun r hr => ((hSL r).1 hr).2.le) (isClosed_le hX continuous_const)
    have hmem : s ∈ closure SL := hs ▸ csSup_mem_closure hSLne hSLbdd
    exact hcl hmem
  have hXs : X s = X u := by
    refine le_antisymm hXs_le (not_lt.1 fun hlt' => ?_)
    rcases eq_or_lt_of_le hsb with heq | hsb'
    · exact absurd (hmin s ⟨heq.ge, heq.le.trans hbc.le⟩) (not_le.2 hlt')
    · obtain ⟨δ, hδ, hδX⟩ := Metric.continuous_iff.1 hX s (X u - X s) (by linarith)
      have hm : 0 < min δ (b - s) := lt_min hδ (sub_pos.2 hsb')
      have hm1 := min_le_left δ (b - s)
      have hm2 := min_le_right δ (b - s)
      have h1 := hδX (s + min δ (b - s) / 2) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rw [Real.dist_eq, abs_lt] at h1
      have h2 := habove (s + min δ (b - s) / 2) (by linarith) (by linarith)
      linarith [h1.2]
  have hsb' : s < b := by
    refine lt_of_le_of_ne hsb fun heq => ?_
    obtain ⟨r, hr1, hr2, hr3⟩ := hob (c - b) (by linarith)
    have h1 := hmin r ⟨hr1.le, by linarith⟩
    rw [← heq, hXs] at hr3
    linarith
  have has' : a < s := by
    refine lt_of_le_of_ne has fun heq => ?_
    have hall : ∀ r ∈ Icc a b, X u ≤ X r := by
      intro r hr
      rcases eq_or_lt_of_le hr.1 with h | h
      · exact le_of_eq (by rw [← h, heq, hXs])
      · exact habove r (by rw [← heq]; exact h) hr.2
    have h1 : X u ≤ sInf (X '' Icc a b) :=
      le_csInf (hIne.image X) (by
        rintro _ ⟨r, hr, rfl⟩
        exact hall r hr)
    linarith
  have hge : ∀ r ∈ Ioo s u, X u ≤ X r := by
    intro r hr
    rcases le_total r b with hrb | hrb
    · exact habove r hr.1 hrb
    · exact hmin r ⟨hrb, hr.2.le.trans huc.le⟩
  have hgt : ∀ r ∈ Ioo s u, X u < X r := by
    intro r hr
    refine lt_of_le_of_ne (hge r hr) fun heq => ?_
    have hmin' : IsMinOn X (Ioo s u) r := isMinOn_iff.2 fun r' hr' => by
      rw [← heq]
      exact hge r' hr'
    exact hlm r u hr.2.ne (hmin'.isLocalMin (Ioo_mem_nhds hr.1 hr.2)) hulm heq.symm
  have hdip : ∀ δ > 0, ∃ r, s - δ < r ∧ r < s ∧ X r < X u := by
    intro δ hδ
    obtain ⟨r, hr, hrs⟩ := exists_lt_of_lt_csSup hSLne (show s - δ < sSup SL by rw [hs]; linarith)
    have hr' := (hSL r).1 hr
    refine ⟨r, hrs, lt_of_le_of_ne (hs_ub r hr) fun h => ?_, hr'.2⟩
    rw [h, hXs] at hr'
    exact lt_irrefl _ hr'.2
  exact ⟨s, ⟨has', hsb'⟩, hXs, hgt, hdip⟩

/-- **The right witness of a strict window** (written answer MQ-sbl-31, line 36), symmetric to
`exists_left_level_witness`: the first time `t` of `[c, d]` at which `X < g` is approached satisfies `t ∈ (c, d)`,
`X t = g`, `X > g` on `(u, t)`, and `X` dips below `g` immediately after `t`. -/
theorem exists_right_level_witness {X : ℝ → ℝ} (hX : Continuous X)
    (hlm : ∀ x y, x ≠ y → IsLocalMin X x → IsLocalMin X y → X x ≠ X y) {b c d u : ℝ} (hbc : b < c)
    (hcd : c < d) (hub : b < u) (hulm : IsLocalMin X u) (hmin : ∀ r ∈ Icc b c, X u ≤ X r)
    (hoc : ∀ δ > 0, ∃ t, c - δ < t ∧ t < c ∧ X t < X c) (hlt : sInf (X '' Icc c d) < X u) :
    ∃ t ∈ Ioo c d, X t = X u ∧ (∀ r ∈ Ioo u t, X u < X r) ∧
      ∀ δ > 0, ∃ r, t < r ∧ r < t + δ ∧ X r < X u := by
  have hIne : (Icc c d).Nonempty := nonempty_Icc.2 hcd.le
  obtain ⟨_, ⟨r₀, hr₀, rfl⟩, hr₀lt⟩ := exists_lt_of_csInf_lt (hIne.image X) hlt
  obtain ⟨SR, hSR⟩ : ∃ SR : Set ℝ, ∀ r, r ∈ SR ↔ r ∈ Icc c d ∧ X r < X u :=
    ⟨{r | r ∈ Icc c d ∧ X r < X u}, fun _ => Iff.rfl⟩
  have hr₀SR : r₀ ∈ SR := (hSR r₀).2 ⟨hr₀, hr₀lt⟩
  have hSRne : SR.Nonempty := ⟨r₀, hr₀SR⟩
  have hSRbdd : BddBelow SR := ⟨c, fun r hr => ((hSR r).1 hr).1.1⟩
  obtain ⟨t, ht⟩ : ∃ t, sInf SR = t := ⟨_, rfl⟩
  have ht_lb : ∀ r ∈ SR, t ≤ r := fun r hr => ht ▸ csInf_le hSRbdd hr
  have hct : c ≤ t := ht ▸ le_csInf hSRne fun r hr => ((hSR r).1 hr).1.1
  have htd : t ≤ d := (ht_lb r₀ hr₀SR).trans hr₀.2
  have hbelow : ∀ r, c ≤ r → r < t → X u ≤ X r := fun r hcr hrt =>
    not_lt.1 fun hlt' => absurd (ht_lb r ((hSR r).2 ⟨⟨hcr, hrt.le.trans htd⟩, hlt'⟩)) (not_le.2 hrt)
  have hXt_le : X t ≤ X u := by
    have hcl : closure SR ⊆ {r | X r ≤ X u} :=
      closure_minimal (fun r hr => ((hSR r).1 hr).2.le) (isClosed_le hX continuous_const)
    have hmem : t ∈ closure SR := ht ▸ csInf_mem_closure hSRne hSRbdd
    exact hcl hmem
  have hXt : X t = X u := by
    refine le_antisymm hXt_le (not_lt.1 fun hlt' => ?_)
    rcases eq_or_lt_of_le hct with heq | hct'
    · exact absurd (hmin t ⟨hbc.le.trans heq.le, heq.ge⟩) (not_le.2 hlt')
    · obtain ⟨δ, hδ, hδX⟩ := Metric.continuous_iff.1 hX t (X u - X t) (by linarith)
      have hm : 0 < min δ (t - c) := lt_min hδ (sub_pos.2 hct')
      have hm1 := min_le_left δ (t - c)
      have hm2 := min_le_right δ (t - c)
      have h1 := hδX (t - min δ (t - c) / 2) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rw [Real.dist_eq, abs_lt] at h1
      have h2 := hbelow (t - min δ (t - c) / 2) (by linarith) (by linarith)
      linarith [h1.2]
  have hct' : c < t := by
    refine lt_of_le_of_ne hct fun heq => ?_
    obtain ⟨r, hr1, hr2, hr3⟩ := hoc (c - b) (by linarith)
    have h1 := hmin r ⟨by linarith, hr2.le⟩
    rw [heq, hXt] at hr3
    linarith
  have htd' : t < d := by
    refine lt_of_le_of_ne htd fun heq => ?_
    have hall : ∀ r ∈ Icc c d, X u ≤ X r := by
      intro r hr
      rcases eq_or_lt_of_le hr.2 with h | h
      · exact le_of_eq (by rw [h, ← heq, hXt])
      · exact hbelow r hr.1 (by rw [heq]; exact h)
    have h1 : X u ≤ sInf (X '' Icc c d) :=
      le_csInf (hIne.image X) (by
        rintro _ ⟨r, hr, rfl⟩
        exact hall r hr)
    linarith
  have hge : ∀ r ∈ Ioo u t, X u ≤ X r := by
    intro r hr
    rcases le_total r c with hrc | hrc
    · exact hmin r ⟨hub.le.trans hr.1.le, hrc⟩
    · exact hbelow r hrc hr.2
  have hgt : ∀ r ∈ Ioo u t, X u < X r := by
    intro r hr
    refine lt_of_le_of_ne (hge r hr) fun heq => ?_
    have hmin' : IsMinOn X (Ioo u t) r := isMinOn_iff.2 fun r' hr' => by
      rw [← heq]
      exact hge r' hr'
    exact hlm r u hr.1.ne' (hmin'.isLocalMin (Ioo_mem_nhds hr.1 hr.2)) hulm heq.symm
  have hdip : ∀ δ > 0, ∃ r, t < r ∧ r < t + δ ∧ X r < X u := by
    intro δ hδ
    obtain ⟨r, hr, hrt⟩ := exists_lt_of_csInf_lt hSRne (show sInf SR < t + δ by rw [ht]; linarith)
    have hr' := (hSR r).1 hr
    refine ⟨r, lt_of_le_of_ne (ht_lb r hr) fun h => ?_, hrt, hr'.2⟩
    rw [← h, hXt] at hr'
    exact lt_irrefl _ hr'.2
  exact ⟨t, ⟨hct', htd'⟩, hXt, hgt, hdip⟩

/-- **A strict window gives a branch time** (written answer MQ-sbl-31, lines 36-38): the minimizer `u` of `X` on
`[b, c]` together with the last visit `s` to the minimum in `[a, b]` and the first visit `t` in `[c, d]` is a witness
of `B_η`: `D_η(s, u)` and `D_η(u, t)` come from the levels just above the minimum, `D_η(s, t)` from the levels just
below it. -/
theorem LevelContactData.exists_mem_cellSideBranchTimes {η : ℝ → ℂ} {X : ℝ → ℝ} {σ τ : ℝ → ℝ → ℝ}
    (C : LevelContactData η X σ τ) (hfin : ∀ z, (η ⁻¹' {z}).Finite) {a b c d : ℝ} (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hob : IsTwoSidedDescent X b) (hoc : IsTwoSidedDescent X c)
    (hstrict : max (sInf (X '' Icc a b)) (sInf (X '' Icc c d)) < sInf (X '' Icc b c)) :
    ∃ u ∈ cellSideBranchTimes a b c d η, ∀ r ∈ Icc b c, X u ≤ X r := by
  have hX := C.continuous
  obtain ⟨u, hub, huc, hulm, hug⟩ := exists_interior_localMin hX hbc hob.1 hoc.2
  have hbdd : BddBelow (X '' Icc b c) := (isCompact_Icc.image hX).bddBelow
  have hmin : ∀ r ∈ Icc b c, X u ≤ X r := fun r hr => by
    rw [← hug]
    exact csInf_le hbdd (mem_image_of_mem X hr)
  rw [hug] at hstrict
  obtain ⟨s, hs, hXs, hsu, hdips⟩ := exists_left_level_witness hX C.locMin_ne hab hbc huc hulm hmin hob.1
    (lt_of_le_of_lt (le_max_left _ _) hstrict)
  obtain ⟨t, ht, hXt, hut, hdipt⟩ := exists_right_level_witness hX C.locMin_ne hbc hcd hub hulm hmin hoc.2
    (lt_of_le_of_lt (le_max_right _ _) hstrict)
  have hsu' : s < u := hs.2.trans hub
  have hut' : u < t := huc.trans ht.1
  have hge : ∀ r ∈ Icc s t, X u ≤ X r := by
    intro r hr
    rcases lt_trichotomy r u with h | h | h
    · rcases eq_or_lt_of_le hr.1 with h' | h'
      · exact le_of_eq (by rw [← h', hXs])
      · exact (hsu r ⟨h', h⟩).le
    · exact le_of_eq (by rw [h])
    · rcases eq_or_lt_of_le hr.2 with h' | h'
      · exact le_of_eq (by rw [h', hXt])
      · exact (hut r ⟨h, h'⟩).le
  refine ⟨u, ⟨⟨hub, huc⟩, s, hs, t, ht, ?_, ?_, ?_⟩, hmin⟩
  · exact C.cellSideContact_of_excursion hfin hsu' hXs rfl hsu
  · exact C.cellSideContact_of_excursion hfin hut' rfl hXt hut
  · exact C.cellSideContact_of_dips hfin (hsu'.trans hut').le hge hdips hdipt

/-! ### The count of branch times -/

/-- **The branch times count the coordinates satisfying the adjacency condition.** For a Peanosphere with finite
fibres, no continuum of points visited three times, no common local minimum of its coordinates, and descent of both
coordinates on both sides of `a < b < c < d`: `B_η` is nonempty if and only if the adjacency condition holds for `L`
or `R`, and contains two distinct times if and only if it holds for both. -/
theorem cellSideBranchTimes_iff {ω : Path2} {η : ℝ → ℂ} (P : Peanosphere ω η) (hfin : ∀ z, (η ⁻¹' {z}).Finite)
    (htriple : ¬ ContainsNondegenerateContinuum (curveTriplePoints η))
    (hcone : ∀ u, ¬ (IsLocalMin (lCoord ω) u ∧ IsLocalMin (rCoord ω) u)) {a b c d : ℝ} (hab : a < b)
    (hbc : b < c) (hcd : c < d) (hda : IsTwoSidedDescent (lCoord ω) a ∧ IsTwoSidedDescent (rCoord ω) a)
    (hdb : IsTwoSidedDescent (lCoord ω) b ∧ IsTwoSidedDescent (rCoord ω) b)
    (hdc : IsTwoSidedDescent (lCoord ω) c ∧ IsTwoSidedDescent (rCoord ω) c)
    (hdd : IsTwoSidedDescent (lCoord ω) d ∧ IsTwoSidedDescent (rCoord ω) d) :
    ((cellSideBranchTimes a b c d η).Nonempty ↔
        IntervalAdjacent (lCoord ω) a b c d ∨ IntervalAdjacent (rCoord ω) a b c d) ∧
      ((∃ u ∈ cellSideBranchTimes a b c d η, ∃ v ∈ cellSideBranchTimes a b c d η, u ≠ v) ↔
        IntervalAdjacent (lCoord ω) a b c d ∧ IntervalAdjacent (rCoord ω) a b c d) := by
  have CL := levelContactData_lCoord P
  have CR := levelContactData_rCoord P
  have hfwd : ∀ u ∈ cellSideBranchTimes a b c d η,
      (IntervalAdjacent (lCoord ω) a b c d ∧ ∀ r ∈ Icc b c, lCoord ω u ≤ lCoord ω r) ∨
        (IntervalAdjacent (rCoord ω) a b c d ∧ ∀ r ∈ Icc b c, rCoord ω u ≤ rCoord ω r) := by
    intro u hu
    obtain ⟨s, hs, t, ht, hc⟩ := isCenteredMin_of_mem_cellSideBranchTimes P htriple hu
    have hu' : u ∈ Icc b c := Ioo_subset_Icc_self hu.1
    rcases hc with hc | hc
    · exact Or.inl ⟨hc.intervalAdjacent CL.continuous (Ioo_subset_Icc_self hs) hu' (Ioo_subset_Icc_self ht),
        fun r hr => hc.2.2 r ⟨hs.2.le.trans hr.1, hr.2.trans ht.1.le⟩⟩
    · exact Or.inr ⟨hc.intervalAdjacent CR.continuous (Ioo_subset_Icc_self hs) hu' (Ioo_subset_Icc_self ht),
        fun r hr => hc.2.2 r ⟨hs.2.le.trans hr.1, hr.2.trans ht.1.le⟩⟩
  have hbwdL : IntervalAdjacent (lCoord ω) a b c d →
      ∃ u ∈ cellSideBranchTimes a b c d η, ∀ r ∈ Icc b c, lCoord ω u ≤ lCoord ω r := fun h =>
    CL.exists_mem_cellSideBranchTimes hfin hab hbc hcd hdb.1 hdc.1
      (h.strict CL.continuous CL.locMin_ne hab hbc hcd hda.1 hdb.1 hdc.1 hdd.1)
  have hbwdR : IntervalAdjacent (rCoord ω) a b c d →
      ∃ u ∈ cellSideBranchTimes a b c d η, ∀ r ∈ Icc b c, rCoord ω u ≤ rCoord ω r := fun h =>
    CR.exists_mem_cellSideBranchTimes hfin hab hbc hcd hdb.2 hdc.2
      (h.strict CR.continuous CR.locMin_ne hab hbc hcd hda.2 hdb.2 hdc.2 hdd.2)
  refine ⟨⟨fun ⟨u, hu⟩ => ?_, fun h => ?_⟩, ⟨fun ⟨u, hu, v, hv, huv⟩ => ?_, fun ⟨hL, hR⟩ => ?_⟩⟩
  · rcases hfwd u hu with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  · rcases h with h | h
    · obtain ⟨u, hu, -⟩ := hbwdL h
      exact ⟨u, hu⟩
    · obtain ⟨u, hu, -⟩ := hbwdR h
      exact ⟨u, hu⟩
  · rcases hfwd u hu with hu' | hu' <;> rcases hfwd v hv with hv' | hv'
    · exact absurd (eq_of_forall_le_of_mem_Ioo CL.locMin_ne hu.1 hv.1 hu'.2 hv'.2) huv
    · exact ⟨hu'.1, hv'.1⟩
    · exact ⟨hv'.1, hu'.1⟩
    · exact absurd (eq_of_forall_le_of_mem_Ioo CR.locMin_ne hu.1 hv.1 hu'.2 hv'.2) huv
  · obtain ⟨u, hu, hu'⟩ := hbwdL hL
    obtain ⟨v, hv, hv'⟩ := hbwdR hR
    refine ⟨u, hu, v, hv, fun h => hcone u ⟨isLocalMin_of_mem_Ioo hu.1 hu', ?_⟩⟩
    rw [h]
    exact isLocalMin_of_mem_Ioo hv.1 hv'

/-- The count `1_{A ∨ B} (1 + 1_{E ∧ A ∧ B})` is `1_C + 1_D` when `E` holds, `C ↔ A ∨ B` and `D ↔ A ∧ B`. -/
theorem ite_or_ite_and_eq_add {A B C D E : Prop} {i₁ : Decidable (A ∨ B)} {i₂ : Decidable (E ∧ A ∧ B)}
    {i₃ : Decidable C} {i₄ : Decidable D} (hE : E) (hC : C ↔ A ∨ B) (hD : D ↔ A ∧ B) :
    (if A ∨ B then (if E ∧ A ∧ B then (2 : ℕ) else 1) else 0) = (if C then 1 else 0) + (if D then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B
  · rw [ite_eq_left (show A ∨ B from Or.inl hA), ite_eq_left (show E ∧ A ∧ B from ⟨hE, hA, hB⟩),
      ite_eq_left (show C from hC.2 (Or.inl hA)), ite_eq_left (show D from hD.2 ⟨hA, hB⟩)]
  · rw [ite_eq_left (show A ∨ B from Or.inl hA), ite_eq_right (show ¬ (E ∧ A ∧ B) from fun h => hB h.2.2),
      ite_eq_left (show C from hC.2 (Or.inl hA)), ite_eq_right (show ¬ D from fun h => hB (hD.1 h).2)]
  · rw [ite_eq_left (show A ∨ B from Or.inr hB), ite_eq_right (show ¬ (E ∧ A ∧ B) from fun h => hA h.2.1),
      ite_eq_left (show C from hC.2 (Or.inr hB)), ite_eq_right (show ¬ D from fun h => hA (hD.1 h).1)]
  · rw [ite_eq_right (show ¬ (A ∨ B) from fun h => h.elim hA hB),
      ite_eq_right (show ¬ C from fun h => (hC.1 h).elim hA hB),
      ite_eq_right (show ¬ D from fun h => hA (hD.1 h).1)]

/-- **The Brownian edge count is the frontier-side multiplicity, deterministically.** For a Peanosphere `(ω, η)`
with finite fibres, no continuum of points visited three times, no common local minimum of its coordinates, and
descent of both coordinates on both sides of every point of `εℤ`, the edge count of Definition 1.1 equals
`cellSideMult ε η`. -/
theorem bmEdgeCount_eq_cellSideMult {ω : Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    (hfin : ∀ z, (η ⁻¹' {z}).Finite) (htriple : ¬ ContainsNondegenerateContinuum (curveTriplePoints η))
    (hcone : ∀ u, ¬ (IsLocalMin (lCoord ω) u ∧ IsLocalMin (rCoord ω) u)) {ε : ℝ} (hε : 0 < ε)
    (hdesc : ∀ k : ℤ, IsTwoSidedDescent (lCoord ω) (ε * k) ∧ IsTwoSidedDescent (rCoord ω) (ε * k))
    (j k : ℤ) : bmEdgeCount ε (lCoord ω) (rCoord ω) j k = cellSideMult ε η j k := by
  by_cases hjk : j = k
  · subst hjk
    simp [bmEdgeCount, cellSideMult]
  have hne : ¬ (ε ≤ 0 ∨ j = k) := fun h => h.elim (fun h' => absurd h' (not_le.2 hε)) hjk
  have hlohi : min j k < max j k := min_lt_max.2 hjk
  have habs : max j k - min j k = |j - k| := by
    rcases le_total j k with hle | hle
    · rw [min_eq_left hle, max_eq_right hle, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
    · rw [min_eq_right hle, max_eq_left hle, abs_of_nonneg (sub_nonneg.2 hle)]
  simp only [bmEdgeCount, hjk, ↓reduceIte]
  rw [cellSideMult, ite_eq_right hne]
  obtain ⟨lo, hlo⟩ : ∃ lo, min j k = lo := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi, max j k = hi := ⟨_, rfl⟩
  rw [hlo] at hlohi habs ⊢
  rw [hhi] at hlohi habs ⊢
  rw [← habs]
  by_cases h1 : hi - lo = 1
  · rw [ite_eq_left h1]
    have hadj : bmAdjacent ε (lCoord ω) lo hi :=
      (bmAdjacent_iff_forall_cellMin hε (levelContactData_lCoord P).continuous hlohi).2 fun i h2 h3 => by omega
    rw [ite_eq_left (show bmAdjacent ε (lCoord ω) lo hi ∨ bmAdjacent ε (rCoord ω) lo hi from Or.inl hadj),
      ite_eq_right (show ¬ (1 < hi - lo ∧ bmAdjacent ε (lCoord ω) lo hi ∧ bmAdjacent ε (rCoord ω) lo hi) from
        fun h => by
          have := h.1
          omega)]
  · rw [ite_eq_right h1]
    have hsep : 1 < hi - lo := by omega
    have h2 : (lo : ℝ) + 2 ≤ hi := by exact_mod_cast (show lo + 2 ≤ hi by omega)
    have hab : ε * ((lo : ℝ) - 1) < ε * lo := mul_lt_mul_of_pos_left (by linarith) hε
    have hbc : ε * (lo : ℝ) < ε * ((hi : ℝ) - 1) := mul_lt_mul_of_pos_left (by linarith) hε
    have hcd : ε * ((hi : ℝ) - 1) < ε * hi := mul_lt_mul_of_pos_left (by linarith) hε
    have hda := hdesc (lo - 1)
    have hdc := hdesc (hi - 1)
    push_cast at hda hdc
    have hadj : ∀ X : ℝ → ℝ, bmAdjacent ε X lo hi ↔
        IntervalAdjacent X (ε * ((lo : ℝ) - 1)) (ε * lo) (ε * ((hi : ℝ) - 1)) (ε * hi) := fun X => by
      have e1 : ε * (lo : ℝ) - ε = ε * ((lo : ℝ) - 1) := by ring
      have e2 : ε * (hi : ℝ) - ε = ε * ((hi : ℝ) - 1) := by ring
      unfold bmAdjacent IntervalAdjacent
      rw [e1, e2]
    obtain ⟨hB1, hB2⟩ := cellSideBranchTimes_iff P hfin htriple hcone hab hbc hcd hda (hdesc lo) hdc (hdesc hi)
    rw [cellSideCount]
    exact ite_or_ite_and_eq_add hsep (hB1.trans (or_congr (hadj (lCoord ω)) (hadj (rCoord ω))).symm)
      (hB2.trans (and_congr (hadj (lCoord ω)) (hadj (rCoord ω))).symm)

/-! ### The identity in a valid environment -/

/-- **The multiplicities of the mated-CRT map are the frontier-side multiplicities of the cells**
(`MatingOfTreesCellSideIdentity`; written answer MQ-sbl-31, lines 26-40). Given the two named literature inputs
`CorrelatedBMNoCommonLocalMin` (Le Gall) and `SpaceFillingSLETriplePointsNoContinuum 𝒮` (Gwynne–Holden–Miller,
Duplantier–Miller–Sheffield), in every valid environment, for every cell size `ε > 0`, almost surely
`S.mult ε = cellSideMult ε (S.η ω)`. The Peanosphere, the finite fibres and the Brownian law of the boundary-length
pair come from the mating-of-trees coupling of the environment. -/
theorem matingOfTreesCellSideIdentity {𝒮 : SpaceFillingSLEModel} (hcone : CorrelatedBMNoCommonLocalMin)
    (htriple : SpaceFillingSLETriplePointsNoContinuum 𝒮) : MatingOfTreesCellSideIdentity 𝒮 := by
  intro γ hγ0 hγ2 Ω _ S hS ε hε
  obtain ⟨ηc, hηc, hP, -⟩ := MatedCRTEnv.IsValid.exists_curve_peanosphere S hS
  obtain ⟨_, _, _, _, _, _, _, _, ηL, η', _, hC, hae⟩ := hS.matingOfTrees
  have hbm : AEMeasurable S.bm S.P := hC.measurable_curves.2.2.2.aemeasurable
  have hμ := hC.boundaryLawBM
  obtain ⟨kv, hkv⟩ := hC.visitBound
  have hfin : ∀ᵐ ω ∂S.P, ∀ z, (S.η ω ⁻¹' {z}).Finite := by
    filter_upwards [hkv, hC.areaParam, hae] with ω hk harea hω
    obtain ⟨⟨φ, -, hφ⟩, -⟩ := harea
    intro z
    have hset : S.η ω ⁻¹' {z} = φ ⁻¹' (ηL ω ⁻¹' {z}) := by
      ext t
      show S.η ω t = z ↔ ηL ω (φ t) = z
      rw [← hω.1, hφ]
    rw [hset]
    exact (Set.encard_lt_top_iff.1 ((hk z).trans_lt (ENat.natCast_lt_top kv))).preimage φ.injective.injOn
  have h16 : 4 < 16 / γ ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have htr := htriple Ω _ S.P S.fieldSigma (16 / γ ^ 2) S.η h16 hS.isSLE
  have hcn := ae_of_ae_map hbm (hcone γ hγ0 hγ2 _ hμ)
  have hd := ae_of_ae_map hbm (ae_all_iff.2 fun i : Fin 2 => ae_all_iff.2 fun k : ℤ =>
    (ae_forall_exists_lt_right hμ i (ε * k)).and (ae_forall_exists_lt_left hμ i (ε * k)))
  filter_upwards [hηc, hP, hfin, htr, hcn, hd] with ω hηω hPω hfinω htrω hcnω hdω
  rw [hηω] at hPω
  funext j k
  exact bmEdgeCount_eq_cellSideMult hPω hfinω htrω (fun u hu => hcnω u hu) hε
    (fun k => ⟨hdω 0 k, hdω 1 k⟩) j k

end MatedCRT
