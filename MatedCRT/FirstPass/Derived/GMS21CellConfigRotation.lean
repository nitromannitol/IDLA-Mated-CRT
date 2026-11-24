import MatedCRT.FirstPass.Derived.GMS21CovarianceIsotropy
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodeMeasurableLocal
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116
import LatticeProb.Walk.CellConfigLawRelabel
import LatticeProb.Walk.CellConfigSRWChain
import LatticeProb.Prob.CellConfigWalkMeasurable

/-!
# Rotations of cell configurations and isotropy of the limiting covariance

Gwynne–Miller–Sheffield, *The Tutte embedding of the mated-CRT map converges to Liouville quantum
gravity* (arXiv 1705.11161), Proposition 3.1: the covariance matrix `Σ` of the limiting Brownian
motion is a positive multiple of the identity, "since the law of `(h, η)` is invariant under
rotations about the origin".  The argument has three steps:

1. a rotation `ρ` of the plane maps a cell configuration `H` to a cell configuration `ρH`, and the
   law of `ρH` is the law of `H` when the latter is rotation invariant;
2. the simple random walk on `ρH` is `ρ` applied to the simple random walk on `H` (cells,
   conductances, areas and holding times are carried over by `ρ`), so for almost every `H` the
   rescaled walk and its rotation converge to the same Brownian motion;
3. a Brownian law invariant under the quarter turn has covariance `c • 1`.

Step 3 is `covariance_eq_smul_one_of_convergesWeaklyInC_quarterTurn`
(`GMS21CovarianceIsotropy.lean`).  This file proves steps 1 and 2 for every linear isometry `e` of
the Euclidean plane, in the setting of the Lean statement `ReflectedGMS.GMS.Theorem1_16`:

* `isometryCellConfig e H`, `isCellConfiguration_isometryCellConfig`: the image of a cell
  configuration under `e` is a cell configuration;
* `isSRWLaw_isometryCellConfig`, `interpolatedWalk_isometryCellEquiv`: the walk on `eH` is the
  image under `e` of the walk on `H`;
* `covariance_eq_smul_one_of_measurePreserving_quarterTurn`: if the law `μ` of the configuration
  is invariant under the quarter turn `quarterTurn` and connected along lines, every Brownian target
  of the quenched invariance principle for `μ` has covariance `c • 1` with `c > 0`;
* `exists_isotropic_target_of_measurePreserving_quarterTurn`: under the hypotheses of GMS
  Theorem 1.16 (`ReflectedGMS.GMS.theorem1_16`) and quarter-turn invariance of the law, the
  limiting Brownian motion has covariance `c • 1`.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Filter
open scoped NNReal Topology

open ReflectedGMS (Plane)
open ReflectedGMS.GMS ReflectedGMS.StatementIngredients
open ReflectedGMS.GMS.CellConfig (mapCell)

/-! ### The quarter turn of the Euclidean plane -/

/-- The quarter turn `(x, y) ↦ (-y, x)` of the Euclidean plane, as a linear isometry. -/
def quarterTurn : Plane ≃ₗᵢ[ℝ] Plane where
  toFun v := WithLp.toLp 2 ![-v 1, v 0]
  invFun v := WithLp.toLp 2 ![v 1, -v 0]
  map_add' v w := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp
  left_inv v := by
    ext i
    fin_cases i <;> simp
  right_inv v := by
    ext i
    fin_cases i <;> simp
  norm_map' v := by
    show ‖(WithLp.toLp 2 ![-v 1, v 0] : Plane)‖ = ‖v‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two,
      add_comm]
    simp

@[simp] theorem quarterTurn_apply_zero (v : Plane) : quarterTurn v 0 = -v 1 := rfl

@[simp] theorem quarterTurn_apply_one (v : Plane) : quarterTurn v 1 = v 0 := rfl

/-- A linear isometry of the plane applied to every value of a planar path. -/
def isometryPath (e : Plane ≃ₗᵢ[ℝ] Plane) (f : BouRabeeGwynne.BrownianPath 2) :
    BouRabeeGwynne.BrownianPath 2 :=
  ⟨fun t => e (f t), e.continuous.comp f.continuous⟩

@[simp] theorem isometryPath_apply (e : Plane ≃ₗᵢ[ℝ] Plane) (f : BouRabeeGwynne.BrownianPath 2)
    (t : ℝ≥0) : isometryPath e f t = e (f t) := rfl

/-- The quarter turn of paths of `GMS21CovarianceIsotropy.lean` is the quarter turn `quarterTurn`
applied to every value. -/
theorem quarterTurnPath_eq_isometryPath (f : BouRabeeGwynne.BrownianPath 2) :
    quarterTurnPath f = isometryPath quarterTurn f := by
  ext t i
  fin_cases i <;> simp [quarterTurnPath, quarterTurnMatrix, Fin.sum_univ_two]

/-- A point of a cell. -/
def cellPoint (K : Cell) : Plane := K.nonempty.some

theorem cellPoint_mem (K : Cell) : cellPoint K ∈ (K : Set Plane) := K.nonempty.some_mem

/-! ### The image of a cell configuration under a linear isometry -/

section Isometry

variable (e : Plane ≃ₗᵢ[ℝ] Plane)

/-- The image `eH` of a cell configuration `H` under a linear isometry `e` of the plane: the cells
are the images `e(K)` of the cells `K` of `H`, and the conductance of `e(K), e(K')` is `c(K, K')`. -/
def isometryCellConfig (H : CellConfig) : CellConfig where
  cells := mapCell e.toHomeomorph '' H.cells
  c K K' := H.c (mapCell e.toHomeomorph.symm K) (mapCell e.toHomeomorph.symm K')

variable {H : CellConfig}

theorem coe_mapCell_eq_preimage (K : Cell) :
    (mapCell e.toHomeomorph K : Set Plane) = e.symm ⁻¹' (K : Set Plane) := by
  rw [CellConfig.coe_mapCell_eq_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show e.symm (e y) ∈ (K : Set Plane)
    rw [e.symm_apply_apply]
    exact hy
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩

/-- A linear isometry preserves the Lebesgue measure of cells. -/
theorem volume_mapCell (K : Cell) :
    volume (mapCell e.toHomeomorph K : Set Plane) = volume (K : Set Plane) := by
  rw [coe_mapCell_eq_preimage]
  exact e.symm.measurePreserving.measure_preimage K.isCompact.measurableSet.nullMeasurableSet

theorem area_mapCell (K : Cell) :
    CellConfig.area (mapCell e.toHomeomorph K) = CellConfig.area K := by
  unfold CellConfig.area
  rw [volume_mapCell]

theorem mem_isometryCellConfig_cells {K : Cell} :
    K ∈ (isometryCellConfig e H).cells ↔ mapCell e.toHomeomorph.symm K ∈ H.cells := by
  constructor
  · rintro ⟨K0, hK0, rfl⟩
    rw [CellConfig.mapCell_symm_mapCell]
    exact hK0
  · intro h
    exact ⟨_, h, CellConfig.mapCell_mapCell_symm _ K⟩

theorem isometryCellConfig_c_mapCell (K K' : Cell) :
    (isometryCellConfig e H).c (mapCell e.toHomeomorph K) (mapCell e.toHomeomorph K') =
      H.c K K' := by
  show H.c (mapCell e.toHomeomorph.symm (mapCell e.toHomeomorph K))
    (mapCell e.toHomeomorph.symm (mapCell e.toHomeomorph K')) = H.c K K'
  rw [CellConfig.mapCell_symm_mapCell, CellConfig.mapCell_symm_mapCell]

/-- **The image of a cell configuration under a linear isometry is a cell configuration**
(GMS Definition 1.15). -/
theorem isCellConfiguration_isometryCellConfig (hH : H.IsCellConfiguration) :
    (isometryCellConfig e H).IsCellConfiguration where
  locallyFinite z := by
    obtain ⟨U, hU, hfin⟩ := hH.locallyFinite (e.toHomeomorph.symm z)
    refine ⟨e.toHomeomorph.symm ⁻¹' U,
      e.toHomeomorph.symm.continuous.continuousAt.preimage_mem_nhds hU,
      (hfin.image (mapCell e.toHomeomorph)).subset ?_⟩
    rintro _ ⟨⟨K0, hK0, rfl⟩, w, hwK, hwU⟩
    refine ⟨K0, ⟨hK0, ?_⟩, rfl⟩
    rw [CellConfig.coe_mapCell_eq_image] at hwK
    obtain ⟨w0, hw0, rfl⟩ := hwK
    refine ⟨w0, hw0, ?_⟩
    rwa [Set.mem_preimage, Homeomorph.symm_apply_apply] at hwU
  isConnected _ hK := by
    obtain ⟨K0, hK0, rfl⟩ := hK
    rw [CellConfig.coe_mapCell_eq_image]
    exact (hH.isConnected K0 hK0).image _ e.toHomeomorph.continuous.continuousOn
  interior_nonempty _ hK := by
    obtain ⟨K0, hK0, rfl⟩ := hK
    rw [CellConfig.coe_mapCell_eq_image]
    obtain ⟨z, hz⟩ := hH.interior_nonempty K0 hK0
    exact ⟨e.toHomeomorph z, interior_maximal (Set.image_mono interior_subset)
      (e.toHomeomorph.isOpenMap _ isOpen_interior) (Set.mem_image_of_mem _ hz)⟩
  iUnion_eq_univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨K0, hK0, hz0⟩ := Set.mem_iUnion₂.mp
      (Set.eq_univ_iff_forall.mp hH.iUnion_eq_univ (e.toHomeomorph.symm z))
    refine Set.mem_iUnion₂.mpr ⟨mapCell e.toHomeomorph K0, ⟨K0, hK0, rfl⟩, ?_⟩
    rw [CellConfig.coe_mapCell_eq_image]
    exact ⟨_, hz0, e.toHomeomorph.apply_symm_apply z⟩
  volume_inter _ hK _ hK' hne := by
    obtain ⟨K0, hK0, rfl⟩ := hK
    obtain ⟨K0', hK0', rfl⟩ := hK'
    rw [coe_mapCell_eq_preimage, coe_mapCell_eq_preimage, ← Set.preimage_inter,
      e.symm.measurePreserving.measure_preimage
        (K0.isCompact.measurableSet.inter K0'.isCompact.measurableSet).nullMeasurableSet]
    exact hH.volume_inter K0 hK0 K0' hK0' fun h => hne (congrArg _ h)
  c_nonneg _ _ := hH.c_nonneg _ _
  c_symm _ _ := hH.c_symm _ _
  adj_mem _ _ h := ⟨(mem_isometryCellConfig_cells e).2 (hH.adj_mem _ _ h).1,
    (mem_isometryCellConfig_cells e).2 (hH.adj_mem _ _ h).2⟩
  adj_ne _ _ h hKK := hH.adj_ne _ _ h (congrArg _ hKK)
  adj_inter _ _ h := by
    have h' := hH.adj_inter _ _ h
    rw [CellConfig.coe_mapCell_eq_image, CellConfig.coe_mapCell_eq_image,
      ← Set.image_inter e.toHomeomorph.symm.injective, Set.image_nonempty] at h'
    exact h'

/-- The image of a configuration of the space `GMSSpace` under a linear isometry of the plane. -/
def isometryGMS (H : GMSSpace) : GMSSpace :=
  ⟨isometryCellConfig e H.1, isCellConfiguration_isometryCellConfig e H.2⟩

variable (H) in
/-- The cells of `H` and of `eH` correspond through `e`. -/
def isometryCellEquiv : H.cells ≃ (isometryCellConfig e H).cells where
  toFun K := ⟨mapCell e.toHomeomorph K, K, K.2, rfl⟩
  invFun K := ⟨mapCell e.toHomeomorph.symm K, (mem_isometryCellConfig_cells e).1 K.2⟩
  left_inv _ := Subtype.ext (CellConfig.mapCell_symm_mapCell _ _)
  right_inv _ := Subtype.ext (CellConfig.mapCell_mapCell_symm _ _)

theorem c_isometryCellEquiv (K L : H.cells) :
    (isometryCellConfig e H).c (isometryCellEquiv e H K) (isometryCellEquiv e H L) = H.c K L :=
  isometryCellConfig_c_mapCell e (K : Cell) L

theorem pi_isometryCellEquiv (K : H.cells) :
    (isometryCellConfig e H).pi (isometryCellEquiv e H K) = H.pi K := by
  unfold CellConfig.pi
  rw [← (isometryCellEquiv e H).tsum_eq]
  exact tsum_congr fun L => c_isometryCellEquiv e K L

theorem transition_isometryCellEquiv (K L : H.cells) :
    (isometryCellConfig e H).transition (isometryCellEquiv e H K) (isometryCellEquiv e H L) =
      H.transition K L := by
  unfold CellConfig.transition
  rw [pi_isometryCellEquiv, c_isometryCellEquiv]

theorem holding_isometryCellEquiv (K : H.cells) :
    (isometryCellConfig e H).holding (isometryCellEquiv e H K) = H.holding K := by
  unfold CellConfig.holding
  rw [pi_isometryCellEquiv]
  exact congrArg (· / H.pi K) (area_mapCell e K)

theorem jumpTime_isometryCellEquiv (ω : ℕ → H.cells) (n : ℕ) :
    (isometryCellConfig e H).jumpTime (fun k => isometryCellEquiv e H (ω k)) n =
      H.jumpTime ω n := by
  unfold CellConfig.jumpTime
  exact Finset.sum_congr rfl fun k _ => holding_isometryCellEquiv e (ω k)

theorem jumpCount_isometryCellEquiv (ω : ℕ → H.cells) (t : ℝ) :
    (isometryCellConfig e H).jumpCount (fun k => isometryCellEquiv e H (ω k)) t =
      H.jumpCount ω t := by
  unfold CellConfig.jumpCount
  simp only [jumpTime_isometryCellEquiv]

theorem interpolatedPath_isometryCellEquiv (p : H.cells → Plane) (ω : ℕ → H.cells) (s : ℝ) :
    (isometryCellConfig e H).interpolatedPath (fun K' => e (p ((isometryCellEquiv e H).symm K')))
        (fun k => isometryCellEquiv e H (ω k)) s = e (H.interpolatedPath p ω s) := by
  unfold CellConfig.interpolatedPath
  simp only [jumpCount_isometryCellEquiv, jumpTime_isometryCellEquiv, holding_isometryCellEquiv,
    Equiv.symm_apply_apply, map_add, map_smul, map_sub]

open Classical in
/-- The path built in `CellConfig.interpolatedWalk` commutes with a linear isometry. -/
theorem dite_continuous_comp_isometry (F G : ℝ≥0 → Plane) (hFG : ∀ t, F t = e (G t)) :
    (if h : Continuous F then (⟨F, h⟩ : BouRabeeGwynne.BrownianPath 2) else 0) =
      isometryPath e (if h : Continuous G then (⟨G, h⟩ : BouRabeeGwynne.BrownianPath 2) else 0) := by
  have hF : F = e ∘ G := funext hFG
  subst hF
  by_cases h : Continuous G
  · rw [dite_eq_left (e.continuous.comp h), dite_eq_left h]
    rfl
  · rw [dite_eq_right (fun hc : Continuous (e ∘ G) => h (e.toHomeomorph.comp_continuous_iff.1 hc)),
      dite_eq_right h]
    ext t : 1
    simp

/-- **The rescaled walk on `eH` is `e` applied to the rescaled walk on `H`**, path by path: the
jump chain `e(Y_n)`, the points `e(p(Y_n))` and the same holding times `Area/π`. -/
theorem interpolatedWalk_isometryCellEquiv (p : H.cells → Plane) (ε : ℝ≥0) (ω : ℕ → H.cells) :
    (isometryCellConfig e H).interpolatedWalk (fun K' => e (p ((isometryCellEquiv e H).symm K')))
        ε (fun k => isometryCellEquiv e H (ω k)) = isometryPath e (H.interpolatedWalk p ε ω) := by
  unfold CellConfig.interpolatedWalk
  exact dite_continuous_comp_isometry e _ _ fun t => by
    simp only [interpolatedPath_isometryCellEquiv, map_smul]

/-- **The simple random walk on `eH` is the image of the walk on `H`**: the jump chain law of the
walk on `eH` from `e(K₀)` is the image of the jump chain law of the walk on `H` from `K₀`. -/
theorem isSRWLaw_isometryCellConfig [Countable H.cells] {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q) :
    (isometryCellConfig e H).IsSRWLaw (isometryCellEquiv e H K₀)
      (Q.map fun ω n => isometryCellEquiv e H (ω n)) := by
  have hc : Countable (isometryCellConfig e H).cells :=
    (isometryCellEquiv e H).symm.injective.countable
  have hQ1 : IsProbabilityMeasure Q := hQ.1
  exact LatticeProb.CellConfigSRW.isSRWLaw_map_of_cylinder (isometryCellConfig e H)
    (isometryCellEquiv e H) K₀ Q (fun v w => ENNReal.ofReal (H.transition v w))
    (fun n x => by
      rw [hQ.2 n x]
      by_cases hx : x 0 = K₀ <;> simp [hx])
    fun v w => by simp only [transition_isometryCellEquiv]

variable (H) in
/-- The correspondence of cells as a measurable equivalence (both sets of cells are countable and
carry σ-algebras with measurable singletons). -/
def isometryCellMeasurableEquiv [Countable H.cells] :
    H.cells ≃ᵐ (isometryCellConfig e H).cells :=
  have : Countable (isometryCellConfig e H).cells :=
    (isometryCellEquiv e H).symm.injective.countable
  { toEquiv := isometryCellEquiv e H
    measurable_toFun := measurable_of_countable _
    measurable_invFun := measurable_of_countable _ }

/-- **Transfer of the quenched invariance principle along a linear isometry.** If the walk on `eH`
(from `e(K₀)`, through the points `e ∘ p`) converges weakly to a Brownian target, then so does `e`
applied to the walk on `H`. -/
theorem convergesWeaklyInC_isometryPath [Countable H.cells] {Q : Measure (ℕ → H.cells)}
    (p : H.cells → Plane) {target : AnisotropicBrownianTarget}
    (h : ConvergesWeaklyInC (Q.map fun ω n => isometryCellEquiv e H (ω n))
      ((isometryCellConfig e H).interpolatedWalk
        fun K' => e (p ((isometryCellEquiv e H).symm K'))) target) :
    ConvergesWeaklyInC Q (fun ε ω => isometryPath e (H.interpolatedWalk p ε ω)) target := by
  have hmap : (Q.map fun ω n => isometryCellEquiv e H (ω n)) =
      Q.map (MeasurableEquiv.piCongrRight fun _ : ℕ => isometryCellMeasurableEquiv e H) := rfl
  have hint : ∀ (G : BouRabeeGwynne.BrownianPath 2 → ℝ) (ε : ℝ≥0),
      ∫ ω', G ((isometryCellConfig e H).interpolatedWalk
          (fun K' => e (p ((isometryCellEquiv e H).symm K'))) ε ω')
          ∂(Q.map fun ω n => isometryCellEquiv e H (ω n)) =
        ∫ ω, G (isometryPath e (H.interpolatedWalk p ε ω)) ∂Q := by
    intro G ε
    rw [hmap, integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact congrArg G (interpolatedWalk_isometryCellEquiv e p ε ω)
  intro G hG hb
  exact Filter.Tendsto.congr (hint G) (h G hG hb)

end Isometry

/-! ### Isotropy of the limiting covariance -/

/-- **Isotropy from one configuration and its quarter turn.** Let `H` be a cell configuration in
which every cell has a neighbour.  If the rescaled walks on `H` and on its quarter turn `ρH` (from
every starting cell, through every choice of points of the cells) converge weakly to the same
Brownian target, then the covariance of the target is `c • 1` with `c > 0`. -/
theorem covariance_eq_smul_one_of_convergesWeaklyInC_quarterTurnCellConfig {H : CellConfig}
    (hH : H.IsCellConfiguration) (hadj : ∀ K : H.cells, ∃ K' : H.cells, H.Adj K K')
    {target : AnisotropicBrownianTarget}
    (h1 : ∀ (K₀ : H.cells) (Q : Measure (ℕ → H.cells)), H.IsSRWLaw K₀ Q →
      ∀ p : H.cells → Plane, (∀ K : H.cells, p K ∈ ((K : Cell) : Set Plane)) →
        ConvergesWeaklyInC Q (H.interpolatedWalk p) target)
    (h2 : ∀ (K₀ : (isometryCellConfig quarterTurn H).cells)
      (Q : Measure (ℕ → (isometryCellConfig quarterTurn H).cells)),
      (isometryCellConfig quarterTurn H).IsSRWLaw K₀ Q →
      ∀ p : (isometryCellConfig quarterTurn H).cells → Plane,
        (∀ K : (isometryCellConfig quarterTurn H).cells, p K ∈ ((K : Cell) : Set Plane)) →
        ConvergesWeaklyInC Q ((isometryCellConfig quarterTurn H).interpolatedWalk p) target) :
    ∃ c : ℝ≥0, 0 < c ∧ target.covariance = (c : ℝ) • 1 := by
  have hc : Countable H.cells :=
    LatticeProb.CellConfigWalk.countable_cells_of_locallyFinite hH.locallyFinite
  have h0 : (0 : Plane) ∈ ⋃ K ∈ H.cells, ((K : Cell) : Set Plane) := by
    rw [hH.iUnion_eq_univ]
    exact Set.mem_univ _
  obtain ⟨K0, hK0, -⟩ := Set.mem_iUnion₂.1 h0
  obtain ⟨K₁, hK₁⟩ := hadj ⟨K0, hK0⟩
  have hQ := LatticeProb.CellConfigSRW.isSRWLaw_walkLaw H hH
    (LatticeProb.CellConfigWalk.pi_pos_of_adj hH hK₁)
  have hp' : ∀ K' : (isometryCellConfig quarterTurn H).cells,
      quarterTurn (cellPoint ((isometryCellEquiv quarterTurn H).symm K')) ∈
        ((K' : Cell) : Set Plane) := by
    intro K'
    obtain ⟨K, rfl⟩ := (isometryCellEquiv quarterTurn H).surjective K'
    rw [Equiv.symm_apply_apply]
    exact Set.mem_image_of_mem quarterTurn.toHomeomorph (cellPoint_mem K)
  have hY := h1 _ _ hQ (fun K => cellPoint K) fun K => cellPoint_mem K
  have hY' := h2 _ _ (isSRWLaw_isometryCellConfig quarterTurn hQ) _ hp'
  have hrot := convergesWeaklyInC_isometryPath quarterTurn (fun K => cellPoint K) hY'
  simp only [← quarterTurnPath_eq_isometryPath] at hrot
  exact covariance_eq_smul_one_of_convergesWeaklyInC_quarterTurn hY hrot

/-- **Isotropy of the limiting covariance (GMS21, Proposition 3.1, last assertion).** Let `μ` be
the law of a random cell configuration which is connected along lines and whose law is invariant
under the quarter turn of the plane.  Then every Brownian target of the quenched invariance
principle for `μ` (the first conclusion of GMS Theorem 1.16) has covariance `c • 1` with
`c > 0`. -/
theorem covariance_eq_smul_one_of_measurePreserving_quarterTurn {μ : Measure GMSSpace}
    [IsProbabilityMeasure μ] (hrot : MeasurePreserving (isometryGMS quarterTurn) μ μ)
    (hconn : ConnectedAlongLines μ) {target : AnisotropicBrownianTarget}
    (hconv : ∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
      ∀ p : H.1.cells → Plane, (∀ K : H.1.cells, p K ∈ ((K : Cell) : Set Plane)) →
        ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target) :
    ∃ c : ℝ≥0, 0 < c ∧ target.covariance = (c : ℝ) • 1 := by
  obtain ⟨H, hH1, hH2, hadj⟩ := (hconv.and ((hrot.quasiMeasurePreserving.ae hconv).and
    (LatticeProb.CellConfigWalk.ae_forall_exists_adj hconn))).exists
  exact covariance_eq_smul_one_of_convergesWeaklyInC_quarterTurnCellConfig H.2 hadj hH1 hH2

/-- **GMS Theorem 1.16 with an isotropic limit.** Under the hypotheses of GMS Theorem 1.16
(proved as `ReflectedGMS.GMS.theorem1_16`) and invariance of the law of the cell configuration
under the quarter turn of the plane, the limiting Brownian motion of the rescaled walk has
covariance `c • 1` with `c > 0`, together with the recurrence and harmonic-coordinate conclusions
of Theorem 1.16. -/
theorem exists_isotropic_target_of_measurePreserving_quarterTurn (μ : Measure GMSSpace)
    [IsProbabilityMeasure μ] (hmt : MassTransport μ) (herg : ErgodicModuloScaling μ)
    (hfin : FiniteExpectation μ) (hconn : ConnectedAlongLines μ)
    (hrot : MeasurePreserving (isometryGMS quarterTurn) μ μ) :
    ∃ target : AnisotropicBrownianTarget,
      (∃ c : ℝ≥0, 0 < c ∧ target.covariance = (c : ℝ) • 1) ∧
      (∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
        ∀ p : H.1.cells → Plane, (∀ K : H.1.cells, p K ∈ ((K : Cell) : Set Plane)) →
          ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target) ∧
      (∀ᵐ H ∂μ, H.1.Recurrent) ∧
      (∀ᵐ H ∂μ, ∃ φ : H.1.cells → Plane, H.1.DiscreteHarmonic φ ∧ H.1.SublinearToCentroid φ) := by
  obtain ⟨target, hconv, hrec, hharm⟩ := theorem1_16 μ hmt herg hfin hconn
  exact ⟨target, covariance_eq_smul_one_of_measurePreserving_quarterTurn hrot hconn hconv, hconv,
    hrec, hharm⟩

end MatedCRT
