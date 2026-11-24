import MatedCRT.FirstPass.Derived.WindowDiscMap
import LatticeProb.Topology.PolishContinuousMap
import LatticeProb.Topology.ContinuousMapBorel
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# A Borel choice of the normalized conformal map of a window

For times `a, u, b` and a curve `η`, the window domain `U = windowDomain η a u b` is the component at `η(u)` of the
interior of `η([a, b])`. When `U` has an inverse chart at `η(u)`, it has a unique normalized conformal map `φ` of the
closed disc onto its closure (`φ 0 = η(u)`, `φ'(0) > 0`; `IsNormalizedDiscMap.eqOn`). This file shows that the map
`η ↦ φ` can be chosen Borel (Berestycki–Gwynne (2020), proof of Lemma 7.18, uses the conformal maps of the windows as
random variables).

The pairs `(η, φ)` with `φ` the normalized conformal map, extended to `ℂ` through the radial retraction onto the
closed disc, form a Borel set `windowDiscMapGraph a u b` of `C(ℝ, ℂ) × C(ℂ, ℂ)`: injectivity on the closed disc is a
`G_δ` condition, holomorphy on the open disc with `φ'(0) ∈ [0, ∞)` is closed (locally uniform limits of holomorphic
maps), and the image conditions reduce to "the open disc is mapped into `η([a, b])` and the circle outside the
interior of `η([a, b])`" (`isDiscMap_connectedComponentIn_iff`). By uniqueness the first projection is injective on
this set, so the choice along it is Borel (Lusin–Souslin, `measurable_graphChoice`).

## Main statements

* `isDiscMap_connectedComponentIn_iff`, `measurableSet_windowDiscMapGraph`, `measurable_graphChoice`.
* `windowDiscMap`, `measurable_windowDiscMap`, `isNormalizedDiscMap_windowDiscMap`.
-/

set_option autoImplicit false

open Set Metric Filter Topology MeasureTheory

namespace MatedCRT

/-! ### Topological preliminaries -/

/-- Projection along a compact set: if `{(x, y) | P x y}` is closed, so is `{x | ∃ y ∈ C, P x y}` for compact `C`. -/
theorem isClosed_setOf_exists_mem_of_isCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {C : Set Y} (hC : IsCompact C) {P : X → Y → Prop} (hP : IsClosed {p : X × Y | P p.1 p.2}) :
    IsClosed {x | ∃ y ∈ C, P x y} := by
  have : CompactSpace C := isCompact_iff_compactSpace.1 hC
  have hc : IsClosed {p : X × C | P p.1 p.2} :=
    hP.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have himg : {x | ∃ y ∈ C, P x y} = Prod.fst '' {p : X × C | P p.1 p.2} := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨(x, ⟨y, hy⟩), hxy, rfl⟩
    · rintro ⟨⟨x', y⟩, h, rfl⟩
      exact ⟨y, y.2, h⟩
  rw [himg]
  exact isClosedMap_fst_of_compactSpace _ hc

/-- `{(η, p) | p ∈ η([a, b])}` is closed in `C(ℝ, ℂ) × ℂ`. -/
theorem isClosed_setOf_mem_image_Icc_prod (a b : ℝ) :
    IsClosed {x : C(ℝ, ℂ) × ℂ | x.2 ∈ x.1 '' Icc a b} :=
  isClosed_setOf_exists_mem_of_isCompact (isCompact_Icc (a := a) (b := b))
    (P := fun (x : C(ℝ, ℂ) × ℂ) (t : ℝ) => x.1 t = x.2)
    (isClosed_eq (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
      (continuous_snd.comp continuous_fst))

/-- A point lies in the interior of `K` iff a closed ball of radius `1/(n+1)` around it lies in `K`. -/
theorem mem_interior_iff_exists_nat_closedBall {K : Set ℂ} {y : ℂ} :
    y ∈ interior K ↔ ∃ n : ℕ, ∀ v ∈ closedBall (0 : ℂ) (1 / ((n : ℝ) + 1)), y + v ∈ K := by
  constructor
  · intro hy
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨n, fun v hv => hball ?_⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (mem_closedBall_zero_iff.1 hv).trans_lt hn
  · rintro ⟨n, hn⟩
    refine mem_interior_iff_mem_nhds.2
      (Metric.mem_nhds_iff.2 ⟨1 / ((n : ℝ) + 1), Nat.one_div_pos_of_nat, fun x hx => ?_⟩)
    rw [mem_ball, dist_eq_norm] at hx
    have h := hn (x - y) (mem_closedBall_zero_iff.2 hx.le)
    simpa using h

/-- For an open set `O`, a point of `O` in the closure of a connected component of `O` lies in that component. -/
theorem mem_connectedComponentIn_of_mem_closure {O : Set ℂ} (hO : IsOpen O) {x z : ℂ} (hx : x ∈ O)
    (hxc : x ∈ closure (connectedComponentIn O z)) : x ∈ connectedComponentIn O z := by
  obtain ⟨y, hyx, hyz⟩ := mem_closure_iff.1 hxc _ hO.connectedComponentIn (mem_connectedComponentIn hx)
  rw [connectedComponentIn_eq hyz, ← connectedComponentIn_eq hyx]
  exact mem_connectedComponentIn hx

/-! ### Conformal maps of the disc onto components -/

theorem closure_image_ball_eq {φ : ℂ → ℂ} (hc : ContinuousOn φ (closedBall 0 1)) :
    closure (φ '' ball 0 1) = φ '' closedBall 0 1 := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono ball_subset_closedBall)
      ((isCompact_closedBall 0 1).image_of_continuousOn hc).isClosed
  · rw [← closure_ball (0 : ℂ) one_ne_zero]
    exact ContinuousOn.image_closure (by rwa [closure_ball (0 : ℂ) one_ne_zero])

/-- The frontier of the image of the open disc under a continuous injection of the closed disc which is
holomorphic on the open disc is the image of the circle. -/
theorem frontier_image_ball {φ : ℂ → ℂ} (hc : ContinuousOn φ (closedBall 0 1)) (hi : InjOn φ (closedBall 0 1))
    (hd : DifferentiableOn ℂ φ (ball 0 1)) : frontier (φ '' ball 0 1) = φ '' sphere 0 1 := by
  have hVo : IsOpen (φ '' ball 0 1) :=
    QuantumZipper.CA.isOpen_image_of_injOn' isOpen_ball hd (hi.mono ball_subset_closedBall)
  rw [hVo.frontier_eq, closure_image_ball_eq hc]
  ext x
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hx⟩
    refine ⟨w, ?_, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    rw [mem_closedBall_zero_iff] at hw
    exact le_antisymm hw (not_lt.1 fun hlt => hx ⟨w, mem_ball_zero_iff.2 hlt, rfl⟩)
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, sphere_subset_closedBall hw, rfl⟩, ?_⟩
    rintro ⟨w', hw', hww⟩
    have h := hi (ball_subset_closedBall hw') (sphere_subset_closedBall hw) hww
    rw [h, mem_ball_zero_iff, mem_sphere_zero_iff_norm.1 hw] at hw'
    exact lt_irrefl _ hw'

/-- **Conformal maps onto a component of an open set.** Let `φ` be continuous and injective on the closed disc and
holomorphic on the open disc, and let `O` be open. Then `φ` maps the open disc onto the component of `O` at `φ 0` and
the circle onto its frontier iff it maps the open disc into `O` and the circle outside `O`. -/
theorem isDiscMap_connectedComponentIn_iff {O : Set ℂ} (hO : IsOpen O) {φ : ℂ → ℂ}
    (hc : ContinuousOn φ (closedBall 0 1)) (hi : InjOn φ (closedBall 0 1)) (hd : DifferentiableOn ℂ φ (ball 0 1)) :
    IsDiscMap (connectedComponentIn O (φ 0)) φ ↔
      MapsTo φ (ball 0 1) O ∧ ∀ w ∈ sphere (0 : ℂ) 1, φ w ∉ O := by
  have hVo : IsOpen (φ '' ball 0 1) :=
    QuantumZipper.CA.isOpen_image_of_injOn' isOpen_ball hd (hi.mono ball_subset_closedBall)
  have hfr := frontier_image_ball hc hi hd
  constructor
  · intro h
    refine ⟨fun w hw => connectedComponentIn_subset O (φ 0) (h.image_ball ▸ mem_image_of_mem φ hw),
      fun w hw hwO => ?_⟩
    have hfw : φ w ∈ frontier (connectedComponentIn O (φ 0)) := h.image_sphere ▸ mem_image_of_mem φ hw
    rw [hO.connectedComponentIn.frontier_eq] at hfw
    exact hfw.2 (mem_connectedComponentIn_of_mem_closure hO hwO hfw.1)
  · rintro ⟨hmaps, hsph⟩
    have h0O : φ 0 ∈ O := hmaps (mem_ball_self one_pos)
    have h0V : φ 0 ∈ φ '' ball 0 1 := mem_image_of_mem φ (mem_ball_self one_pos)
    have hsub : φ '' ball 0 1 ⊆ connectedComponentIn O (φ 0) :=
      ((convex_ball (0 : ℂ) 1).isPreconnected.image φ (hc.mono ball_subset_closedBall)).subset_connectedComponentIn
        h0V hmaps.image_subset
    have hsup : connectedComponentIn O (φ 0) ⊆ φ '' ball 0 1 := by
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hVo isClosed_closure.isOpen_compl
        (disjoint_compl_right.mono_left subset_closure) ?_ ⟨φ 0, mem_connectedComponentIn h0O, h0V⟩
      intro y hy
      by_cases hyV : y ∈ φ '' ball 0 1
      · exact Or.inl hyV
      · refine Or.inr fun hycl => ?_
        have hyf : y ∈ frontier (φ '' ball 0 1) := by
          rw [hVo.frontier_eq]
          exact ⟨hycl, hyV⟩
        rw [hfr] at hyf
        obtain ⟨w, hw, rfl⟩ := hyf
        exact hsph w hw (connectedComponentIn_subset O (φ 0) hy)
    have hball : φ '' ball 0 1 = connectedComponentIn O (φ 0) := Subset.antisymm hsub hsup
    exact ⟨hc, hi, hd, hball, by rw [← hball, hfr]⟩

/-! ### The Borel graph -/

/-- Injectivity on the closed disc is a Borel (`G_δ`) condition on `C(ℂ, ℂ)`. -/
theorem measurableSet_setOf_injOn_closedBall :
    MeasurableSet {φ : C(ℂ, ℂ) | InjOn φ (closedBall 0 1)} := by
  have h : {φ : C(ℂ, ℂ) | InjOn φ (closedBall 0 1)} = ⋂ n : ℕ, {φ : C(ℂ, ℂ) | ∃ p ∈
      (closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ) 1) ∩ {p : ℂ × ℂ | 1 / ((n : ℝ) + 1) ≤ dist p.1 p.2},
      φ p.1 = φ p.2}ᶜ := by
    ext φ
    simp only [mem_iInter, mem_compl_iff]
    constructor
    · intro hφ n hex
      obtain ⟨p, hp, hpe⟩ := hex
      have hinj : InjOn φ (closedBall 0 1) := hφ
      have hd : 1 / ((n : ℝ) + 1) ≤ dist p.1 p.2 := hp.2
      rw [hinj hp.1.1 hp.1.2 hpe, dist_self] at hd
      exact absurd hd (not_le.2 Nat.one_div_pos_of_nat)
    · intro hφ w hw w' hw' hww
      by_contra hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.2 hne)
      exact hφ n ⟨(w, w'), ⟨⟨hw, hw'⟩, hn.le⟩, hww⟩
  rw [h]
  refine MeasurableSet.iInter fun n => (IsClosed.measurableSet ?_).compl
  refine isClosed_setOf_exists_mem_of_isCompact (((isCompact_closedBall 0 1).prod
    (isCompact_closedBall 0 1)).inter_right (isClosed_le continuous_const continuous_dist)) ?_
  exact isClosed_eq (continuous_eval.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
    (continuous_eval.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

/-- Holomorphy on the open disc together with `φ'(0) ∈ [0, ∞)` is a closed condition on `C(ℂ, ℂ)` (locally uniform
limits of holomorphic maps are holomorphic, with the limit derivatives). -/
theorem isClosed_setOf_differentiableOn_ball_deriv :
    IsClosed {φ : C(ℂ, ℂ) | DifferentiableOn ℂ φ (ball 0 1) ∧ 0 ≤ (deriv φ 0).re ∧ (deriv φ 0).im = 0} := by
  set S := {φ : C(ℂ, ℂ) | DifferentiableOn ℂ φ (ball 0 1) ∧ 0 ≤ (deriv φ 0).re ∧ (deriv φ 0).im = 0}
  refine isClosed_iff_clusterPt.2 fun φ hφ => ?_
  have hl : (𝓝 φ ⊓ 𝓟 S).NeBot := hφ
  have ht : Tendsto (fun g : C(ℂ, ℂ) => g) (𝓝 φ ⊓ 𝓟 S) (𝓝 φ) := tendsto_id.mono_left inf_le_left
  have hlu : TendstoLocallyUniformlyOn (fun (g : C(ℂ, ℂ)) (z : ℂ) => g z) φ (𝓝 φ ⊓ 𝓟 S) (ball 0 1) :=
    (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 ht).tendstoLocallyUniformlyOn
  have hev : ∀ᶠ g in 𝓝 φ ⊓ 𝓟 S, g ∈ S := mem_inf_of_right (mem_principal_self S)
  have hd : ∀ᶠ g in 𝓝 φ ⊓ 𝓟 S, DifferentiableOn ℂ (fun z => (g : C(ℂ, ℂ)) z) (ball 0 1) :=
    hev.mono fun g hg => hg.1
  have hφd : DifferentiableOn ℂ φ (ball 0 1) := hlu.differentiableOn hd isOpen_ball
  have hder := (hlu.deriv hd isOpen_ball).tendsto_at (mem_ball_self one_pos)
  have hT : IsClosed {w : ℂ | 0 ≤ w.re ∧ w.im = 0} :=
    (isClosed_le continuous_const Complex.continuous_re).inter (isClosed_eq Complex.continuous_im continuous_const)
  exact ⟨hφd, hT.mem_of_tendsto hder (hev.mono fun g hg => hg.2)⟩

/-- The radial retraction of `ℂ` onto the closed unit disc, `w ↦ w / max 1 |w|`. -/
noncomputable def discRetract : C(ℂ, ℂ) :=
  ⟨fun w => (max 1 ‖w‖)⁻¹ • w,
    ((continuous_const.max continuous_norm).inv₀ fun w => (one_pos.trans_le (le_max_left 1 ‖w‖)).ne').smul
      continuous_id⟩

theorem discRetract_apply (w : ℂ) : discRetract w = (max 1 ‖w‖)⁻¹ • w :=
  rfl

theorem discRetract_mem (w : ℂ) : discRetract w ∈ closedBall (0 : ℂ) 1 := by
  have hpos : 0 < max 1 ‖w‖ := one_pos.trans_le (le_max_left 1 ‖w‖)
  rw [mem_closedBall_zero_iff, discRetract_apply, norm_smul, norm_inv, Real.norm_of_nonneg hpos.le]
  calc (max 1 ‖w‖)⁻¹ * ‖w‖ ≤ (max 1 ‖w‖)⁻¹ * max 1 ‖w‖ :=
        mul_le_mul_of_nonneg_left (le_max_right 1 ‖w‖) (inv_nonneg.2 hpos.le)
    _ = 1 := inv_mul_cancel₀ hpos.ne'

theorem discRetract_of_mem {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) : discRetract w = w := by
  rw [discRetract_apply, max_eq_left (mem_closedBall_zero_iff.1 hw), inv_one, one_smul]

/-- A map agreeing with a normalized conformal map on the closed disc is a normalized conformal map. -/
theorem IsNormalizedDiscMap.congr {U : Set ℂ} {z : ℂ} {φ φ' : ℂ → ℂ} (h : IsNormalizedDiscMap U z φ)
    (hE : EqOn φ φ' (closedBall 0 1)) : IsNormalizedDiscMap U z φ' := by
  have hEb : EqOn φ φ' (ball 0 1) := hE.mono ball_subset_closedBall
  have hev : φ' =ᶠ[𝓝 0] φ :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) fun w hw => (hEb hw).symm
  refine ⟨⟨h.isDiscMap.continuousOn.congr fun w hw => (hE hw).symm, h.isDiscMap.injOn.congr hE,
    h.isDiscMap.differentiableOn.congr fun w hw => (hEb hw).symm, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [← hEb.image_eq]
    exact h.isDiscMap.image_ball
  · rw [← (hE.mono sphere_subset_closedBall).image_eq]
    exact h.isDiscMap.image_sphere
  · rw [← hE (mem_closedBall_self zero_le_one)]
    exact h.apply_zero
  · rw [hev.deriv_eq]
    exact h.deriv_re_pos
  · rw [hev.deriv_eq]
    exact h.deriv_im

/-- The graph of the normalized conformal maps of the windows `(a, u, b)`: the pairs `(η, φ)` with `φ` the normalized
conformal map of `windowDomain η a u b` at `η(u)`, constant along the rays outside the closed disc. -/
def windowDiscMapGraph (a u b : ℝ) : Set (C(ℝ, ℂ) × C(ℂ, ℂ)) :=
  {p | IsNormalizedDiscMap (windowDomain p.1 a u b) (p.1 u) p.2 ∧ ∀ w, p.2 w = p.2 (discRetract w)}

theorem mem_windowDiscMapGraph {a u b : ℝ} {η : C(ℝ, ℂ)} {φ : C(ℂ, ℂ)} :
    (η, φ) ∈ windowDiscMapGraph a u b ↔
      IsNormalizedDiscMap (windowDomain η a u b) (η u) φ ∧ ∀ w, φ w = φ (discRetract w) :=
  Iff.rfl

/-- **The graph is Borel.** -/
theorem measurableSet_windowDiscMapGraph (a u b : ℝ) : MeasurableSet (windowDiscMapGraph a u b) := by
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have : PolishSpace C(ℂ, ℂ) := LatticeProb.polishSpace_continuousMap ℂ ℂ
  have heq : windowDiscMapGraph a u b =
      {p : C(ℝ, ℂ) × C(ℂ, ℂ) | InjOn p.2 (closedBall 0 1)} ∩
      {p : C(ℝ, ℂ) × C(ℂ, ℂ) | DifferentiableOn ℂ p.2 (ball 0 1) ∧ 0 ≤ (deriv p.2 0).re ∧
        (deriv p.2 0).im = 0} ∩
      {p : C(ℝ, ℂ) × C(ℂ, ℂ) | p.2 0 = p.1 u} ∩
      {p : C(ℝ, ℂ) × C(ℂ, ℂ) | ∀ w ∈ ball (0 : ℂ) 1, p.2 w ∈ p.1 '' Icc a b} ∩
      {p : C(ℝ, ℂ) × C(ℂ, ℂ) | ∀ w ∈ sphere (0 : ℂ) 1, p.2 w ∉ interior (p.1 '' Icc a b)} ∩
      {p : C(ℝ, ℂ) × C(ℂ, ℂ) | ∀ w, p.2 w = p.2 (discRetract w)} := by
    ext ⟨η, φ⟩
    have hO : IsOpen (interior (η '' Icc a b)) := isOpen_interior
    have hc : ContinuousOn φ (closedBall 0 1) := φ.continuous.continuousOn
    constructor
    · intro hp
      obtain ⟨hN, hR⟩ := mem_windowDiscMapGraph.1 hp
      have hU : windowDomain η a u b = connectedComponentIn (interior (η '' Icc a b)) (φ 0) := by
        rw [hN.apply_zero]
        rfl
      have hD : IsDiscMap (connectedComponentIn (interior (η '' Icc a b)) (φ 0)) φ := hU ▸ hN.isDiscMap
      obtain ⟨hmaps, hsph⟩ :=
        (isDiscMap_connectedComponentIn_iff hO hc hN.isDiscMap.injOn hN.isDiscMap.differentiableOn).1 hD
      exact ⟨⟨⟨⟨⟨hN.isDiscMap.injOn, hN.isDiscMap.differentiableOn, hN.deriv_re_pos.le, hN.deriv_im⟩,
        hN.apply_zero⟩, fun w hw => interior_subset (hmaps hw)⟩, hsph⟩, hR⟩
    · rintro ⟨⟨⟨⟨⟨hi, hd, hre, him⟩, h0⟩, hF⟩, hG⟩, hR⟩
      have hVo : IsOpen (φ '' ball 0 1) :=
        QuantumZipper.CA.isOpen_image_of_injOn' isOpen_ball hd (hi.mono ball_subset_closedBall)
      have hmaps : MapsTo φ (ball 0 1) (interior (η '' Icc a b)) := fun w hw =>
        interior_maximal (by rintro _ ⟨w', hw', rfl⟩; exact hF w' hw') hVo (mem_image_of_mem φ hw)
      have hD := (isDiscMap_connectedComponentIn_iff hO hc hi hd).2 ⟨hmaps, hG⟩
      have h0' : φ 0 = η u := h0
      have hU : windowDomain η a u b = connectedComponentIn (interior (η '' Icc a b)) (φ 0) := by
        rw [h0']
        rfl
      have hne : deriv φ 0 ≠ 0 :=
        QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hd (hi.mono ball_subset_closedBall)
          (mem_ball_self one_pos)
      have hpos : 0 < (deriv φ 0).re := by
        refine lt_of_le_of_ne hre fun h => hne (Complex.ext ?_ ?_)
        · simpa using h.symm
        · simpa using him
      refine mem_windowDiscMapGraph.2 ⟨⟨?_, h0', hpos, him⟩, hR⟩
      rw [hU]
      exact hD
  have m4 : IsClosed {p : C(ℝ, ℂ) × C(ℂ, ℂ) | ∀ w ∈ ball (0 : ℂ) 1, p.2 w ∈ p.1 '' Icc a b} := by
    have : {p : C(ℝ, ℂ) × C(ℂ, ℂ) | ∀ w ∈ ball (0 : ℂ) 1, p.2 w ∈ p.1 '' Icc a b} =
        ⋂ w ∈ ball (0 : ℂ) 1, {p : C(ℝ, ℂ) × C(ℂ, ℂ) | p.2 w ∈ p.1 '' Icc a b} := by
      ext p
      simp only [mem_iInter, mem_ofPred_eq]
    rw [this]
    exact isClosed_biInter fun w _ => (isClosed_setOf_mem_image_Icc_prod a b).preimage
      (continuous_fst.prodMk ((continuous_eval_const w).comp continuous_snd))
  have m5 : MeasurableSet
      {p : C(ℝ, ℂ) × C(ℂ, ℂ) | ∀ w ∈ sphere (0 : ℂ) 1, p.2 w ∉ interior (p.1 '' Icc a b)} := by
    have : {p : C(ℝ, ℂ) × C(ℂ, ℂ) | ∀ w ∈ sphere (0 : ℂ) 1, p.2 w ∉ interior (p.1 '' Icc a b)} =
        (⋃ n : ℕ, {p : C(ℝ, ℂ) × C(ℂ, ℂ) | ∃ w ∈ sphere (0 : ℂ) 1,
          ∀ v ∈ closedBall (0 : ℂ) (1 / ((n : ℝ) + 1)), p.2 w + v ∈ p.1 '' Icc a b})ᶜ := by
      ext p
      simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq]
      constructor
      · rintro h ⟨n, w, hw, hv⟩
        exact h w hw (mem_interior_iff_exists_nat_closedBall.2 ⟨n, hv⟩)
      · intro h w hw hint
        obtain ⟨n, hv⟩ := mem_interior_iff_exists_nat_closedBall.1 hint
        exact h ⟨n, w, hw, hv⟩
    rw [this]
    refine (MeasurableSet.iUnion fun n => IsClosed.measurableSet ?_).compl
    refine isClosed_setOf_exists_mem_of_isCompact (isCompact_sphere 0 1) ?_
    have : {x : (C(ℝ, ℂ) × C(ℂ, ℂ)) × ℂ | ∀ v ∈ closedBall (0 : ℂ) (1 / ((n : ℝ) + 1)),
        x.1.2 x.2 + v ∈ x.1.1 '' Icc a b} = ⋂ v ∈ closedBall (0 : ℂ) (1 / ((n : ℝ) + 1)),
        {x : (C(ℝ, ℂ) × C(ℂ, ℂ)) × ℂ | x.1.2 x.2 + v ∈ x.1.1 '' Icc a b} := by
      ext x
      simp only [mem_iInter, mem_ofPred_eq]
    rw [this]
    exact isClosed_biInter fun v _ => (isClosed_setOf_mem_image_Icc_prod a b).preimage
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).add continuous_const))
  have m6 : IsClosed {p : C(ℝ, ℂ) × C(ℂ, ℂ) | ∀ w, p.2 w = p.2 (discRetract w)} := by
    have : {p : C(ℝ, ℂ) × C(ℂ, ℂ) | ∀ w, p.2 w = p.2 (discRetract w)} =
        ⋂ w, {p : C(ℝ, ℂ) × C(ℂ, ℂ) | p.2 w = p.2 (discRetract w)} := by
      ext p
      simp only [mem_iInter, mem_ofPred_eq]
    rw [this]
    exact isClosed_iInter fun w => isClosed_eq ((continuous_eval_const w).comp continuous_snd)
      ((continuous_eval_const (discRetract w)).comp continuous_snd)
  rw [heq]
  exact ((((measurable_snd measurableSet_setOf_injOn_closedBall).inter
    (measurable_snd isClosed_setOf_differentiableOn_ball_deriv.measurableSet)).inter
    (isClosed_eq ((continuous_eval_const 0).comp continuous_snd)
      ((continuous_eval_const u).comp continuous_fst)).measurableSet).inter m4.measurableSet).inter m5 |>.inter
    m6.measurableSet

/-- Uniqueness: the graph is the graph of a function. -/
theorem eq_of_mem_windowDiscMapGraph {a u b : ℝ} {η : C(ℝ, ℂ)} {φ₁ φ₂ : C(ℂ, ℂ)}
    (h₁ : (η, φ₁) ∈ windowDiscMapGraph a u b) (h₂ : (η, φ₂) ∈ windowDiscMapGraph a u b) : φ₁ = φ₂ := by
  obtain ⟨hN₁, hR₁⟩ := mem_windowDiscMapGraph.1 h₁
  obtain ⟨hN₂, hR₂⟩ := mem_windowDiscMapGraph.1 h₂
  have hE := hN₁.eqOn hN₂
  ext w
  rw [hR₁ w, hR₂ w]
  exact hE (discRetract_mem w)

/-- A window with an inverse chart has its normalized conformal map in the graph. -/
theorem exists_mem_windowDiscMapGraph {a u b : ℝ} {η : C(ℝ, ℂ)} {ψ : C(ℂ, ℂ)}
    (hψ : IsInverseChart (windowDomain η a u b) (η u) ψ) : ∃ φ, (η, φ) ∈ windowDiscMapGraph a u b := by
  obtain ⟨R, hR⟩ := exists_nat_windowDomain_subset_ball η a u b
  obtain ⟨φ, hφ⟩ := exists_isNormalizedDiscMap_of_isInverseChart hψ (isOpen_windowDomain η a u b)
    (isBounded_ball.subset hR)
  refine ⟨φ.comp discRetract, mem_windowDiscMapGraph.2 ⟨hφ.congr fun w hw => ?_, fun w => ?_⟩⟩
  · show φ w = φ (discRetract w)
    rw [discRetract_of_mem hw]
  · show φ (discRetract w) = φ (discRetract (discRetract w))
    rw [discRetract_of_mem (discRetract_mem w)]

/-! ### Borel choice along a Borel graph -/

open Classical in
/-- **Borel choice along a Borel graph** (Lusin–Souslin). If `G ⊆ X × Y` is a Borel subset of a product of standard
Borel spaces which is the graph of a partial function, then the choice `x ↦ the y with (x, y) ∈ G` (and `y₀` off the
projection of `G`) is measurable. -/
theorem measurable_graphChoice {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]
    [StandardBorelSpace Y] {G : Set (X × Y)} (hG : MeasurableSet G)
    (huniq : ∀ x y y', (x, y) ∈ G → (x, y') ∈ G → y = y') (y₀ : Y) :
    Measurable fun x => if h : ∃ y, (x, y) ∈ G then h.choose else y₀ := by
  have hinj : InjOn Prod.fst G := by
    rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' (h : x = x')
    subst h
    rw [huniq x y y' hp hp']
  have himg : ∀ T : Set (X × Y), MeasurableSet T → T ⊆ G → MeasurableSet (Prod.fst '' T) := fun T hT hTG =>
    hT.image_of_measurable_injOn measurable_fst (hinj.mono hTG)
  intro B hB
  have hpre : (fun x => if h : ∃ y, (x, y) ∈ G then h.choose else y₀) ⁻¹' B =
      Prod.fst '' (G ∩ (univ ×ˢ B)) ∪ ((Prod.fst '' G)ᶜ ∩ {_x | y₀ ∈ B}) := by
    ext x
    rw [mem_preimage]
    by_cases h : ∃ y, (x, y) ∈ G
    · rw [dite_eq_left h]
      constructor
      · intro hB'
        exact Or.inl ⟨(x, h.choose), ⟨h.choose_spec, mem_univ _, hB'⟩, rfl⟩
      · rintro (⟨⟨x', y⟩, ⟨hG', -, hyB⟩, rfl⟩ | ⟨hx, -⟩)
        · rw [huniq x' _ y h.choose_spec hG']
          exact hyB
        · exact (hx ⟨(x, h.choose), h.choose_spec, rfl⟩).elim
    · rw [dite_eq_right h]
      constructor
      · intro hB'
        refine Or.inr ⟨?_, hB'⟩
        rintro ⟨⟨x', y⟩, hG', rfl⟩
        exact h ⟨y, hG'⟩
      · rintro (⟨⟨x', y⟩, ⟨hG', -⟩, rfl⟩ | ⟨-, hB'⟩)
        · exact (h ⟨y, hG'⟩).elim
        · exact hB'
  rw [hpre]
  exact (himg _ (hG.inter (MeasurableSet.univ.prod hB)) inter_subset_left).union
    ((himg G hG subset_rfl).compl.inter (MeasurableSet.const _))

/-! ### The normalized conformal map of a window -/

open Classical in
/-- **The normalized conformal map of the window `(a, u, b)` of the curve `η`**: the conformal map `φ` of the closed
disc onto the closure of `windowDomain η a u b` with `φ 0 = η(u)` and `φ'(0) > 0`, constant along the rays outside the
closed disc (and `0` when the window has no inverse chart). -/
noncomputable def windowDiscMap (a u b : ℝ) (η : C(ℝ, ℂ)) : C(ℂ, ℂ) :=
  if h : ∃ φ, (η, φ) ∈ windowDiscMapGraph a u b then h.choose else 0

/-- **The normalized conformal map of a window is a Borel function of the curve.** -/
theorem measurable_windowDiscMap (a u b : ℝ) : Measurable (windowDiscMap a u b) := by
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have : PolishSpace C(ℂ, ℂ) := LatticeProb.polishSpace_continuousMap ℂ ℂ
  exact measurable_graphChoice (measurableSet_windowDiscMapGraph a u b)
    (fun _ _ _ h₁ h₂ => eq_of_mem_windowDiscMapGraph h₁ h₂) 0

theorem windowDiscMap_mem {a u b : ℝ} {η : C(ℝ, ℂ)} (h : ∃ φ, (η, φ) ∈ windowDiscMapGraph a u b) :
    (η, windowDiscMap a u b η) ∈ windowDiscMapGraph a u b := by
  unfold windowDiscMap
  rw [dite_eq_left h]
  exact h.choose_spec

/-- If the window has an inverse chart at `η(u)`, then `windowDiscMap a u b η` is its normalized conformal map. -/
theorem isNormalizedDiscMap_windowDiscMap {a u b : ℝ} {η : C(ℝ, ℂ)} {ψ : C(ℂ, ℂ)}
    (hψ : IsInverseChart (windowDomain η a u b) (η u) ψ) :
    IsNormalizedDiscMap (windowDomain η a u b) (η u) (windowDiscMap a u b η) :=
  (mem_windowDiscMapGraph.1 (windowDiscMap_mem (exists_mem_windowDiscMapGraph hψ))).1

end MatedCRT
