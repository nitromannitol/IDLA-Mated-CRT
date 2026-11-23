import MatedCRT.FirstPass.Derived.HN9OfWindowCharts
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.Complex
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Complex.Tietze

/-!
# Inverse charts of bounded domains with Jordan frontier

Let `U ⊆ ℂ` be a bounded connected open set whose frontier is a Jordan curve (`IsJordanCurve`, the image of the unit
circle under a map continuous and injective on it). By the Jordan curve theorem
(`jordan_curve_components_complex`), `U` is the bounded component of the complement of its frontier, and the
complement of `U` is the closure of the unbounded component, which is connected and unbounded
(`forall_not_isBounded_connectedComponentIn_compl_of_isJordanCurve`). Carathéodory's theorem for Jordan domains
(Pommerenke (1992), Theorem 2.6; `jm_jordan_closedDisc_extension'`) gives a map `φ`, continuous and injective on the
closed unit disc and holomorphic on the open disc, with `φ(0) = z` after translation, `φ(𝔻) = U` and
`φ(∂𝔻) = ∂U`. Its inverse on the closure of `U` is continuous (a continuous bijection of a compact space onto a
Hausdorff space), holomorphic on `U` (the inverse of a univalent map, `differentiableOn_univalentOPH_symm`), and
extends continuously to `ℂ` (Tietze). This is an inverse chart (`exists_isInverseChart_of_isJordanCurve`).

This is the step of Berestycki–Gwynne (2020), proof of Lemma 7.21: "`∂U` is a Jordan curve so the desired extension
of `φ` follows from [Pom92, Theorem 2.6]". That the frontier of the window domain is a Jordan curve is the SLE
input ([MS17, Section 1.2.3]).
-/

set_option autoImplicit false

open Set Metric Topology Filter Bornology

namespace MatedCRT

/-- **A bounded domain with Jordan frontier is the inner domain of its frontier.** If `U` is a nonempty bounded
preconnected open set whose frontier is a Jordan curve, then every connected component of the complement of `U`
is unbounded (the complement is the closure of the unbounded component of the complement of the frontier). -/
theorem forall_not_isBounded_connectedComponentIn_compl_of_isJordanCurve {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUb : IsBounded U)
    (hJ : LQGMetric.JordanMap.IsJordanCurve (frontier U)) :
    ∀ a ∉ U, ¬ IsBounded (connectedComponentIn Uᶜ a) := by
  obtain ⟨x₁, -, x₀, -, -, hO, -, hunion, -, hfO⟩ :=
    MatedCRTHarmonic.Planar.Jordan.jordan_curve_components_complex hJ
  set J := frontier U
  set O := connectedComponentIn Jᶜ x₀
  obtain ⟨p, hp⟩ := hUne
  have hUJ : U ⊆ Jᶜ := fun x hx hxJ =>
    (hUo.inter_frontier_eq.subset ⟨hx, hxJ⟩ : x ∈ (∅ : Set ℂ))
  have hpJ : p ∈ Jᶜ := hUJ hp
  have hUC : U = connectedComponentIn Jᶜ p := by
    refine le_antisymm (hUc.subset_connectedComponentIn hp hUJ) ?_
    have hsub : connectedComponentIn Jᶜ p ⊆ U ∪ (closure U)ᶜ := by
      intro x hx
      by_cases hxc : x ∈ closure U
      · left
        by_contra hxU
        have hxf : x ∈ frontier U := by
          rw [hUo.frontier_eq]
          exact ⟨hxc, hxU⟩
        exact (connectedComponentIn_subset _ _ hx) hxf
      · exact Or.inr hxc
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hUo isClosed_closure.isOpen_compl
      (disjoint_compl_right_iff_subset.2 subset_closure) hsub ⟨p, mem_connectedComponentIn hpJ, hp⟩
  have hpO : p ∉ O := by
    intro hpO
    have hCO : connectedComponentIn Jᶜ p = O := (connectedComponentIn_eq hpO).symm
    have hb := hUb
    rw [hUC, hCO] at hb
    exact hO hb
  have hp1 : p ∈ connectedComponentIn Jᶜ x₁ := by
    have hpu : p ∈ connectedComponentIn Jᶜ x₁ ∪ O := by
      rw [← hunion]
      exact hpJ
    rcases hpu with h | h
    · exact h
    · exact absurd h hpO
  have hcompl : Uᶜ = closure O := by
    rw [closure_eq_self_union_frontier, hfO]
    ext x
    constructor
    · intro hx
      by_cases hxJ : x ∈ J
      · exact Or.inr hxJ
      · left
        have hxu : x ∈ connectedComponentIn Jᶜ x₁ ∪ O := by
          rw [← hunion]
          exact hxJ
        rcases hxu with hx1 | hxO
        · exfalso
          have hC : connectedComponentIn Jᶜ p = connectedComponentIn Jᶜ x₁ :=
            (connectedComponentIn_eq hp1).symm
          have hxU : x ∈ U := by
            rw [hUC, hC]
            exact hx1
          exact hx hxU
        · exact hxO
    · rintro (hxO | hxJ) hxU
      · have hpx : connectedComponentIn Jᶜ p = O := by
          rw [hUC] at hxU
          rw [connectedComponentIn_eq hxU]
          exact (connectedComponentIn_eq hxO).symm
        exact hpO (by rw [← hpx]; exact mem_connectedComponentIn hpJ)
      · exact hUJ hxU hxJ
  have hconn : IsPreconnected Uᶜ := by
    rw [hcompl]
    exact isPreconnected_connectedComponentIn.closure
  intro a ha hab
  rw [hconn.connectedComponentIn ha, hcompl] at hab
  exact hO (hab.subset subset_closure)

/-- **Inverse charts of bounded domains with Jordan frontier** (Pommerenke (1992), Theorem 2.6, through
`jm_jordan_closedDisc_extension'`, and Tietze's extension theorem). If `U` is a bounded preconnected open set with
`z ∈ U` whose frontier is a Jordan curve, then `U` has an inverse chart at `z`. -/
theorem exists_isInverseChart_of_isJordanCurve {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUb : IsBounded U) {z : ℂ} (hz : z ∈ U) (hJ : LQGMetric.JordanMap.IsJordanCurve (frontier U)) :
    ∃ ψ : C(ℂ, ℂ), IsInverseChart U z ψ := by
  let T : ℂ ≃ₜ ℂ := Homeomorph.addRight z
  have hT : ∀ w, T w = w + z := fun _ => rfl
  set V := T ⁻¹' U with hVdef
  have hVo : IsOpen V := hUo.preimage T.continuous
  have hVc : IsPreconnected V := T.isPreconnected_preimage.2 hUc
  have hV0 : (0 : ℂ) ∈ V := by
    show T 0 ∈ U
    rw [hT, zero_add]
    exact hz
  have hVb : IsBounded V := by
    obtain ⟨R, hR⟩ := hUb.subset_closedBall 0
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := R + ‖z‖)).subset fun w hw => ?_
    have hw' : w + z ∈ closedBall (0 : ℂ) R := hR hw
    rw [mem_closedBall_zero_iff] at hw' ⊢
    calc ‖w‖ = ‖(w + z) - z‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖w + z‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ R + ‖z‖ := by linarith
  have hfV : frontier V = T ⁻¹' frontier U := (T.preimage_frontier U).symm
  have hJV : LQGMetric.JordanMap.IsJordanCurve (frontier V) := by
    obtain ⟨γ, hγc, hγi, hγ⟩ := hJ
    refine ⟨fun w => γ w - z, hγc.sub continuousOn_const,
      fun w hw w' hw' h => hγi hw hw' (sub_left_inj.1 h), ?_⟩
    rw [hfV, ← hγ]
    ext y
    simp only [mem_image, mem_preimage, hT]
    exact exists_congr fun w => and_congr_right fun _ => sub_eq_iff_eq_add
  have hcompV := forall_not_isBounded_connectedComponentIn_compl_of_isJordanCurve hVo hVc ⟨0, hV0⟩ hVb hJV
  obtain ⟨φ, hφc, hφi, hφd, hφ0, hφB, hφS⟩ :=
    LQGMetric.JordanMap.jm_jordan_closedDisc_extension' hVo hVc hV0 hVb hcompV hJV
  set Φ : ℂ → ℂ := fun w => φ w + z with hΦdef
  have himg : ∀ s : Set ℂ, Φ '' s = T '' (φ '' s) := fun s => by
    rw [image_image]
    rfl
  have hΦB : Φ '' ball 0 1 = U := by
    rw [himg, hφB, hVdef, image_preimage_eq U T.surjective]
  have hΦS : Φ '' sphere 0 1 = frontier U := by
    rw [himg, hφS, hfV, image_preimage_eq _ T.surjective]
  have hΦcl : Φ '' closedBall 0 1 = closure U := by
    rw [← ball_union_sphere, image_union, hΦB, hΦS, closure_eq_self_union_frontier]
  have hΦc : ContinuousOn Φ (closedBall 0 1) := hφc.add continuousOn_const
  have hΦi : InjOn Φ (closedBall 0 1) := fun w hw w' hw' h => hφi hw hw' (add_right_cancel h)
  have hbij : BijOn Φ (closedBall 0 1) (closure U) :=
    ⟨fun w hw => hΦcl ▸ mem_image_of_mem Φ hw, hΦi, by rw [← hΦcl]; exact surjOn_image Φ _⟩
  let e : closedBall (0 : ℂ) 1 ≃ closure U := hbij.equiv Φ
  have he : Continuous e := hΦc.domRestrict.subtype_mk _
  have : CompactSpace (closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  let h : closedBall (0 : ℂ) 1 ≃ₜ closure U := he.homeoOfEquivCompactToT2
  have hh : ∀ x, (h x : ℂ) = Φ x := fun _ => rfl
  let g : C(closure U, ℂ) := ⟨fun y => (h.symm y : ℂ), continuous_subtype_val.comp h.symm.continuous⟩
  obtain ⟨ψ, hψ⟩ := ContinuousMap.exists_restrict_eq isClosed_closure g
  have hψy : ∀ y (hy : y ∈ closure U), ψ y = (h.symm ⟨y, hy⟩ : ℂ) := fun y hy =>
    DFunLike.congr_fun hψ ⟨y, hy⟩
  have hΦψ : ∀ y ∈ closure U, Φ (ψ y) = y := fun y hy => by
    rw [hψy y hy, ← hh, h.apply_symm_apply]
  have hψΦ : ∀ w ∈ closedBall (0 : ℂ) 1, ψ (Φ w) = w := fun w hw => by
    have hmem : Φ w ∈ closure U := hbij.mapsTo hw
    rw [hψy _ hmem]
    have : (⟨Φ w, hmem⟩ : closure U) = h ⟨w, hw⟩ := rfl
    rw [this, h.symm_apply_apply]
  have hΦ0 : Φ 0 = z := by
    rw [hΦdef]
    simp only [hφ0, zero_add]
  let eU := QuantumZipper.CA.univalentOPH isOpen_ball hφd (hφi.mono ball_subset_closedBall)
  have heU : DifferentiableOn ℂ eU.symm (φ '' ball 0 1) :=
    QuantumZipper.CA.differentiableOn_univalentOPH_symm isOpen_ball hφd (hφi.mono ball_subset_closedBall)
  refine ⟨ψ, hz, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hΦ0]
    exact hψΦ 0 (mem_closedBall_self zero_le_one)
  · intro y hy y' hy' hyy
    rw [← hΦψ y hy, ← hΦψ y' hy', hyy]
  · have hmaps : MapsTo (fun y => y - z) U (φ '' ball 0 1) := fun y hy => by
      rw [hφB]
      show T (y - z) ∈ U
      rw [hT, sub_add_cancel]
      exact hy
    refine (heU.comp (differentiableOn_id.sub_const z) hmaps).congr fun y hy => ?_
    obtain ⟨w, hw, rfl⟩ := hΦB.symm ▸ hy
    rw [hψΦ w (ball_subset_closedBall hw)]
    show w = eU.symm (φ w + z - z)
    rw [add_sub_cancel_right]
    exact (QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball hφd
      (hφi.mono ball_subset_closedBall) hw).symm
  · ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w', hw', rfl⟩ := hΦB.symm ▸ hy
      rw [hψΦ w' (ball_subset_closedBall hw')]
      exact hw'
    · intro hw
      exact ⟨Φ w, hΦB ▸ mem_image_of_mem Φ hw, hψΦ w (ball_subset_closedBall hw)⟩
  · ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w', hw', rfl⟩ := hΦS.symm ▸ hy
      rw [hψΦ w' (sphere_subset_closedBall hw')]
      exact hw'
    · intro hw
      exact ⟨Φ w, hΦS ▸ mem_image_of_mem Φ hw, hψΦ w (sphere_subset_closedBall hw)⟩

/-- **Inverse charts of a window.** If `η(u)` lies in the interior of `η([a, b])` and the frontier of the window
domain (the component of that interior containing `η(u)`) is a Jordan curve, then the window domain has an inverse
chart at `η(u)`. -/
theorem exists_isInverseChart_windowDomain (η : C(ℝ, ℂ)) {a u b : ℝ} (hu : η u ∈ interior (η '' Icc a b))
    (hJ : LQGMetric.JordanMap.IsJordanCurve (frontier (windowDomain η a u b))) :
    ∃ ψ : C(ℂ, ℂ), IsInverseChart (windowDomain η a u b) (η u) ψ := by
  obtain ⟨R, hR⟩ := exists_nat_windowDomain_subset_ball η a u b
  exact exists_isInverseChart_of_isJordanCurve (isOpen_windowDomain η a u b) isPreconnected_connectedComponentIn
    (isBounded_ball.subset hR) (mem_connectedComponentIn hu) hJ

end MatedCRT
