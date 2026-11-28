import MatedCRT.FirstPass.Derived.MatingOfTreesCellSideIdentityProof
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.TripleCoverCover

/-!
# A countable compact cover of the triple points of a Peanosphere curve

Let `(L, R)` be the pair of boundary-length coordinates of a Peanosphere curve `η`. Suppose that no
time is a minimum of `L` on a left neighbourhood and of `R` on a right neighbourhood, nor the
reverse, and that neither `L` nor `R` is monotone on any interval. Then the points visited at least
three times by `η` are covered by `η`-images of countably many compact sets of times with empty
interior, on each of which `η` is injective.

The fibres of `η` are the classes of the relation joining two times through a minimum of `L` or of
`R` (`Jrel`). A class with three times either has a middle time, which is a local minimum of one
coordinate and is isolated among such times, or contains the common left end (or right end) of a
nonsingleton class of each coordinate; near such a time the sets `Eset` of `TripleCoverSets`
(or their time reversals) apply.
-/

set_option autoImplicit false

open Set
open MatedCRTHarmonic.MatedCRT (Path2)
open MatedCRTHarmonic.RouteM (Peanosphere directRel)

namespace MatedCRT.PeanosphereTriplePoints

theorem sim_of_directRel {X : ℝ → ℝ} {a b : ℝ} (h : directRel X a b) : Sim X a b := by
  refine ⟨h.2.1, fun u hu => ?_⟩
  rw [uIcc_of_le h.1.le] at hu
  rcases hu.1.eq_or_lt with rfl | hlt
  · exact le_rfl
  · rcases hu.2.eq_or_lt with rfl | hlt'
    · exact h.2.1.le
    · exact (h.2.2 u ⟨hlt, hlt'⟩).le

theorem eqvGen_directRel_of_sim {X : ℝ → ℝ} (hX : Coord X) {a b : ℝ} (hab : a < b)
    (h : Sim X a b) : Relation.EqvGen (directRel X) a b := by
  have hle : ∀ u ∈ Ioo a b, X a ≤ X u := fun u hu =>
    h.2 u (by rw [uIcc_of_le hab.le]; exact ⟨hu.1.le, hu.2.le⟩)
  by_cases hex : ∃ u ∈ Ioo a b, X u = X a
  · obtain ⟨u, hu, hXu⟩ := hex
    have hloc : ∀ v ∈ Ioo a b, X v = X a → IsLocalMin X v := by
      intro v hv hXv
      refine isLocalMin_of_Ioo hv.1 hv.2 fun x hx => ?_
      rw [hXv]
      exact h.2 x (by rw [uIcc_of_le hab.le]; exact ⟨hx.1.le, hx.2.le⟩)
    have d1 : directRel X a u := by
      refine ⟨hu.1, hXu.symm, fun v hv => ?_⟩
      have hv' : v ∈ Ioo a b := ⟨hv.1, hv.2.trans hu.2⟩
      rcases (hle v hv').eq_or_lt with heq | hlt
      · exact (hX.locMin_ne v u (ne_of_lt hv.2) (hloc v hv' heq.symm) (hloc u hu hXu)
          (heq.symm.trans hXu.symm)).elim
      · exact hlt
    have d2 : directRel X u b := by
      refine ⟨hu.2, hXu.trans h.1, fun v hv => ?_⟩
      have hv' : v ∈ Ioo a b := ⟨hu.1.trans hv.1, hv.2⟩
      rcases (hle v hv').eq_or_lt with heq | hlt
      · exact (hX.locMin_ne u v (ne_of_lt hv.1) (hloc u hu hXu) (hloc v hv' heq.symm)
          (hXu.trans heq)).elim
      · rw [hXu]
        exact hlt
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ d1) (Relation.EqvGen.rel _ _ d2)
  · refine Relation.EqvGen.rel _ _ ⟨hab, h.1, fun u hu => ?_⟩
    exact lt_of_le_of_ne (hle u hu) (fun e => hex ⟨u, hu, e.symm⟩)

theorem eta_eq_of_sim {X : ℝ → ℝ} (hX : Coord X) {η : ℝ → ℂ}
    (hm : ∀ a b, directRel X a b → η a = η b) {a b : ℝ} (h : Sim X a b) : η a = η b := by
  have key : ∀ a b, Relation.EqvGen (directRel X) a b → η a = η b := by
    intro a b hab
    induction hab with
    | rel a b h => exact hm a b h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact key a b (eqvGen_directRel_of_sim hX hab h)
  · rfl
  · exact (key b a (eqvGen_directRel_of_sim hX hba (sim_symm h))).symm

theorem coord_fst {p : Path2} {η : ℝ → ℂ} (hη : Peanosphere p η) : Coord (fun t => (p t).1) where
  cont := continuous_fst.comp p.continuous
  below_right M T := (hη.liminf_L M T).1
  below_left M T := by
    obtain ⟨t, ht, h⟩ := (hη.liminf_L M (-T)).2
    exact ⟨t, by linarith, h⟩
  locMin_ne a b hab ha hb := by
    have := hη.locMinDistinct 0 a b hab (by simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using ha)
      (by simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using hb)
    simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using this

theorem coord_snd {p : Path2} {η : ℝ → ℂ} (hη : Peanosphere p η) : Coord (fun t => (p t).2) where
  cont := continuous_snd.comp p.continuous
  below_right M T := (hη.liminf_R M T).1
  below_left M T := by
    obtain ⟨t, ht, h⟩ := (hη.liminf_R M (-T)).2
    exact ⟨t, by linarith, h⟩
  locMin_ne a b hab ha hb := by
    have := hη.locMinDistinct 1 a b hab (by simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using ha)
      (by simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using hb)
    simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using this

theorem setup_of_peanosphere {p : Path2} {η : ℝ → ℂ} (hη : Peanosphere p η)
    (hLR : NoOppositeSideMin (fun t => (p t).1) (fun t => (p t).2))
    (hRL : NoOppositeSideMin (fun t => (p t).2) (fun t => (p t).1)) :
    Setup (fun t => (p t).1) (fun t => (p t).2) η where
  coordX := coord_fst hη
  coordY := coord_snd hη
  noXY := hLR
  noYX := hRL
  fib s t := by
    constructor
    · intro h
      have key : ∀ a b : ℝ,
          (directRel (fun u => (p u).1) a b ∨ directRel (fun u => (p u).2) a b) →
          (Sim (fun u => (p u).1) a b ∨ Sim (fun u => (p u).2) a b) := fun a b hab =>
        hab.imp sim_of_directRel sim_of_directRel
      exact Relation.EqvGen.mono key _ _ (hη.onlyMerge s t h)
    · intro h
      have key : ∀ a b, Jrel (fun t => (p t).1) (fun t => (p t).2) a b → η a = η b := by
        intro a b hab
        induction hab with
        | rel a b h =>
          rcases h with h | h
          · exact eta_eq_of_sim (coord_fst hη) (fun a b hd => hη.merge a b (Or.inl hd)) h
          · exact eta_eq_of_sim (coord_snd hη) (fun a b hd => hη.merge a b (Or.inr hd)) h
        | refl => rfl
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
      exact key s t h

/-- The points visited at least three times by a Peanosphere curve are covered by the images of
countably many compact sets of times with empty interior on each of which the curve is injective. -/
theorem exists_countable_compact_cover_curveTriplePoints {p : Path2} {η : ℝ → ℂ}
    (hη : Peanosphere p η)
    (hLR : NoOppositeSideMin (fun t => (p t).1) (fun t => (p t).2))
    (hRL : NoOppositeSideMin (fun t => (p t).2) (fun t => (p t).1))
    (hL : NowhereMonotone (fun t => (p t).1)) (hR : NowhereMonotone (fun t => (p t).2)) :
    ∃ S : Set (Set ℝ), S.Countable ∧ (∀ E ∈ S, IsCompact E ∧ interior E = ∅ ∧ Set.InjOn η E) ∧
      MatedCRT.curveTriplePoints η ⊆ ⋃ E ∈ S, η '' E := by
  have hS := setup_of_peanosphere hη hLR hRL
  refine ⟨SetS _ _, SetS_countable hS.coordX hS.coordY, SetS_props hS hL hR, ?_⟩
  rintro z ⟨t1, t2, t3, h12, h23, e1, e2, e3⟩
  obtain ⟨E, hE, hz⟩ := SetS_cover hS h12 h23 (e1.trans e2.symm) (e2.trans e3.symm)
  rw [e1] at hz
  exact mem_iUnion₂.2 ⟨E, hE, hz⟩

end MatedCRT.PeanosphereTriplePoints
