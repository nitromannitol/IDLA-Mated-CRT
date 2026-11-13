import MatedCRT.FirstPass.Derived.MatingTwoPointClass

/-!
# Triple points of the mating relation and straddling pairs

Deterministic step of the one-sided mating rigidity argument for the mating relation `matingRel b` of a
boundary-length pair `b = (L, R)` (Duplantier-Miller-Sheffield (2014), Section 8.1).

The *triple points* of `matingRel b` are the times whose class contains at least two further times. Off the triple
points of `b'`, every class of `matingRel b'` that contains a pair `s ≠ t` is exactly `{s, t}`. Hence, when the
mating relation of `b` is contained in that of `b'`, every straddling pair of a coordinate of `b` whose left time is
not a triple point of `b'` is a direct identification (a contour pair) of a coordinate of `b'`.

* `matingTriplePoints`: the set of triple points of `matingRel b`.
* `eq_or_eq_of_not_mem_matingTriplePoints`: off the triple points, the class of `s` is contained in `{s, t}` for every
  `t ≠ s` related to `s`.
* `directRel_straddle_of_not_mem_matingTriplePoints`: a straddling pair of a coordinate of `b` whose left time is not
  a triple point of `b'` is a direct `L'`- or `R'`-identification of `b'`, when `matingRel b ≤ matingRel b'`.
* `forall_directRel_straddle_of_not_mem_matingTriplePoints`: the same for all times and levels, given that the
  coordinate of `b` takes values below every level before and after every time.
-/

set_option autoImplicit false

namespace MatedCRT

open Set MatedCRTHarmonic.MatedCRT

private theorem continuous_coord_path (i : Fin 2) (b : Path2) : Continuous fun u : ℝ => lrCoord i u b := by
  by_cases hi : i = 0
  · simp only [lrCoord, hi, ↓reduceIte]
    exact b.continuous.fst
  · simp only [lrCoord, hi, ↓reduceIte]
    exact b.continuous.snd

/-- The **triple points** of the mating relation of `b`: the times `s` related by `matingRel b` to two distinct times
`u, v`, both different from `s`. -/
def matingTriplePoints (b : Path2) : Set ℝ :=
  {s | ∃ u v, u ≠ s ∧ v ≠ s ∧ u ≠ v ∧ matingRel b s u ∧ matingRel b s v}

/-- **Classes off the triple points have at most two elements.** If `s` is not a triple point of `matingRel b` and
`t ≠ s` is related to `s`, then every time related to `s` is `s` or `t`. -/
theorem eq_or_eq_of_not_mem_matingTriplePoints {b : Path2} {s t : ℝ} (hs : s ∉ matingTriplePoints b)
    (hts : t ≠ s) (hst : matingRel b s t) : ∀ u, matingRel b s u → u = s ∨ u = t := by
  intro u hu
  by_contra h
  obtain ⟨h1, h2⟩ := not_or.1 h
  exact hs ⟨u, t, h1, hts, h2, hu, hst⟩

/-- **Straddling pairs off the triple points are direct identifications.** If the mating relation of `b` is contained
in that of `b'`, then a straddling pair `(s_ℓ, t_ℓ)` of a coordinate of `b` whose left time `s_ℓ` is not a triple
point of `matingRel b'` is a direct `L'`- or `R'`-identification of `b' = (L', R')`. -/
theorem directRel_straddle_of_not_mem_matingTriplePoints {b b' : Path2} (i : Fin 2)
    (hle : ∀ s t : ℝ, matingRel b s t → matingRel b' s t) {v l : ℝ} (hl : l < lrCoord i v b)
    (ha : ∃ a ≤ v, lrCoord i a b ≤ l) (hb : ∃ c, v ≤ c ∧ lrCoord i c b ≤ l)
    (hZ : LatticeProb.lastBelow (fun u => lrCoord i u b) v l ∉ matingTriplePoints b') :
    DirectRel (fun u => lrCoord 0 u b') (LatticeProb.lastBelow (fun u => lrCoord i u b) v l)
        (LatticeProb.firstBelow (fun u => lrCoord i u b) v l) ∨
      DirectRel (fun u => lrCoord 1 u b') (LatticeProb.lastBelow (fun u => lrCoord i u b) v l)
        (LatticeProb.firstBelow (fun u => lrCoord i u b) v l) := by
  have h := directRel_straddle (continuous_coord_path i b) hl ha hb
  exact directRel_straddle_of_class_subset_pair i hle hl ha hb
    (eq_or_eq_of_not_mem_matingTriplePoints hZ h.1.ne' (hle _ _ (matingRel_of_directRel_coord h)))

/-- **All straddling pairs off the triple points.** If the mating relation of `b` is contained in that of `b'` and the
coordinate `i` of `b` takes values below every level before and after every time, then for every time `w` and level
`ℓ < X w` (`X` the coordinate `i` of `b`) whose straddling pair has its left time off the triple points of
`matingRel b'`, that pair is a direct `L'`- or `R'`-identification of `b'`. -/
theorem forall_directRel_straddle_of_not_mem_matingTriplePoints {b b' : Path2} (i : Fin 2)
    (hle : ∀ s t : ℝ, matingRel b s t → matingRel b' s t)
    (hlow : ∀ w l, (∃ a ≤ w, lrCoord i a b ≤ l) ∧ ∃ c, w ≤ c ∧ lrCoord i c b ≤ l) :
    ∀ w l, LatticeProb.lastBelow (fun u => lrCoord i u b) w l ∉ matingTriplePoints b' → l < lrCoord i w b →
      DirectRel (fun u => lrCoord 0 u b') (LatticeProb.lastBelow (fun u => lrCoord i u b) w l)
          (LatticeProb.firstBelow (fun u => lrCoord i u b) w l) ∨
        DirectRel (fun u => lrCoord 1 u b') (LatticeProb.lastBelow (fun u => lrCoord i u b) w l)
          (LatticeProb.firstBelow (fun u => lrCoord i u b) w l) :=
  fun w l hZ hl => directRel_straddle_of_not_mem_matingTriplePoints i hle hl (hlow w l).1 (hlow w l).2 hZ

end MatedCRT
