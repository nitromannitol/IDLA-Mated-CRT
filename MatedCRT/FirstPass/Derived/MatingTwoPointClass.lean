import MatedCRT.FirstPass.Derived.MatingRelation
import LatticeProb.Order.EqvGenTwoPointClass
import LatticeProb.Analysis.StraddlingLevelPairs

/-!
# Two-point mating classes and straddling pairs

Deterministic steps of the one-sided mating rigidity argument for the mating relation `matingRel b` of a
boundary-length pair `b = (L, R)` (Duplantier-Miller-Sheffield (2014), Section 8.1).

For a continuous path `X`, a time `v` and a level `ℓ < X v` that `X` reaches on both sides of `v`, the *straddling
pair* of `X` at `v` at level `ℓ` is `(s_ℓ, t_ℓ)`, with `s_ℓ` the last time `≤ v` and `t_ℓ` the first time `≥ v` at
which `X ≤ ℓ` (`LatticeProb.lastBelow`, `LatticeProb.firstBelow`). The straddling pairs at `v` form the chain of
excursion intervals of `X` above its levels that contain `v`.

* `directRel_of_matingRel_of_class_subset_pair`: if `s < t` are related by the mating relation of `b`, the mating
  relation of `b` is contained in that of `b'`, and the `b'`-class of `s` is contained in `{s, t}`, then `(s, t)` is
  a direct `L'`- or `R'`-identification of `b'`.
* `directRel_straddle`: a straddling pair of a continuous path is a direct identification of that path.
* `straddle_eq_of_directRel`: conversely, a direct identification `(a, c)` of `X` with `a < v < c` is the straddling
  pair of `X` at `v` at level `X a`, and this level lies below `X v`.
* `matingRel_of_directRel_coord`: direct identifications of either coordinate of `b` are related by `matingRel b`.
* `directRel_straddle_of_class_subset_pair`: a straddling pair of a coordinate of `b` whose `b'`-class has at most
  the two points of the pair is a direct `L'`- or `R'`-identification of `b'`.
-/

namespace MatedCRT

open Set MatedCRTHarmonic.MatedCRT

private theorem continuous_coord (i : Fin 2) (b : Path2) : Continuous fun u : ℝ => lrCoord i u b := by
  by_cases hi : i = 0
  · simp only [lrCoord, hi, ↓reduceIte]
    exact b.continuous.fst
  · simp only [lrCoord, hi, ↓reduceIte]
    exact b.continuous.snd

/-- A direct identification of either of two paths is a strictly ordered pair of times. -/
theorem lt_of_directRel_or {X Y : ℝ → ℝ} {s t : ℝ} (h : DirectRel X s t ∨ DirectRel Y s t) : s < t :=
  h.elim (fun h => h.1) (fun h => h.1)

/-- **Two-point classes are direct identifications.** If `s < t` are related by the mating relation of `b`, the
mating relation of `b` is contained in that of `b'`, and the `b'`-class of `s` is contained in `{s, t}`, then
`(s, t)` is a direct `L'`- or `R'`-identification of `b' = (L', R')`: an `EqvGen` chain from `s` to `t` stays inside
the class of `s`. -/
theorem directRel_of_matingRel_of_class_subset_pair {b b' : Path2} {s t : ℝ} (hlt : s < t)
    (hst : matingRel b s t) (hle : ∀ s t : ℝ, matingRel b s t → matingRel b' s t)
    (hcls : ∀ u, matingRel b' s u → u = s ∨ u = t) :
    DirectRel (fun u => lrCoord 0 u b') s t ∨ DirectRel (fun u => lrCoord 1 u b') s t :=
  LatticeProb.Relation.rel_of_eqvGen_of_class_subset_pair (fun _ _ h => lt_of_directRel_or h) hlt
    (hle s t hst) hcls

/-- **Straddling pairs are direct identifications.** For a continuous path `X`, a time `v` and a level `ℓ < X v`
reached by `X` before and after `v`, the straddling pair `(s_ℓ, t_ℓ)` is a direct `X`-identification. -/
theorem directRel_straddle {X : ℝ → ℝ} (hX : Continuous X) {v l : ℝ} (hl : l < X v)
    (ha : ∃ a ≤ v, X a ≤ l) (hb : ∃ c, v ≤ c ∧ X c ≤ l) :
    DirectRel X (LatticeProb.lastBelow X v l) (LatticeProb.firstBelow X v l) :=
  LatticeProb.straddle_pair hX hl ha hb

/-- The straddling pair at `v` contains `v` in its interior. -/
theorem lastBelow_lt_lt_firstBelow {X : ℝ → ℝ} (hX : Continuous X) {v l : ℝ} (hl : l < X v)
    (ha : ∃ a ≤ v, X a ≤ l) (hb : ∃ c, v ≤ c ∧ X c ≤ l) :
    LatticeProb.lastBelow X v l < v ∧ v < LatticeProb.firstBelow X v l :=
  ⟨LatticeProb.lastBelow_lt hX hl ha, LatticeProb.lt_firstBelow hX hl hb⟩

/-- **Direct identifications straddling `v` are straddling pairs.** A direct `X`-identification `(a, c)` with
`a < v < c` is the straddling pair of `X` at `v` at level `X a`, and `X a < X v`. -/
theorem straddle_eq_of_directRel {X : ℝ → ℝ} {a c v : ℝ} (h : DirectRel X a c) (hav : a < v) (hvc : v < c) :
    X a < X v ∧ LatticeProb.lastBelow X v (X a) = a ∧ LatticeProb.firstBelow X v (X a) = c :=
  ⟨h.2.2 v ⟨hav, hvc⟩, LatticeProb.lastBelow_eq_and_firstBelow_eq hav hvc h.2.1 h.2.2⟩

/-- A direct identification of a coordinate of `b` is related by the mating relation of `b`. -/
theorem matingRel_of_directRel_coord {b : Path2} {i : Fin 2} {s t : ℝ}
    (h : DirectRel (fun u => lrCoord i u b) s t) : matingRel b s t := by
  refine Relation.EqvGen.rel _ _ ?_
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · exact Or.inl h
  · exact Or.inr h

/-- **Generic chain pairs are direct pairs of the coarser pair.** Let the mating relation of `b` be contained in
that of `b'`, let `X = lrCoord i · b` be a coordinate of `b`, and let `(s_ℓ, t_ℓ)` be the straddling pair of `X` at
`v` at a level `ℓ < X v` reached on both sides of `v`. If the `b'`-class of `s_ℓ` is contained in `{s_ℓ, t_ℓ}`, then
`(s_ℓ, t_ℓ)` is a direct `L'`- or `R'`-identification of `b'`. -/
theorem directRel_straddle_of_class_subset_pair {b b' : Path2} (i : Fin 2)
    (hle : ∀ s t : ℝ, matingRel b s t → matingRel b' s t) {v l : ℝ} (hl : l < lrCoord i v b)
    (ha : ∃ a ≤ v, lrCoord i a b ≤ l) (hb : ∃ c, v ≤ c ∧ lrCoord i c b ≤ l)
    (hcls : ∀ u, matingRel b' (LatticeProb.lastBelow (fun u => lrCoord i u b) v l) u →
      u = LatticeProb.lastBelow (fun u => lrCoord i u b) v l ∨
        u = LatticeProb.firstBelow (fun u => lrCoord i u b) v l) :
    DirectRel (fun u => lrCoord 0 u b') (LatticeProb.lastBelow (fun u => lrCoord i u b) v l)
        (LatticeProb.firstBelow (fun u => lrCoord i u b) v l) ∨
      DirectRel (fun u => lrCoord 1 u b') (LatticeProb.lastBelow (fun u => lrCoord i u b) v l)
        (LatticeProb.firstBelow (fun u => lrCoord i u b) v l) := by
  have h := directRel_straddle (continuous_coord i b) hl ha hb
  exact directRel_of_matingRel_of_class_subset_pair h.1 (matingRel_of_directRel_coord h) hle hcls

end MatedCRT
