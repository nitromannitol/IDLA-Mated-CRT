import MatedCRT.Proofs.Sec4.Prop42Closure.HalfBallPlateau

/-! # Deterministic scaling of the plateau values (closure of Proposition 4.2)

In particular the
paragraph "The random positive change of time preserves the set of plateau values ... Consequently `P(h_a) = a⁻¹ P(h)`"
(draft lines 252-256). With `R_Λ(t) = familyRadius (Λ t)` (`R_h` of draft line 232) this file proves the deterministic
content, with no field-law input:

* `familyRadius_image_mul_of_pos`: the spatial dilation `x ↦ b x` (`b > 0`) multiplies the radius by `b`.
* `familyRadius_monotoneOn_of_regularized`: the radius of a regularized cluster family is increasing on `(0, ∞)`.
  The hypotheses are the monotonicity and the boundedness (finite radius) of `SatisfiesHarmonicBallConditions`.
  Nonemptiness of the members is not needed: the radius of `∅` is `0`, and radii are nonnegative.
* `mem_plateauValues_iff_of_radius`: if `R_{Λ'}(t) = b R_Λ(c t)` for `t > 0`, with `b, c > 0` and `R_Λ` increasing on
  `(0, ∞)`, then `r ∈ P(Λ') ↔ b⁻¹ r ∈ P(Λ)`. The rational witnesses come from `exists_rat_pair_of_eq_endpoints`:
  a nondegenerate interval of constancy of a monotone function contains two rational times. The factor `c` may be any
  positive real: the lemma is pathwise, so `c` may depend on the sample (the paper's `c = e^{γ c_a}` is random).
* `plateauValues_comp_mul` (`b = 1`) and `plateauValues_eq_image_of_radius` (`P(Λ') = b • P(Λ)`; for `b = a⁻¹` this is
  `P(h_a) = a⁻¹ P(h)`, draft line 256).
* `plateau_prob_scale_of_pathwise`: the reduction of `PlateauScaleInvarianceStep` (`HalfBallPlateau.lean`) to two inputs
  that are NOT proved here: the law identity `hlaw` and the pathwise identity `hpath`.

Uses of the cited regularized family: `IsRegularizedClusterFamily` (`HarmonicBalls/Draft/Section5.lean:88`), through
`SatisfiesHarmonicBallConditions` (`HarmonicBalls/Draft/Section1.lean:58`, fields `monotoneOn`, `isBounded`). -/

namespace MatedCRT

open MeasureTheory Filter Set HarmonicBalls
open scoped Pointwise

/-- **Spatial dilation.** For `b > 0`, the dilation `x ↦ b x` of a set of `ℂ` multiplies its radius by `b`:
`sup {‖b x‖ : x ∈ Λ} = b · sup {‖x‖ : x ∈ Λ}`. No boundedness is needed (`Real.sSup_smul_of_nonneg`). -/
theorem familyRadius_image_mul_of_pos {b : ℝ} (hb : 0 < b) (Λ : Set ℂ) :
    familyRadius ((fun x : ℂ => (b : ℂ) * x) '' Λ) = b * familyRadius Λ := by
  have hnorm : (fun x : ℂ => ‖x‖) '' ((fun x : ℂ => (b : ℂ) * x) '' Λ) =
      (fun x : ℂ => b * ‖x‖) '' Λ := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    show ‖(b : ℂ) * x‖ = b * ‖x‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
  have hsmul : (fun x : ℂ => b * ‖x‖) '' Λ = b • ((fun x : ℂ => ‖x‖) '' Λ) := by
    rw [← Set.image_smul, Set.image_image]
    rfl
  unfold familyRadius
  rw [hnorm, hsmul, Real.sSup_smul_of_nonneg hb.le, smul_eq_mul]

/-- **Radius monotonicity under inclusion.** If `S ⊆ T` and `T` is bounded, then `sup ‖S‖ ≤ sup ‖T‖`. The set `S` may be
empty: its radius is `0 ≤ sup ‖T‖`. -/
theorem familyRadius_mono_of_subset {S T : Set ℂ} (hST : S ⊆ T) (hT : Bornology.IsBounded T) :
    familyRadius S ≤ familyRadius T := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hT
  have hbdd : BddAbove ((fun x : ℂ => ‖x‖) '' T) :=
    bddAbove_def.2 ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
  unfold familyRadius
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Set.image_empty, Real.sSup_empty]
    apply Real.sSup_nonneg
    rintro _ ⟨x, -, rfl⟩
    exact norm_nonneg x
  · exact csSup_le_csSup hbdd (hS.image _) (Set.image_mono hST)

/-- **Monotone radius.** If the family is increasing on `(0, ∞)` and its members are bounded there, then its radius
`R_Λ(t) = sup ‖Λ t‖` is increasing on `(0, ∞)` (draft line 232: `R_h` is increasing; finiteness is boundedness). -/
theorem familyRadius_monotoneOn {Λ : ℝ → Set ℂ} (hmono : MonotoneOn Λ (Set.Ioi 0))
    (hbdd : ∀ t : ℝ, 0 < t → Bornology.IsBounded (Λ t)) :
    MonotoneOn (fun t => familyRadius (Λ t)) (Set.Ioi 0) := by
  intro s hs t ht hst
  exact familyRadius_mono_of_subset (hmono hs ht hst : Λ s ⊆ Λ t) (hbdd t ht)

/-- **The radius of a regularized cluster family is increasing on `(0, ∞)`.** The cited family
`IsRegularizedClusterFamily` (the family of [HB] Theorem 5.5, `HarmonicBalls/Draft/Section5.lean:88`) satisfies
`SatisfiesHarmonicBallConditions`, whose fields `monotoneOn` (`Λ_t` increases in `t`) and `isBounded` (`Λ_t` is bounded,
for `t > 0`) are exactly what `sSup` needs. -/
theorem familyRadius_monotoneOn_of_regularized {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {z : ℂ}
    (h : IsRegularizedClusterFamily μ Λ z) : MonotoneOn (fun t => familyRadius (Λ t)) (Set.Ioi 0) := by
  obtain ⟨hHB, -⟩ := h
  exact familyRadius_monotoneOn hHB.monotoneOn hHB.isBounded

/-- Two rational times in any nondegenerate real interval (draft lines 237-242: a nondegenerate plateau interval still
contains two rational times). -/
theorem exists_two_rat_between {x y : ℝ} (h : x < y) :
    ∃ q₁ q₂ : ℚ, x < q₁ ∧ (q₁ : ℝ) < q₂ ∧ (q₂ : ℝ) < y := by
  obtain ⟨q₁, hx, hy⟩ := exists_rat_btwn h
  obtain ⟨q₂, hq, hy'⟩ := exists_rat_btwn hy
  exact ⟨q₁, q₂, hx, hq, hy'⟩

/-- **Sandwich.** A monotone function on `(0, ∞)` which takes the value `v` at `x` and at `y` takes `v` on `[x, y]`. -/
theorem eq_of_monotoneOn_of_eq_endpoints {R : ℝ → ℝ} (hR : MonotoneOn R (Set.Ioi 0)) {x y z v : ℝ}
    (hx : 0 < x) (hxz : x ≤ z) (hzy : z ≤ y) (hRx : R x = v) (hRy : R y = v) : R z = v := by
  have hz : 0 < z := lt_of_lt_of_le hx hxz
  have hy : 0 < y := lt_of_lt_of_le hz hzy
  apply le_antisymm
  · rw [← hRy]
    exact hR (Set.mem_Ioi.mpr hz) (Set.mem_Ioi.mpr hy) hzy
  · rw [← hRx]
    exact hR (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hz) hxz

/-- **Rational witnesses on a plateau interval** (draft lines 237-242). If the radius is increasing on `(0, ∞)` and
takes the value `v` at two points `0 < x < y`, then it takes `v` at two rational times `0 < q₁ < q₂`. -/
theorem exists_rat_pair_of_eq_endpoints {R : ℝ → ℝ} (hR : MonotoneOn R (Set.Ioi 0)) {x y v : ℝ}
    (hx : 0 < x) (hxy : x < y) (hRx : R x = v) (hRy : R y = v) :
    ∃ q₁ q₂ : ℚ, 0 < (q₁ : ℝ) ∧ (q₁ : ℝ) < q₂ ∧ R (q₁ : ℝ) = v ∧ R (q₂ : ℝ) = v := by
  obtain ⟨q₁, q₂, h₁, h₂, h₃⟩ := exists_two_rat_between hxy
  exact ⟨q₁, q₂, lt_trans hx h₁, h₂,
    eq_of_monotoneOn_of_eq_endpoints hR hx h₁.le (h₂.trans h₃).le hRx hRy,
    eq_of_monotoneOn_of_eq_endpoints hR hx (h₁.trans h₂).le h₃.le hRx hRy⟩

/-- The plateau set of `Λ`, unfolded (`plateauValues`, draft lines 237-242). -/
theorem mem_plateauValues_iff (Λ : ℝ → Set ℂ) (r : ℝ) :
    r ∈ plateauValues Λ ↔ 0 < r ∧ ∃ s t : ℚ, 0 < (s : ℝ) ∧ (s : ℝ) < t ∧
      familyRadius (Λ s) = r ∧ familyRadius (Λ t) = r :=
  Iff.rfl

/-- **Deterministic scaling of the plateau values** (draft lines 252-256: `Λ^{h_a}_t = a⁻¹ Λ^h_{e^{γ c_a} t}` gives
`P(h_a) = a⁻¹ P(h)`). Let `b, c > 0`, let `R_Λ` be increasing on `(0, ∞)`, and let `R_{Λ'}(t) = b R_Λ(c t)` for `t > 0`.
Then `r ∈ P(Λ') ↔ b⁻¹ r ∈ P(Λ)`. The factor `c` is any positive real: the lemma is pathwise, so `c` may depend on the
sample. -/
theorem mem_plateauValues_iff_of_radius {Λ Λ' : ℝ → Set ℂ} {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hmono : MonotoneOn (fun t => familyRadius (Λ t)) (Set.Ioi 0))
    (hΛ' : ∀ t : ℝ, 0 < t → familyRadius (Λ' t) = b * familyRadius (Λ (c * t))) (r : ℝ) :
    r ∈ plateauValues Λ' ↔ b⁻¹ * r ∈ plateauValues Λ := by
  have key : ∀ x : ℝ, 0 < x → (familyRadius (Λ' x) = r ↔ familyRadius (Λ (c * x)) = b⁻¹ * r) := by
    intro x hx
    rw [hΛ' x hx]
    constructor
    · intro h
      rw [← h, ← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]
    · intro h
      rw [h, mul_inv_cancel_left₀ hb.ne']
  have hmono_c : MonotoneOn (fun t => familyRadius (Λ (c * t))) (Set.Ioi 0) := by
    intro x hx y hy hxy
    exact hmono (mul_pos hc hx) (mul_pos hc hy) (mul_le_mul_of_nonneg_left hxy hc.le)
  constructor
  · intro hr
    obtain ⟨hr0, s, t, hs, hst, hsr, htr⟩ := (mem_plateauValues_iff _ _).1 hr
    have hRs : familyRadius (Λ (c * (s : ℝ))) = b⁻¹ * r := (key (s : ℝ) hs).1 hsr
    have hRt : familyRadius (Λ (c * (t : ℝ))) = b⁻¹ * r := (key (t : ℝ) (hs.trans hst)).1 htr
    obtain ⟨q₁, q₂, hq₁, hq₁₂, h₁, h₂⟩ :=
      exists_rat_pair_of_eq_endpoints hmono (mul_pos hc hs) (mul_lt_mul_of_pos_left hst hc) hRs hRt
    exact (mem_plateauValues_iff _ _).2
      ⟨mul_pos (inv_pos.mpr hb) hr0, q₁, q₂, hq₁, hq₁₂, h₁, h₂⟩
  · intro hr
    obtain ⟨hv, s, t, hs, hst, hsv, htv⟩ := (mem_plateauValues_iff _ _).1 hr
    have hr0 : 0 < r := by
      have h := mul_pos hb hv
      rwa [mul_inv_cancel_left₀ hb.ne'] at h
    have hc0 : c ≠ 0 := hc.ne'
    have hsc : c * ((s : ℝ) / c) = s := by field_simp
    have htc : c * ((t : ℝ) / c) = t := by field_simp
    have hx : 0 < (s : ℝ) / c := div_pos hs hc
    have hxy : (s : ℝ) / c < (t : ℝ) / c := div_lt_div_of_pos_right hst hc
    have hRx : familyRadius (Λ (c * ((s : ℝ) / c))) = b⁻¹ * r := by rw [hsc]; exact hsv
    have hRy : familyRadius (Λ (c * ((t : ℝ) / c))) = b⁻¹ * r := by rw [htc]; exact htv
    obtain ⟨q₁, q₂, hq₁, hq₁₂, h₁, h₂⟩ := exists_rat_pair_of_eq_endpoints hmono_c hx hxy hRx hRy
    exact (mem_plateauValues_iff _ _).2
      ⟨hr0, q₁, q₂, hq₁, hq₁₂, (key (q₁ : ℝ) hq₁).2 h₁, (key (q₂ : ℝ) (hq₁.trans hq₁₂)).2 h₂⟩

/-- **Set form of the scaling**: `P(Λ') = b • P(Λ)` (draft line 256: `P(h_a) = a⁻¹ P(h)` for `b = a⁻¹`). -/
theorem plateauValues_eq_image_of_radius {Λ Λ' : ℝ → Set ℂ} {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hmono : MonotoneOn (fun t => familyRadius (Λ t)) (Set.Ioi 0))
    (hΛ' : ∀ t : ℝ, 0 < t → familyRadius (Λ' t) = b * familyRadius (Λ (c * t))) :
    plateauValues Λ' = (fun r : ℝ => b * r) '' plateauValues Λ := by
  ext r
  constructor
  · intro hr
    exact ⟨b⁻¹ * r, (mem_plateauValues_iff_of_radius hb hc hmono hΛ' r).1 hr,
      mul_inv_cancel_left₀ hb.ne' r⟩
  · rintro ⟨p, hp, rfl⟩
    refine (mem_plateauValues_iff_of_radius hb hc hmono hΛ' (b * p)).2 ?_
    rw [inv_mul_cancel_left₀ hb.ne']
    exact hp

/-- **Positive time dilation preserves the plateau set** (draft lines 252-256: "The random positive change of time
preserves the set of plateau values"). For `c > 0` and an increasing radius, `P(t ↦ Λ(c t)) = P(Λ)`. -/
theorem plateauValues_comp_mul {Λ : ℝ → Set ℂ} {c : ℝ} (hc : 0 < c)
    (hmono : MonotoneOn (fun t => familyRadius (Λ t)) (Set.Ioi 0)) :
    plateauValues (fun t => Λ (c * t)) = plateauValues Λ := by
  ext r
  have h := mem_plateauValues_iff_of_radius (Λ' := fun t => Λ (c * t)) (b := 1) one_pos hc hmono
    (fun t _ => (one_mul _).symm) r
  rwa [inv_one, one_mul] at h

/-- **The form used by `PlateauScaleInvarianceStep`** (`b = a⁻¹`, draft line 256): `r ∈ P(Λ') ↔ a r ∈ P(Λ)` for `a > 0`.
This gives the identity `p(r) = p(a r)` of draft line 265 once the law of the scaled family is known. -/
theorem mem_plateauValues_iff_mul_of_radius {Λ Λ' : ℝ → Set ℂ} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hmono : MonotoneOn (fun t => familyRadius (Λ t)) (Set.Ioi 0))
    (hΛ' : ∀ t : ℝ, 0 < t → familyRadius (Λ' t) = a⁻¹ * familyRadius (Λ (c * t))) (r : ℝ) :
    r ∈ plateauValues Λ' ↔ a * r ∈ plateauValues Λ := by
  have h := mem_plateauValues_iff_of_radius (inv_pos.mpr ha) hc hmono hΛ' r
  rwa [inv_inv] at h

/-- **Set-level spatial dilation.** If `Λ'(t) = b • Λ(c t)` (the dilation `x ↦ b x` of the family), then the plateau
statement of `mem_plateauValues_iff_of_radius` holds. -/
theorem mem_plateauValues_iff_of_set_image {Λ Λ' : ℝ → Set ℂ} {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hmono : MonotoneOn (fun t => familyRadius (Λ t)) (Set.Ioi 0))
    (hΛ' : ∀ t : ℝ, 0 < t → Λ' t = (fun x : ℂ => (b : ℂ) * x) '' Λ (c * t)) (r : ℝ) :
    r ∈ plateauValues Λ' ↔ b⁻¹ * r ∈ plateauValues Λ :=
  mem_plateauValues_iff_of_radius hb hc hmono
    (fun t ht => by rw [hΛ' t ht, familyRadius_image_mul_of_pos hb]) r

/-- **Reduction of `PlateauScaleInvarianceStep` to its two open inputs** (draft lines 245-256 and 265).
Let `Λ ω` be the global family of the field `h` and `Λ' ω` that of the scaled field `h_a` (`a > 0`), with random time
change `c ω > 0` (`c = e^{γ c_a}`). Assume
* `hreg`: `Λ ω` is a regularized cluster family for `μ ω` (the hypothesis of `PlateauScaleInvarianceStep`);
* `hc`: `c ω > 0` almost surely;
* `hpath`: for almost every `ω` and all `t > 0`, `R_{Λ' ω}(t) = a⁻¹ R_{Λ ω}(c ω · t)` (the pathwise identity
  `Λ^{h_a}_t = a⁻¹ Λ^h_{e^{γ c_a} t}`; NOT proved here);
* `hlaw`: `Λ'` has the same plateau probabilities as `Λ` (the law identity `h_a =_d h`; NOT proved here).
Then `P[r ∈ P(Λ)] = P[a r ∈ P(Λ)]`, the conclusion of `PlateauScaleInvarianceStep`. No measurability is needed: the two
plateau events agree almost surely, and `measure_congr` applies to arbitrary sets. -/
theorem plateau_prob_scale_of_pathwise {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (Λ Λ' : Ω → ℝ → Set ℂ) (c : Ω → ℝ) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ᵐ ω ∂P, IsRegularizedClusterFamily (μ ω) (Λ ω) 0)
    (hc : ∀ᵐ ω ∂P, 0 < c ω)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → familyRadius (Λ' ω t) = a⁻¹ * familyRadius (Λ ω (c ω * t)))
    (hlaw : ∀ r : ℝ, P {ω | r ∈ plateauValues (Λ' ω)} = P {ω | r ∈ plateauValues (Λ ω)})
    (r : ℝ) :
    P {ω | r ∈ plateauValues (Λ ω)} = P {ω | a * r ∈ plateauValues (Λ ω)} := by
  have hae : {ω | r ∈ plateauValues (Λ' ω)} =ᵐ[P] {ω | a * r ∈ plateauValues (Λ ω)} := by
    filter_upwards [hreg, hc, hpath] with ω hω hcω hpω
    exact propext (mem_plateauValues_iff_mul_of_radius ha hcω
      (familyRadius_monotoneOn_of_regularized hω) hpω r)
  calc P {ω | r ∈ plateauValues (Λ ω)} = P {ω | r ∈ plateauValues (Λ' ω)} := (hlaw r).symm
    _ = P {ω | a * r ∈ plateauValues (Λ ω)} := measure_congr hae

end MatedCRT
