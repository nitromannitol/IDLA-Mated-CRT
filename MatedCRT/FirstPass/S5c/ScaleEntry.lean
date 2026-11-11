import MatedCRT.FirstPass.S5c.EntryTimes
import MatedCRT.FirstPass.S5c.FixedIndexGap

/-!
# FIRST PASS, Lemma 5.3 (statement (a) almost surely): the cover (3.1) at every time

For a random family `Λ ω t` of open sets, monotone in `t > 0`, the new-entrance event at time `t`
`E(t) = {∃ y ∈ Λ_t, ∀ s ∈ (0, t), y ∉ Λ_s}` (three-inputs A2) is the complement of the outcome-wise cover
`Λ_t ⊆ ⋃_{s<t} Λ_s` used in FixedIndexGap (three-inputs (3.1)).

* `cover_of_not_newEntrance`, `cover_ae_of_null_entrance`: a null new-entrance event gives the a.s. cover at `t`.
* `nullEntrance_of_scale`: the scaling identity `P(E(b t)) = P(E t)` (three-inputs A4; it comes from the scaling law
  Lemma 2.6, `ConeScaleInvarianceStmt`) transports the null event of `exists_entry_free_time` (one time `t₀ ∈ (1,2)`)
  to every `t > 0`.
* `cover_ae_all_of_scale`: the a.s. cover (3.1) at every `t > 0`.
* `fixedIndexMargin_compact_ae`: statement (a) of three-inputs section 1, almost surely on `{t < T}`.

Open inputs, all explicit hypotheses (none is proved here): `hmeas` (null measurability of `{D ⊆ Λ_t}`, the A1-A3 input,
see EntryTimes.lean), `hscale` (the A4 identity; its derivation from Lemma 2.6 needs the pathwise identity
`E^b(t) = E(bt)` for `Λ^b_s = R_b⁻¹ Λ_{bs}` and the measurability of `E(t)` in the countable code), and the frozen
`FPStrongMinimumPrinciple` (A7). Terminology: Armitage-Gardiner (strong minimum principle), Duplantier-Sheffield and
Berestycki-Powell (the cluster `Λ_t`, the time-`t` harmonic ball).
-/

namespace MatedCRT.S5c

open HarmonicBalls MeasureTheory Filter Set

/-- The new-entrance event at time `t` (three-inputs A2): some point of the cluster `Λ_t` lies in no earlier cluster
`Λ_s`, `0 < s < t`. -/
def newEntranceEvent {Ω : Type} (Λ : Ω → ℝ → Set ℂ) (t : ℝ) : Set Ω :=
  {ω | ∃ y ∈ Λ ω t, ∀ s ∈ Ioo (0 : ℝ) t, y ∉ Λ ω s}

/-- Outcome-wise (3.1): off the new-entrance event, every point of `Λ_t` lies in some `Λ_s` with `0 < s < t`. -/
theorem cover_of_not_newEntrance {Ω : Type} {Λ : Ω → ℝ → Set ℂ} {t : ℝ} {ω : Ω}
    (h : ω ∉ newEntranceEvent Λ t) : ∀ x ∈ Λ ω t, ∃ s, 0 < s ∧ s < t ∧ x ∈ Λ ω s := by
  intro x hx
  by_contra hcon
  exact h ⟨x, hx, fun s hs hxs => hcon ⟨s, hs.1, hs.2, hxs⟩⟩

/-- A null new-entrance event at `t` gives the almost-sure cover (3.1) at `t`. -/
theorem cover_ae_of_null_entrance {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Λ : Ω → ℝ → Set ℂ} {t : ℝ}
    (h : P (newEntranceEvent Λ t) = 0) :
    ∀ᵐ ω ∂P, ∀ x ∈ Λ ω t, ∃ s, 0 < s ∧ s < t ∧ x ∈ Λ ω s := by
  refine ae_iff.2 (measure_mono_null ?_ h)
  intro ω hω
  by_contra hn
  exact hω (cover_of_not_newEntrance hn)

/-- Scaling transport (three-inputs A4): if `P(E(b t)) = P(E t)` for all `b, t > 0` and `E` is null at one time
`t₀ > 0`, then `E` is null at every `t > 0` (take `b = t₀ / t`). -/
theorem nullEntrance_of_scale {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (E : ℝ → Set Ω)
    (hscale : ∀ b t : ℝ, 0 < b → 0 < t → P (E (b * t)) = P (E t))
    {t₀ : ℝ} (ht₀ : 0 < t₀) (h0 : P (E t₀) = 0) : ∀ t : ℝ, 0 < t → P (E t) = 0 := by
  intro t ht
  have h := hscale (t₀ / t) t (div_pos ht₀ ht) ht
  have e : t₀ / t * t = t₀ := by field_simp
  rw [e, h0] at h
  exact h.symm

/-- The almost-sure cover (3.1) at every `t > 0` (three-inputs A1-A4), from the open-and-monotone outcomes `hgood`,
the null measurability `hmeas` (A1-A3 input, open), and the scaling identity `hscale` (A4, from Lemma 2.6). -/
theorem cover_ae_all_of_scale {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : Ω → ℝ → Set ℂ)
    (hgood : ∀ᵐ ω ∂P, (∀ t : ℝ, 0 < t → IsOpen (Λ ω t)) ∧ MonotoneOn (Λ ω) (Ioi 0))
    (hmeas : ∀ (x : MatedCRT.RatDiscIndex) (t : ℝ), 0 < t → NullMeasurableSet {ω | MatedCRT.ratDisc x ⊆ Λ ω t} P)
    (hscale : ∀ b t : ℝ, 0 < b → 0 < t → P (newEntranceEvent Λ (b * t)) = P (newEntranceEvent Λ t)) :
    ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂P, ∀ x ∈ Λ ω t, ∃ s, 0 < s ∧ s < t ∧ x ∈ Λ ω s := by
  obtain ⟨t₀, ht₀, h0⟩ := MatedCRT.exists_entry_free_time P Λ hgood hmeas
  have ht₀pos : 0 < t₀ := lt_trans zero_lt_one ht₀.1
  intro t ht
  exact cover_ae_of_null_entrance (nullEntrance_of_scale (newEntranceEvent Λ) hscale ht₀pos h0 t ht)

/-- Statement (a) of three-inputs section 1, almost surely: on `{t < T}`, every compact `K ⊆ Λ_t` carries a uniform
positive lower bound on `w_t - 2 w_{t/2}` (FixedIndexGap, outcome-wise, fed by the a.s. cover (3.1)). -/
theorem fixedIndexMargin_compact_ae {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (Λ : Ω → ℝ → Set ℂ) (hmin : FPStrongMinimumPrinciple)
    (hfam : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    (hgood : ∀ᵐ ω ∂P, (∀ t : ℝ, 0 < t → IsOpen (Λ ω t)) ∧ MonotoneOn (Λ ω) (Ioi 0))
    (hmeas : ∀ (x : MatedCRT.RatDiscIndex) (t : ℝ), 0 < t → NullMeasurableSet {ω | MatedCRT.ratDisc x ⊆ Λ ω t} P)
    (hscale : ∀ b t : ℝ, 0 < b → 0 < t → P (newEntranceEvent Λ (b * t)) = P (newEntranceEvent Λ t))
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    ∀ᵐ ω ∂P, t < clusterExitTime (Λ ω) ρ → ∀ K : Set ℂ, IsCompact K → K ⊆ Λ ω t →
      ∃ β : ℝ, 0 < β ∧
        ∀ x ∈ K, β ≤ leastSupersolution (μ ω) ρ 0 t x - 2 * leastSupersolution (μ ω) ρ 0 (t / 2) x := by
  filter_upwards [hfam, cover_ae_all_of_scale P Λ hgood hmeas hscale t ht] with ω hf hc hT K hK hKΛ
  exact fixedIndexMargin_lower_bound_on_compact hmin hf hρ hT ht hc hK hKΛ

end MatedCRT.S5c
