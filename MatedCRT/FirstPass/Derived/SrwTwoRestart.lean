import MatedCRT.FirstPass.S4S6c.StrongMarkovState
import MatedCRT.FirstPass.S4S6c.TraceFrom68

/-!
# Two strong-Markov restarts for simple random walk on a multigraph

Berestycki–Gwynne (2020), proof of Lemma 3.10 from Gwynne–Miller–Sheffield (2019), Proposition 3.6 and Lemma 3.11: the
walk first reaches a set `I₀` (a grid circle), then restarts from the hit vertex and follows the itinerary of
Proposition 3.6 until it enters a set `B` (a small ball), then restarts from the vertex of `B` and performs the event of
Lemma 3.11.  The probability of the combined event is at least the product of the two start-uniform probabilities.

* `srwLaw_restart_lower`: if `S ∩ {τ = k}` is determined by the history up to time `k` and the future event `G (x_τ)`
  has probability at least `p` from every vertex of `S ∩ {τ = k}`, then `P(S ∩ {τ < ∞, shift_τ ∈ G (x_τ)}) ≥
  p · P(S ∩ {τ < ∞})`.
* `srwLaw_restartEvent_lower`: one restart at the hitting time of `B` of a path that has not met `I` before.
* `srwLaw_twoRestart_lower`: two restarts, the first at the hitting time of `I₀`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

open WalkPotential

/-- Every event determined by the history up to time `k` is measurable. -/
theorem measurableSet_pathHist_preimage (k : ℕ) (F : Set (Fin (k + 1) → ℤ)) :
    MeasurableSet {x : ℕ → ℤ | pathHist k x ∈ F} :=
  TraceFrom68.measurable_pathHist_fin k (Set.to_countable F).measurableSet

/-- **Restart lower bound.** -/
theorem srwLaw_restart_lower (m : ℤ → ℤ → ℕ) (a : ℤ) (τ : (ℕ → ℤ) → ℕ∞) (G : ℤ → Set (ℕ → ℤ))
    (hG : ∀ y, MeasurableSet (G y)) {S : Set (ℕ → ℤ)}
    (hS : ∀ k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      S ∩ {x | τ x = (k : ℕ∞)} = {x | pathHist k x ∈ F})
    {p : ℝ≥0∞} (hp : ∀ k : ℕ, ∀ x ∈ S ∩ {x | τ x = (k : ℕ∞)}, p ≤ srwLaw m (x k) (G (x k))) :
    p * srwLaw m a (S ∩ {x | τ x ≠ ⊤}) ≤
      srwLaw m a (S ∩ {x | ∃ k : ℕ, τ x = (k : ℕ∞) ∧ pathShift k x ∈ G (x k)}) := by
  rw [srwLaw_strong_markov_state m a τ G hG hS]
  have hmeas : ∀ k : ℕ, MeasurableSet (S ∩ {x | τ x = (k : ℕ∞)}) := by
    intro k
    obtain ⟨F, -, hEq⟩ := hS k
    rw [hEq]
    exact measurableSet_pathHist_preimage k F
  have hdec : S ∩ {x | τ x ≠ ⊤} = ⋃ k : ℕ, S ∩ {x | τ x = (k : ℕ∞)} := by
    ext x
    simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hx, hτ⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hτ
      exact ⟨k, hx, hk.symm⟩
    · rintro ⟨k, hx, hk⟩
      exact ⟨hx, by rw [hk]; exact ENat.natCast_ne_top k⟩
  calc p * srwLaw m a (S ∩ {x | τ x ≠ ⊤})
      ≤ p * ∑' k : ℕ, srwLaw m a (S ∩ {x | τ x = (k : ℕ∞)}) := by
        rw [hdec]
        exact mul_le_mul_right (measure_iUnion_le _) p
    _ = ∑' k : ℕ, p * srwLaw m a (S ∩ {x | τ x = (k : ℕ∞)}) := ENNReal.tsum_mul_left.symm
    _ = ∑' k : ℕ, ∫⁻ _ in S ∩ {x | τ x = (k : ℕ∞)}, p ∂srwLaw m a := by
        refine tsum_congr fun k => ?_
        rw [setLIntegral_const]
    _ ≤ _ := ENNReal.tsum_le_tsum fun k => setLIntegral_mono' (hmeas k) (hp k)

/-- The event that a path hits `B` at a finite time `t` without meeting `I` up to time `t`, and then the future event `E`
occurs after time `t`. -/
def restartEvent (B I : Set ℤ) (E : Set (ℕ → ℤ)) : Set (ℕ → ℤ) :=
  {ζ | ∃ t : ℕ, vHitTime B ζ = (t : ℕ∞) ∧ (∀ i ≤ t, ζ i ∉ I) ∧ pathShift t ζ ∈ E}

/-- The event that a path hits `I₀` at a finite time `k` without meeting `I` up to time `k`, and then the shifted path is
in the `restartEvent` for `B`, `I`, `E`. -/
def twoRestartEvent (I₀ B I : Set ℤ) (E : Set (ℕ → ℤ)) : Set (ℕ → ℤ) :=
  {ξ | ∃ k : ℕ, vHitTime I₀ ξ = (k : ℕ∞) ∧ (∀ i ≤ k, ξ i ∉ I) ∧ pathShift k ξ ∈ restartEvent B I E}

/-- The paths that hit `B` at time `k` and do not meet `I` up to time `k` are the histories in a set of finite paths. -/
theorem exists_pathHist_hit (B I : Set ℤ) (k : ℕ) :
    ∃ F : Set (Fin (k + 1) → ℤ), {x : ℕ → ℤ | vHitTime B x = (k : ℕ∞) ∧ ∀ i ≤ k, x i ∉ I} =
      {x | pathHist k x ∈ F} := by
  refine ⟨{h | h (Fin.last k) ∈ B ∧ (∀ i : Fin (k + 1), (i : ℕ) < k → h i ∉ B) ∧ ∀ i : Fin (k + 1), h i ∉ I},
    ?_⟩
  ext x
  constructor
  · rintro ⟨hτ, hI⟩
    rw [TraceFrom68.vHitTime_eq_iff] at hτ
    exact ⟨hτ.1, fun i hi => hτ.2 i hi, fun i => hI i (Nat.lt_succ_iff.1 i.2)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(TraceFrom68.vHitTime_eq_iff B k x).2 ⟨h1, fun i hi => h2 ⟨i, by omega⟩ hi⟩,
      fun i hi => h3 ⟨i, by omega⟩⟩

theorem measurableSet_restartEvent (B I : Set ℤ) {E : Set (ℕ → ℤ)} (hE : MeasurableSet E) :
    MeasurableSet (restartEvent B I E) := by
  have h : restartEvent B I E = ⋃ t : ℕ, {x : ℕ → ℤ | vHitTime B x = (t : ℕ∞) ∧ ∀ i ≤ t, x i ∉ I} ∩
      pathShift t ⁻¹' E := by
    ext ζ
    simp only [restartEvent, Set.mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, and_assoc]
  rw [h]
  refine MeasurableSet.iUnion fun t => ?_
  obtain ⟨F, hF⟩ := exists_pathHist_hit B I t
  rw [hF]
  exact (measurableSet_pathHist_preimage t F).inter (walk_measurable_pathShift t hE)

/-- **One restart.** If from each vertex of `B` the event `E` has probability at least `p₁`, and the event `Itin`, of
probability at least `p₀` from the start `y`, forces a finite hitting time of `B` before which `I` is not met, then the
`restartEvent` has probability at least `p₀ p₁` from `y`. -/
theorem srwLaw_restartEvent_lower (m : ℤ → ℤ → ℕ) (B I : Set ℤ) {E Itin : Set (ℕ → ℤ)}
    (hE : MeasurableSet E) {p₀ p₁ : ℝ≥0∞} (h₁ : ∀ y ∈ B, p₁ ≤ srwLaw m y E)
    (hsub : ∀ ζ ∈ Itin, vHitTime B ζ ≠ ⊤ ∧ ∀ i : ℕ, (i : ℕ∞) ≤ vHitTime B ζ → ζ i ∉ I) (y : ℤ)
    (h₀ : p₀ ≤ srwLaw m y Itin) : p₀ * p₁ ≤ srwLaw m y (restartEvent B I E) := by
  set S : Set (ℕ → ℤ) := {ζ | vHitTime B ζ ≠ ⊤ ∧ ∀ i : ℕ, (i : ℕ∞) ≤ vHitTime B ζ → ζ i ∉ I} with hSdef
  have hSk : ∀ k : ℕ, S ∩ {x | vHitTime B x = (k : ℕ∞)} =
      {x : ℕ → ℤ | vHitTime B x = (k : ℕ∞) ∧ ∀ i ≤ k, x i ∉ I} := by
    intro k
    ext x
    constructor
    · rintro ⟨⟨_, hI⟩, hk⟩
      refine ⟨hk, fun i hi => hI i ?_⟩
      rw [hk]
      exact_mod_cast hi
    · rintro ⟨hk, hI⟩
      refine ⟨⟨by rw [hk]; exact ENat.natCast_ne_top k, fun i hi => hI i ?_⟩, hk⟩
      rw [hk] at hi
      exact_mod_cast hi
  have hR := srwLaw_restart_lower m y (vHitTime B) (fun _ => E) (fun _ => hE) (S := S)
    (fun k => by
      obtain ⟨F, hF⟩ := exists_pathHist_hit B I k
      exact ⟨F, (Set.to_countable F).measurableSet, by rw [hSk k, hF]⟩)
    (p := p₁) (fun k x hx => by
      rw [hSk k] at hx
      exact h₁ (x k) ((TraceFrom68.vHitTime_eq_iff B k x).1 hx.1).1)
  have hsubset : S ∩ {x | ∃ k : ℕ, vHitTime B x = (k : ℕ∞) ∧ pathShift k x ∈ E} ⊆ restartEvent B I E := by
    rintro x ⟨⟨_, hI⟩, k, hk, hE'⟩
    refine ⟨k, hk, fun i hi => hI i ?_, hE'⟩
    rw [hk]
    exact_mod_cast hi
  have hItin : Itin ⊆ S ∩ {x | vHitTime B x ≠ ⊤} := fun ζ hζ => ⟨hsub ζ hζ, (hsub ζ hζ).1⟩
  calc p₀ * p₁ ≤ srwLaw m y (S ∩ {x | vHitTime B x ≠ ⊤}) * p₁ :=
        mul_le_mul_left (h₀.trans (measure_mono hItin)) p₁
    _ = p₁ * srwLaw m y (S ∩ {x | vHitTime B x ≠ ⊤}) := mul_comm _ _
    _ ≤ _ := hR.trans (measure_mono hsubset)

/-- **Two restarts.** The walk from `a` almost surely hits `I₀` at a finite time without meeting `I` before; from each
vertex of `I₀` the event `Itin` has probability at least `p₀` and forces a finite hitting time of `B` without meeting
`I`; from each vertex of `B` the event `E` has probability at least `p₁`.  Then the walk from `a` has probability at
least `p₀ p₁` of the `twoRestartEvent`. -/
theorem srwLaw_twoRestart_lower (m : ℤ → ℤ → ℕ) (a : ℤ) (I₀ B I : Set ℤ) {E Itin : Set (ℕ → ℤ)}
    (hE : MeasurableSet E) {p₀ p₁ : ℝ≥0∞} (h₀ : ∀ y ∈ I₀, p₀ ≤ srwLaw m y Itin)
    (hsub : ∀ ζ ∈ Itin, vHitTime B ζ ≠ ⊤ ∧ ∀ i : ℕ, (i : ℕ∞) ≤ vHitTime B ζ → ζ i ∉ I)
    (h₁ : ∀ y ∈ B, p₁ ≤ srwLaw m y E)
    (hpre : ∀ᵐ ξ ∂srwLaw m a, vHitTime I₀ ξ ≠ ⊤ ∧ ∀ i : ℕ, (i : ℕ∞) ≤ vHitTime I₀ ξ → ξ i ∉ I) :
    p₀ * p₁ ≤ srwLaw m a (twoRestartEvent I₀ B I E) := by
  have hhit : ∀ k : ℕ, {x : ℕ → ℤ | vHitTime I₀ x = (k : ℕ∞)} =
      {x : ℕ → ℤ | vHitTime I₀ x = (k : ℕ∞) ∧ ∀ i ≤ k, x i ∉ (∅ : Set ℤ)} := by
    intro k
    ext x
    simp
  have hR := srwLaw_restart_lower m a (vHitTime I₀) (fun _ => restartEvent B I E)
    (fun _ => measurableSet_restartEvent B I hE) (S := Set.univ)
    (fun k => by
      obtain ⟨F, hF⟩ := exists_pathHist_hit I₀ ∅ k
      exact ⟨F, (Set.to_countable F).measurableSet, by rw [Set.univ_inter, hhit k, hF]⟩)
    (p := p₀ * p₁) (fun k x hx => by
      rw [Set.univ_inter] at hx
      exact (srwLaw_restartEvent_lower m B I hE h₁ hsub (x k)
        (h₀ (x k) ((TraceFrom68.vHitTime_eq_iff I₀ k x).1 hx).1)))
  have hone : srwLaw m a (Set.univ ∩ {x | vHitTime I₀ x ≠ ⊤}) = 1 := by
    have hae : (Set.univ ∩ {x | vHitTime I₀ x ≠ ⊤} : Set (ℕ → ℤ)) =ᵐ[srwLaw m a] Set.univ := by
      filter_upwards [hpre] with ξ hξ
      exact propext ⟨fun _ => trivial, fun _ => ⟨trivial, hξ.1⟩⟩
    rw [measure_congr hae, measure_univ]
  rw [hone, mul_one] at hR
  refine hR.trans (measure_mono_ae ?_)
  filter_upwards [hpre] with ξ hξ hx
  obtain ⟨-, k, hk, hE'⟩ := hx
  exact ⟨k, hk, fun i hi => hξ.2 i (by rw [hk]; exact_mod_cast hi), hE'⟩

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.srwLaw_restart_lower
#print axioms MatedCRT.srwLaw_restartEvent_lower
#print axioms MatedCRT.srwLaw_twoRestart_lower
