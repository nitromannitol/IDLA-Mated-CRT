import MatedCRT.FirstPass.Derived.SrwChainBridge
import MatedCRT.FirstPass.S5c.GreenDiagDomination
import MatedCRT.Proofs.WalkPotential.GreenFirstStep

/-!
# Harnack inequality for the Green kernel from a separation event

For simple random walk on a locally finite multigraph `m` on `ℤ` (consecutive integers adjacent),
a finite set `B` and a pole `b ∈ B`, let `I = {b} ∪ Bᶜ` and `h(x) = P_x(X_{T_I} = b)`, the probability of
reaching `b` before leaving `B`.

* `greenFn_eq_mul_greenHit`: `G_B(x, b) = G_B(b, b) · h(x)` (the hitting identity, proved without the
  strong Markov property: both sides are harmonic on `B \ {b}` and agree at `b` and off `B`);
* `greenKernel_eq_mul_greenHit`: the same for the Green kernel;
* `mul_greenKernel_le_of_separation`: if from `a` the trace of the walk before `T_I` separates `y` from `I`
  with probability at least `p`, then `p · g_B(y, b) ≤ g_B(a, b)`. This is the deterministic part of the
  Harnack inequality for the Green kernel on circles (Berestycki-Gwynne, Proposition 3.8), via the
  multiplicative hitting-law bound of the nearest-neighbour chain API.
-/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity

/-- The probability that simple random walk from `x` reaches `b` before leaving `B`
(the hitting law of `{b} ∪ Bᶜ` at the vertex `b`). -/
noncomputable def greenHit (m : ℤ → ℤ → ℕ) (B : Set ℤ) (b x : ℤ) : ℝ :=
  (hitLaw (srwKernel m) (id : ℤ → ℤ) ({b} ∪ Bᶜ) {b} x).toReal

open Classical in
/-- A walk started in the target set hits it at time `0`: the hitting law is `1` or `0` according as the
start lies in `W`. -/
theorem hitLaw_srwKernel_of_mem (m : ℤ → ℤ → ℕ) {I W : Set ℤ} {s : ℤ} (hs : s ∈ I) :
    hitLaw (srwKernel m) (id : ℤ → ℤ) I W s = if s ∈ W then 1 else 0 := by
  unfold hitLaw
  have hae := Markov.chainLaw_ae_start (srwKernel m) s
  have key : ∀ ω : ℕ → ℤ, ω 0 = s →
      (ω ∈ hitEvent (id ⁻¹' I) (id ⁻¹' W) ↔ s ∈ W) := by
    intro ω hω
    have h0 : Markov.hitTime (id ⁻¹' I) ω = 0 := by
      refine le_antisymm ?_ bot_le
      exact iInf₂_le_of_le 0 (by simpa [hω] using hs) le_rfl
    have hst : Markov.stopState (Markov.hitTime (id ⁻¹' I)) ω = s := by
      unfold Markov.stopState
      rw [h0]
      simpa using hω
    change Markov.hitTime (id ⁻¹' I) ω ≠ ⊤ ∧
      Markov.stopState (Markov.hitTime (id ⁻¹' I)) ω ∈ id ⁻¹' W ↔ s ∈ W
    rw [h0, hst]
    simp
  split_ifs with hsW
  · rw [measure_congr (t := Set.univ) (Filter.eventuallyEqSet_iff.2 ?_), measure_univ]
    filter_upwards [hae] with ω hω
    exact ⟨fun _ => trivial, fun _ => (key ω hω).2 hsW⟩
  · rw [measure_congr (t := (∅ : Set (ℕ → ℤ))) (Filter.eventuallyEqSet_iff.2 ?_), measure_empty]
    filter_upwards [hae] with ω hω
    exact ⟨fun h => hsW ((key ω hω).1 h), fun h => h.elim⟩

theorem greenHit_self (m : ℤ → ℤ → ℕ) (B : Set ℤ) (b : ℤ) : greenHit m B b b = 1 := by
  unfold greenHit
  rw [hitLaw_srwKernel_of_mem m (Or.inl rfl)]
  simp

theorem greenHit_eq_zero_of_not_mem (m : ℤ → ℤ → ℕ) {B : Set ℤ} {b x : ℤ} (hbB : b ∈ B) (hx : x ∉ B) :
    greenHit m B b x = 0 := by
  unfold greenHit
  have hxb : x ≠ b := fun h => hx (h ▸ hbB)
  rw [hitLaw_srwKernel_of_mem m (Or.inr hx)]
  simp [hxb]

/-- Away from the target set the hitting probability is an average over the first step. -/
theorem greenHit_eq_avg {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) {B : Set ℤ} {b s : ℤ}
    (hdeg : mdeg m s ≠ 0) (hs : s ∉ ({b} ∪ Bᶜ : Set ℤ)) :
    greenHit m B b s = ((mdeg m s : ℝ))⁻¹ * ∑ c ∈ nbrs hlf s, (m s c : ℝ) * greenHit m B b c := by
  have h1 := hitLaw_srwKernel_step m ({b} ∪ Bᶜ) {b} hs
  have h2 := (WalkPotential.toReal_lintegral_srwStep hlf hdeg
    (f := fun t => hitLaw (srwKernel m) (id : ℤ → ℤ) ({b} ∪ Bᶜ) {b} t)
    (fun c => hitLaw_ne_top _ _ c)).2
  unfold greenHit
  rw [h1]
  exact h2

/-- **Hitting identity** `G_B(x, b) = G_B(b, b) · P_x(reach b before leaving B)`. -/
theorem greenFn_eq_mul_greenHit {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {B : Set ℤ} (hB : B.Finite) {b : ℤ} (hbB : b ∈ B) (x : ℤ) :
    greenFn m B x b = greenFn m B b b * greenHit m B b x := by
  have hdeg : ∀ a, mdeg m a ≠ 0 := fun a => mdeg_ne_zero_of_ne_zero hlf (hcons a)
  set c := greenFn m B b b with hc
  -- the combination `α G + β h` is harmonic on `B \ {b}`
  have hharm : ∀ y ∈ B \ {b}, ∀ α β : ℝ,
      mLaplacian m (fun x => α * greenFn m B x b + β * greenHit m B b x) y = 0 := by
    rintro y ⟨hyB, hyb⟩ α β
    have hyb' : y ≠ b := hyb
    have hG := WalkPotential.mLaplacian_greenFn hlf hcons hB b y hyB
    simp [hyb'] at hG
    have hGe := (WalkPotential.mLaplacian_eq_neg_iff hlf (hdeg y) (fun x => greenFn m B x b) 0).1 (by simpa using hG)
    have hy : y ∉ ({b} ∪ Bᶜ : Set ℤ) := by simp [hyb', hyB]
    have hHe := greenHit_eq_avg hlf (hdeg y) hy
    have hsum : ∑ c ∈ nbrs hlf y, (m y c : ℝ) * (α * greenFn m B c b + β * greenHit m B b c)
        = α * ∑ c ∈ nbrs hlf y, (m y c : ℝ) * greenFn m B c b
          + β * ∑ c ∈ nbrs hlf y, (m y c : ℝ) * greenHit m B b c := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    have key := (WalkPotential.mLaplacian_eq_neg_iff hlf (hdeg y)
      (fun x => α * greenFn m B x b + β * greenHit m B b x) 0).2 (by
        show α * greenFn m B y b + β * greenHit m B b y = 0 + ((mdeg m y : ℝ))⁻¹ *
          ∑ c ∈ nbrs hlf y, (m y c : ℝ) * (α * greenFn m B c b + β * greenHit m B b c)
        rw [hsum, hGe, hHe]
        ring)
    simpa using key
  have hfin : (B \ {b}).Finite := hB.sdiff
  have hle : ∀ α β : ℝ, (α * greenFn m B b b + β * 1 = 0) →
      ∀ x, α * greenFn m B x b + β * greenHit m B b x ≤ 0 := by
    intro α β hαβ x
    refine le_zero_of_subharmonic_of_nonpos_off hcons hlf hfin ?_ (fun y hy => (hharm y hy α β).ge) x
    intro x hx
    by_cases hxb : x = b
    · rw [hxb, greenHit_self]
      exact hαβ.le
    · have hxB : x ∉ B := fun h => hx ⟨h, hxb⟩
      rw [greenFn_eq_zero_of_not_mem m hxB, greenHit_eq_zero_of_not_mem m hbB hxB]
      simp
  have h1 := hle 1 (-c) (by rw [hc]; ring) x
  have h2 := hle (-1) c (by rw [hc]; ring) x
  linarith

/-- **Hitting identity for the Green kernel**: `g_B(x, b) = g_B(b, b) · P_x(reach b before leaving B)`. -/
theorem greenKernel_eq_mul_greenHit {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {B : Set ℤ} (hB : B.Finite) {b : ℤ} (hbB : b ∈ B) (x : ℤ) :
    greenKernel m B x b = greenKernel m B b b * greenHit m B b x := by
  unfold greenKernel
  rw [greenFn_eq_mul_greenHit hlf hcons hB hbB x]
  ring

/-- **Harnack inequality for the Green kernel from a separation event.** If, started from `a`, the vertices
visited before the walk reaches `{b} ∪ Bᶜ` separate `y` from `{b} ∪ Bᶜ` with probability at least `p`, then
`p · g_B(y, b) ≤ g_B(a, b)`. -/
theorem mul_greenKernel_le_of_separation {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {B : Set ℤ} (hB : B.Finite) {b : ℤ} (hbB : b ∈ B) {a y : ℤ} {p : ℝ}
    (hp : 0 ≤ p)
    (hsep : ENNReal.ofReal p ≤ srwLaw m a {x | GraphSeparates (srwGraph m)
      (traceBefore (id : ℤ → ℤ) ({b} ∪ Bᶜ) x) {y} ({b} ∪ Bᶜ)}) :
    p * greenKernel m B y b ≤ greenKernel m B a b := by
  rw [greenKernel_eq_mul_greenHit hlf hcons hB hbB y, greenKernel_eq_mul_greenHit hlf hcons hB hbB a]
  have hg : 0 ≤ greenKernel m B b b := div_nonneg (greenFn_nonnegative m B b b) (Nat.cast_nonneg _)
  suffices hh : p * greenHit m B b y ≤ greenHit m B b a by
    calc p * (greenKernel m B b b * greenHit m B b y)
        = greenKernel m B b b * (p * greenHit m B b y) := by ring
      _ ≤ greenKernel m B b b * greenHit m B b a := mul_le_mul_of_nonneg_left hh hg
  by_cases h0 : hitLaw (srwKernel m) (id : ℤ → ℤ) ({b} ∪ Bᶜ) {b} y = 0
  · have hy0 : greenHit m B b y = 0 := by
      unfold greenHit
      rw [h0]
      simp
    rw [hy0, mul_zero]
    exact ENNReal.toReal_nonneg
  · have hpos : 0 < hitLaw (srwKernel m) (id : ℤ → ℤ) ({b} ∪ Bᶜ) {b} y := pos_iff_ne_zero.2 h0
    obtain ⟨a0, ha0, w, hw⟩ := exists_walk_hitLaw_le (isNNChain_srwKernel m) ({b} ∪ Bᶜ) {b} y hpos
    have hmul := mul_chainLaw_separates_le (isNNChain_srwKernel m) ({b} ∪ Bᶜ) {b} ha0 w hw a
    rw [chainLaw_srwKernel] at hmul
    have h1 : hitLaw (srwKernel m) (id : ℤ → ℤ) ({b} ∪ Bᶜ) {b} y * ENNReal.ofReal p ≤
        hitLaw (srwKernel m) (id : ℤ → ℤ) ({b} ∪ Bᶜ) {b} a :=
      le_trans (mul_le_mul_right hsep _) hmul
    have h2 := ENNReal.toReal_mono (hitLaw_ne_top _ _ a) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp] at h2
    unfold greenHit
    linarith

end MatedCRT
