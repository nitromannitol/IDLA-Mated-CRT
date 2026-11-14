import MatedCRT.FirstPass.Derived.SrwHitLawSeparation
import MatedCRT.FirstPass.Frozen.S5cSec9

/-!
# Hitting distributions from the points of a disconnected set

Set form of [GMS21, Lemma 3.12] (Gwynne-Miller-Sheffield, arXiv:1807.07515), as used in the proof of their
Lemma 3.14: if the simple random walk from `x` disconnects the whole set `B` from `I` before hitting `I` with
probability at least `1 - δ`, then for every `y ∈ B` the hitting distributions of `I` from `x` and from `y` are within
`δ` in total variation.

* `walkDisconnectsBeforeHit_of_mem`: disconnecting the set `B` disconnects each of its points;
* `abs_srwLaw_hit_sub_le_of_mem`: the bound of `abs_srwLaw_hit_sub_le` with the set event;
* `abs_srwLaw_hit_sub_le_of_le`: the uniform bound `δ` over `y ∈ B`.
-/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

/-- A walk which disconnects the set `B` from `A` before hitting `A` disconnects every point of `B` from `A`. -/
theorem walkDisconnectsBeforeHit_of_mem {m : ℤ → ℤ → ℕ} {B A : Set ℤ} {y : ℤ} (hyB : y ∈ B) {w : ℕ → ℤ}
    (h : walkSetDisconnectsBeforeHit m B A w) : walkDisconnectsBeforeHit m A y w :=
  fun hyK a ha hak => h y hyB hyK a ha hak

/-- **[GMS21, Lemma 3.12], set form.** If simple random walk on a multigraph hits `I` almost surely from `x` and
from `y ∈ B`, then for every `W`, `|P^x(X_{τ_I} ∈ W) - P^y(X_{τ_I} ∈ W)| ≤ 1 - P^x(D_B)`, where `D_B` is the event
that the walk from `x` disconnects `B` from `I` strictly before `τ_I`. -/
theorem abs_srwLaw_hit_sub_le_of_mem (m : ℤ → ℤ → ℕ) (I W B : Set ℤ) {x y : ℤ} (hyB : y ∈ B)
    (hx : srwLaw m x {w | vHitTime I w ≠ ⊤} = 1) (hy : srwLaw m y {w | vHitTime I w ≠ ⊤} = 1) :
    |(srwLaw m x {w | vHitTime I w ≠ ⊤ ∧ w (vHitTime I w).toNat ∈ W}).toReal -
        (srwLaw m y {w | vHitTime I w ≠ ⊤ ∧ w (vHitTime I w).toNat ∈ W}).toReal| ≤
      1 - (srwLaw m x {w | walkSetDisconnectsBeforeHit m B I w}).toReal :=
  (abs_srwLaw_hit_sub_le m I W hx hy).trans <| sub_le_sub_left
    (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun _ hw => walkDisconnectsBeforeHit_of_mem hyB hw)) 1

/-- **Uniform form.** If the walk from `x` disconnects `B` from `I` before `τ_I` with probability at least `1 - δ`,
then the hitting distributions of `I` from `x` and from any `y ∈ B` (both hitting `I` almost surely) differ by at
most `δ` on every set `W`. -/
theorem abs_srwLaw_hit_sub_le_of_le (m : ℤ → ℤ → ℕ) (I W B : Set ℤ) {x y : ℤ} {δ : ℝ} (hyB : y ∈ B)
    (hD : 1 - δ ≤ (srwLaw m x {w | walkSetDisconnectsBeforeHit m B I w}).toReal)
    (hx : srwLaw m x {w | vHitTime I w ≠ ⊤} = 1) (hy : srwLaw m y {w | vHitTime I w ≠ ⊤} = 1) :
    |(srwLaw m x {w | vHitTime I w ≠ ⊤ ∧ w (vHitTime I w).toNat ∈ W}).toReal -
        (srwLaw m y {w | vHitTime I w ≠ ⊤ ∧ w (vHitTime I w).toNat ∈ W}).toReal| ≤ δ := by
  have h := abs_srwLaw_hit_sub_le_of_mem m I W B hyB hx hy
  linarith

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.walkDisconnectsBeforeHit_of_mem
#print axioms MatedCRT.abs_srwLaw_hit_sub_le_of_mem
#print axioms MatedCRT.abs_srwLaw_hit_sub_le_of_le
