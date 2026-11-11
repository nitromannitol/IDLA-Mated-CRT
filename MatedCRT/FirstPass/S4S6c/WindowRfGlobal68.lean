import MatedCRT.FirstPass.S4S6c.ShellWindowRf68
import MatedCRT.FirstPass.S6r.ShellOmega

/-!
# Global bound of the window radius and the discharge of `hRbd`

`windowRf μ c₀ C a d ω z` is `Classical.epsilon` of the predicate `P z r := r ∈ shortWindowRadii d a ∧
IsGoodAnnulusEvent (μ ω) c₀ C r z`. If some `r` satisfies `P z`, the chosen value lies in `shortWindowRadii d a`,
hence in `[d, d^a]`. If no `r` does, `P z` is the constantly false predicate, and the value is the fixed real
`windowRfJunk := Classical.epsilon (fun _ : ℝ => False)`, independent of `z`, `ω` and `μ`. Hence
`windowRf ≤ max (d^a) windowRfJunk` for every centre and every environment. The definition of `windowRf` is not
changed here (ShellWindowRf68.lean).

For `windowRfT` the bad branch gives the value `d ≤ d^a` (`le_rpow_short68`, `0 < d ≤ 1`, `a ≤ 1`).
So the leaf binder `hRbd` (`∃ t, ∀ w, shellExit k w < ⊤ → Rf (shellCentre k w) ≤ t`) holds for the instance
`Rf := windowRfT μ ρ a c₀ C d ω` with the constant `max (d^a) windowRfJunk`, without `prefixSet` or `hEl`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT
namespace Lemma68WindowRfGlobal

open MatedCRT.Lemma68WindowRf MatedCRT.Lemma68Omega MatedCRT.Lemma68Window

/-- The junk value of `Classical.epsilon` on the constantly false real predicate. It does not depend on any
argument, so it is a fixed real bound for `windowRf` (Armitage-Gardiner: no measure or ball enters). -/
noncomputable def windowRfJunk : ℝ := Classical.epsilon (fun _ : ℝ => False)

/-- **Global upper bound of the window radius (item 1).** For every environment `ω` and every
centre `z`, `windowRf ≤ max (d^a) windowRfJunk`: the chosen good window radius lies in `[d, d^a]`, and without a good
window radius the value is the fixed junk real. -/
theorem windowRf_le_global {Ω : Type} (μ : Ω → Measure ℂ) (c₀ C a d : ℝ) (ω : Ω) (z : ℂ) :
    windowRf μ c₀ C a d ω z ≤ max (d ^ a) windowRfJunk := by
  classical
  by_cases h : ∃ r, r ∈ shortWindowRadii d a ∧ IsGoodAnnulusEvent (μ ω) c₀ C r z
  · have hs := Classical.epsilon_spec h
    exact le_max_of_le_left hs.1.2.2
  · have hfun : (fun r => r ∈ shortWindowRadii d a ∧ IsGoodAnnulusEvent (μ ω) c₀ C r z) =
        fun _ : ℝ => False :=
      funext fun r => eq_false fun hr => h ⟨r, hr⟩
    show Classical.epsilon (fun r => r ∈ shortWindowRadii d a ∧ IsGoodAnnulusEvent (μ ω) c₀ C r z) ≤
      max (d ^ a) windowRfJunk
    rw [hfun]
    exact le_max_right _ _

/-- **Global upper bound of the total window radius (item 4).** The bad branch of `windowRfT` is `d`,
and `d ≤ d^a` for `0 < d ≤ 1`, `a ≤ 1`. -/
theorem windowRfT_le_global {Ω : Type} (μ : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (ha : a ≤ 1) (ω : Ω) (z : ℂ) :
    windowRfT μ ρ a c₀ C d ω z ≤ max (d ^ a) windowRfJunk := by
  dsimp only [windowRfT]
  split_ifs with hb
  · exact le_max_of_le_left (le_rpow_short68 hd0 hd1 ha)
  · exact windowRf_le_global μ c₀ C a d ω z

/-- **The leaf binder `hRbd`, discharged for the total window radius (item 5).** For the instance
`Rf := windowRfT μ ρ a c₀ C d ω` the radius bound holds on every walk, with the constant `max (d^a) windowRfJunk`
(independent of `k` and `w`); no prefix set, eligibility or `hRr_ae_setup` is used. -/
theorem windowRfT_hRbd_global {Ω : Type} (μ : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (ha : a ≤ 1) (ω : Ω) (ε : ℝ) (η : ℝ → ℂ) (Kset : Set ℂ) (r s : ℝ) (k : ℕ) :
    ∃ t : ℝ, ∀ w : ℕ → ℤ,
      shellExit ε η Kset r s d (windowRfT μ ρ a c₀ C d ω) k w < ⊤ →
        windowRfT μ ρ a c₀ C d ω (shellCentre ε η Kset r s d k w) ≤ t :=
  ⟨max (d ^ a) windowRfJunk, fun _ _ => windowRfT_le_global μ ρ a c₀ C d hd0 hd1 ha ω _⟩

end Lemma68WindowRfGlobal
end MatedCRT

#print axioms MatedCRT.Lemma68WindowRfGlobal.windowRf_le_global
#print axioms MatedCRT.Lemma68WindowRfGlobal.windowRfT_le_global
#print axioms MatedCRT.Lemma68WindowRfGlobal.windowRfT_hRbd_global
