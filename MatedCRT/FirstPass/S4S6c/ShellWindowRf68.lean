import MatedCRT.FirstPass.S4S6c.ShellChain68

/-!
# The window radius choice `Rf` of the shell chain (q2, fp-S4S6c-hU-chain; the `Rf` of `ShellOneTestOrderAeStmt`)

If the window event does not occur at scale `d` (`ω ∉ badWindowOf μ ρ a c₀ C d`, ShellChain68.lean:33), every eligible
centre `z ∈ shortEligible ρ d a` (S6r/ShortWindow.lean:54) has a good seven-adic radius `r ∈ shortWindowRadii d a`
(S6r/ShortWindow.lean:51), that is a good annulus event `IsGoodAnnulusEvent (μ ω) c₀ C r z` (Defs/Setting.lean:333).
`windowRf` chooses one such radius per centre. It depends on `ω` (the good event does), so it is not a deterministic
radius function of the centre; `ShellOrderFullAdm.lean` (`shellOrder_fullAdm_ae`) takes a fixed `Rf`. That mismatch is
reported, not routed around here.

Terminology: good annuli and good radii (Armstrong-Kuusi-Mourrat, prevalence of good radii); Armitage-Gardiner (balls).
-/

open MeasureTheory Set

namespace MatedCRT
namespace Lemma68WindowRf

open MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Window

/-- **Good radius of an eligible centre, on the complement of the window event.** If `ω ∉ badWindowOf μ ρ a c₀ C d`
and `z` is eligible, some seven-adic radius of the short window is a good annulus radius at `z` for `μ ω`. -/
theorem exists_good_radius_of_not_bad {Ω : Type} (μ : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) (ω : Ω)
    (hω : ω ∉ badWindowOf μ ρ a c₀ C d) {z : ℂ} (hz : z ∈ shortEligible ρ d a) :
    ∃ r ∈ shortWindowRadii d a, IsGoodAnnulusEvent (μ ω) c₀ C r z := by
  by_contra h
  exact hω ⟨z, hz, fun r hr hg => h ⟨r, hr, hg⟩⟩

/-- **The window radius choice.** For each centre, a chosen good window radius (when one exists), and `d` otherwise.
Depends on `ω` through the good event `IsGoodAnnulusEvent (μ ω)`. -/
noncomputable def windowRf {Ω : Type} (μ : Ω → Measure ℂ) (c₀ C a d : ℝ) (ω : Ω) : ℂ → ℝ :=
  fun z => Classical.epsilon (fun r => r ∈ shortWindowRadii d a ∧ IsGoodAnnulusEvent (μ ω) c₀ C r z)

/-- The chosen radius of an eligible centre is a window radius and a good annulus radius for `μ ω`. -/
theorem windowRf_spec {Ω : Type} (μ : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) (ω : Ω)
    (hω : ω ∉ badWindowOf μ ρ a c₀ C d) {z : ℂ} (hz : z ∈ shortEligible ρ d a) :
    windowRf μ c₀ C a d ω z ∈ shortWindowRadii d a ∧
      IsGoodAnnulusEvent (μ ω) c₀ C (windowRf μ c₀ C a d ω z) z :=
  Classical.epsilon_spec (exists_good_radius_of_not_bad μ ρ a c₀ C d ω hω hz)

/-- The window radius of an eligible centre lies in the short window `[d, d^a]`: the range `hR` of
`shellOrder_fullAdm_ae` (ShellOrderFullAdm.lean:63) with `Elig = shortEligible ρ d a`, `Rf = windowRf`. -/
theorem windowRf_bounds {Ω : Type} (μ : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) (ω : Ω)
    (hω : ω ∉ badWindowOf μ ρ a c₀ C d) {z : ℂ} (hz : z ∈ shortEligible ρ d a) :
    d ≤ windowRf μ c₀ C a d ω z ∧ windowRf μ c₀ C a d ω z ≤ d ^ a := by
  obtain ⟨hmem, _⟩ := windowRf_spec μ ρ a c₀ C d ω hω hz
  rcases hmem with ⟨_, h1, h2⟩
  exact ⟨h1, h2⟩

end Lemma68WindowRf
end MatedCRT
