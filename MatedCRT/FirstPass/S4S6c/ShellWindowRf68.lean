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

open scoped Classical in
/-- **The total window radius of the shell chain.** On the complement of the window event `badWindowOf μ ρ a c₀ C d`
it is the chosen good radius `windowRf`; on the event it is `d`. Its range `d ≤ · ≤ d^a` holds for every `ω`
(`windowRfT_bounds`), so the range `hR` of `shellOrder_fullAdm_ae_omega` needs no almost-sure window hypothesis. -/
noncomputable def windowRfT {Ω : Type} (μ : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) (ω : Ω) : ℂ → ℝ :=
  fun z => if ω ∈ badWindowOf μ ρ a c₀ C d then d else windowRf μ c₀ C a d ω z

/-- `d ≤ d^a` for `0 < d ≤ 1` and `a ≤ 1`: the power is antitone in the exponent on `(0,1]`. -/
theorem le_rpow_short68 {d a : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) (ha : a ≤ 1) : d ≤ d ^ a := by
  have h := Real.rpow_le_rpow_of_exponent_ge hd0 hd1 ha
  rwa [Real.rpow_one] at h

/-- **Range of the total window radius, for every environment.** For `z` eligible, `windowRfT` lies in `[d, d^a]`. -/
theorem windowRfT_bounds {Ω : Type} (μ : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1) (ha : a ≤ 1)
    (ω : Ω) {z : ℂ} (hz : z ∈ shortEligible ρ d a) :
    d ≤ windowRfT μ ρ a c₀ C d ω z ∧ windowRfT μ ρ a c₀ C d ω z ≤ d ^ a := by
  unfold windowRfT
  split_ifs with hb
  · exact ⟨le_rfl, le_rpow_short68 hd0 hd1 ha⟩
  · exact windowRf_bounds μ ρ a c₀ C d ω hb hz

/-- **Off the window event, the total radius is the chosen good radius.** -/
theorem windowRfT_of_not_bad {Ω : Type} (μ : Ω → Measure ℂ) (ρ a c₀ C d : ℝ) (ω : Ω)
    (hω : ω ∉ badWindowOf μ ρ a c₀ C d) (z : ℂ) :
    windowRfT μ ρ a c₀ C d ω z = windowRf μ c₀ C a d ω z := by
  simp [windowRfT, hω]

end Lemma68WindowRf
end MatedCRT
