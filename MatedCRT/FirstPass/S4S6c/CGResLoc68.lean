import MatedCRT.FirstPass.S4S6c.ShellCoreCG68
import MatedCRT.FirstPass.S4S6c.ShellOrderPw68
import MatedCRT.FirstPass.S4S6c.ShellHdePw68
import MatedCRT.FirstPass.S4S6c.HoneElAe68
import MatedCRT.FirstPass.S4S6c.ShellChainGlue68
import MatedCRT.FirstPass.S4S6c.ShellConstOrder68
import MatedCRT.FirstPass.S6r.KilledExitAe

/-!
# The residual `ShellCGResLoc`, pointwise

Step A: at ONE environment point `ω`, the body of `ShellCGResLoc` (`ShellCoreCG68.lean`) after its two premises
(`CellDiamLe` on `ball 0 (rhoCell68 ρ)` and `FullAdmAt`) follows from individual clauses of `ShellPtPremCG` and from
one named input `htest`: the finiteness of the test ends `testEnd ≠ ⊤` on the shell chain, almost surely in the walk.
No almost-sure quantifier over `ω` is used, and the full-support clause is not used.

Route (`ShellOrderPw68.hShellLoc_pw_g` at `c0W := shellC0 CG`, `s1 := shellS1CG γ CG`):
* `hgap`: the clause `2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ rhoCell68 ρ - ρ` and `dyadicD r ^ shortExp ζ ≥ 0`.
* `hη`, `hmap`, `hdg`: the clauses `Continuous (S.η ω)`, open-cell adjacency at `ε`, edge mass at `ε`.
* `hkill`: `Lemma68KilledExitAe.ae_killed_exit_ne_top` from local finiteness and `m(k, k+1) ≠ 0` at `ε`.
* `hstart`: `Lemma68HoneElAe.hstart_of_fullAdmAt_s1`.
* `hde`: `Lemma68ShellHdePw68.shellHde_pw68_s1` (shell exits finite, centres eligible; its mesh on `ball 0 ρ` is the
  premise on `ball 0 (rhoCell68 ρ)` restricted), joined with `htest` for the test-end part.
* `hR`: `Lemma68HoneRadii.windowRfT_rangeShortEligible`.
* `hrz`: `r ≤ R ≤ rAmp q0 ζ ≤ countThreshold ζ`, with `q0 ≤ 1` from `q0 ≤ (1/4)^2/(4 shellChone68 CE C)` and
  `1 ≤ shellChone68 CE C`.
-/

open MeasureTheory Set Filter Metric
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry

namespace MatedCRT
namespace Lemma68CGResLoc

/-- Step A of the residual `ShellCGResLoc` at one environment point `ω` (Duplantier-Sheffield shell chain,
Armstrong-Kuusi-Mourrat shell order). The binders are the clauses of `ShellPtPremCG` that the proof uses, the
named input `htest`, and the two premises of the residual (`hmesh`, `hFA`). -/
theorem resLoc_pt {γ ω₀ ζ ρ CG CE C q0 R s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hq0 : 0 < q0)
    (hq0C : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * Lemma68ConstOrder.shellChone68 CE C)) (hρ1 : ρ < 1)
    (hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ) (hRρ : R ≤ ρ / 4)
    (hr10 : 10 * ε ^ ω₀ ≤ r) (hrR : r ≤ R)
    (hgapCl : 2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hη : Continuous (S.η ω))
    (hfin : ∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0)
    (hcell : ∀ ε' : ℝ, 0 < ε' → ∀ u v : ℤ, S.mult ε' ω u v ≠ 0 → (cell ε' (S.η ω) u ∩ cell ε' (S.η ω) v).Nonempty)
    (hdg : ∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤)
    (htest : Lemma68Config.FullAdmAt (Lemma68Guard10.shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
        testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) (Lemma68ConstOrder.shellC0 CG) C (dyadicD r) ω) k x ≠ ⊤)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100)
      (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)))
    (hFA : Lemma68Config.FullAdmAt (Lemma68Guard10.shellS1CG γ CG) S ρ s₀ γ ε ω r i) :
    Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r)
      (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) (Lemma68ConstOrder.shellC0 CG) C (dyadicD r) ω)
      (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  have hεω : 0 < ε ^ ω₀ := Real.rpow_pos_of_pos hε ω₀
  have hr : 0 < r := by linarith
  have hsc : 1 ≤ Lemma68ConstOrder.shellChone68 CE C := Lemma68ConstOrder.one_le_shellChone68 CE C
  have hq1 : q0 ≤ 1 := by
    have hpos : 0 < 4 * Lemma68ConstOrder.shellChone68 CE C := by linarith
    have h1 : (1 / 4 : ℝ) ^ 2 / (4 * Lemma68ConstOrder.shellChone68 CE C) ≤ 1 := by
      rw [div_le_one hpos]
      nlinarith
    exact hq0C.trans h1
  have hrz : r ≤ countThreshold ζ :=
    hrR.trans (hRA.trans (Lemma68ChainGlue.rAmp_le_countThreshold hq0 hq1 hζ0 hζ1))
  have hrρ : r ≤ ρ / 4 := hrR.trans hRρ
  have hgap : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
    have hd := dyadicD_pos r
    have := Real.rpow_nonneg hd.le (shortExp ζ)
    linarith
  have hR := Lemma68HoneRadii.windowRfT_rangeShortEligible S.μ ρ (shortExp ζ) (Lemma68ConstOrder.shellC0 CG) C
    (dyadicD r) (dyadicD_pos r) (dyadicD_le_one r) (by unfold shortExp; linarith) ω
  have hmesh_ball : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ) :=
    Lemma68ShellOrderPw.cellDiamLe_mono_set
      (Metric.ball_subset_ball (by unfold Lemma68HoneCellGood.rhoCell68; linarith)) hmesh
  have hkill : ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), vExitTime (killed ε (S.η ω) i.Θ i.F0 r) x ≠ ⊤ :=
    Lemma68KilledExitAe.ae_killed_exit_ne_top (hfin ε hε).1 (hfin ε hε).2 i.a ε (S.η ω) i.Θ i.F0 r
  have hmap : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    fun j k hjk => hcell ε hε j k hjk
  have hstart : Lemma68Config.FullAdmAt (Lemma68Guard10.shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty :=
    fun hFA' => Lemma68HoneElAe.hstart_of_fullAdmAt_s1 S hε hs₀ ω hη r hr i hFA'
  exact Lemma68ShellOrderPw.hShellLoc_pw_g (γ := γ) (Lemma68Guard10.shellS1CG γ CG) S ω
    (Lemma68ConstOrder.shellC0 CG) C hε hs₀ hζ0 hζ1 hr hrz hrρ i hgap hη hmap hdg hkill hstart
    (fun hFA' => by
      filter_upwards [Lemma68ShellHdePw68.shellHde_pw68_s1 (Rf := Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ)
          (Lemma68ConstOrder.shellC0 CG) C (dyadicD r) ω)
          (Elig := fun w => w ∈ shortEligible ρ (dyadicD r) (shortExp ζ))
          (Lemma68Guard10.shellS1CG γ CG) S hε hs₀ hζ0 hζ1 hr hrz hrρ i hη hmap hkill hR (fun _ hw => hw)
          hmesh_ball hstart hFA', htest hFA'] with x hx ht
      exact ⟨fun k hk => ⟨hx.1 k hk, ht k hk⟩, hx.2⟩)
    hmesh hFA

/-- The named input `htest` of `resLoc_pt`, quantified as in `ShellCGResLoc`: on the shell chain of `ShellPtPremCG`,
the test ends are almost surely finite (the finite-test-domain route of `ShellTestPw68`, with the mesh bound localised to
`ball 0 ρ`). This Prop is NOT proved here; it is the single missing input of the CG residual. -/
def ShellCGTestEndLoc (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    Lemma68ShellCoreCG.ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
      Lemma68Config.FullAdmAt (Lemma68Guard10.shellS1CG γ CG) S ρ s₀ γ ε ω r i →
        ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a), ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (Lemma68WindowRf.windowRfT S.μ ρ (shortExp ζ) (Lemma68ConstOrder.shellC0 CG) C (dyadicD r) ω) k x ≠ ⊤

/-- The residual `ShellCGResLoc 𝒮` from its named test-end input `ShellCGTestEndLoc 𝒮`: destructure `ShellPtPremCG`
(43 conjuncts, current form of `ShellCoreCG68.lean`) and apply `resLoc_pt`. -/
theorem shellCGResLoc_of_test (𝒮 : SpaceFillingSLEModel) (hTest : ShellCGTestEndLoc 𝒮) :
    Lemma68ShellCoreCG.ShellCGResLoc 𝒮 := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω _ S Ew ω i hP hmesh hFA
  have hT := hTest γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hP
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hζ0, hζ1, _, hρ1, _, hq0, hq0C, _, _, hRρ, hRA, _, hs0, _, _, hε, _,
    hr10, hrR, _, _, hgap, _, hfin, hη, _, _, hdg, _, hcell, _, _⟩ := hP
  exact resLoc_pt S ω i hε hs0 hζ0 hζ1 hq0 hq0C hρ1 hRA hRρ hr10 hrR hgap hη hfin hcell hdg
    hT hmesh hFA

end Lemma68CGResLoc
end MatedCRT

#print axioms MatedCRT.Lemma68CGResLoc.resLoc_pt
#print axioms MatedCRT.Lemma68CGResLoc.shellCGResLoc_of_test
