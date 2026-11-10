import MatedCRT.FirstPass.S4S6c.ShellCoreCG68
import MatedCRT.FirstPass.S4S6c.HoneRrLocal68

/-!
# The residual `hRr` of the CG shell producer (fp-S4S6c-cgres-rr, z12)

Owner: z12. This file discharges the residual `ShellCGResRr` of `ShellCoreCG68.lean` (the window lies in
`[r², 1]` on the leaf of the shell walk) from the individual `ω`-level clauses of `ShellPtPremCG` that the
argument uses, and from the full-admissibility premise `FullAdmAt`.

* `resRr_pt` (STEP A): the binders are the clauses of `ShellPtPremCG` (ShellCoreCG68.lean:311-335) that the
  proof reads, with their exact types; the global full-support clause `∀ w t, 0 < t → 0 < S.μ ω (ball w t)` is
  not used. The conclusion is the body of `ShellCGResRr` after its two premises.
* The producer is `hRr_fixedOmega_loc_half_g` (HoneRrLocal68.lean), at the mesh radius `rhoCell68 ρ = (1 + ρ) / 2`,
  with `s1 := shellS1CG γ CG` and `c0W := shellC0 CG`. The cell-diameter bound at that radius comes from
  `cellDiamLe_rhoCell_of_meshEventR` with the leaf threshold `shellKCG_eps_cell`, as in the CG producer.
-/

namespace MatedCRT
namespace Lemma68CGResRr

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellConstants MatedCRT.Lemma68Guard10 MatedCRT.Lemma68ConstOrder
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open MatedCRT.Lemma68ShellCoreCG
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow
open MatedCRT.Lemma68B1Assembly MatedCRT.Lemma68Omega

/-- **STEP A of `ShellCGResRr` (z12).** The body of the residual `ShellCGResRr` (ShellCoreCG68.lean:374) at one
scale `ε`, one radius `r`, one environment `ω` and one leaf `i`, from the clauses of `ShellPtPremCG` used here and
the premise `FullAdmAt`. -/
theorem resRr_pt {γ ω₀ α ζ ρ CG CE C q0 R s₀ ε r : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) (i : Lemma68Config.Config68)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hω₀ : 0 < ω₀) (hκ2 : 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ)
    (hCG : 0 < CG) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hRρ : R ≤ ρ / 4) (hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ)
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hεe : ε ≤ shellEps0ZCG γ α ω₀ ζ CG) (hr10 : 10 * ε ^ ω₀ ≤ r) (hrR : r ≤ R)
    (hmeshω : ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε)
    (hcurve : Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hmult : ∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0)
    (hcont : Continuous (S.η ω))
    (hadjAll : ∀ ε' : ℝ, 0 < ε' → ∀ u v : ℤ, S.mult ε' ω u v ≠ 0 →
      (cell ε' (S.η ω) u ∩ cell ε' (S.η ω) v).Nonempty)
    (hFA : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i) :
    ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
        r ^ 2 ≤ (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
            (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
            (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1 := by
  have hr0 : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _)) hr10
  have hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ := le_trans hrR hRA
  have hrρ : r ≤ ρ / 4 := le_trans hrR hRρ
  have hεcell := shellKCG_eps_cell (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) ω₀ α ζ CG
    hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG rfl hκ2 hε hεe hr10
  have hmesh := cellDiamLe_rhoCell_of_meshEventR (c0 := shellC0 CG) S ω hmeshω hε hρ1 hr0 hrρ
    (shellC0_le_one_cg hCG) hεcell
  exact MatedCRT.Lemma68HoneRrLocal.hRr_fixedOmega_loc_half_g (s1 := shellS1CG γ CG) (c0W := shellC0 CG) S
    hρ1 hζ0 hζ1 hq0 hq0c hs₀ hε hr0 hrρ hrA i ω hmesh hcont
    (Lemma68Geometry.tendsto_cocompact_of_escapes hcurve) (fun j k hjk => hadjAll ε hε j k hjk) (hmult ε hε) hFA

end Lemma68CGResRr
end MatedCRT

#print axioms MatedCRT.Lemma68CGResRr.resRr_pt
