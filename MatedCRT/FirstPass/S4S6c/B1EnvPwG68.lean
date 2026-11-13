import MatedCRT.FirstPass.S4S6c.B1Assembly68
import MatedCRT.FirstPass.S4S6c.HoneEnvEvents68
import MatedCRT.FirstPass.S4S6c.HoneWalkAe68
import MatedCRT.FirstPass.S4S6c.HoneRcell68
import MatedCRT.FirstPass.S4S6c.ShellChainGlue68
import MatedCRT.FirstPass.S6e.Geometry
import MatedCRT.FirstPass.S4S6c.HoneRrLocal68
import MatedCRT.FirstPass.S4S6c.B1EnvPw68
/-!
# Generic adapters for the binders of the one-radius assembly

Generic copies, at one environment `ω`, of the pointwise adapters `hGreen_pw`, `hCountGood_pw`, `hRcell_pw` and
`hWalk_pw` of B1EnvPw68.lean (e0cc869), which are left unchanged. The sparsity exponent is a parameter `s1`
(replacing `Lemma68Config.sparsityS1 γ` in every `FullAdmAt`), and the window constant is a parameter `c0W`
(replacing `shellC068` in the window radius, written inline as `windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω`).
`hGreen_pw_g` and `hCountGood_pw_g` have no window, so they take `s1` only.

The named gaps stay explicit binders: `hcut` (G2) of `hRcell_pw_g`; `hωm`, `hr10` (G1) of `hWalk_pw_g`.
The start lemma of `hWalk_pw_g` is the `s1`-generic `Lemma68HoneRrLocal.hstart_of_fullAdmAt_s1`
(HoneRrLocal68.lean:226); `walk_conclusion_of_ball` is taken from B1EnvPw68.lean.

Terminology: polynomially high probability (Armstrong-Kuusi-Mourrat), Lemma 2.9 and 2.16 (Berestycki-Gwynne;
Berestycki-Powell), Duplantier-Sheffield (mated-CRT shells), Armitage-Gardiner (balls, spheres, Green kernel).
-/
open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68B1EnvPwG

open MatedCRT.Lemma68B1Assembly
open MatedCRT.Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow

/-- **`hGreen_pw` with the sparsity coefficient `s1` as a parameter (`hGreen_pw_g`).** Copy of `hGreen_pw`
(B1EnvPw68.lean:52) with `Lemma68Config.sparsityS1 γ` replaced by `s1`. The proof does not use the guard, so no
hypothesis on `s1` is needed. -/
theorem hGreen_pw_g {γ ρ s₀ ε r s1 : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (K : Constants68 γ ρ) (ω : Ω) (i : Lemma68Config.Config68)
    (hω : ω ∈ HoneModelInputs68.greenLowerGoodEvent K.ω K.C ρ S ε) :
    Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)), ∀ r' : ℝ, ε ^ K.ω ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          K.C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b :=
  fun _ => HoneEnvEvents68.hGreen_of_mem hω


/-- **`hCountGood_pw` with the sparsity coefficient `s1` as a parameter (`hCountGood_pw_g`).** Copy of `hCountGood_pw`
(B1EnvPw68.lean:67) with `Lemma68Config.sparsityS1 γ` replaced by `s1`. The proof does not use the guard, so no
hypothesis on `s1` is needed. -/
theorem hCountGood_pw_g {γ ρ s₀ ε r α β s1 : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68) (hβ : 0 ≤ β) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hω : ω ∈ HoneModelInputs68.countingGoodEvent S α β ρ ε) :
    Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ) := by
  intro _ D hD w hw
  have hpow : (1 : ℝ) ≤ ε ^ (-β) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have hbound : ∀ x ∈ thickening (ε ^ α) D, 0 ≤ (fun _ : ℂ => (1 : ℝ)) x ∧
      |(fun _ : ℂ => (1 : ℝ)) x| ≤ ε ^ (-β) := fun _ _ => by
    show 0 ≤ (1 : ℝ) ∧ |(1 : ℝ)| ≤ ε ^ (-β)
    rw [abs_one]
    exact ⟨zero_le_one, hpow⟩
  have hlip : ∀ x ∈ thickening (ε ^ α) D, ∀ y ∈ thickening (ε ^ α) D,
      |(fun _ : ℂ => (1 : ℝ)) x - (fun _ : ℂ => (1 : ℝ)) y| ≤ ε ^ (-β) * ‖x - y‖ := fun x _ y _ => by
    show |(1 : ℝ) - 1| ≤ ε ^ (-β) * ‖x - y‖
    rw [sub_self, abs_zero]
    exact mul_nonneg (zero_le_one.trans hpow) (norm_nonneg _)
  exact (hω D (fun _ => (1 : ℝ)) w hD hbound hlip hw).1


/-- **`hRcell_pw` with the sparsity coefficient `s1` and the window constant `c0W` as parameters (`hRcell_pw_g`).**
Copy of `hRcell_pw` (B1EnvPw68.lean:92) with `Lemma68Config.sparsityS1 γ` replaced by `s1`, `shellC068` replaced by
`c0W`, and `winRf S ρ ζ C r ω` written inline as `windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω`. The bound
`windowRfT_bounds` (ShellWindowRf68.lean:65) has no hypothesis on its constant, so no hypothesis on `s1` or `c0W` is
needed. The named gap `hcut` (G2) is kept as an explicit binder, as in `hRcell_pw`. -/
theorem hRcell_pw_g {γ ρ ζ C s₀ ε r s1 c0W : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hEl : Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))
    (hcut : dyadicD r ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) :
    Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k x) / 4 < Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
  intro hFA
  have hd : 0 < dyadicD r := dyadicD_pos r
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω z ≤ dyadicD r ^ shortExp ζ := fun z hz =>
    (windowRfT_bounds S.μ ρ (shortExp ζ) c0W C (dyadicD r) hd hd1 ha1 ω hz).2
  exact Lemma68RcellDischarge.hRcell_of_eligible (A := ↑i.A)
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    (m := S.mult ε ω) (a0 := i.a) (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)
    (sc := dyadicD r ^ shortExp ζ) (d := dyadicD r) (aW := shortExp ζ) (g := Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    hd hRf (hEl hFA) hcut


/-- **`hWalk_pw` with the sparsity coefficient `s1` and the window constant `c0W` as parameters (`hWalk_pw_g`).**
Copy of `hWalk_pw` (B1EnvPw68.lean:140) with `Lemma68Config.sparsityS1 γ` replaced by `s1`, `shellC068` replaced by
`c0W`, and `winRf` written inline as `windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω`. The start lemma is the
`s1`-generic `Lemma68HoneRrLocal.hstart_of_fullAdmAt_s1` (HoneRrLocal68.lean:226), which uses only `ConfigOK` and
`Admissible` of `FullAdmAt`. The named gaps `hωm`, `hr10` (G1) are kept as binders, as in `hWalk_pw`. -/
theorem hWalk_pw_g {γ ρ ζ C CG α CE s₀ ε r ω₀ ωm s1 c0W : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (K : Constants68 γ ρ) (ω : Ω) (i : Lemma68Config.Config68)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4)
    (hrz : r ≤ countThreshold ζ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hs₀ : 0 < s₀)
    (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hωm : 2 * ωm < K.ω) (hr10 : 10 * ε ^ ωm ≤ r) :
    Lemma68Config.FullAdmAt (s1) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ K.ω ≤ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat)) (sphere 0 ρ) := by
  intro hFA
  have hcont : Continuous (S.η ω) := hreg.2.2.2.1
  have hr1 : r ≤ 1 := by linarith
  have hdpos : 0 < dyadicD r := dyadicD_pos r
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  obtain ⟨hdr, hd2⟩ := Lemma68ChainGlue.dyadicD_mem hr0 hr1
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have ha0 : 0 < shortExp ζ := by unfold shortExp; linarith
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hdpos hd1 ha1
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrz hdpos hd2
  have hspos : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hdpos _
  obtain ⟨-, hjs, hN800, -⟩ := shell_parameters hr0 hdpos hζ0.le rfl hdr hd2 hs4
  have hN1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    have h0 : (0 : ℝ) < (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) :=
      lt_of_lt_of_le (div_pos hr0 (mul_pos (by norm_num) hspos)) hN800
    exact_mod_cast h0
  have hNs : 20 * ((shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [Nat.sub_add_cancel hN1]
    exact (hjs 1 le_rfl hN1).2.2
  have hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) :=
    Lemma68Geometry.tendsto_cocompact_of_escapes hreg.2.1
  have hlf : IsLocallyFiniteMult (S.mult ε ω) := (hreg.2.2.1 ε hε).1
  have hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := (hreg.2.2.1 ε hε).2
  have hedge : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    fun j k h => hreg.2.2.2.2.2.2.2.2 ε hε j k h
  have hdeg := hreg.2.2.2.2.2.2.1
  have hF0 : (↑i.F0 : Set ℤ) = cellVertices ε (S.η ω) (ball 0 ρ) := hFA.1.1
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ ball (0 : ℂ) (ρ / 2) := subset_closure.trans hFA.1.2.1
  have h0 : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hFA.1.2.2 (mem_ball_self hs₀)
  have hst := Lemma68HoneRrLocal.hstart_of_fullAdmAt_s1 S hε hs₀ ω hcont r hr0 i hFA
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω z ∧ windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω z ≤ dyadicD r ^ shortExp ζ := fun z hz =>
    windowRfT_bounds S.μ ρ (shortExp ζ) c0W C (dyadicD r) hdpos hd1 ha1 ω hz
  have hW := Lemma68HoneWalkAe.hWalk_ae_of_walk (ε := ε) (η := S.η ω) K hcont hε hε1 hp hedge hlf hcons i.a
    (Θ := i.Θ) (F0 := i.F0) (ρ := ρ) (r := r) (d := dyadicD r) (a := shortExp ζ)
    (s := dyadicD r ^ shortExp ζ) (ρmom := ρ) (ω0 := ωm) (Rf := windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (A := ↑i.A)
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hr0 hrρ hdpos hdr hds hs4 hNs rfl hr10 hωm le_rfl hmesh hF0 h0 hKb hRf hst hdeg
  intro k hk
  filter_upwards [hW k hk] with x hx hpre
  obtain ⟨hv, hR8⟩ := hx hpre
  obtain ⟨hcv, hinf⟩ := Lemma68B1EnvPw.walk_conclusion_of_ball hε hρ0 hv hR8 (Real.rpow_pos_of_pos hε _)
  exact ⟨hcv, hR8, hinf⟩


end Lemma68B1EnvPwG
end MatedCRT

#print axioms MatedCRT.Lemma68B1EnvPwG.hGreen_pw_g
#print axioms MatedCRT.Lemma68B1EnvPwG.hCountGood_pw_g
#print axioms MatedCRT.Lemma68B1EnvPwG.hRcell_pw_g
#print axioms MatedCRT.Lemma68B1EnvPwG.hWalk_pw_g
