import MatedCRT.FirstPass.S4S6c.ShellWire68
import MatedCRT.FirstPass.S6r.Count
import MatedCRT.FirstPass.S6e.Cutoff
import MatedCRT.FirstPass.S6r.Window

/-!
# Glue of the shell-chain core: count, dyadic scale, radius range

* `countBound_zeta`: the count bound `c_N r^{-ζ} ≤ shellCount r (d^a)` of `count_bound` (S6r/Count.lean) with the constant
  `K` replaced by the exponent `ζ` (the proof of `count_bound` uses only `ζ > 0`). Constants68 is not needed.
* `dyadicD_mem`: the dyadic scale `dyadicD r` (S6r/Window.lean:25) satisfies `r² ≤ dyadicD r < 2 r²` for `0 < r ≤ 1`.
* `rAmp_le_countThreshold`: the amplitude radius `rAmp q₀ ζ` (S6e/Cutoff.lean:24) is at most the count threshold
  `countThreshold ζ` (S6r/Count.lean:32), for `0 < q₀ ≤ 1` and `0 < ζ < 1/2`. So a radius `r ≤ R ≤ rAmp q₀ ζ` lies in the
  range of the count bound.
* `exitQ_le_pow_count`: the pointwise glue. For one environment point `ω` and one configuration `i`, given the one-test
  bound on the shells `k ≤ n` (in the walk-centred form of `exitQ_le_pow_shell_walk`), the shell order `ShellOrderAe` for
  `n`, and the multigraph hypotheses, the exit probability is at most `(1 - q)^N` with `N = shellCount r s ≥ c_N r^{-ζ}`.

Terminology: Armstrong-Kuusi-Mourrat (shells, count of shells), Armitage-Gardiner (exit times of balls).
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MatedCRT
namespace Lemma68ChainGlue

open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **The count bound with the exponent only (from `count_bound`).** For `0 < r ≤ countThreshold ζ` and
`r² ≤ d < 2r²`, `c_N r^{-ζ} ≤ shellCount r (d^a)` with `c_N = countConst ζ`, `a = shortExp ζ`. -/
theorem countBound_zeta {ζ r d : ℝ} (hζ : 0 < ζ) (hr : 0 < r) (hrle : r ≤ countThreshold ζ) (hd : 0 < d)
    (hrd : r ^ 2 ≤ d) (hd2 : d < 2 * r ^ 2) :
    countConst ζ * r ^ (-ζ) ≤ (shellCount r (d ^ shortExp ζ) : ℝ) := by
  have hsr : d ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ hr hrle hd hd2
  exact (shell_parameters (s := d ^ shortExp ζ) (ζ := ζ) hr hd hζ.le rfl hrd hd2 hsr).2.2.2

/-- **The dyadic scale.** For `0 < r ≤ 1`, `r² ≤ dyadicD r < 2 r²` (`dyadic_bounds`, S6r/Window.lean:28). -/
theorem dyadicD_mem {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : r ^ 2 ≤ dyadicD r ∧ dyadicD r < 2 * r ^ 2 := by
  have hx : (1 : ℝ) ≤ 1 / r ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨h1, h2⟩ := Lemma68Window.dyadic_bounds (1 / r ^ 2) hx
  have e : (1 : ℝ) / (1 / r ^ 2) = r ^ 2 := by field_simp
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

/-- **The radius range sits under the count threshold.** For `0 < q₀ ≤ 1` and `0 < ζ < 1/2`,
`rAmp q₀ ζ ≤ countThreshold ζ`. Proof: `rAmp ≤ X^(2/ζ) = (X²)^(1/ζ)` with `X = q₀ζ²/(3200 log 2) ≤ 1/8000`, and
`countThreshold ζ = (2^{-a}/4000)^(1/ζ) ≥ (1/8000)^(1/ζ)` since `2^{-a} ≥ 1/2` for `a ≤ 1`. -/
theorem rAmp_le_countThreshold {q0 ζ : ℝ} (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) :
    Lemma68Cutoff.rAmp q0 ζ ≤ countThreshold ζ := by
  have hlog : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpos16 : (0 : ℝ) < 16 * Real.log 2 := by linarith
  unfold Lemma68Cutoff.rAmp countThreshold
  set X : ℝ := q0 / 200 * ζ ^ 2 / (16 * Real.log 2) with hXdef
  have hX0 : 0 < X := div_pos (mul_pos (div_pos hq0 (by norm_num)) (pow_pos hζ 2)) hpos16
  have h1 : q0 / 200 ≤ 1 / 200 := by linarith
  have h2 : ζ ^ 2 ≤ 1 / 4 := by nlinarith
  have h3 : q0 / 200 * ζ ^ 2 ≤ 1 / 200 * (1 / 4) := mul_le_mul h1 h2 (sq_nonneg ζ) (by norm_num)
  have hXle : X ≤ 1 / 8000 := by
    rw [hXdef, div_le_iff₀ hpos16]
    linarith
  have hX2 : X ^ 2 ≤ 1 / 8000 := by nlinarith
  have ha1 : shortExp ζ ≤ 1 := shortExp_le_one (by linarith)
  have h2a : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-shortExp ζ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (-1 : ℝ) ≤ -shortExp ζ by linarith)
    rw [Real.rpow_neg_one] at h
    have h' : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    linarith
  have hY : 1 / 8000 ≤ (2 : ℝ) ^ (-shortExp ζ) / 4000 := by linarith
  refine (min_le_right _ _).trans ?_
  have e1 : X ^ (2 / ζ) = (X ^ (2 : ℝ)) ^ (1 / ζ) := by
    rw [← Real.rpow_mul hX0.le]
    congr 1
    ring
  rw [e1, Real.rpow_two]
  exact Real.rpow_le_rpow (sq_nonneg X) (le_trans hX2 hY) (one_div_nonneg.mpr hζ.le)

/-- **The pointwise glue of the shell chain.** At a fixed environment point `ω` and configuration `i`, with the shell
scale `s = d^a` (`a = shortExp ζ`) and `r² ≤ d < 2r²`, `0 < r ≤ countThreshold ζ`: if the one-test bound holds on the
shells `k ≤ shellCount r s - 1` (the walk-centred form of `exitQ_le_pow_shell_walk`), and the shell order `ShellOrderAe`
holds for `n = shellCount r s - 1`, then `exitQ ≤ (1 - q)^N` with `N = shellCount r s`, and `N ≥ c_N r^{-ζ}`.
Named inputs: `hone` (the one-test bound, from `hone_exitQ_walk_of_env_direct`), `hShell` (from `shell_order_env_ae_closed`),
`hlf, hcons` (the multigraph hypotheses of the chain core). -/
theorem exitQ_le_pow_count {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω) (ζ r s d : ℝ)
    (R : ℂ → ℝ) (i : Lemma68Config.Config68) {q : ℝ} (hq1 : q ≤ 1)
    (hζ : 0 < ζ) (hr : 0 < r) (hrz : r ≤ countThreshold ζ) (hd : 0 < d) (hrd : r ^ 2 ≤ d) (hd2 : d < 2 * r ^ 2)
    (hs : s = d ^ shortExp ζ)
    (hone : ∀ k ≤ shellCount r s - 1, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      x ∈ prefixSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
          (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
          (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) →
        (srwLaw (S.mult ε ω) i.a)[(testFailSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
          (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
          (Lemma68Window.testEndExit ε (S.η ω)
            (shellWalkParam ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k)
            (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k))).indicator (fun _ => (1 : ℝ)) |
          (isStoppingTime_shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r s d R k).measurableSpace] x
          ≤ 1 - q)
    (hShell : Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r s d R (shellCount r s - 1) (S.mult ε ω) i.a)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧ Lemma68Config.exitQ S ε ω r i ≤ (1 - q) ^ N := by
  have hcount : countConst ζ * r ^ (-ζ) ≤ (shellCount r s : ℝ) := by
    rw [hs]
    exact countBound_zeta hζ hr hrz hd hrd hd2
  have hcpos : 0 < countConst ζ * r ^ (-ζ) :=
    mul_pos (countConst_pos ζ) (Real.rpow_pos_of_pos hr _)
  have hreal : (0 : ℝ) < (shellCount r s : ℝ) := lt_of_lt_of_le hcpos hcount
  have hpos : 0 < shellCount r s := by exact_mod_cast hreal
  have hpos1 : 1 ≤ shellCount r s := hpos
  refine ⟨shellCount r s, hcount, ?_⟩
  have h := Lemma68ShellWire.exitQ_le_pow_shell_walk S ε ω r s d R i hq1 (shellCount r s - 1) hone hShell hlf hcons
  rwa [Nat.sub_add_cancel hpos1] at h

end Lemma68ChainGlue
end MatedCRT

namespace MatedCRT
namespace Lemma68ChainGlue

open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- The one-test parameter `q = q₀ / (1 + log(1/r))²` lies in `[0, 1]` for `0 < q₀ ≤ 1` and `0 < r ≤ 1`. -/
theorem oneTest_q_le_one {q0 r : ℝ} (hq1 : q0 ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) :
    q0 / (1 + Real.log (1 / r)) ^ 2 ≤ 1 := by
  have hl : 0 ≤ Real.log (1 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
  have h1 : 1 ≤ (1 + Real.log (1 / r)) ^ 2 := by nlinarith
  exact (div_le_one (by linarith)).mpr (by linarith)

/-- **The pointwise step of `ShellChainCoreStmt`, parameters discharged.** For the parameters of the core
(`0 < ζ < 1/2`, `0 < q₀ ≤ 1`, `0 < r ≤ 1`, `r ≤ R ≤ rAmp q₀ ζ`) and the shell scale `s = d^a` with `d = dyadicD r`, the
exit bound of the core, `∃ N, c_N r^{-ζ} ≤ N ∧ exitQ ≤ (1 - q₀/(1+log(1/r))²)^N`, follows from the two named inputs
`hone` (one-test bound on the shells, walk-centred form) and `hShell` (shell order, `n = shellCount r s - 1`).
The radius range is used only through `rAmp_le_countThreshold` (so `r ≤ countThreshold ζ`) and `dyadicD_mem`. -/
theorem exitQ_core_step {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω) (ζ q0 r : ℝ)
    (Rf : ℂ → ℝ) (i : Lemma68Config.Config68)
    (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (hone : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
      x ∈ prefixSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
          (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k)
          (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) →
        (srwLaw (S.mult ε ω) i.a)[(testFailSet (fun j (y : ℕ → ℤ) => y j) (↑i.A : Set ℤ)
          (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k)
          (Lemma68Window.testEndExit ε (S.η ω)
            (shellWalkParam ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k)
            (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k))).indicator
          (fun _ => (1 : ℝ)) |
          (isStoppingTime_shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
            k).measurableSpace] x
          ≤ 1 - q0 / (1 + Real.log (1 / r)) ^ 2)
    (hShell : Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
      (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :
    ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
      Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
  obtain ⟨hrd, hd2⟩ := dyadicD_mem hr hr1
  have hd : 0 < dyadicD r := lt_of_lt_of_le (by positivity) hrd
  have hrz : r ≤ countThreshold ζ := hRA.trans (rAmp_le_countThreshold hq0 hq1 hζ hζ1)
  exact exitQ_le_pow_count S ε ω ζ r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf i (oneTest_q_le_one hq1 hr hr1)
    hζ hr hrz hd hrd hd2 rfl hone hShell hlf hcons

end Lemma68ChainGlue
end MatedCRT
