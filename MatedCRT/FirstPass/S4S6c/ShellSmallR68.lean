import MatedCRT.FirstPass.S6r.Window
import MatedCRT.FirstPass.S4S6c.HoneCellGood68
import MatedCRT.FirstPass.S6r.Count
import MatedCRT.FirstPass.S6e.Cutoff

/-!
# Deterministic small-radius binders of the CG shell composition

For fixed `0 < ρ < 1`, `0 < ζ < 1/2` and `0 < q0`, each deterministic binder of
`shellOneTest_at_of_goodEnv_loc_g` (B1Assembly68.lean:1216) and of `hShellBall_loc_s1`
(ShellBallLoc68.lean) that depends only on the radius `r` and the constants is satisfied for all
radii below a positive threshold `r₀`. The binders are:

* `hcutR : dyadicD r ^ shortExp ζ < rhoCell68 ρ - ρ` (goodEnv_loc_g; B1EnvPw68),
* `hgapShell : 2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ rhoCell68 ρ - ρ`
  (the antecedent of `hShellBall_loc_s1`, with `ρmesh := rhoCell68 ρ`),
* `hrρ : r ≤ ρ / 4`, `hrz : r ≤ countThreshold ζ`, `_hRA : r ≤ rAmp q0 ζ`.

The two helpers `dyadicD_pow_le_sq` and `gap_of_pow_le` below are copies of ShellCoreCG68.lean:199 and :187
(an earlier import of ShellCoreCG68 made the lb of this module fail at ShellCoreCG68.lean:531:25, linarith). No hypothesis on `ε` or `ω` enters.
-/

namespace MatedCRT
namespace Lemma68ShellSmallR

open MatedCRT.Lemma68Window

/-- **Square bound for `dyadicD`** (copy of `dyadicD_pow_le_of_sq`, ShellCoreCG68.lean:199, kept local because `lb`
of ShellCoreCG68 failed at line 531 in the current working tree). For `0 < r ≤ 1`, `2 r² ≤ c^(1/shortExp ζ)` gives
`dyadicD r ^ shortExp ζ ≤ c` (`dyadicD r < 2 r²`, `dyadicD_lt_two_mul_sq`). -/
theorem dyadicD_pow_le_sq {r ζ c : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hζ0 : 0 < ζ) (hc0 : 0 < c)
    (hrc : 2 * r ^ 2 ≤ c ^ (1 / shortExp ζ)) : dyadicD r ^ shortExp ζ ≤ c := by
  have ha : 0 < shortExp ζ := by unfold shortExp; linarith
  have hd0 : 0 ≤ dyadicD r := (dyadicD_pos r).le
  have hlt : dyadicD r ≤ 2 * r ^ 2 := (dyadicD_lt_two_mul_sq hr0 hr1).le
  calc dyadicD r ^ shortExp ζ ≤ (2 * r ^ 2) ^ shortExp ζ := Real.rpow_le_rpow hd0 hlt ha.le
    _ ≤ (c ^ (1 / shortExp ζ)) ^ shortExp ζ :=
        Real.rpow_le_rpow (by positivity) hrc ha.le
    _ = c := by rw [← Real.rpow_mul hc0.le, one_div_mul_cancel ha.ne', Real.rpow_one]

/-- **Gap at `ρmesh = rhoCell68 ρ`** (copy of `hgapShell_of_pow_le`, ShellCoreCG68.lean:187). From
`d ^ shortExp ζ ≤ (rhoCell68 ρ - ρ)/4`, `0 < d ≤ 1` and `ζ < 1/2`:
`2 * (d/100) + 2 * d ^ shortExp ζ ≤ rhoCell68 ρ - ρ`, using `d ≤ d ^ shortExp ζ` (`shortExp ζ ≤ 1`). -/
theorem gap_of_pow_le {ρ ζ d : ℝ} (hζ1 : ζ < 1 / 2) (hd0 : 0 < d)
    (hd1 : d ≤ 1) (hsmall : d ^ shortExp ζ ≤ (Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4) :
    2 * (d / 100) + 2 * d ^ shortExp ζ ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hda : d ≤ d ^ shortExp ζ := by
    have h := Real.rpow_le_rpow_of_exponent_ge hd0 hd1 ha1
    rwa [Real.rpow_one] at h
  have hdef : Lemma68HoneCellGood.rhoCell68 ρ = (1 + ρ) / 2 := rfl
  rw [hdef] at hsmall ⊢
  linarith

/-- **Small-radius power of `dyadicD`.** For `0 < ζ` and `0 < c` there is `r₀ > 0` with
`dyadicD r ^ shortExp ζ < c` for `0 < r < r₀`. The proof takes `r₀ = min 1 ((c/2)^(1/shortExp ζ) / 2)`
and uses `dyadicD_pow_le_sq` at the level `c/2`. -/
theorem exists_dyadicD_pow_lt {ζ c : ℝ} (hζ0 : 0 < ζ) (hc : 0 < c) :
    ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ → dyadicD r ^ shortExp ζ < c := by
  have ha : 0 < shortExp ζ := by unfold shortExp; linarith
  have hc2 : 0 < c / 2 := by linarith
  have hp : 0 < (c / 2) ^ (1 / shortExp ζ) := Real.rpow_pos_of_pos hc2 _
  refine ⟨min 1 ((c / 2) ^ (1 / shortExp ζ) / 2), lt_min one_pos (half_pos hp),
    fun r hr0 hr => ?_⟩
  have hr1 : r ≤ 1 := (lt_of_lt_of_le hr (min_le_left _ _)).le
  have hr2 : r < (c / 2) ^ (1 / shortExp ζ) / 2 := lt_of_lt_of_le hr (min_le_right _ _)
  have hsq : r ^ 2 ≤ r := by nlinarith
  have hrc : 2 * r ^ 2 ≤ (c / 2) ^ (1 / shortExp ζ) := by linarith
  have hle := dyadicD_pow_le_sq hr0 hr1 hζ0 hc2 hrc
  linarith

/-- **`hcutR` at small radius.** `dyadicD r ^ shortExp ζ < rhoCell68 ρ - ρ` for `0 < r < r₀`
(`rhoCell68 ρ - ρ = (1 - ρ)/2 > 0`). -/
theorem shellSmallR_hcutR {ρ ζ : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) :
    ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ →
      dyadicD r ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
  have hc : 0 < Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
    unfold Lemma68HoneCellGood.rhoCell68; linarith
  exact exists_dyadicD_pow_lt hζ0 hc

/-- **`hgapShell` at small radius** (ShellBallLoc68 antecedent with `ρmesh := rhoCell68 ρ`):
`2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ rhoCell68 ρ - ρ` for `0 < r < r₀`.
The threshold is that of `exists_dyadicD_pow_lt` at the level `(rhoCell68 ρ - ρ)/4`, and the
inequality is `gap_of_pow_le`. -/
theorem shellSmallR_hgapShell {ρ ζ : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) :
    ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ →
      2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
  have hc : 0 < (Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4 := by
    unfold Lemma68HoneCellGood.rhoCell68; linarith
  obtain ⟨r₀, hr₀, h⟩ := exists_dyadicD_pow_lt hζ0 hc
  exact ⟨r₀, hr₀, fun r hr0 hr =>
    gap_of_pow_le hζ1 (dyadicD_pos r) (dyadicD_le_one r)
      (h r hr0 hr).le⟩

/-- **`hrρ` at small radius:** `r ≤ ρ / 4` for `0 < r < ρ / 4` (B1Assembly68 binder `hrρ`). -/
theorem shellSmallR_hrRho {ρ : ℝ} (hρ0 : 0 < ρ) :
    ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ → r ≤ ρ / 4 :=
  ⟨ρ / 4, by linarith, fun _ _ hr => hr.le⟩

/-- **`hrz` at small radius:** `r ≤ countThreshold ζ` for `0 < r < countThreshold ζ`
(B1Assembly68 binder `hrz`). The threshold `countThreshold ζ = (2^(-shortExp ζ)/4000)^(1/ζ)` is positive. -/
theorem shellSmallR_hrz {ζ : ℝ} :
    ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ → r ≤ countThreshold ζ := by
  have hpos : 0 < countThreshold ζ := by
    unfold countThreshold
    exact Real.rpow_pos_of_pos (by positivity) _
  exact ⟨countThreshold ζ, hpos, fun _ _ hr => hr.le⟩

/-- **`_hRA` at small radius:** `r ≤ rAmp q0 ζ` for `0 < r < rAmp q0 ζ` (B1Assembly68 binder `_hRA`).
`rAmp q0 ζ = min 1 ((q0/200 · ζ²/(16 log 2))^(2/ζ))` is positive for `0 < q0` and `0 < ζ`. -/
theorem shellSmallR_hRA {q0 ζ : ℝ} (hq0 : 0 < q0) (hζ0 : 0 < ζ) :
    ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ → r ≤ Lemma68Cutoff.rAmp q0 ζ := by
  have hb : 0 < q0 / 200 * ζ ^ 2 / (16 * Real.log 2) :=
    div_pos (mul_pos (div_pos hq0 (by norm_num)) (pow_pos hζ0 2))
      (mul_pos (by norm_num) (Real.log_pos one_lt_two))
  have hpos : 0 < Lemma68Cutoff.rAmp q0 ζ := by
    unfold Lemma68Cutoff.rAmp
    exact lt_min one_pos (Real.rpow_pos_of_pos hb _)
  exact ⟨Lemma68Cutoff.rAmp q0 ζ, hpos, fun _ _ hr => hr.le⟩

/-- **Conjunction of the r-small binders.** For fixed `0 < ρ < 1`, `0 < ζ < 1/2`, `0 < q0`, there is
`r₀ > 0` such that every `0 < r < r₀` satisfies the five deterministic binders at once:
`hcutR`, `hgapShell` (with `ρmesh := rhoCell68 ρ`), `hrρ`, `hrz`, `_hRA`. -/
theorem shellSmallR_all {ρ ζ q0 : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hq0 : 0 < q0) :
    ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ →
      dyadicD r ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ ∧
      2 * (dyadicD r / 100) + 2 * dyadicD r ^ shortExp ζ ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ ∧
      r ≤ ρ / 4 ∧ r ≤ countThreshold ζ ∧ r ≤ Lemma68Cutoff.rAmp q0 ζ := by
  obtain ⟨a, ha, ha'⟩ := shellSmallR_hcutR hρ1 hζ0
  obtain ⟨b, hb, hb'⟩ := shellSmallR_hgapShell hρ1 hζ0 hζ1
  obtain ⟨c, hc, hc'⟩ := shellSmallR_hrRho hρ0
  obtain ⟨d, hd, hd'⟩ := shellSmallR_hrz (ζ := ζ)
  obtain ⟨e, he, he'⟩ := shellSmallR_hRA hq0 hζ0
  refine ⟨min (min (min a b) (min c d)) e,
    lt_min (lt_min (lt_min ha hb) (lt_min hc hd)) he, fun r hr0 hr => ?_⟩
  have h1 : r < a := lt_of_lt_of_le hr
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have h2 : r < b := lt_of_lt_of_le hr
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have h3 : r < c := lt_of_lt_of_le hr
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h4 : r < d := lt_of_lt_of_le hr
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have h5 : r < e := lt_of_lt_of_le hr (min_le_right _ _)
  exact ⟨ha' r hr0 h1, hb' r hr0 h2, hc' r hr0 h3, hd' r hr0 h4, he' r hr0 h5⟩

end Lemma68ShellSmallR
end MatedCRT

#print axioms MatedCRT.Lemma68ShellSmallR.exists_dyadicD_pow_lt
#print axioms MatedCRT.Lemma68ShellSmallR.shellSmallR_hcutR
#print axioms MatedCRT.Lemma68ShellSmallR.shellSmallR_hgapShell
#print axioms MatedCRT.Lemma68ShellSmallR.shellSmallR_hrRho
#print axioms MatedCRT.Lemma68ShellSmallR.shellSmallR_hrz
#print axioms MatedCRT.Lemma68ShellSmallR.shellSmallR_hRA
#print axioms MatedCRT.Lemma68ShellSmallR.shellSmallR_all
