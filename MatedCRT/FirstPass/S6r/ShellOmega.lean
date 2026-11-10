import MatedCRT.Defs.Map
import MatedCRT.FirstPass.S6r.Shells.Parameters

/-!
# Lemma 6.8, S8' on path space: the shell times `T k`, `L k` as stopping times

Source: `notes/fp-gaps/CHATGPT-idla-6-8-redesign-PRO.md` step 12 (l.634-679) and notes (7.33)-(7.35).
Path space `Ω = ℕ → ℤ` with the coordinate filtration `coordFiltration` (`WalkBridge68.lean:33`).

All shell times are `ℕ∞`-valued path functionals, `⊤` when the event never occurs:
* `shellHit k x` is the first hit `C_{k+1}` of the shell `Σ_{k+1}` (notes (7.20); `⊤` if no hit, unlike the
  junk value `0` of `firstShellHit`);
* `shellCentre k x = Q_d(η(x C_{k+1}))` is the grid centre `z_k` of step 5;
* `shellExit k x` is the first exit `T_k` of `I(B_{4R/3}(z_k))` at or after `C_{k+1}` (notes (7.33));
* `testEnd k x` is the first exit `L_k` of the local disk `B_{R/4}(η(x T_k))` at or after `T_k` (notes (7.35)).

Main results: each functional is prefix-local (its sublevel sets `{F ≤ n}` and its values there depend only on
`x 0, …, x n`); the stopping-time forms `IsStoppingTime coordFiltration` are in `ShellOmegaStop.lean`.
-/

namespace MatedCRT
namespace Lemma68Omega

open Set Metric MeasureTheory
open Lemma68Window
open scoped Classical

open Classical in
/-- The first time `m` with `P m`, as an element of `ℕ∞`, and `⊤` if there is none (the convention of
`vExitTime`). -/
noncomputable def firstTime (P : ℕ → Prop) : ℕ∞ :=
  if h : ∃ m, P m then ((Nat.find h : ℕ) : ℕ∞) else ⊤

lemma firstTime_le_iff (P : ℕ → Prop) (n : ℕ) : firstTime P ≤ n ↔ ∃ m ≤ n, P m := by
  unfold firstTime
  split_ifs with h
  · constructor
    · intro hle
      exact ⟨Nat.find h, by exact_mod_cast hle, Nat.find_spec h⟩
    · rintro ⟨m, hm, hPm⟩
      exact_mod_cast (Nat.find_min' h hPm).trans hm
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨m, -, hPm⟩
      exact absurd ⟨m, hPm⟩ h

lemma toNat_le_of_le_nat {c : ℕ∞} {m : ℕ} (h : c ≤ m) : c.toNat ≤ m := by
  have hne : c ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top m) h
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hne
  rw [ENat.toNat_natCast]
  exact_mod_cast h

/-- If `P` and `Q` agree up to `m` and `Q` is reached by time `m`, then `P` is reached no later than `Q`. -/
lemma firstTime_le_of_congr {P Q : ℕ → Prop} {m : ℕ} (hPQ : ∀ k ≤ m, (P k ↔ Q k))
    (hQ : firstTime Q ≤ m) : firstTime P ≤ firstTime Q := by
  have hne : firstTime Q ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top m) hQ
  have hb : firstTime Q = ((firstTime Q).toNat : ℕ∞) := (ENat.natCast_toNat hne).symm
  have hbm : (firstTime Q).toNat ≤ m := toNat_le_of_le_nat hQ
  obtain ⟨k, hk, hQk⟩ := (firstTime_le_iff Q (firstTime Q).toNat).1 hb.le
  have hPk : P k := (hPQ k (le_trans hk hbm)).2 hQk
  rw [hb]
  exact (firstTime_le_iff P _).2 ⟨k, hk, hPk⟩

lemma firstTime_congr {P Q : ℕ → Prop} {m : ℕ} (hPQ : ∀ k ≤ m, (P k ↔ Q k))
    (hle : firstTime P ≤ m) : firstTime P = firstTime Q := by
  have hQle : firstTime Q ≤ m := by
    obtain ⟨k, hk, hPk⟩ := (firstTime_le_iff P m).1 hle
    exact (firstTime_le_iff Q m).2 ⟨k, hk, (hPQ k hk).1 hPk⟩
  exact le_antisymm (firstTime_le_of_congr hPQ hQle)
    (firstTime_le_of_congr (fun k hk => (hPQ k hk).symm) hle)

/-- A path functional is prefix-local: up to time `m ≤ n` its sublevel sets and its values depend only on
`x 0, …, x n`. -/
def PrefixLocal (F : (ℕ → ℤ) → ℕ∞) : Prop :=
  ∀ (n : ℕ) (x y : ℕ → ℤ), (∀ j ≤ n, x j = y j) → ∀ m ≤ n,
    (F x ≤ m ↔ F y ≤ m) ∧ (F x ≤ m → F x = F y)

/-- A first-time functional of a family of predicates that are prefix-determined is prefix-local. -/
lemma prefixLocal_firstTime {P : (ℕ → ℤ) → ℕ → Prop}
    (hP : ∀ (n : ℕ) (x y : ℕ → ℤ), (∀ j ≤ n, x j = y j) → ∀ m ≤ n, (P x m ↔ P y m)) :
    PrefixLocal (fun x => firstTime (P x)) := by
  intro n x y hxy m hm
  have hiff : firstTime (P x) ≤ m ↔ firstTime (P y) ≤ m := by
    rw [firstTime_le_iff, firstTime_le_iff]
    constructor
    · rintro ⟨k, hk, hPk⟩
      exact ⟨k, hk, (hP n x y hxy k (hk.trans hm)).1 hPk⟩
    · rintro ⟨k, hk, hPk⟩
      exact ⟨k, hk, (hP n x y hxy k (hk.trans hm)).2 hPk⟩
  refine ⟨hiff, fun hle => ?_⟩
  exact firstTime_congr (fun k hk => hP n x y hxy k (hk.trans hm)) hle

/-! ### The shell times on path space -/

variable (ε : ℝ) (η : ℝ → ℂ) (K : Set ℂ) (r s d : ℝ) (R : ℂ → ℝ)

/-- Notes (7.20), `ℕ∞`-valued: the first hit `C_{k+1}` of the shell `Σ_{k+1}` (`⊤` if never). -/
noncomputable def shellHit (k : ℕ) (x : ℕ → ℤ) : ℕ∞ :=
  firstTime (fun m => (cell ε η (x m) ∩ twoSidedShell K r (shellOffset s (k + 1))).Nonempty)

/-- The grid centre `z_k = Q_d(η(X_{C_{k+1}}))` of step 5 (notes (7.23)); junk value when `C_{k+1} = ⊤`. -/
noncomputable def shellCentre (k : ℕ) (x : ℕ → ℤ) : ℂ :=
  gridRound (d / 100) (vertexPoint ε η (x (shellHit ε η K r s k x).toNat))

/-- Notes (7.33), PRO step 12: the first exit `T_k` of `I(B_{4R/3}(z_k))` at or after the hit `C_{k+1}`. -/
noncomputable def shellExit (k : ℕ) (x : ℕ → ℤ) : ℕ∞ :=
  firstTime (fun m => shellHit ε η K r s k x ≤ (m : ℕ∞) ∧
    x m ∉ interiorCellVertices ε η (ball (shellCentre ε η K r s d k x) (4 * R (shellCentre ε η K r s d k x) / 3)))

/-- Notes (7.35): the test end `L_k`, the first exit of the local disk `B_{R/4}(η(X_{T_k}))` at or after `T_k`. -/
noncomputable def testEnd (k : ℕ) (x : ℕ → ℤ) : ℕ∞ :=
  firstTime (fun m => shellExit ε η K r s d R k x ≤ (m : ℕ∞) ∧
    x m ∉ interiorCellVertices ε η (ball (vertexPoint ε η (x (shellExit ε η K r s d R k x).toNat))
      (R (shellCentre ε η K r s d k x) / 4)))

lemma shellHit_prefixLocal (k : ℕ) : PrefixLocal (shellHit ε η K r s k) := by
  refine prefixLocal_firstTime (P := fun x m => (cell ε η (x m) ∩ twoSidedShell K r (shellOffset s (k + 1))).Nonempty)
    (fun n x y hxy m hm => ?_)
  rw [hxy m hm]

lemma shellCentre_congr {n m k : ℕ} {x y : ℕ → ℤ} (hxy : ∀ j ≤ n, x j = y j) (hm : m ≤ n)
    (hh : shellHit ε η K r s k x ≤ (m : ℕ∞)) :
    shellCentre ε η K r s d k x = shellCentre ε η K r s d k y := by
  have hval : shellHit ε η K r s k x = shellHit ε η K r s k y :=
    ((shellHit_prefixLocal ε η K r s k) n x y hxy m hm).2 hh
  have hc : (shellHit ε η K r s k y).toNat ≤ n :=
    (toNat_le_of_le_nat (by rw [← hval]; exact hh)).trans hm
  unfold shellCentre
  rw [hval, hxy _ hc]

lemma shellHit_le_of_exit {k m : ℕ} {x : ℕ → ℤ}
    (h : shellExit ε η K r s d R k x ≤ (m : ℕ∞)) : shellHit ε η K r s k x ≤ (m : ℕ∞) := by
  unfold shellExit at h
  obtain ⟨j, hj, hj'⟩ := (firstTime_le_iff _ m).1 h
  exact le_trans hj'.1 (by exact_mod_cast hj)

/-- The exit `T_k` is prefix-local: the exit predicate at time `m` reads only `x 0, …, x m` and the centre. -/
lemma shellExit_prefixLocal (k : ℕ) : PrefixLocal (shellExit ε η K r s d R k) := by
  refine prefixLocal_firstTime (P := fun x m => shellHit ε η K r s k x ≤ (m : ℕ∞) ∧
    x m ∉ interiorCellVertices ε η (ball (shellCentre ε η K r s d k x) (4 * R (shellCentre ε η K r s d k x) / 3)))
    (fun n x y hxy m hm => ?_)
  have hiff := (shellHit_prefixLocal ε η K r s k n x y hxy m hm).1
  by_cases hh : shellHit ε η K r s k x ≤ (m : ℕ∞)
  · have hh' : shellHit ε η K r s k y ≤ (m : ℕ∞) := hiff.1 hh
    rw [shellCentre_congr ε η K r s d hxy hm hh, hxy m hm]
    exact ⟨fun h => ⟨hh', h.2⟩, fun h => ⟨hh, h.2⟩⟩
  · have hh' : ¬ shellHit ε η K r s k y ≤ (m : ℕ∞) := fun h => hh (hiff.2 h)
    exact ⟨fun h => absurd h.1 hh, fun h => absurd h.1 hh'⟩

/-- The test end `L_k` is prefix-local (its centre `x T_k` is read at a time `≤ m ≤ n`). -/
lemma testEnd_prefixLocal (k : ℕ) : PrefixLocal (testEnd ε η K r s d R k) := by
  refine prefixLocal_firstTime (P := fun x m => shellExit ε η K r s d R k x ≤ (m : ℕ∞) ∧
    x m ∉ interiorCellVertices ε η (ball (vertexPoint ε η (x (shellExit ε η K r s d R k x).toNat))
      (R (shellCentre ε η K r s d k x) / 4)))
    (fun n x y hxy m hm => ?_)
  have hiff := (shellExit_prefixLocal ε η K r s d R k n x y hxy m hm).1
  by_cases hh : shellExit ε η K r s d R k x ≤ (m : ℕ∞)
  · have hh' : shellExit ε η K r s d R k y ≤ (m : ℕ∞) := hiff.1 hh
    have hval : shellExit ε η K r s d R k x = shellExit ε η K r s d R k y :=
      ((shellExit_prefixLocal ε η K r s d R k) n x y hxy m hm).2 hh
    have hc : (shellExit ε η K r s d R k y).toNat ≤ n := (toNat_le_of_le_nat hh').trans hm
    have hcen : shellCentre ε η K r s d k x = shellCentre ε η K r s d k y :=
      shellCentre_congr ε η K r s d hxy hm (shellHit_le_of_exit ε η K r s d R hh)
    have hpt : vertexPoint ε η (x (shellExit ε η K r s d R k x).toNat) =
        vertexPoint ε η (y (shellExit ε η K r s d R k y).toNat) := by
      rw [hval, hxy _ hc]
    rw [hpt, hcen, hxy m hm]
    exact ⟨fun h => ⟨hh', h.2⟩, fun h => ⟨hh, h.2⟩⟩
  · have hh' : ¬ shellExit ε η K r s d R k y ≤ (m : ℕ∞) := fun h => hh (hiff.2 h)
    exact ⟨fun h => absurd h.1 hh, fun h => absurd h.1 hh'⟩

end Lemma68Omega
end MatedCRT
