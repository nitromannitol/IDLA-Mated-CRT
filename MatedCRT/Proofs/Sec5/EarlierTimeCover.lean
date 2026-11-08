import HarmonicBalls.Proofs.Sec5.CountableTimeMeasurability
import MatedCRT.Defs.Setting

/-!
# Earlier-time compact covers of the cluster family (E-c1-5, Section 5.1 route)

Formalizes the written conditional argument of `docs/campaign/GAPS-SEC2567A.md`, entry `E-c1-5`, paragraph at line 257
("One such property is exactly the strict obstacle gap ..."): if the raw cluster `C_t = cluster μ ρ 0 t` contains
`Λ_t` at one fixed target time `t`, then every compact `K ⊆ Λ_t` lies in `Λ_q` for a single rational `q ∈ (0, t)`.

Rational-time input (read-only): `HarmonicBalls.mem_cluster_exists_earlier_rat`
(`../Harmonic-Balls-LQG/HarmonicBalls/Proofs/Sec5/CountableTimeMeasurability.lean:30`).

Fixed-time inputs are explicit hypotheses, never proved here:
* `hgap : Λ t ⊆ cluster μ ρ 0 t` (only at the target time `t`; the strict obstacle gap at `t`);
* `hloc : ∀ s, 0 < s → s < t → cluster μ ρ 0 s ⊆ Λ s` (local characterization at earlier times; see
  `cluster_subset_of_obstacle` for its derivation from openness of the cluster and the obstacle identity);
* `hopen`, `hmono` (or `IsConeHarmonicBallFamily μ Λ`, which supplies them).

No strict-growth statement `closure (Λ s) ⊆ Λ t` for `s < t` is assumed or used.
-/

namespace MatedCRT

open MeasureTheory Set HarmonicBalls

namespace EarlierTimeCover

variable {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {ρ t : ℝ} {K : Set ℂ}

/-- The positive rationals below `T`: the index set of the earlier-time covers. -/
abbrev PosRatBelow (T : ℝ) : Type := {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < T}

/-- Local characterization from the obstacle identity. If the raw cluster `C` is open and
`Λs = int (cl C)` (the identity in `SatisfiesObstacleCharacterization`, `MatedCRT/Defs/Setting.lean:257`),
then `C ⊆ Λs`. Openness of the cluster under volume growth is `HarmonicBalls.isOpen_cluster_of_volumeGrowth`
(`HarmonicBalls/Proofs/Sec5/GeneralDomainClusterOpen.lean:62`). -/
theorem cluster_subset_of_obstacle {C Λs : Set ℂ} (hC : IsOpen C) (hΛ : Λs = interior (closure C)) :
    C ⊆ Λs := by
  rw [hΛ]
  exact interior_maximal subset_closure hC

/-- Pointwise step: a point of the fixed-time set `Λ t` lies in `Λ q` for some rational `q ∈ (0, t)`. -/
theorem exists_rat_mem_of_mem_fixedTime (ht : 0 < t) (hgap : Λ t ⊆ cluster μ ρ 0 t)
    (hloc : ∀ s : ℝ, 0 < s → s < t → cluster μ ρ 0 s ⊆ Λ s) {x : ℂ} (hx : x ∈ Λ t) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < t ∧ x ∈ Λ (q : ℝ) := by
  obtain ⟨q, hq0, hqt, hxq⟩ := mem_cluster_exists_earlier_rat ht (hgap hx)
  exact ⟨q, hq0, hqt, hloc q hq0 hqt hxq⟩

/-- **Earlier-time compact cover.** Let `0 < t`, and assume the fixed-time inclusion `Λ t ⊆ cluster μ ρ 0 t` (`hgap`),
the local characterization `cluster μ ρ 0 s ⊆ Λ s` for `0 < s < t` (`hloc`), openness of `Λ s` for `0 < s < t`
(`hopen`), and monotonicity `Λ s ⊆ Λ u` for `0 < s ≤ u < t` (`hmono`). Then every compact `K ⊆ Λ t` lies in `Λ q` for one
rational `q` with `0 < q < t`. The index set `PosRatBelow t` is nonempty by density, which also covers `K = ∅`. -/
theorem exists_rat_lt_subset_of_isCompact (ht : 0 < t) (hK : IsCompact K) (hKΛ : K ⊆ Λ t)
    (hgap : Λ t ⊆ cluster μ ρ 0 t)
    (hloc : ∀ s : ℝ, 0 < s → s < t → cluster μ ρ 0 s ⊆ Λ s)
    (hopen : ∀ s : ℝ, 0 < s → s < t → IsOpen (Λ s))
    (hmono : ∀ s u : ℝ, 0 < s → s ≤ u → u < t → Λ s ⊆ Λ u) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < t ∧ K ⊆ Λ (q : ℝ) := by
  have hne : Nonempty (PosRatBelow t) := by
    obtain ⟨q, hq0, hqt⟩ := exists_rat_btwn ht
    exact ⟨⟨q, hq0, hqt⟩⟩
  have hsU : K ⊆ ⋃ i : PosRatBelow t, Λ (i.1 : ℝ) := by
    intro x hx
    obtain ⟨q, hq0, hqt, hxq⟩ := exists_rat_mem_of_mem_fixedTime ht hgap hloc (hKΛ hx)
    exact mem_iUnion.2 ⟨⟨q, hq0, hqt⟩, hxq⟩
  have hdU : Directed (· ⊆ ·) fun i : PosRatBelow t => Λ (i.1 : ℝ) := by
    intro i j
    rcases le_total i.1 j.1 with h | h
    · exact ⟨j, hmono _ _ i.2.1 (by exact_mod_cast h) j.2.2, subset_rfl⟩
    · exact ⟨i, subset_rfl, hmono _ _ j.2.1 (by exact_mod_cast h) i.2.2⟩
  obtain ⟨i, hi⟩ := hK.elim_directed_cover (fun i : PosRatBelow t => Λ (i.1 : ℝ))
    (fun i => hopen _ i.2.1 i.2.2) hsU hdU
  exact ⟨i.1, i.2.1, i.2.2, hi⟩

/-- The same conclusion for a cone family `IsConeHarmonicBallFamily μ Λ`. Openness of each `Λ s` is the `IsOpen`
field of `IsHarmonicBall` (`HarmonicBalls/Defs/HarmonicBall.lean:79`), and monotonicity is the field `monotoneOn` of
`SatisfiesHarmonicBallConditions` (`HarmonicBalls/Draft/Section1.lean:58`). The fixed-time inclusion `hgap` and the
local characterization `hloc` stay explicit hypotheses. -/
theorem exists_rat_lt_subset_of_isCompact_of_family (hfam : IsConeHarmonicBallFamily μ Λ) (ht : 0 < t)
    (hK : IsCompact K) (hKΛ : K ⊆ Λ t) (hgap : Λ t ⊆ cluster μ ρ 0 t)
    (hloc : ∀ s : ℝ, 0 < s → s < t → cluster μ ρ 0 s ⊆ Λ s) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < t ∧ K ⊆ Λ (q : ℝ) := by
  obtain ⟨hH, hcond, -⟩ := hfam
  exact exists_rat_lt_subset_of_isCompact ht hK hKΛ hgap hloc
    (fun s hs _ => (hH s hs).1)
    (fun s u hs hsu _ => hcond.monotoneOn (Set.mem_Ioi.2 hs) (Set.mem_Ioi.2 (hs.trans_le hsu)) hsu)

end EarlierTimeCover

end MatedCRT
