import MatedCRT.FirstPass.S6r.ShellOmegaStop
import MatedCRT.FirstPass.S6r.OneTest.SrwStrongMarkov
import MatedCRT.FirstPass.S6r.Shells.Choice

/-!
# First pass: the shell parameter `ρ_k` is measurable for the stopping-time σ-algebra of `T_k`

The parametric one-test (`MatedCRT/FirstPass/S6r/OneTest/ExitQHone.lean`, hypothesis `hρ`) needs, for the paper's shell
parameters, that `ρ_k : (ℕ → ℤ) → ℝ × ℂ` be `𝓕_{T_k}`-measurable, where `T_k` is the shell exit of `ShellOmega`
(`shellExit`) and `ρ_k` is the pair (radius, centre) chosen at the shell hit `C_{k+1}` (`shellHit`).

Route. The centre `z_k = shellCentre k x = Q_{d/100}(η(x_{C_{k+1}}))` depends on the path only through the value of the
coordinate process at the stopping time `C_{k+1}`; the radius `R z_k` is a function of `z_k`. Let `H : ℤ → ℝ × ℂ` be the index
map `j ↦ (R (Q_{d/100}(η j)), Q_{d/100}(η j))`. Then `ρ_k x = H (x_{C_{k+1}})`, and:
* `x ↦ x (C x).toNat` is `𝓕_C`-measurable (`measurable_coord_toNat_stop`): on `{C < ⊤}` it is the indicator of
  `measurable_stopped_indicator` (`SrwStrongMarkov.lean`), on `{C = ⊤}` it is `x 0` (`(⊤ : ℕ∞).toNat = 0`), and `x 0` is
  `𝓕_C`-measurable (`measurable_coord_zero_stop`); `{C < ⊤}` is `𝓕_C`-measurable (`measurableSet_lt_top_stop`).
* `C_{k+1} ≤ T_k` pointwise (`shellHit_le_shellExit`, from the definition of `shellExit` as a first time), so
  `𝓕_{C_{k+1}} ≤ 𝓕_{T_k}` (`IsStoppingTime.measurableSpace_mono`).

Identification. The parameter is built from `ShellOmega.shellCentre` and `R` exactly as `shellExit` and `testEnd`
use them. The total choices `shellCentreAt` / `shellRadiusAt` of `Shells/Choice.lean` differ from those of `ShellOmega` (default `0` for the
centre and `d` for the radius at a missing hit; grid `g` instead of `d/100`; `firstShellHit` instead of `shellHit`), so they are
not used for `ρ_k`. The variant `shellParamAt` with `shellRadiusAt` is also proved measurable, for the case that the eligibility default in the radius is wanted (this would also require changing `shellExit` to the same radius).
-/

namespace MatedCRT
namespace Lemma68ShellParam

open MeasureTheory Set Metric
open Lemma68Window Lemma68WalkBridge Lemma68Omega Lemma68OmegaStop
open scoped Classical

variable (ε : ℝ) (η : ℝ → ℂ) (K : Set ℂ) (r s d : ℝ) (R : ℂ → ℝ)

/-- The index map of the shell centre: `j ↦ (R z, z)` with `z = Q_{d/100}(η(j))` the grid centre of the vertex point of the
cell with index `j` (the centre of `shellCentre`, notes (7.23)); `R z` is the good radius of notes (7.33). -/
noncomputable def shellParamOfIndex (j : ℤ) : ℝ × ℂ :=
  (R (gridRound (d / 100) (vertexPoint ε η j)), gridRound (d / 100) (vertexPoint ε η j))

/-- The shell parameter `ρ_k = (R z_k, z_k)` at the shell hit `C_{k+1}`, with `z_k = shellCentre k` (ShellOmega). -/
noncomputable def shellParam (k : ℕ) (x : ℕ → ℤ) : ℝ × ℂ :=
  (R (shellCentre ε η K r s d k x), shellCentre ε η K r s d k x)

/-- The variant with the eligibility default of `shellRadiusAt` (Shells/Choice.lean) in the radius. -/
noncomputable def shellParamAt (Elig : ℂ → Prop) (dflt : ℝ) (k : ℕ) (x : ℕ → ℤ) : ℝ × ℂ :=
  (shellRadiusAt R Elig dflt (shellCentre ε η K r s d k x), shellCentre ε η K r s d k x)

/-- For a `ℕ∞`-valued stopping time `C` of the coordinates, `x_0` is `𝓕_C`-measurable. -/
theorem measurable_coord_zero_stop {C : (ℕ → ℤ) → ℕ∞} (hC : IsStoppingTime coordFiltration C) :
    Measurable[hC.measurableSpace] (fun x : ℕ → ℤ => x 0) := by
  intro B hB
  rw [hC.measurableSet]
  refine ⟨?_, fun i => ?_⟩
  · exact (le_iSup (fun t => coordFiltration t) 0) _ (coord_measurable 0 hB)
  · exact ((coordFiltration.mono (Nat.zero_le i)) _ (coord_measurable 0 hB)).inter (hC i)

/-- For a `ℕ∞`-valued stopping time `C` of the coordinates, `{C < ⊤}` is `𝓕_C`-measurable. -/
theorem measurableSet_lt_top_stop {C : (ℕ → ℤ) → ℕ∞} (hC : IsStoppingTime coordFiltration C) :
    MeasurableSet[hC.measurableSpace] {w : ℕ → ℤ | C w < ⊤} := by
  rw [hC.measurableSet]
  refine ⟨?_, fun i => ?_⟩
  · have hEq : {w : ℕ → ℤ | C w < ⊤} = ⋃ i : ℕ, {w : ℕ → ℤ | C w ≤ (i : ℕ∞)} := by
      ext w
      simp only [Set.mem_ofPred_eq, mem_iUnion]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt h)
        exact ⟨n, le_of_eq hn.symm⟩
      · rintro ⟨i, hi⟩
        exact lt_of_le_of_lt hi (ENat.natCast_lt_top i)
    rw [hEq]
    exact MeasurableSet.iUnion fun i => (le_iSup (fun t => coordFiltration t) i) _ (hC i)
  · convert hC i using 1
    ext w
    exact ⟨fun h => h.2, fun h => ⟨lt_of_le_of_lt h (WithTop.coe_lt_top i), h⟩⟩

/-- For a `ℕ∞`-valued stopping time `C` of the coordinates and any index map `H : ℤ → β`, the map
`x ↦ H (x_{C}) = H (x (C x).toNat)` is `𝓕_C`-measurable. On `{C = ⊤}` the value is `H (x 0)`, since `(⊤ : ℕ∞).toNat = 0`. -/
theorem measurable_coord_toNat_stop {C : (ℕ → ℤ) → ℕ∞} (hC : IsStoppingTime coordFiltration C)
    {β : Type*} [MeasurableSpace β] [Zero β] (H : ℤ → β) :
    Measurable[hC.measurableSpace] (fun x : ℕ → ℤ => H (x (C x).toNat)) := by
  have hind : Measurable[hC.measurableSpace]
      (fun w : ℕ → ℤ => {w : ℕ → ℤ | C w < ⊤}.indicator (fun w => H (w (C w).toNat)) w) :=
    measurable_stopped_indicator hC H
  have hzero : Measurable[hC.measurableSpace] (fun x : ℕ → ℤ => H (x 0)) :=
    (measurable_of_countable H).comp (measurable_coord_zero_stop hC)
  have key : (fun x : ℕ → ℤ => H (x (C x).toNat)) =
      fun x => if C x < ⊤ then {w : ℕ → ℤ | C w < ⊤}.indicator (fun w => H (w (C w).toNat)) x
        else H (x 0) := by
    funext x
    by_cases h : C x < ⊤
    · simp only [h, ↓reduceIte]
      rw [Set.indicator_of_mem (show x ∈ {w : ℕ → ℤ | C w < ⊤} from h)]
    · have htop : C x = ⊤ := top_le_iff.mp (not_lt.mp h)
      simp only [h, ↓reduceIte]
      rw [htop, ENat.toNat_top]
  rw [key]
  exact Measurable.ite (measurableSet_lt_top_stop hC) hind hzero

/-- Pointwise: the shell hit `C_{k+1}` precedes the shell exit `T_k` (both `⊤` together when there is no hit). -/
theorem shellHit_le_shellExit (k : ℕ) (x : ℕ → ℤ) :
    shellHit ε η K r s k x ≤ shellExit ε η K r s d R k x := by
  unfold shellExit firstTime
  split_ifs with h
  · convert (Nat.find_spec h).1
  · exact le_top

/-- The shell parameter is `H` composed with the coordinate at the shell hit `C_{k+1}`. -/
theorem shellParam_eq_index (k : ℕ) (x : ℕ → ℤ) :
    shellParam ε η K r s d R k x = shellParamOfIndex ε η d R (x (shellHit ε η K r s k x).toNat) :=
  rfl

/-- The shell parameter `ρ_k = (R z_k, z_k)` is measurable for the stopping-time σ-algebra of the shell exit `T_k`. -/
theorem measurable_shellParam_stopped_at (k : ℕ) :
    Measurable[(isStoppingTime_shellExit ε η K r s d R k).measurableSpace]
      (shellParam ε η K r s d R k) := by
  have hC : IsStoppingTime coordFiltration (shellHit ε η K r s k) := isStoppingTime_shellHit ε η K r s k
  have hT : IsStoppingTime coordFiltration (shellExit ε η K r s d R k) :=
    isStoppingTime_shellExit ε η K r s d R k
  have hle : shellHit ε η K r s k ≤ shellExit ε η K r s d R k := fun x => shellHit_le_shellExit ε η K r s d R k x
  have h1 : Measurable[hC.measurableSpace]
      (fun x : ℕ → ℤ => shellParamOfIndex ε η d R (x (shellHit ε η K r s k x).toNat)) :=
    measurable_coord_toNat_stop hC (shellParamOfIndex ε η d R)
  have h2 : Measurable[hT.measurableSpace]
      (fun x : ℕ → ℤ => shellParamOfIndex ε η d R (x (shellHit ε η K r s k x).toNat)) :=
    h1.mono (hC.measurableSpace_mono hT hle) le_rfl
  exact h2

/-- **The shell parameter for the parametric one-test** (`hρ` of `hone_exitQ_of_param_family`, `ExitQHone.lean`): for every
`k`, `ρ_k = (radius, centre)` chosen at the shell hit `C_{k+1}` is `𝓕_{T_k}`-measurable, where `T_k = shellExit k`. -/
theorem measurable_shellParam_stopped :
    ∀ k : ℕ, Measurable[(isStoppingTime_shellExit ε η K r s d R k).measurableSpace]
      (shellParam ε η K r s d R k) :=
  fun k => measurable_shellParam_stopped_at ε η K r s d R k

/-- The variant with `shellRadiusAt` (eligibility default `dflt` at an ineligible centre): also `𝓕_{T_k}`-measurable. -/
theorem measurable_shellParamAt_stopped (Elig : ℂ → Prop) (dflt : ℝ) (k : ℕ) :
    Measurable[(isStoppingTime_shellExit ε η K r s d R k).measurableSpace]
      (shellParamAt ε η K r s d R Elig dflt k) := by
  have hC : IsStoppingTime coordFiltration (shellHit ε η K r s k) := isStoppingTime_shellHit ε η K r s k
  have hT : IsStoppingTime coordFiltration (shellExit ε η K r s d R k) :=
    isStoppingTime_shellExit ε η K r s d R k
  have hle : shellHit ε η K r s k ≤ shellExit ε η K r s d R k := fun x => shellHit_le_shellExit ε η K r s d R k x
  have h1 : Measurable[hC.measurableSpace]
      (fun x : ℕ → ℤ => (shellRadiusAt R Elig dflt (gridRound (d / 100) (vertexPoint ε η (x (shellHit ε η K r s k x).toNat))),
        gridRound (d / 100) (vertexPoint ε η (x (shellHit ε η K r s k x).toNat)))) :=
    measurable_coord_toNat_stop hC (fun j : ℤ =>
      (shellRadiusAt R Elig dflt (gridRound (d / 100) (vertexPoint ε η j)), gridRound (d / 100) (vertexPoint ε η j)))
  exact h1.mono (hC.measurableSpace_mono hT hle) le_rfl

end Lemma68ShellParam
end MatedCRT
