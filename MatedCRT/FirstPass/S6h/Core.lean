import Mathlib
import MatedCRT.FirstPass.S6e.C17Induction
import MatedCRT.FirstPass.S6e.Admissible
import MatedCRT.FirstPass.S6e.Walk
import MatedCRT.FirstPass.S6e.Cutoff
import MatedCRT.Proofs.IDLA.Measurable

/-!
# FIRST PASS: the configuration bound of Lemma 6.8

Sources: the bridge argument §1 (`exitQ`), §2.1 (`FullAdm`; the zero extension is `Lemma68Final.guardedExit`), §3 Steps A–F
(`configuration_le_pow`), §4 (`hpt`); the test schedule of Steps B–C is the write-up's C1–C3
(the Lemma 6.8 open-parts write-up, lines 657–741).

The quenched exit probability `exitQ` is `P^a(exitEvent U A)` for the walk killed off `U` (Walk.lean's `exitEvent`).
The configuration bound is the composition (C12) ∘ (C17): `exitEvent U A ⊆ᵐ H_N` (C12, Step D) and
`P(H_N) ≤ (1 - q0/(1+log(1/r))²)^N` (`Lemma68Induction.C17_le_pow`, Step F).

Explicit inputs (named fields of `TestSchedule.Valid`, one per written step, none proved here):
`hC12` (C12: `T_N < τ_U` almost surely), `hstep` (the conditional test bound C15, proved by S6j.lean),
the C3 structure (`hmono`, `hTmono`, `hG`, `hGad`, `hR`), and the count `hcount` (Step B). -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Config

/-- A configuration of Lemma 6.8 (bridge note §1): the frozen cell set `F0`, the blocked set `Θ`, the target set `A` and
the start vertex `a` (the vertex `i.a` of `srwLaw`). -/
structure Config68 where
  F0 : Finset ℤ
  Θ : Finset ℤ
  A : Finset ℤ
  a : ℤ

/-- The radius-independent part of the configuration guard (bridge note §2.1). -/
def ConfigOK {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ s₀ ε : ℝ) (ω : Ω) (i : Config68) : Prop :=
  (↑i.F0 : Set ℤ) = cellVertices ε (S.η ω) (Metric.ball 0 ρ) ∧
    closure (fillCells ε (S.η ω) (↑i.Θ : Set ℤ)) ⊆ Metric.ball 0 (ρ / 2) ∧
    Metric.ball 0 s₀ ⊆ fillCells ε (S.η ω) (↑i.Θ : Set ℤ)

/-- The sparsity coefficient of the shell-chain constants (`s_guard = K.s1`): `K.s1 = c0^βm/44`
with `c0 = exp(-2)/32` and `βm = (2+γ)²/2 + 1` (ShellConstants68.lean `shellK68`, `shellK68_s1`). It depends on `γ` only. -/
noncomputable def sparsityS1 (γ : ℝ) : ℝ := (Real.exp (-2) / 32) ^ ((2 + γ) ^ 2 / 2 + 1) / 44

theorem sparsityS1_pos (γ : ℝ) : 0 < sparsityS1 γ := by
  unfold sparsityS1
  positivity

theorem sparsityS1_lt_one (γ : ℝ) : sparsityS1 γ < 1 := by
  have hexp : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hc : Real.exp (-2) / 32 ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ) < 32)]
    linarith
  have hp : (Real.exp (-2) / 32) ^ ((2 + γ) ^ 2 / 2 + 1) ≤ 1 :=
    Real.rpow_le_one (by positivity) hc (by positivity)
  unfold sparsityS1
  rw [div_lt_one (by norm_num : (0 : ℝ) < 44)]
  linarith

/-- The full admissibility guard `FullAdmAt s₁` at radius `r` (preferred repair): `ConfigOK` and
`Lemma68Admissible.Admissible` with the sparsity coefficient `s₁` (the witness of `UniformConstantOrderLowerBoundStmt`)
and `chosenBetaMinus γ`. The shell chain uses `s₁ = sparsityS1 γ`. -/
def FullAdmAt (s₁ : ℝ) {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ s₀ γ ε : ℝ) (ω : Ω) (r : ℝ)
    (i : Config68) : Prop :=
  ConfigOK S ρ s₀ ε ω i ∧
    Lemma68Admissible.Admissible ε (S.η ω) i.Θ i.F0 i.A i.a s₁ ((2 + γ) ^ 2 / 2 + 1) r

/-- LEGACY guard (write-up coefficient `1/4` hardcoded). NOT used by the shell chain (`hU_top`): the chain uses
`FullAdmAt (sparsityS1 γ)`. Kept only so that legacy modules (S6e/Guard, S6h, S6h/Schedule, S6m, ShellOrderFullAdm,
ShellHde68, B1Assembly68) still compile; they should be rewired to `FullAdmAt` and this declaration retired. -/
def FullAdm {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ s₀ γ ε : ℝ) (ω : Ω) (r : ℝ) (i : Config68) : Prop :=
  ConfigOK S ρ s₀ ε ω i ∧
    Lemma68Admissible.Admissible ε (S.η ω) i.Θ i.F0 i.A i.a (1 / 4) ((2 + γ) ^ 2 / 2 + 1) r

/-- The raw quenched exit probability `exitQ` (bridge note §1): `P^a(exitEvent U A)` for the simple random walk law
`srwLaw (S.mult ε ω) i.a` and the killed set `U = killed ε η Θ F0 r`. -/
noncomputable def exitQ {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω) (r : ℝ)
    (i : Config68) : ℝ :=
  (srwLaw (S.mult ε ω) i.a).real
    (Lemma68Walk.exitEvent (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) (↑i.A : Set ℤ))

/-- The test-hit event `G_j` of test `j` (bridge note §3 Step C, (3)): the walk leaves `A` between the test times
`T j` and `T (j+1)`. -/
def testHit (A : Set ℤ) (T : ℕ → (ℕ → ℤ) → ℕ∞) (j : ℕ) : Set (ℕ → ℤ) :=
  {x | ∃ n : ℕ, T j x ≤ n ∧ (n : ℕ∞) < T (j + 1) x ∧ x n ∉ A}

/-- The failure events `H_N` of the test chain (bridge note (3)): `H 0 = univ`, `H (j+1) = H j ∩ (G_j)ᶜ`. -/
def testFail (A : Set ℤ) (T : ℕ → (ℕ → ℤ) → ℕ∞) : ℕ → Set (ℕ → ℤ)
  | 0 => univ
  | j + 1 => testFail A T j ∩ (testHit A T j)ᶜ

/-- Unfolded form of `H_N` (bridge note (4)): the path avoids `A` at every time of every test interval `j < N`. -/
theorem mem_testFail_iff (A : Set ℤ) (T : ℕ → (ℕ → ℤ) → ℕ∞) (x : ℕ → ℤ) (N : ℕ) :
    x ∈ testFail A T N ↔ ∀ j < N, x ∉ testHit A T j := by
  induction N with
  | zero => simp [testFail]
  | succ N ih =>
    rw [testFail, mem_inter_iff, mem_compl_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h1 j hj
      · exact h2
    · intro h
      exact ⟨fun j hj => h j (by omega), h N (by omega)⟩

/-- The cutoff `rAmp` is at most one (it is a minimum with `1`, write-up D3). -/
theorem rAmp_le_one (q0 ζ : ℝ) : Lemma68Cutoff.rAmp q0 ζ ≤ 1 := by
  unfold Lemma68Cutoff.rAmp
  exact min_le_left _ _

/-- The concrete test schedule of one configuration (bridge note §3 Steps B–C; write-up C1–C3): the test count `N`,
the test times `T j`, the radii `R j` and the stopping σ-algebras `m j = F_{T_j}`. Its properties are in `Valid`. -/
structure TestSchedule where
  N : ℕ
  T : ℕ → (ℕ → ℤ) → ℕ∞
  R : ℕ → (ℕ → ℤ) → ℝ
  m : ℕ → MeasurableSpace (ℕ → ℤ)

/-- The inputs of the configuration bound for a schedule `sc`, on the quenched law `ν` of the walk killed off `U`, with
target `A`, exponent `p`, constant `qStar` (C15) and cutoff exponent `ζ`:
* the C3 structure: `m` monotone and below the product σ-algebra, `T j ≤ T (j+1)`, the test events measurable and
  `G_j` `F_{T_{j+1}}`-measurable, and the radii in `(r^p/2, 1]` almost surely;
* `hcount`: the count of Step B, `r^(-ζ)/200 ≤ N`;
* `hC12`: the almost-sure containment `T_N < τ_U` (write-up C12);
* `hstep`: the conditional test bound of C15 on `H_j`, in the form of `C17_le_pow` (proved in S6j.lean). -/
structure TestSchedule.Valid (sc : TestSchedule) (ν : Measure (ℕ → ℤ)) (U A : Set ℤ) (r p qStar ζ : ℝ) :
    Prop where
  hmono : Monotone sc.m
  hm : ∀ j, sc.m j ≤ MeasurableSpace.pi
  hTmono : ∀ (x : ℕ → ℤ) (j : ℕ), sc.T j x ≤ sc.T (j + 1) x
  hG : ∀ j, MeasurableSet (testHit A sc.T j)
  hGad : ∀ j, MeasurableSet[sc.m (j + 1)] (testHit A sc.T j)
  hR : ∀ j, ∀ᵐ x ∂ν, 0 < sc.R j x ∧ sc.R j x ≤ 1 ∧ r ^ p / 2 < sc.R j x
  hcount : r ^ (-ζ) / 200 ≤ (sc.N : ℝ)
  hC12 : ∀ᵐ x ∂ν, sc.T sc.N x < vExitTime U x
  hstep : ∀ j, ∀ᵐ x ∂ν, x ∈ testFail A sc.T j →
    qStar / (1 + Real.log (1 / sc.R j x)) ^ 2 ≤ (ν[(testHit A sc.T j).indicator (fun _ => (1 : ℝ)) | sc.m j]) x

/-- (Step D) Almost surely `T_N < τ_U` implies that the exit event lies in `H_N`: a path in `exitEvent U A` avoids `A`
during each test interval `[T_j, T_{j+1})`, `j < N`, because every time before `T_N` is before the exit time. -/
theorem exitEvent_ae_le_testFail {ν : Measure (ℕ → ℤ)} {U A : Set ℤ} {T : ℕ → (ℕ → ℤ) → ℕ∞} {N : ℕ}
    (hTmono : ∀ (x : ℕ → ℤ) (j : ℕ), T j x ≤ T (j + 1) x)
    (hC12 : ∀ᵐ x ∂ν, T N x < vExitTime U x) :
    Lemma68Walk.exitEvent U A ≤ᵐ[ν] testFail A T N := by
  filter_upwards [hC12] with x hx
  intro hB
  rw [mem_testFail_iff]
  have hmono : Monotone (fun j => T j x) := monotone_nat_of_le_succ (fun k => hTmono x k)
  intro j hj ⟨n, h1, h2, hn⟩
  have hnU : (n : ℕ∞) < vExitTime U x :=
    lt_of_lt_of_le h2 ((hmono (Nat.succ_le_of_lt hj)).trans hx.le)
  exact hn (hB n (natCast_lt_vExitTime_iff.1 hnU))

/-- A measure-real monotonicity along an almost-sure inclusion. -/
theorem measureReal_le_of_ae_le {ν : Measure (ℕ → ℤ)} [IsFiniteMeasure ν] {s t : Set (ℕ → ℤ)}
    (h : s ≤ᵐ[ν] t) : ν.real s ≤ ν.real t :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h)

/-- (Steps D–F) The exit probability of a configuration with a valid schedule is at most `(1 - q0/(1+log(1/r))²)^N`,
`q0 = qStar/9`, with the count `N` of the schedule. Composition of `exitEvent_ae_le_testFail` with `C17_le_pow`. -/
theorem configuration_le_pow_of_schedule {ν : Measure (ℕ → ℤ)} [IsProbabilityMeasure ν] {U A : Set ℤ}
    {r p qStar ζ : ℝ} (hq : 0 ≤ qStar) (hq9 : qStar ≤ 9) (hp : p ≤ 3) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (sc : TestSchedule) (hV : sc.Valid ν U A r p qStar ζ) :
    ν.real (Lemma68Walk.exitEvent U A) ≤ (1 - qStar / 9 / (1 + Real.log (1 / r)) ^ 2) ^ sc.N := by
  have hD : Lemma68Walk.exitEvent U A ≤ᵐ[ν] testFail A sc.T sc.N :=
    exitEvent_ae_le_testFail hV.hTmono hV.hC12
  have hC17 := Lemma68Induction.C17_le_pow ν sc.m hV.hmono hV.hm hV.hG hV.hGad hq hq9 hp hr0 hr1 sc.R hV.hR
    (testFail A sc.T) rfl (fun j => rfl) hV.hstep sc.N
  exact (measureReal_le_of_ae_le hD).trans hC17

/-- (Lemma 6.8, per configuration; bridge note §3, `configuration_le_pow`) On the good event `E ε ∩ G`, for every admissible
radius `r ∈ [α ε, dd ω]` and every configuration satisfying the guard `FullAdm`, the exit probability `exitQ` is at most
`(1 - q0/(1+log(1/r))²)^N` for a count `N ≥ r^(-ζ)/200`. The schedule `sc` (C1–C3) and its inputs C12, C15 are the
hypotheses `hsch`. -/
theorem configuration_le_pow {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ s₀ γ : ℝ)
    (E : ℝ → Set Ω) (G : Set Ω) (α : ℝ → ℝ) (dd : Ω → ℝ) (R : ℝ) (ζ p qStar q0 : ℝ)
    (hq0 : q0 = qStar / 9) (hq : 0 ≤ qStar) (hq9 : qStar ≤ 9) (hp : p ≤ 3)
    (hα : ∀ ε, 0 < ε → 0 < α ε) (hdd : ∀ ω, dd ω ≤ R) (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ)
    (sc : ℝ → Ω → ℝ → Config68 → TestSchedule)
    (hsch : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      FullAdm S ρ s₀ γ ε ω r i →
        (sc ε ω r i).Valid (srwLaw (S.mult ε ω) i.a)
          (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) (↑i.A : Set ℤ) r p qStar ζ) :
    ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      FullAdm S ρ s₀ γ ε ω r i →
        ∃ N : ℕ, r ^ (-ζ) / 200 ≤ (N : ℝ) ∧
          exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := by
  intro ε hε ω hω r hαr hrd i hi
  have hr0 : 0 < r := (hα ε hε).trans_le hαr
  have hr1 : r ≤ 1 := ((hrd.trans (hdd ω)).trans hR).trans (rAmp_le_one q0 ζ)
  have hV := hsch ε hε ω hω r hαr hrd i hi
  refine ⟨(sc ε ω r i).N, hV.hcount, ?_⟩
  unfold exitQ
  rw [hq0]
  exact configuration_le_pow_of_schedule hq hq9 hp hr0 hr1 (sc ε ω r i) hV

end Lemma68Config

end MatedCRT
