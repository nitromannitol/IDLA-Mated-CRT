import Mathlib
import MatedCRT.FirstPass.S6h
import MatedCRT.FirstPass.S6e.Relation
import MatedCRT.FirstPass.S6e.Geometry
import MatedCRT.FirstPass.S6e.Inputs
import MatedCRT.FirstPass.S6d
import MatedCRT.Proofs.Infra.DiscretePotential
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# FIRST PASS: the uniform constant-order lower bound of Lemma 6.8 (task fp-S6e-lemma68-C17, bridge step 6, z9)

Assembly of `UniformConstantOrderLowerBoundStmt` (`FirstPass/S6d.lean`) from
* `Lemma68Relation.relation_of_phi` (`S6e/Relation.lean`; the instance of `constantOrderLowerBound_core`), and
* the guarded exit bound of `Lemma68Config.probTendsToOne_lemma68_guarded` (`FirstPass/S6h.lean`).

Constants: `s₁` (a parameter, see `Lemma68Relation.S1CoveringSmall`; the guard still fixes `1/4`, see uniform_of_guard), `s₂ = 1/2` (independent of `s₀`), `dd` the guard's radius, `ω₀` and `(ζ, p, q⋆, q₀, R)` from the guard.

Named inputs (Props below; none is proved here):
* `GuardProbStmt 𝒮`: the guarded exit bound holds with probability tending to one (the output of z8's
  `probTendsToOne_lemma68_guarded`, whose schedule input `hsch` is not yet discharged);
* `EscapeAeStmt 𝒮`: almost surely `η` escapes both ends (the field `eta_escapes` of `Lemma68MeasurableInputs`);
* `FiniteExitAeStmt 𝒮`: almost surely, for every `ε > 0`, `S.mult ε ω` is locally finite with `m k (k+1) ≠ 0`.

Proved here: the cell-meeting input (`MatedCRT.adjacentCellsMeetAeStep`), finiteness of the vertex sets from
`CurveEscapesBothEnds`, the `Phi` bound from the guard (`killed` is unchanged when `F0` is replaced by any finset
containing `V(B_r(K))`), and the exit-null input (`ExitNull68.exit_null_of_finite`).
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRT
namespace Lemma68Uniform

open Lemma68Admissible Lemma68Relation Lemma68Config Lemma68Geometry Lemma68Final

lemma cellVertices_mono' {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    cellVertices ε η D ⊆ cellVertices ε η D' :=
  fun _ hk => Set.Nonempty.mono (Set.inter_subset_inter_right _ h) hk

lemma cell_nonempty {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (k : ℤ) : (cell ε η k).Nonempty :=
  Set.Nonempty.image _ (Set.nonempty_Icc.2 (mul_le_mul_of_nonneg_left (by linarith) hε.le))

lemma finite_of_closure_ball {ε ρ : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (hesc : Lemma68Inputs.CurveEscapesBothEnds η)
    {Θ : Set ℤ} (hcl : closure (fillCells ε η Θ) ⊆ ball 0 (ρ / 2)) : Θ.Finite := by
  refine (cellVertices_ball_finite_of_escapes (ρ := ρ / 2) hε hesc).subset fun k hk => ?_
  obtain ⟨x, hx⟩ := cell_nonempty (η := η) hε k
  show (cell ε η k ∩ ball 0 (ρ / 2)).Nonempty
  exact ⟨x, hx, hcl (subset_closure (Set.mem_iUnion₂.2 ⟨k, hk, hx⟩))⟩

lemma thickening_fill_subset_ball {ε ρ r : ℝ} {η : ℝ → ℂ} (hr : r ≤ ρ / 4) {Θ : Set ℤ}
    (hcl : closure (fillCells ε η Θ) ⊆ ball 0 (ρ / 2)) :
    thickening r (fillCells ε η Θ) ⊆ ball 0 ρ := by
  intro z hz
  obtain ⟨x, hx, hzx⟩ := Metric.mem_thickening_iff.1 hz
  have hx0 : dist x 0 < ρ / 2 := mem_ball.1 (hcl (subset_closure hx))
  have hxn : 0 ≤ dist x 0 := dist_nonneg
  have htri := dist_triangle z x 0
  rw [mem_ball]
  linarith

lemma admissible_congr {ε : ℝ} {η : ℝ → ℂ} {Θ F0 F1 A : Finset ℤ} {a : ℤ} {s1 βm x : ℝ}
    (h : killed ε η Θ F0 x = killed ε η Θ F1 x) :
    Admissible ε η Θ F0 A a s1 βm x ↔ Admissible ε η Θ F1 A a s1 βm x := by
  unfold Admissible
  rw [h]

/-- The `Phi`-bound at a finset `F1` with `V^ε(B_r(K)) ⊆ F1`, from the same bound at `F0`: the killed sets agree
(`killed_eq_W`), so the admissibility hypotheses agree. -/
lemma phi_of_bound {ε : ℝ} {η : ℝ → ℂ} (P : Measure (ℕ → ℤ)) [IsFiniteMeasure P] {Θ F0 F1 A : Finset ℤ}
    {a : ℤ} {βm r s₁ : ℝ} (hη : Continuous η) (hε : 0 < ε)
    (hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty)
    (hF0 : cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) ⊆ ↑F0)
    (hF1 : cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) ⊆ ↑F1)
    (hG : Admissible ε η Θ F0 A a s₁ βm r → P.real (Lemma68Walk.exitEvent (killed ε η Θ F0 r) ↑A) ≤ 1 / 2) :
    Phi ε η Θ F1 A a s₁ βm P r := by
  unfold Phi
  intro hadm
  have hk : killed ε η Θ F0 r = killed ε η Θ F1 r := by
    rw [killed_eq_W hη hε hK hF0, killed_eq_W hη hε hK hF1]
  apply measure_le_half_of_real_le
  rw [← hk]
  exact hG ((admissible_congr hk).2 hadm)

/-- The conclusion of Lemma 6.8 at one radius `r` for a finite `Θ`, `S'`, from the guard at `F0 = V^ε(B_ρ)`. -/
lemma event_of_bound {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {ε ρ s₀ β r s₁ : ℝ} {Θ S' : Finset ℤ} {a : ℤ}
    (hε : 0 < ε) (hη : Continuous η) (hesc : Lemma68Inputs.CurveEscapesBothEnds η)
    (hcell : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hexitNull : ∀ A : Set ℤ, A.Finite → ∀ y : ℤ, srwLaw m y {x | vExitTime A x = ⊤} = 0)
    (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hβ : 0 < β) (hs₁ : 0 < s₁) (hs0 : 0 < s₀)
    (hcl : closure (fillCells ε η (↑Θ : Set ℤ)) ⊆ ball 0 (ρ / 2))
    (hs : ball 0 s₀ ⊆ fillCells ε η (↑Θ : Set ℤ))
    (ha : a ∈ vClosure m (↑Θ : Set ℤ))
    (hS' : (↑S' : Set ℤ) ⊆ cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))))
    (hcard : (((↑S' : Set ℤ) \ (↑Θ : Set ℤ)).ncard : ℝ) < s₁ * r ^ (2 * β) / ε)
    (hG : ∀ (F0 A : Finset ℤ) (b : ℤ), (↑F0 : Set ℤ) = cellVertices ε η (ball 0 ρ) →
      Admissible ε η Θ F0 A b s₁ β r →
        (srwLaw m b).real (Lemma68Walk.exitEvent (killed ε η Θ F0 r) ↑A) ≤ 1 / 2) :
    ENNReal.ofReal (1 / 2) ≤ srwLaw m a {x | ∃ n : ℕ,
      (n : ℕ∞) < vExitTime (cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ)))) x ∧
        x n ∈ cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) \ ((↑S' : Set ℤ) ∪ (↑Θ : Set ℤ))} := by
  have hball : (cellVertices ε η (ball 0 ρ)).Finite := cellVertices_ball_finite_of_escapes (ρ := ρ) hε hesc
  have hFb : cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) ⊆ cellVertices ε η (ball 0 ρ) :=
    cellVertices_mono' (thickening_fill_subset_ball hrρ hcl)
  have hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty := ⟨0, hs (mem_ball_self hs0)⟩
  have hUfin : (cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ)))).Finite := hball.subset hFb
  have hr2 : r / 2 ≤ ρ / 4 := by linarith
  have hA : (interiorCellVertices ε η (thickening (r / 2) (fillCells ε η (↑Θ : Set ℤ)))).Finite :=
    hball.subset (Set.sdiff_subset.trans (cellVertices_mono' (thickening_fill_subset_ball hr2 hcl)))
  have hPhi : ∀ (A : Finset ℤ) (b : ℤ),
      b ∈ cellVertices ε η (frontier (thickening (r / 2) (fillCells ε η (↑Θ : Set ℤ)))) →
        Phi ε η Θ hUfin.toFinset A b s₁ β (srwLaw m b) r := by
    intro A b _
    exact phi_of_bound (srwLaw m b) hη hε hK (hFb.trans hball.coe_toFinset.symm.subset)
      hUfin.coe_toFinset.symm.subset
      (fun hadm => hG _ A b hball.coe_toFinset hadm)
  exact Lemma68Relation.relation_of_phi MatedCRT.srwHitDecompositionStep MatedCRT.srwAeAdjacentStep hε hη hcell hK
    hr0 hβ hs₁ hUfin (fun b => hexitNull _ hA b) hPhi ha hS' hcard

/-- Almost surely, the cell-meeting, continuity, escape and exit-finiteness inputs hold for all `ε > 0`. -/
lemma probTendsToOne_of_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : Ω → Prop}
    (h : ∀ᵐ ω ∂P, p ω) : ProbTendsToOne P (fun _ => {ω | p ω}) := by
  have h1 : P {ω | p ω}ᶜ = 0 := ae_iff.1 h
  exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun _ => h1.symm)

/-- Named input: the guarded exit bound (write-up (17)) holds with probability tending to one, with constants
`ω₀` (depending on `γ`), `R ≤ min(ρ/4, rAmp q₀ ζ)`, `q₀ = q⋆/9`, `p ≤ 3`, `ζ < 1/2`, and a measurable radius `dd`
with `0 < dd ≤ R`. This is the output of `Lemma68Config.probTendsToOne_lemma68_guarded` once its schedule input
`hsch` is discharged; it is NOT proved here. -/
def GuardProbStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∃ R ζ p qStar q0 : ℝ, 0 < R ∧ R ≤ ρ / 4 ∧ R ≤ Lemma68Cutoff.rAmp q0 ζ ∧
    0 < ζ ∧ ζ < 1 / 2 ∧ 0 < q0 ∧ q0 ≤ 1 ∧ q0 = qStar / 9 ∧ 0 ≤ qStar ∧ qStar ≤ 9 ∧ p ≤ 3 ∧
  ∃ s₁ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧ (∀ ω, dd ω ≤ R) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ i : Config68,
      guardedExit (fun ε ω r i => FullAdmAt s₁ S ρ s₀ γ ε ω r i) (exitQ S) ε ω r i ≤ 1 / 2}

/-- Named input: almost surely `η` escapes both ends (the field `eta_escapes` of `Lemma68MeasurableInputs`). -/
def EscapeAeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, Lemma68Inputs.CurveEscapesBothEnds (S.η ω)

/-- Named input: almost surely, for every `ε > 0`, the multiplicities `S.mult ε ω` are locally finite and
`m k (k+1) ≠ 0` for all `k`. -/
def FiniteExitAeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0

/-- The uniform constant-order lower bound of Lemma 6.8 from the three named inputs. -/
theorem uniform_of_guard (𝒮 : SpaceFillingSLEModel) (hG : GuardProbStmt 𝒮) (hEsc : EscapeAeStmt 𝒮)
    (hFin : FiniteExitAeStmt 𝒮)
    (hNull : ∀ (m : ℤ → ℤ → ℕ), IsLocallyFiniteMult m → (∀ k : ℤ, m k (k + 1) ≠ 0) →
      ∀ A : Set ℤ, A.Finite → ∀ y : ℤ, srwLaw m y {x | vExitTime A x = ⊤} = 0) :
    UniformConstantOrderLowerBoundStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ω₀, hω₀, hG'⟩ := hG γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨R, ζ, p, qStar, q0, hR0, hRρ, hRz, hζ0, hζ1, hq00, hq01, hq0d, hq0', hq9, hp, s₁, hs₁0, hs₁1, hG2⟩ :=
    hG' ρ hρ0 hρ1
  -- the witness `s₁` is the sparsity coefficient of the guard (CHATGPT-237 §1: `s₁ ≤ K.s1`), `s₂ = 1/2`
  refine ⟨s₁, 1 / 2, hs₁0, hs₁1, by norm_num, by norm_num, fun s₀ hs₀0 hs₀1 Ω _ S hS => ?_⟩
  obtain ⟨dd, hdm, hdpos, hddR, hP⟩ := hG2 s₀ hs₀0 hs₀1 Ω S hS
  refine ⟨dd, hdm, hdpos, ?_⟩
  have hAe : ∀ᵐ ω ∂S.P, Continuous (S.η ω) ∧ Lemma68Inputs.CurveEscapesBothEnds (S.η ω) ∧
      (∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) ∧
      (∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) :=
    (Lemma68Inputs.ae_continuous_of_isValid hS).and
      ((hEsc γ hγ0 hγ2 Ω S hS).and
        ((adjacentCellsMeetAeStep 𝒮 γ hγ0 hγ2 Ω S hS).and (hFin γ hγ0 hγ2 Ω S hS)))
  refine (ProbTendsToOne.inter hP (probTendsToOne_of_ae hAe)).mono_pos fun ε hε => ?_
  intro ω hω
  obtain ⟨hgd, hcont, hesc, hadj, hfin⟩ := hω
  simp only [Set.mem_ofPred_eq] at hgd ⊢
  intro r hr1 hr2 Θ hΘ1 hΘ2 a ha S' hS' hcard
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hβ : 0 < chosenBetaMinus γ := by unfold chosenBetaMinus; positivity
  have hrρ : r ≤ ρ / 4 := le_trans hr2 ((hddR ω).trans hRρ)
  obtain ⟨hlf, hcons⟩ := hfin ε hε
  have hΘf : Θ.Finite := finite_of_closure_ball hε hesc hΘ1
  obtain ⟨Θf, rfl⟩ := hΘf.exists_finset_coe
  have hUfin : (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) (↑Θf : Set ℤ)))).Finite :=
    (cellVertices_ball_finite_of_escapes (ρ := ρ) hε hesc).subset
      (cellVertices_mono' (thickening_fill_subset_ball hrρ hΘ1))
  obtain ⟨S'f, rfl⟩ := (hUfin.subset hS').exists_finset_coe
  refine event_of_bound (η := S.η ω) (m := S.mult ε ω) hε hcont hesc (hadj ε hε)
    (fun A hA y => hNull _ hlf hcons A hA y) hr0 hrρ hβ hs₁0
    hs₀0 hΘ1 hΘ2 ha hS' hcard ?_
  intro F0 A b hF0 hadm
  have hFA : FullAdmAt s₁ S ρ s₀ γ ε ω r ⟨F0, Θf, A, b⟩ := by
    unfold FullAdmAt ConfigOK
    exact ⟨⟨hF0, hΘ1, hΘ2⟩, hadm⟩
  have hgE := hgd r hr1 hr2 ⟨F0, Θf, A, b⟩
  simp only [Lemma68Final.guardedExit, hFA, ↓reduceIte] at hgE
  exact hgE

end Lemma68Uniform
end MatedCRT
