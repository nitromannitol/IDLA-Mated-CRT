import MatedCRT.FirstPass.S4S6c.HoneReduced68
import MatedCRT.FirstPass.S4S6c.HspRepair68
import MatedCRT.FirstPass.S4S6c.HoneCellR68
import MatedCRT.FirstPass.S4S6c.HoneRcell68
import MatedCRT.FirstPass.S4S6c.BallExitMeasAe68

/-!
# The one-test leaf with almost-sure walk binders (q1, fp-S4S6c-leaf-ae)

`shellOneTest_of_direct_ae` has the conclusion of `shellOneTest_of_direct_reduced68` (HoneReduced68.lean:41). Every binder of
the form `∀ k, ∀ ω ∈ prefixSet … (T k) τU, P k ω` is restated as `∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet … → P k x`
(the shape of `radius_bounds_ae`, HoneRadii68.lean:150). The pointwise chain
`hone_exitQ_walk_of_env_direct_repaired` (HspRepair68.lean:502) is applied unchanged, with the walk space trimmed:

* `Bs` is the union of the walks where some restated binder fails (for `k ≤ n`); it is null under `srwLaw m a`.
* `τU' := Bsᶜ.indicator τU` has the same prefix sets off `Bs` (`mem_prefix_indicator`), so the pointwise binders hold on them.
* `T' k := Tn T n k` is `T k` for `k ≤ n` and `⊤` beyond (the prefix set is empty there, `not_mem_prefixSet_Tn_top`);
  `R' k := Rn R n k` is `R k` for `k ≤ n` and `0` beyond.
* The conclusion is transferred back on `k ≤ n` by the congruence `condExp_testInd_congr` and `x ∉ Bs` a.s.

No edit of another worker's file. Terminology: Armstrong-Kuusi-Mourrat (shells, one-test bound), Armitage-Gardiner (exit times).
-/

open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68LeafAe

open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst

/-- The stopping times of the trimmed family: `T k` for `k ≤ n`, the constant `⊤` beyond. -/
noncomputable def Tn (T : ℕ → (ℕ → ℤ) → ℕ∞) (n k : ℕ) : (ℕ → ℤ) → ℕ∞ :=
  if k ≤ n then T k else fun _ => ⊤

/-- The radii of the trimmed family: `R k` for `k ≤ n`, the constant `0` beyond. -/
noncomputable def Rn (R : ℕ → (ℕ → ℤ) → ℝ) (n k : ℕ) : (ℕ → ℤ) → ℝ :=
  if k ≤ n then R k else fun _ => 0

theorem Tn_of_le {T : ℕ → (ℕ → ℤ) → ℕ∞} {n k : ℕ} (hk : k ≤ n) : Tn T n k = T k := by
  simp [Tn, hk]

theorem Tn_of_not_le {T : ℕ → (ℕ → ℤ) → ℕ∞} {n k : ℕ} (hk : ¬ k ≤ n) : Tn T n k = fun _ => ⊤ := by
  simp [Tn, hk]

theorem Rn_of_le {R : ℕ → (ℕ → ℤ) → ℝ} {n k : ℕ} (hk : k ≤ n) : Rn R n k = R k := by
  simp [Rn, hk]

theorem Rn_of_not_le {R : ℕ → (ℕ → ℤ) → ℝ} {n k : ℕ} (hk : ¬ k ≤ n) : Rn R n k = fun _ => 0 := by
  simp [Rn, hk]

/-- The constant stopping time `⊤` (`IsStoppingTime`, Mathlib Probability/Process/Stopping.lean:76). -/
theorem isStoppingTime_top_walk :
    IsStoppingTime coordFiltration (fun _ : ℕ → ℤ => (⊤ : ℕ∞)) := fun i => by simp

theorem isStoppingTime_Tn {T : ℕ → (ℕ → ℤ) → ℕ∞} (n : ℕ) (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    (k : ℕ) : IsStoppingTime coordFiltration (Tn T n k) := by
  by_cases hk : k ≤ n
  · rw [Tn_of_le hk]; exact hT k
  · rw [Tn_of_not_le hk]; exact isStoppingTime_top_walk

/-- The stopping-time σ-algebra depends only on the stopping time as a function. -/
theorem msp_congr {τ τ' : (ℕ → ℤ) → ℕ∞} (h : τ = τ')
    (h₁ : IsStoppingTime coordFiltration τ) (h₂ : IsStoppingTime coordFiltration τ') :
    h₁.measurableSpace = h₂.measurableSpace := by
  subst h; rfl

theorem measurable_Rn {T : ℕ → (ℕ → ℤ) → ℕ∞} {R : ℕ → (ℕ → ℤ) → ℝ} (n : ℕ)
    (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k)) (k : ℕ) :
    Measurable[(isStoppingTime_Tn n hT k).measurableSpace] (Rn R n k) := by
  by_cases hk : k ≤ n
  · rw [msp_congr (Tn_of_le (T := T) (n := n) hk) (isStoppingTime_Tn n hT k) (hT k), Rn_of_le hk]
    exact hR k
  · rw [Rn_of_not_le hk]; exact measurable_const

/-- A walk in the prefix set of `⊤` is impossible. -/
theorem not_mem_prefixSet_Tn_top {A : Set ℤ} {T : ℕ → (ℕ → ℤ) → ℕ∞} {τ : (ℕ → ℤ) → ℕ∞} {n k : ℕ}
    (hk : ¬ k ≤ n) (x : ℕ → ℤ)
    (hx : x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (Tn T n k) τ) : False := by
  rw [Tn_of_not_le hk] at hx
  simp only [prefixSet, Set.mem_ofPred_eq] at hx
  exact not_top_lt hx.1

/-- **Trimming.** The walks of `prefixSet` for the trimmed end `Bᶜ.indicator τU` are the walks of the original prefix set
outside `B`. -/
theorem mem_prefix_indicator {A : Set ℤ} {T τ : (ℕ → ℤ) → ℕ∞} {B : Set (ℕ → ℤ)} (x : ℕ → ℤ) :
    x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A T (Bᶜ.indicator τ) ↔
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A T τ ∧ x ∉ B := by
  by_cases hx : x ∈ B
  · simp [prefixSet, hx]
  · simp [prefixSet, hx]

/-- **The null bad set of a restated binder.** From `∀ k ≤ n, ∀ᵐ x, x ∈ prefixSet … → P k x` there is a set `B` with
`∀ᵐ x, x ∉ B` and `P k x` for every `k ≤ n` and every `x` in the prefix set outside `B`. -/
theorem exists_bad_walks (n : ℕ) {A : Set ℤ} {T : ℕ → (ℕ → ℤ) → ℕ∞} {τU : (ℕ → ℤ) → ℕ∞}
    {P : ℕ → (ℕ → ℤ) → Prop} (μ : Measure (ℕ → ℤ))
    (h : ∀ k, k ≤ n → ∀ᵐ x ∂μ, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU → P k x) :
    ∃ B : Set (ℕ → ℤ), (∀ᵐ x ∂μ, x ∉ B) ∧
      ∀ k, k ≤ n → ∀ x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, x ∉ B → P k x := by
  classical
  refine ⟨{x | ∃ k, k ≤ n ∧ x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU ∧ ¬ P k x}, ?_, ?_⟩
  · have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, k ≤ n →
        x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU → P k x := by
      refine ae_all_iff.2 fun k => ?_
      by_cases hk : k ≤ n
      · filter_upwards [h k hk] with x hx
        exact fun _ => hx
      · exact Eventually.of_forall fun x h' => absurd h' hk
    filter_upwards [hall] with x hx
    rintro ⟨k, hk, hP, hnP⟩
    exact hnP (hx k hk hP)
  · intro k hk x hx hxB
    by_contra hP
    exact hxB ⟨k, hk, hx, hP⟩

/-- **A restated binder transferred to the trimmed walk space.** If the binder holds on the prefix set outside `Bi ⊆ B`,
then it holds (after the `Tn`, `Rn` substitution `hΦ'`) on the prefix set of the trimmed end, for every `k`. -/
theorem trim_binder {A : Set ℤ} {T : ℕ → (ℕ → ℤ) → ℕ∞} {τU : (ℕ → ℤ) → ℕ∞} {n : ℕ}
    {B Bi : Set (ℕ → ℤ)} (hBi : Bi ⊆ B)
    {Φ : ℕ → (ℕ → ℤ) → Prop}
    (hΦ : ∀ k, k ≤ n → ∀ x, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU → x ∉ Bi → Φ k x)
    {Φ' : ℕ → (ℕ → ℤ) → Prop} (hΦ' : ∀ k, k ≤ n → ∀ x, Φ k x → Φ' k x) :
    ∀ (k : ℕ) (ω : ℕ → ℤ),
      ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (Tn T n k) (Bᶜ.indicator τU) → Φ' k ω := by
  intro k ω hω
  by_cases hk : k ≤ n
  · rw [Tn_of_le hk] at hω
    obtain ⟨hP, hωB⟩ := (mem_prefix_indicator ω).1 hω
    exact hΦ' k hk ω (hΦ k hk ω hP (fun h => hωB (hBi h)))
  · exact (not_mem_prefixSet_Tn_top hk ω hω).elim

/-- The test indicator of the walk-centred one-test bound, as a function of the stopping time and the radius. -/
noncomputable def testInd (A : Set ℤ) (ε : ℝ) (η : ℝ → ℂ) (T : (ℕ → ℤ) → ℕ∞) (R : (ℕ → ℤ) → ℝ) :
    (ℕ → ℤ) → ℝ :=
  (testFailSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A T (testEndExit ε η (walkParam ε η R T) T)).indicator
    (fun _ => (1 : ℝ))

/-- The conditional expectation of the test indicator depends only on the values `T`, `R`. -/
theorem condExp_testInd_congr (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (ε : ℝ) (η : ℝ → ℂ)
    {T T' : (ℕ → ℤ) → ℕ∞} {R R' : (ℕ → ℤ) → ℝ}
    (hT : IsStoppingTime coordFiltration T) (hT' : IsStoppingTime coordFiltration T')
    (hTT : T = T') (hRR : R = R') (x : ℕ → ℤ) :
    (srwLaw m a)[testInd A ε η T R | hT.measurableSpace] x
      = (srwLaw m a)[testInd A ε η T' R' | hT'.measurableSpace] x := by
  subst hTT; subst hRR; rfl

/-- **The one-test leaf with almost-sure walk binders (abstract stopping time).** Same conclusion as
`hone_exitQ_walk_of_env_direct_repaired` (HspRepair68.lean:502); every binder over the prefix set is restated almost surely
under `srwLaw m a` for `k ≤ n`. -/
theorem hone_exitQ_walk_of_env_direct_ae {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    {r q0 q α C_exit C_good Dbl C : ℝ} {N_cov : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hmom1 : ∀ k ≤ n, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k ≤ n, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    (hRr : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      r ^ 2 ≤ R k x ∧ R k x ≤ 1)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (rmin : ℝ)
    (hRmin : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      rmin ≤ K.c0 * R k x)
    (hVolC : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ENNReal.ofReal ((K.c0 * R k x) ^ K.βm) ≤ μ (ball (vertexPoint ε η (x (T k x).toNat)) (K.c0 * R k x)))
    (hVolY : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ∀ y ∈ ball (0 : ℂ) (1 - R k x / 4), ENNReal.ofReal ((R k x / 4) ^ K.βm) ≤ μ (ball y (R k x / 4)))
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ K.ω ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      x (T k x).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ K.ω ≤ R k x / 8 ∧
        R k x / 8 ≤ infDist (vertexPoint ε η (x (T k x).toNat)) (sphere 0 ρc))
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (ρcell : ℝ) (hρgap : ρc < ρcell)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρcell).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hRcell : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
        R k x / 4 < ρcell - ρc)
    (hωκ : K.ω ≤ 2 / (2 + γ) ^ 2 - ζc)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hfinE : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (x (T k x).toNat)) (R k x / 4)))
        (x (T k x).toNat) ≠ ⊤)
    (hsc : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (x (T k x).toNat)) (K.c0 * R k x))).toReal)
    {Z : ℕ → (ℕ → ℤ) → ℂ}
    (hεα : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ε ^ α ≤ R k x / 100)
    (hεmass : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ε ^ α ≤ (R k x / 4) ^ K.βm)
    (hb : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      x (T k x).toNat ∈ cellVertices ε η (sphere (Z k x) (4 * R k x / 3)))
    (hx1 : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ‖vertexPoint ε η (x (T k x).toNat)‖ < 1 - R k x / 4)
    (hmomS : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      IsGoodAnnulusEvent μ K.c0 C_good (R k x) (Z k x))
    (hN : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      0 < ⨅ w ∈ annulus (Z k x) (R k x) (2 * R k x), μ (ball w (K.c0 * R k x)))
    (hdbl : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      (μ (ball (vertexPoint ε η (x (T k x).toNat)) (3 * K.c0 * R k x))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (x (T k x).toNat)) (K.c0 * R k x))).toReal) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (walkParam ε η (R k) (T k)) (T k))).indicator (fun _ => (1 : ℝ))
          | (hT k).measurableSpace] x ≤ 1 - q := by
  classical
  -- (1) the null bad walks of each restated binder
  obtain ⟨B1, hB1a, hB1⟩ := exists_bad_walks n (srwLaw m a) hRr
  obtain ⟨B2, hB2a, hB2⟩ := exists_bad_walks n (srwLaw m a) hRmin
  obtain ⟨B3, hB3a, hB3⟩ := exists_bad_walks n (srwLaw m a) hVolC
  obtain ⟨B4, hB4a, hB4⟩ := exists_bad_walks n (srwLaw m a) hVolY
  obtain ⟨B5, hB5a, hB5⟩ := exists_bad_walks n (srwLaw m a) hWalk
  obtain ⟨B6, hB6a, hB6⟩ := exists_bad_walks n (srwLaw m a) hfinE
  obtain ⟨B7, hB7a, hB7⟩ := exists_bad_walks n (srwLaw m a) hsc
  obtain ⟨B8, hB8a, hB8⟩ := exists_bad_walks n (srwLaw m a) hεα
  obtain ⟨B9, hB9a, hB9⟩ := exists_bad_walks n (srwLaw m a) hεmass
  obtain ⟨B10, hB10a, hB10⟩ := exists_bad_walks n (srwLaw m a) hb
  obtain ⟨B11, hB11a, hB11⟩ := exists_bad_walks n (srwLaw m a) hx1
  obtain ⟨B12, hB12a, hB12⟩ := exists_bad_walks n (srwLaw m a) hmomS
  obtain ⟨B13, hB13a, hB13⟩ := exists_bad_walks n (srwLaw m a) hgood
  obtain ⟨B14, hB14a, hB14⟩ := exists_bad_walks n (srwLaw m a) hN
  obtain ⟨B15, hB15a, hB15⟩ := exists_bad_walks n (srwLaw m a) hpos
  obtain ⟨B16, hB16a, hB16⟩ := exists_bad_walks n (srwLaw m a) hdbl
  obtain ⟨B17, hB17a, hB17⟩ := exists_bad_walks n (srwLaw m a) hRcell
  -- (2) the union of the bad walks, and the trimmed end
  obtain ⟨B, hBeq⟩ : ∃ B : Set (ℕ → ℤ), B = B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7 ∪ B8 ∪ B9 ∪ B10 ∪ B11 ∪ B12 ∪ B13 ∪ B14 ∪ B15 ∪ B16 ∪ B17 :=
    ⟨_, rfl⟩
  have hBa : ∀ᵐ x ∂srwLaw m a, x ∉ B := by
    filter_upwards [hB1a, hB2a, hB3a, hB4a, hB5a, hB6a, hB7a, hB8a, hB9a, hB10a, hB11a, hB12a, hB13a, hB14a,
      hB15a, hB16a, hB17a] with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rw [hBeq]
    intro hx
    simp only [Set.mem_union] at hx
    tauto
  have sub1 : B1 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub2 : B2 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub3 : B3 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub4 : B4 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub5 : B5 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub6 : B6 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub7 : B7 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub8 : B8 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub9 : B9 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub10 : B10 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub11 : B11 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub12 : B12 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub13 : B13 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub14 : B14 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub15 : B15 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub16 : B16 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub17 : B17 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have hRcell' := trim_binder sub17 hB17 (Φ' := fun k x => Rn R n k x / 4 < ρcell - ρc)
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  -- (3) the pointwise binders on the trimmed prefix sets (k ≤ n; empty for k > n)
  have hRr' := trim_binder sub1 hB1 (Φ' := fun k x => r ^ 2 ≤ Rn R n k x ∧ Rn R n k x ≤ 1)
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hRmin' := trim_binder sub2 hB2 (Φ' := fun k x => rmin ≤ K.c0 * Rn R n k x)
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hVolC' := trim_binder sub3 hB3
    (Φ' := fun k x => ENNReal.ofReal ((K.c0 * Rn R n k x) ^ K.βm) ≤
      μ (ball (vertexPoint ε η (x (Tn T n k x).toNat)) (K.c0 * Rn R n k x)))
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hVolY' := trim_binder sub4 hB4
    (Φ' := fun k x => ∀ y ∈ ball (0 : ℂ) (1 - Rn R n k x / 4),
      ENNReal.ofReal ((Rn R n k x / 4) ^ K.βm) ≤ μ (ball y (Rn R n k x / 4)))
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hWalk' := trim_binder sub5 hB5
    (Φ' := fun k x => x (Tn T n k x).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
      ε ^ K.ω ≤ Rn R n k x / 8 ∧
        Rn R n k x / 8 ≤ infDist (vertexPoint ε η (x (Tn T n k x).toNat)) (sphere 0 ρc))
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hfinE' := trim_binder sub6 hB6
    (Φ' := fun k x => expectedExitTime m
      (interiorCellVertices ε η (ball (vertexPoint ε η (x (Tn T n k x).toNat)) (Rn R n k x / 4)))
      (x (Tn T n k x).toNat) ≠ ⊤)
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hsc' := trim_binder sub7 hB7
    (Φ' := fun k x => 4 * ε ^ α ≤
      (μ (ball (vertexPoint ε η (x (Tn T n k x).toNat)) (K.c0 * Rn R n k x))).toReal)
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hεα' := trim_binder sub8 hB8 (Φ' := fun k x => ε ^ α ≤ Rn R n k x / 100)
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hεmass' := trim_binder sub9 hB9 (Φ' := fun k x => ε ^ α ≤ (Rn R n k x / 4) ^ K.βm)
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hb' := trim_binder sub10 hB10
    (Φ' := fun k x => x (Tn T n k x).toNat ∈ cellVertices ε η (sphere (Z k x) (4 * Rn R n k x / 3)))
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hx1' := trim_binder sub11 hB11
    (Φ' := fun k x => ‖vertexPoint ε η (x (Tn T n k x).toNat)‖ < 1 - Rn R n k x / 4)
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hmomS' := trim_binder sub12 hB12 (Φ' := fun k x => ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 →
      ENNReal.ofReal (ε ^ α) ≤ μ D → ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (fun k hk x h => h)
  have hgood' := trim_binder sub13 hB13
    (Φ' := fun k x => IsGoodAnnulusEvent μ K.c0 C_good (Rn R n k x) (Z k x))
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hN' := trim_binder sub14 hB14 (Φ' := fun k x => ∀ (R' : ℝ) (z' : ℂ), 0 < R' →
      ∃ t : Finset ℂ, t.card ≤ N_cov ∧ (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧
        annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (fun k hk x h => h)
  have hpos' := trim_binder sub15 hB15
    (Φ' := fun k x => 0 < ⨅ w ∈ annulus (Z k x) (Rn R n k x) (2 * Rn R n k x), μ (ball w (K.c0 * Rn R n k x)))
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hdbl' := trim_binder sub16 hB16
    (Φ' := fun k x => (μ (ball (vertexPoint ε η (x (Tn T n k x).toNat)) (3 * K.c0 * Rn R n k x))).toReal
      ≤ Dbl * (μ (ball (vertexPoint ε η (x (Tn T n k x).toNat)) (K.c0 * Rn R n k x))).toReal)
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  -- (4) the moment integrability on the trimmed stopping times
  have hmom1' : ∀ k, Integrable ({w | Tn T n k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (Rn R n k) (Tn T n k) w)
        (postTimePath (fun n w => w n) (Tn T n k) w) : ℕ) : ℝ))) (srwLaw m a) := by
    intro k
    by_cases hk : k ≤ n
    · simp only [Tn_of_le hk, Rn_of_le hk]; exact hmom1 k hk
    · simp only [Tn_of_not_le hk]; simp
  have hmom2' : ∀ k, Integrable ({w | Tn T n k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (Rn R n k) (Tn T n k) w)
        (postTimePath (fun n w => w n) (Tn T n k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a) := by
    intro k
    by_cases hk : k ≤ n
    · simp only [Tn_of_le hk, Rn_of_le hk]; exact hmom2 k hk
    · simp only [Tn_of_not_le hk]; simp
  -- (5) the pointwise chain on the trimmed end
  have hone := MatedCRT.Lemma68CellR.hone_exitQ_walk_of_env_cellR K ε η hη hprop hε hεc hμNull m a A hA n
    (τU := Bᶜ.indicator τU) hr hr1 hq0c hq hC hCw hCg (T := Tn T n) (hT := isStoppingTime_Tn n hT)
    (R := Rn R n) (hR := measurable_Rn n hT hR) (hmom1 := hmom1') (hmom2 := hmom2') (hRr := hRr')
    (hL68 := hL68) (rmin := rmin) (hRmin := hRmin') (hVolC := hVolC') (hVolY := hVolY') (hGreen := hGreen)
    (hWalk := hWalk') (hCountGood := hCountGood) (ζc := ζc) (hζc0 := hζc0) (hζc1 := hζc1)
    (ρcell := ρcell) (hρgap := hρgap) (hCellGood := hCellGood) (hRcell := hRcell') (hωκ := hωκ)
    (hεcell := hεcell) (hfinE := hfinE') (hsc := hsc') (Z := Z)
    (hεα := hεα') (hεmass := hεmass') (hb := hb') (hx1 := hx1') (hmomS := hmomS') (hgood := hgood')
    (hN := hN') (hpos := hpos') (hdbl := hdbl')
  -- (6) transfer of the conclusion back to `T k`, `R k` on `k ≤ n`
  intro k hk
  filter_upwards [hone k hk, hBa] with x hx hxB hP
  have hxT : x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (Tn T n k) (Bᶜ.indicator τU) := by
    rw [Tn_of_le hk]; exact (mem_prefix_indicator x).2 ⟨hP, hxB⟩
  have hc := hx hxT
  have hcong := condExp_testInd_congr m a A ε η (isStoppingTime_Tn n hT k) (hT k)
    (Tn_of_le (T := T) (n := n) hk) (Rn_of_le (R := R) (n := n) hk) x
  calc (srwLaw m a)[testInd A ε η (T k) (R k) | (hT k).measurableSpace] x
      = (srwLaw m a)[testInd A ε η (Tn T n k) (Rn R n k) | (isStoppingTime_Tn n hT k).measurableSpace] x :=
        hcong.symm
    _ ≤ 1 - q := hc

/-- **The one-test bound with almost-sure walk binders (shell times).** Same conclusion as
`shellOneTest_of_direct_reduced68` (HoneReduced68.lean:41). The prefix binders are restated almost surely for `k ≤ n`;
`hfinE` is discharged as there (`finite_expectedExitTime`, Audit/StatementsSec3Sec5M1.lean:441). -/
theorem shellOneTest_of_direct_ae {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    (Kset : Set ℂ) (Rf : ℂ → ℝ) (r s d q0 α C_exit C_good C : ℝ) {N_cov : ℕ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C))
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * (shellDbl68 C_good) ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hTdom : ∀ k, ∃ D : Set ℤ, D.Finite ∧ ∀ w, shellExit ε η Kset r s d Rf k w < ⊤ →
      shellExit ε η Kset r s d Rf k w ≤ vExitTime D w)
    (hRbd : ∀ k, ∃ s' : ℝ, ∀ w, shellExit ε η Kset r s d Rf k w < ⊤ →
      Rf (shellCentre ε η Kset r s d k w) ≤ s')
    (hRr : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k x) ∧ Rf (shellCentre ε η Kset r s d k x) ≤ 1)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (rmin : ℝ)
    (hRmin : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        rmin ≤ K.c0 * Rf (shellCentre ε η Kset r s d k x))
    (hVolC : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ENNReal.ofReal ((K.c0 * Rf (shellCentre ε η Kset r s d k x)) ^ K.βm)
          ≤ μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k x))))
    (hVolY : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ∀ y ∈ ball (0 : ℂ) (1 - Rf (shellCentre ε η Kset r s d k x) / 4),
          ENNReal.ofReal ((Rf (shellCentre ε η Kset r s d k x) / 4) ^ K.βm)
            ≤ μ (ball y (Rf (shellCentre ε η Kset r s d k x) / 4)))
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ K.ω ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        x (shellExit ε η Kset r s d Rf k x).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
          ε ^ K.ω ≤ Rf (shellCentre ε η Kset r s d k x) / 8 ∧
          Rf (shellCentre ε η Kset r s d k x) / 8 ≤
            infDist (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat)) (sphere 0 ρc))
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (ρcell : ℝ) (hρgap : ρc < ρcell)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρcell).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hRcell : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        Rf (shellCentre ε η Kset r s d k x) / 4 < ρcell - ρc)
    (hωκ : K.ω ≤ 2 / (2 + γ) ^ 2 - ζc)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hsc : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k x)))).toReal)
    (hεα : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ε ^ α ≤ Rf (shellCentre ε η Kset r s d k x) / 100)
    (hεmass : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ε ^ α ≤ (Rf (shellCentre ε η Kset r s d k x) / 4) ^ K.βm)
    (hb : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        x (shellExit ε η Kset r s d Rf k x).toNat ∈
          cellVertices ε η (sphere (shellCentre ε η Kset r s d k x) (4 * Rf (shellCentre ε η Kset r s d k x) / 3)))
    (hx1 : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ‖vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat)‖
          < 1 - Rf (shellCentre ε η Kset r s d k x) / 4)
    (hmomS : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ μ D →
        ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
          exitTimeMoment m (interiorCellVertices ε η D) a N ≤
            ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
              (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
                ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        IsGoodAnnulusEvent μ K.c0 C_good (Rf (shellCentre ε η Kset r s d k x)) (shellCentre ε η Kset r s d k x))
    (hN : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
          (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        0 < ⨅ w ∈ annulus (shellCentre ε η Kset r s d k x) (Rf (shellCentre ε η Kset r s d k x))
          (2 * Rf (shellCentre ε η Kset r s d k x)), μ (ball w (K.c0 * Rf (shellCentre ε η Kset r s d k x))))
    (hdbl : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        (μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
          (3 * K.c0 * Rf (shellCentre ε η Kset r s d k x)))).toReal
          ≤ shellDbl68 C_good * (μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k x)))).toReal) :
    ShellOneTestAt m a A η ε Kset τU r s d Rf n (q0 / (1 + Real.log (1 / r)) ^ 2) := by
  have hpair := fun k : ℕ => BallExitMeas68.hmom_pair_of_finiteDomain_meas hlf hcons hη hprop hε a
    (T := fun k => shellExit ε η Kset r s d Rf k) (R := fun k w => Rf (shellCentre ε η Kset r s d k w))
    (fun k => isStoppingTime_shellExit ε η Kset r s d Rf k)
    (fun k => measurable_shellRadius_stopped ε η Kset r s d Rf k) hTdom hRbd k
  have hfinD : ∀ (x : ℂ) (ρ : ℝ), (interiorCellVertices ε η (ball x ρ)).Finite := fun x ρ =>
    (TraceInputs68.cellVertices_finite_of_tendsto hε hprop Metric.isBounded_ball).subset fun _ hk => hk.1
  exact hone_exitQ_walk_of_env_direct_ae (T := fun k => shellExit ε η Kset r s d Rf k)
    (R := fun k w => Rf (shellCentre ε η Kset r s d k w)) K ε η hη hprop hε hεc hμNull m a A hA n hr hr1 hq0c rfl
    hC hCw hCg (fun k => isStoppingTime_shellExit ε η Kset r s d Rf k)
    (fun k => measurable_shellRadius_stopped ε η Kset r s d Rf k) (fun k _ => (hpair k).1) (fun k _ => (hpair k).2)
    hRr hL68 rmin hRmin hVolC hVolY hGreen hWalk hCountGood ζc hζc0 hζc1 ρcell hρgap hCellGood hRcell hωκ hεcell
    (fun k _ => Filter.Eventually.of_forall fun x _ =>
      MatedCRT.Audit.StatementsSec3Sec5M1.finite_expectedExitTime hlf hcons (hfinD _ _) _)
    hsc hεα hεmass hb hx1 hmomS hgood hN hpos hdbl

theorem shellOneTest_of_direct_ae_rcell {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    (Kset : Set ℂ) (Rf : ℂ → ℝ) (r s d q0 α C_exit C_good C : ℝ) {N_cov : ℕ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C))
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * (shellDbl68 C_good) ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hTdom : ∀ k ≤ n, ∃ D : Set ℤ, D.Finite ∧ ∀ᵐ x ∂srwLaw m a,
      shellExit ε η Kset r s d Rf k x < ⊤ → shellExit ε η Kset r s d Rf k x ≤ vExitTime D x)
    (hRbd : ∀ k ≤ n, ∃ s' : ℝ, ∀ᵐ x ∂srwLaw m a,
      shellExit ε η Kset r s d Rf k x < ⊤ → Rf (shellCentre ε η Kset r s d k x) ≤ s')
    (hRr : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k x) ∧ Rf (shellCentre ε η Kset r s d k x) ≤ 1)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (rmin : ℝ)
    (hRmin : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        rmin ≤ K.c0 * Rf (shellCentre ε η Kset r s d k x))
    (hVolC : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ENNReal.ofReal ((K.c0 * Rf (shellCentre ε η Kset r s d k x)) ^ K.βm)
          ≤ μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k x))))
    (hVolY : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ∀ y ∈ ball (0 : ℂ) (1 - Rf (shellCentre ε η Kset r s d k x) / 4),
          ENNReal.ofReal ((Rf (shellCentre ε η Kset r s d k x) / 4) ^ K.βm)
            ≤ μ (ball y (Rf (shellCentre ε η Kset r s d k x) / 4)))
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ K.ω ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        x (shellExit ε η Kset r s d Rf k x).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
          ε ^ K.ω ≤ Rf (shellCentre ε η Kset r s d k x) / 8 ∧
          Rf (shellCentre ε η Kset r s d k x) / 8 ≤
            infDist (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat)) (sphere 0 ρc))
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (ρcell : ℝ) (hρgap : ρc < ρcell)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρcell).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hd : 0 < d) (aW : ℝ)
    (hRf : ∀ z ∈ shortEligible ρc d aW, Rf z ≤ d ^ aW)
    (hEl : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        shellCentre ε η Kset r s d k x ∈ shortEligible ρc d aW)
    (hcut : d ^ aW < ρcell - ρc)
    (hωκ : K.ω ≤ 2 / (2 + γ) ^ 2 - ζc)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hsc : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k x)))).toReal)
    (hεα : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ε ^ α ≤ Rf (shellCentre ε η Kset r s d k x) / 100)
    (hεmass : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ε ^ α ≤ (Rf (shellCentre ε η Kset r s d k x) / 4) ^ K.βm)
    (hb : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        x (shellExit ε η Kset r s d Rf k x).toNat ∈
          cellVertices ε η (sphere (shellCentre ε η Kset r s d k x) (4 * Rf (shellCentre ε η Kset r s d k x) / 3)))
    (hx1 : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ‖vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat)‖
          < 1 - Rf (shellCentre ε η Kset r s d k x) / 4)
    (hmomS : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ μ D →
        ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
          exitTimeMoment m (interiorCellVertices ε η D) a N ≤
            ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
              (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
                ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        IsGoodAnnulusEvent μ K.c0 C_good (Rf (shellCentre ε η Kset r s d k x)) (shellCentre ε η Kset r s d k x))
    (hN : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
          (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        0 < ⨅ w ∈ annulus (shellCentre ε η Kset r s d k x) (Rf (shellCentre ε η Kset r s d k x))
          (2 * Rf (shellCentre ε η Kset r s d k x)), μ (ball w (K.c0 * Rf (shellCentre ε η Kset r s d k x))))
    (hdbl : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        (μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
          (3 * K.c0 * Rf (shellCentre ε η Kset r s d k x)))).toReal
          ≤ shellDbl68 C_good * (μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k x)))).toReal) :
    ShellOneTestAt m a A η ε Kset τU r s d Rf n (q0 / (1 + Real.log (1 / r)) ^ 2) := by
  have hpair := fun (k : ℕ) (hk : k ≤ n) => BallExitMeasAe68.hmom_pair_ae hlf hcons hη hprop hε a
    (T := fun k => shellExit ε η Kset r s d Rf k) (R := fun k w => Rf (shellCentre ε η Kset r s d k w))
    (fun k => isStoppingTime_shellExit ε η Kset r s d Rf k)
    (fun k => measurable_shellRadius_stopped ε η Kset r s d Rf k) k (hTdom k hk) (hRbd k hk)
  have hfinD : ∀ (x : ℂ) (ρ : ℝ), (interiorCellVertices ε η (ball x ρ)).Finite := fun x ρ =>
    (TraceInputs68.cellVertices_finite_of_tendsto hε hprop Metric.isBounded_ball).subset fun _ hk => hk.1
  exact hone_exitQ_walk_of_env_direct_ae (T := fun k => shellExit ε η Kset r s d Rf k)
    (R := fun k w => Rf (shellCentre ε η Kset r s d k w)) K ε η hη hprop hε hεc hμNull m a A hA n hr hr1 hq0c rfl
    hC hCw hCg (fun k => isStoppingTime_shellExit ε η Kset r s d Rf k)
    (fun k => measurable_shellRadius_stopped ε η Kset r s d Rf k) (fun k hk => (hpair k hk).1) (fun k hk => (hpair k hk).2)
    hRr hL68 rmin hRmin hVolC hVolY hGreen hWalk hCountGood ζc hζc0 hζc1 ρcell hρgap hCellGood (Lemma68RcellDischarge.hRcell_of_eligible hd hRf hEl hcut) hωκ hεcell
    (fun k _ => Filter.Eventually.of_forall fun x _ =>
      MatedCRT.Audit.StatementsSec3Sec5M1.finite_expectedExitTime hlf hcons (hfinD _ _) _)
    hsc hεα hεmass hb hx1 hmomS hgood hN hpos hdbl

end Lemma68LeafAe
end MatedCRT

#print axioms MatedCRT.Lemma68LeafAe.hone_exitQ_walk_of_env_direct_ae
#print axioms MatedCRT.Lemma68LeafAe.shellOneTest_of_direct_ae
#print axioms MatedCRT.Lemma68LeafAe.shellOneTest_of_direct_ae_rcell
