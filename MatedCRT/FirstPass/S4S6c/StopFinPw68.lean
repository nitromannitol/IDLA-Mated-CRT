import MatedCRT.FirstPass.S4S6c.HoneExitGeom68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S4S6c.ShellWindowRf68
import MatedCRT.FirstPass.S6h.Core
import MatedCRT.FirstPass.S6r.ShellOmega
import MatedCRT.FirstPass.S6r.Shells.Parameters

/-!
# The stopped shell vertex lies in a finite set (binder `hstopFin`)

The binder `hstopFin` of `shellOneTest_at_of_goodEnv_loc_g` (B1Assembly68.lean) asks, at one environment `ω`
under `FullAdmAt`, that for each shell `k` there is a finite set `F` of vertices such that almost surely, on the event
that the shell exit `T_k` is finite, the exit vertex `X_{T_k}` lies in `F`: a finite stopped-range localisation of the shell exits.

Route (pointwise at `ω`, with `η = S.η ω` and `m = S.mult ε ω`).
* `K = fillCells ε η Θ` is nonempty and bounded (`ConfigOK`: `closure K ⊆ B(0, ρ/2)`, `B(0, s₀) ⊆ K`, `0 < s₀`).
  So the two-sided shell `Σ_{k+1} = twoSidedShell K r (shellOffset s (k+1))` is bounded, and the vertex set
  `A = V^ε(Σ_{k+1})` is finite (`TraceInputs68.cellVertices_finite_of_tendsto`, `η` proper).
* The shell hit `C_{k+1}` is a vertex of `A`. The centre `shellCentre` depends on the path only through the hit vertex,
  so the union `D` of the balls `B(c_v, 4R(c_v)/3)`, `v ∈ A`, is bounded, and `B = V^ε(D)` is finite.
* At the finite exit time `n`, either the exit vertex is the hit vertex (so it lies in `A`), or the exit predicate fails
  at `n - 1`: the vertex `X_{n-1}` is interior to the ball, so its cell meets `D` and `X_{n-1} ∈ B`. The step
  `X_{n-1} → X_n` is an edge almost surely (`srwLaw_step_ae_adjacent`), so `X_n` lies in the neighbour set of `B`,
  which is finite by local finiteness of `m`.
* `F = A ∪ ⋃_{u ∈ B} {b | m u b ≠ 0}` is finite and does not depend on the path.

The proof reads the window radius `R` only as a function, so the sparsity exponent `s1` and the window constant `c0W`
are free. The pointwise hypotheses at `ω` are: `η` proper, `m` locally finite, the degree positivity `hdeg` of `m`
(the input of the a.s. step adjacency), and `0 < ε`, `0 < s₀`.
Terminology: Armstrong-Kuusi-Mourrat (cells `H^ε_a`, vertex sets `V^ε(D)`, interior vertices), Duplantier-Sheffield
(boundary-length parametrisation `η`), Armitage-Gardiner (balls and their frontiers).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68StopFinPw

open MatedCRT.Lemma68Omega MatedCRT.Lemma68Window MatedCRT.Lemma68Config MatedCRT.Lemma68WindowRf

/-- A two-sided shell over a nonempty set `K ⊆ closedBall 0 M` is bounded. If `|dist(x,K) - r/2| = λ` then
`dist(x,K) < r/2 + λ + 1`, so some `y ∈ K` has `dist(x,y) < r/2 + λ + 1`, and `dist(x,0) ≤ |r/2 + λ + 1| + M`. -/
lemma isBounded_twoSidedShell {K : Set ℂ} {M : ℝ} (hK : K ⊆ closedBall (0 : ℂ) M) (hKne : K.Nonempty)
    (r lam : ℝ) : Bornology.IsBounded (twoSidedShell K r lam) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
  refine ⟨|r / 2 + lam + 1| + M, fun x hx => ?_⟩
  have hx' : |infDist x K - r / 2| = lam := hx
  have hle : infDist x K ≤ r / 2 + lam := by
    have := le_abs_self (infDist x K - r / 2)
    rw [hx'] at this
    linarith
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff hKne).1 (show infDist x K < r / 2 + lam + 1 by linarith)
  have hy0 : dist y 0 ≤ M := mem_closedBall.1 (hK hy)
  have htri : dist x 0 ≤ dist x y + dist y 0 := dist_triangle x y 0
  rw [mem_closedBall]
  have := le_abs_self (r / 2 + lam + 1)
  linarith

/-- The value of `firstTime` is attained: if `firstTime P = n` then `P n`. -/
lemma pred_at_firstTime {P : ℕ → Prop} {n : ℕ} (h : firstTime P = n) : P n := by
  obtain ⟨m, hm, hPm⟩ := (firstTime_le_iff P n).1 h.le
  have hle : firstTime P ≤ m := (firstTime_le_iff P m).2 ⟨m, le_rfl, hPm⟩
  rw [h] at hle
  have hnm : n ≤ m := by exact_mod_cast hle
  obtain rfl : m = n := le_antisymm hm hnm
  exact hPm

/-- Before the first time `firstTime P = n`, the predicate fails. -/
lemma not_pred_of_lt_firstTime {P : ℕ → Prop} {n m : ℕ} (h : firstTime P = n) (hm : m < n) : ¬ P m := by
  intro hPm
  have hle : firstTime P ≤ m := (firstTime_le_iff P m).2 ⟨m, le_rfl, hPm⟩
  rw [h] at hle
  have : n ≤ m := by exact_mod_cast hle
  omega

/-- **The stopped shell vertex is a.s. in a finite set.** This is the binder `hstopFin` of
`shellOneTest_at_of_goodEnv_loc_g` (B1Assembly68.lean), stated for a free sparsity exponent `s1` (the caller takes
`s1 := shellS1CG γ CG`) and a free window constant `c0W` (the caller takes `c0W := shellC0 CG`). The hypotheses at `ω`:
`0 < ε`, `0 < s₀` (for the nonemptiness of `K`), `η` proper, `m` locally finite, and the degree positivity `hdeg`. -/
theorem hstopFin_pw_g {γ ρ s₀ ε s1 r ζ C c0W : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (i : Lemma68Config.Config68) (hε : 0 < ε) (hs₀ : 0 < s₀)
    (htend : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hloc : IsLocallyFiniteMult (S.mult ε ω))
    (hdeg : ∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤) :
    FullAdmAt s1 S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∃ F : Set ℤ, F.Finite ∧
        ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x < ⊤ →
            x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) k x).toNat ∈ F := by
  intro hFA k _hk
  obtain ⟨_, hcl, hball⟩ := hFA.1
  set K : Set ℂ := fillCells ε (S.η ω) (↑i.Θ : Set ℤ) with hKdef
  have hKne : K.Nonempty := ⟨0, hball (Metric.mem_ball_self hs₀)⟩
  have hKM : K ⊆ closedBall (0 : ℂ) (ρ / 2) :=
    subset_closure.trans (hcl.trans ball_subset_closedBall)
  set s : ℝ := dyadicD r ^ shortExp ζ with hsdef
  set R : ℂ → ℝ := windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω with hRdef
  set A : Set ℤ := cellVertices ε (S.η ω) (twoSidedShell K r (shellOffset s (k + 1))) with hAdef
  have hA : A.Finite :=
    TraceInputs68.cellVertices_finite_of_tendsto hε htend (isBounded_twoSidedShell hKM hKne r _)
  obtain ⟨cen, hcen_def⟩ : ∃ cen : ℤ → ℂ,
      ∀ v, cen v = shellCentre ε (S.η ω) K r s (dyadicD r) k (fun _ => v) := ⟨_, fun _ => rfl⟩
  set D : Set ℂ := ⋃ v ∈ A, ball (cen v) (4 * R (cen v) / 3) with hDdef
  have hD : Bornology.IsBounded D := (Bornology.isBounded_biUnion hA).2 fun v _ => isBounded_ball
  set B : Set ℤ := cellVertices ε (S.η ω) D with hBdef
  have hB : B.Finite := TraceInputs68.cellVertices_finite_of_tendsto hε htend hD
  refine ⟨A ∪ ⋃ u ∈ B, {b | S.mult ε ω u b ≠ 0}, hA.union (hB.biUnion fun u _ => hloc u), ?_⟩
  filter_upwards [Lemma68HoneExitGeom.srwLaw_step_ae_adjacent (S.mult ε ω) hdeg i.a] with x hx hT
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hT.ne
  have hQ := hn.symm
  unfold shellExit at hQ
  obtain ⟨hHn, _⟩ := pred_at_firstTime hQ
  have hHfin : shellHit ε (S.η ω) K r s k x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hHn
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.1 hHfin
  have hHh : firstTime (fun m => x m ∈ A) = h := hh.symm
  have hAx : x h ∈ A := pred_at_firstTime hHh
  have hhn : h ≤ n := by
    rw [← hh] at hHn
    exact_mod_cast hHn
  have hcen : shellCentre ε (S.η ω) K r s (dyadicD r) k x = cen (x h) := by
    rw [hcen_def]
    unfold shellCentre
    rw [← hh, ENat.toNat_natCast]
  rw [← hn, ENat.toNat_natCast]
  rcases Nat.lt_or_ge h n with hlt | hge
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    have hHp : shellHit ε (S.η ω) K r s k x ≤ (p : ℕ∞) := by
      rw [← hh]
      exact_mod_cast (by omega : h ≤ p)
    have hpI : x p ∈ interiorCellVertices ε (S.η ω) (ball (shellCentre ε (S.η ω) K r s (dyadicD r) k x)
        (4 * R (shellCentre ε (S.η ω) K r s (dyadicD r) k x) / 3)) := by
      by_contra hc
      exact (not_pred_of_lt_firstTime hQ (Nat.lt_succ_self p)) ⟨hHp, hc⟩
    have hsub : ball (shellCentre ε (S.η ω) K r s (dyadicD r) k x)
        (4 * R (shellCentre ε (S.η ω) K r s (dyadicD r) k x) / 3) ⊆ D := by
      rw [hcen]
      exact Set.subset_biUnion_of_mem (u := fun v => ball (cen v) (4 * R (cen v) / 3)) hAx
    have hxpB : x p ∈ B := Set.Nonempty.mono (inter_subset_inter_right _ hsub) hpI.1
    exact Set.mem_union_right _ (Set.mem_iUnion₂.2 ⟨x p, hxpB, hx p⟩)
  · obtain rfl : h = n := le_antisymm hhn hge
    exact Set.mem_union_left _ hAx

end Lemma68StopFinPw
end MatedCRT

#print axioms MatedCRT.Lemma68StopFinPw.isBounded_twoSidedShell
#print axioms MatedCRT.Lemma68StopFinPw.pred_at_firstTime
#print axioms MatedCRT.Lemma68StopFinPw.not_pred_of_lt_firstTime
#print axioms MatedCRT.Lemma68StopFinPw.hstopFin_pw_g
