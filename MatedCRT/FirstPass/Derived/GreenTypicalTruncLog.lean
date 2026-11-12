import MatedCRT.FirstPass.Derived.ExitTimeNearTypicalSplit
import MatedCRT.FirstPass.S3c.ExitTimeBridge
import MatedCRT.FirstPass.S6n
import MatedCRT.Draft.Section2
import LatticeProb.Analysis.TruncatedLog

/-!
# Typical part of the Green kernel bound (BG20, proof of Lemma 5.8, (5.43))

In the proof of (5.38) of Berestycki–Gwynne (2020), Lemma 5.8, the vertices `b ∈ A` are split into those whose cells
meet `B_{ε^β}(η(a))` (the near part, counted by (5.41)) and the others (the typical part). For a typical vertex
`|η(a) − η(b)| ≥ ε^β`, so the Green kernel bound of Lemma 5.4 (`GreenKernelUpperBoundStmt`, Lemma 2.14 of the paper)
applies: `g_B(a, b) ≤ C log (1/|η(a) − η(b)|) + C`. Its right side is the value at `(η(a), η(b))` of the truncated
logarithmic kernel at scale `ε^{-β}` (`LatticeProb.TruncatedLog.truncLogKernel`), which is nonnegative, bounded by
`C (β log ε⁻¹ + 1)` and `C ε^{-β}`-Lipschitz in its second point: the form in which the typical sum is compared with an
integral against the LQG area measure (Lemma A.5).

* `le_norm_vertexPoint_sub_of_not_mem`: a vertex outside `V^ε(B_r(η(a)))` sits at distance at least `r` from `η(a)`;
* `greenKernel_le_truncLogKernel`: on the event of Lemma 5.4, `g_B(a, b) ≤ truncLogKernel C ε^{-β} (η(a)) (η(b))` for
  every typical vertex `b`;
* `polyHighProb_greenKernel_le_truncLogKernel`: the same bound with polynomially high probability, from Lemma 5.4;
* `expectedExitTime_le_near_truncLogKernel`: the near/typical split (5.39)–(5.44) with the truncated kernel as typical
  bound.
-/

open HarmonicBalls

namespace MatedCRT

open Set Metric MeasureTheory LatticeProb.TruncatedLog

namespace GreenTypicalTruncLog

/-- A vertex whose cell misses `B_r(η(a))` sits at distance at least `r` from `η(a)`: its position `η(b)` lies in its
cell. -/
theorem le_norm_vertexPoint_sub_of_not_mem {ε r : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε) {a b : ℤ}
    (hb : b ∉ cellVertices ε η (ball (vertexPoint ε η a) r)) :
    r ≤ ‖vertexPoint ε η a - vertexPoint ε η b‖ := by
  refine not_lt.mp fun h => hb ⟨vertexPoint ε η b, Lemma68C12Geom.vertexPoint_mem_cell hε b, ?_⟩
  rw [mem_ball, dist_comm, dist_eq_norm]
  exact h

/-- **Typical bound** (BG20 (5.43)). On the event of Lemma 5.4 (Green kernel upper bound on `V^ε(B_ρ)` for points at
distance at least `ε^β`), every vertex `b ∈ V^ε(B_ρ)` whose cell misses `B_{ε^β}(η(a))` satisfies
`g_B(a, b) ≤ truncLogKernel C ε^{-β} (η(a)) (η(b))`. -/
theorem greenKernel_le_truncLogKernel {m : ℤ → ℤ → ℕ} {B : Set ℤ} {ε β C ρ : ℝ} {η : ℝ → ℂ} (hε : 0 < ε)
    (hev : ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ b ∈ cellVertices ε η (ball 0 ρ),
      ε ^ β ≤ ‖vertexPoint ε η a - vertexPoint ε η b‖ →
      greenKernel m B a b ≤ C * Real.log (1 / ‖vertexPoint ε η a - vertexPoint ε η b‖) + C)
    {a b : ℤ} (ha : a ∈ cellVertices ε η (ball 0 ρ)) (hb : b ∈ cellVertices ε η (ball 0 ρ))
    (hbY : b ∉ cellVertices ε η (ball (vertexPoint ε η a) (ε ^ β))) :
    greenKernel m B a b ≤ truncLogKernel C (ε ^ (-β)) (vertexPoint ε η a) (vertexPoint ε η b) := by
  have hd := le_norm_vertexPoint_sub_of_not_mem hε.le hbY
  have hinv : (ε ^ (-β))⁻¹ ≤ ‖vertexPoint ε η a - vertexPoint ε η b‖ := by
    rwa [Real.rpow_neg hε.le, inv_inv]
  refine (hev a ha b hb hd).trans ?_
  rw [one_div]
  exact le_truncLogKernel_of_inv_le hinv

/-- **Typical bound with polynomially high probability** (BG20 (5.43)), from Lemma 5.4 (`GreenKernelUpperBoundStmt`,
Lemma 2.14 of the paper): there is `β₀ > 0` such that for each `ρ ∈ (0, 1)` there is `C > 0` with: for every
`β ≤ β₀`, with polynomially high probability as `ε → 0`, for all `a, b ∈ V^ε(B_ρ)` with `b ∉ V^ε(B_{ε^β}(η(a)))`,
`g_{V^ε(B_ρ) \ V^ε(∂B_ρ)}(a, b) ≤ truncLogKernel C ε^{-β} (η(a)) (η(b))`. The exponent may be decreased ("if `β` is
chosen sufficiently small", BG20 p. 35): for `ε < 1`, `ε^{β₀} ≤ ε^β`. -/
theorem polyHighProb_greenKernel_le_truncLogKernel {𝒮 : SpaceFillingSLEModel}
    (h214 : GreenKernelUpperBoundStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ≤ β₀ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      b ∉ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (ε ^ β)) →
      greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a b ≤
        truncLogKernel C (ε ^ (-β)) (vertexPoint ε (S.η ω) a) (vertexPoint ε (S.η ω) b)} := by
  obtain ⟨β₀, hβ₀, h⟩ := h214 γ hγ hγ2
  refine ⟨β₀, hβ₀, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨C, hC, h'⟩ := h ρ hρ hρ1
  refine ⟨C, hC, fun β hββ₀ Ω _ S hS => ?_⟩
  refine S3cBridge.polyHighProb_mono_ae_small one_pos (h' Ω S hS) (ae_of_all _ fun _ => trivial)
    fun ε hε hε1 ω hω _ a ha b hb hbY => greenKernel_le_truncLogKernel hε (fun a ha b hb hd => ?_) ha hb hbY
  exact hω a ha b hb ((Real.rpow_le_rpow_of_exponent_ge hε hε1.le hββ₀).trans hd)

/-- **Near/typical split with the truncated logarithmic kernel** (BG20 (5.39)–(5.44)). Let `A ⊆ B` be finite vertex
sets, `A ⊆ V^ε(B_ρ)`, `a ∈ V^ε(B_ρ)`, all vertices of `A` of positive degree, and assume the event of Lemma 5.4 for
the Green kernel of `B`. If at most `K` vertices of `A` have cells meeting `B_{ε^β}(η(a))` (near part, (5.41)) and
`G_B(a, b) ≤ M` for those (BG20 Lemma 5.6), then
`E^a τ_A ≤ K M + ∑_{b ∈ A} deg(b) · truncLogKernel C ε^{-β} (η(a)) (η(b))`. -/
theorem expectedExitTime_le_near_truncLogKernel {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A B : Set ℤ} (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B)
    {ε β C ρ K M : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (hAρ : A ⊆ cellVertices ε η (ball 0 ρ))
    (hev : ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ b ∈ cellVertices ε η (ball 0 ρ),
      ε ^ β ≤ ‖vertexPoint ε η a - vertexPoint ε η b‖ →
      greenKernel m B a b ≤ C * Real.log (1 / ‖vertexPoint ε η a - vertexPoint ε η b‖) + C)
    {a : ℤ} (ha : a ∈ cellVertices ε η (ball 0 ρ))
    (hY : ∀ s : Finset ℤ,
      (s : Set ℤ) ⊆ A ∩ cellVertices ε η (ball (vertexPoint ε η a) (ε ^ β)) → (s.card : ℝ) ≤ K)
    (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ A ∩ cellVertices ε η (ball (vertexPoint ε η a) (ε ^ β)), greenFn m B a b ≤ M)
    (hdeg : ∀ b ∈ A, 0 < mdeg m b) :
    expectedExitTime m A a ≤ ENNReal.ofReal (K * M + ∑ b ∈ hA.toFinset,
      (mdeg m b : ℝ) * truncLogKernel C (ε ^ (-β)) (vertexPoint ε η a) (vertexPoint ε η b)) :=
  ExitTimeMoment.expectedExitTime_le_near_typical_greenKernel hlf hcons hA hB hAB a _ hY hM0 hM hdeg
    (fun b => truncLogKernel C (ε ^ (-β)) (vertexPoint ε η a) (vertexPoint ε η b))
    (fun _ _ => truncLogKernel_nonneg _ _ _ _)
    fun _ hb hbY => greenKernel_le_truncLogKernel hε hev ha (hAρ hb) hbY

end GreenTypicalTruncLog

end MatedCRT
