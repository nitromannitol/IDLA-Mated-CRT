import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.SelectionStep
import MatedCRT.Draft.Section3Prepared

/-! Simultaneous pathwise extraction for the prepared Lemma 3.1. -/

namespace MatedCRT.Tightness

open Filter Topology Set Metric

/-- Countably many domains share one pathwise subsequence whenever their proxy
coordinates are eventually bounded and their interior and conditional boundary
moduli satisfy the asymptotic estimates of the proof of Lemma 3.1. -/
theorem simultaneous_tightness_of_proxy_bounds
    {D : ℕ → Set ℂ} {η : ℝ → ℂ} {ε mε : ℕ → ℝ} {u : ℕ → ℕ → ℤ → ℝ}
    {Cm : ℝ} (hDo : ∀ j, IsOpen (D j)) (hDb : ∀ j, Bornology.IsBounded (D j))
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hCm : 0 < Cm)
    (hm : ∀ᶠ n in atTop, 0 ≤ (mε n)⁻¹ ∧ (mε n)⁻¹ ≤ Cm * ε n)
    (hEQ : ∀ j K, IsCompact K → K ⊆ D j →
      IsVertexAsymptoticallyEquicontinuous ε η (u j) K)
    (P : ℕ → Prop)
    (hboundary : ∀ j, P j → IsVertexAsymptoticallyEquicontinuous ε η (u j) (closure (D j)))
    (hbound : ∀ j c, ∃ M, ∀ᶠ n in atTop, |proxyCoord ε η (D j) mε (u j) n c| ≤ M) :
    ∃ Φ : ℕ → ℕ, StrictMono Φ ∧ ∀ j, ∃ v : ℂ → ℝ, ContinuousOn v (D j) ∧
      (∀ O : Set ℂ, IsCompact O → closure O ⊆ D j →
        TendstoUniformlyOn (fun k => rescale (mε (Φ k)) (ε (Φ k)) η (u j (Φ k))) v atTop O) ∧
      (P j → TendstoUniformlyOn
        (fun k => rescale (mε (Φ k)) (ε (Φ k)) η (u j (Φ k))) v atTop (closure (D j))) := by
  let y : ℕ → ℕ → ℝ := fun n i => proxyCoord ε η (D i.unpair.1) mε (u i.unpair.1) n i.unpair.2
  refine ⟨diagSeq y, diagSeq_strictMono y, ?_⟩
  intro j
  have hy : ∀ c, ∃ l, Tendsto (fun k => proxyCoord ε η (D j) mε (u j)
      (diagSeq y k) c) atTop (𝓝 l) := by
    intro c
    obtain ⟨M, hM⟩ := hbound j c
    have hM' : ∀ᶠ n in atTop, |y n (Nat.pair j c)| ≤ M := by simpa [y] using hM
    have h := tendsto_diagSeq y (Nat.pair j c) hM'
    simpa [y] using h
  obtain ⟨v, hv, hlocal, hclosed⟩ := tightness_of_proxies (hDo j) (hDb j) hη hp hsurj
    hε hε0 hCm hm (hEQ j) (diagSeq_strictMono y) hy
  exact ⟨v, hv, hlocal, fun hP => hclosed (hboundary j hP)⟩

end MatedCRT.Tightness
