import MatedCRT.FirstPass.S4S6c.HoneSetup68

/-!
# Discharge of the cap-radius input and of the leaf binder `hL68` (z12, fp-S4S6c-setup-239)

Following chat 239 §2 (notes/fp-gaps/CHATGPT-239-idla-hU-named-inputs-PRO.md, l.114-236), checked against the definitions:

* `capRadius ε η B = ⨅ z : ℚ × ℚ, ⨆ v : B, ⨅ q : ratInt ε v, edist z (η q)` (S6e/Geometry.lean:46) and
  `cRad = (capRadius).toReal` (S6e/Admissible.lean:35). The infimum runs over rational centres, so a witness centre
  `z` with every cell `cell ε η v`, `v ∈ B`, meeting the open ball `ball z r` gives `cRad ε η B < r`.
* `cRad_lt_of_subset_cellVertices_ball`: this witness statement, with the rational centre chosen by density.
* `hL68_fixedOmega'`: the leaf binder `hL68` at one `ω` for every `r > 0` with `FullAdmAt (sparsityS₁ γ)`. The named
  input `hcap` of `hL68_of_clause` is discharged by the witness lemma; no hypothesis on `r` beyond `0 < r`.

Terminology: Armstrong-Kuusi-Mourrat (shells, good annuli), Armitage-Gardiner (exit times of balls),
Duplantier-Sheffield (quantum-length balls, `η` as the boundary-length parametrisation).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68HoneSetup239

open MatedCRT.Lemma68Admissible MatedCRT.Lemma68Geometry MatedCRT.Lemma68HoneSetup
open MatedCRT.Lemma68Window

/-- A cell meeting an open ball contains the image of a rational parameter lying in that ball: the rationals are dense
in the parameter interval `Icc (ε (k-1)) (ε k)` of the cell `cell ε η k = η '' Icc (ε (k-1)) (ε k)`, and `η` is
continuous. This is the density step that lets the infimum over rational parameters in `capRadius` see the cell. -/
theorem exists_ratInt_mem_ball_of_cell {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε) {k : ℤ} {z : ℂ}
    {r : ℝ} (h : (cell ε η k ∩ Metric.ball z r).Nonempty) :
    ∃ q : ℚ, q ∈ ratInt ε k ∧ dist (η q) z < r := by
  obtain ⟨p, ⟨t, ht, rfl⟩, hp⟩ := h
  have hab : ε * ((k : ℝ) - 1) < ε * k := mul_lt_mul_of_pos_left (by linarith) hε
  have hU : IsOpen (η ⁻¹' Metric.ball z r) := Metric.isOpen_ball.preimage hη
  have htU : t ∈ η ⁻¹' Metric.ball z r := hp
  have hcl : t ∈ closure (Ioo (ε * ((k : ℝ) - 1)) (ε * k)) := by
    rw [closure_Ioo hab.ne]
    exact ht
  have hne : ((η ⁻¹' Metric.ball z r) ∩ Ioo (ε * ((k : ℝ) - 1)) (ε * k)).Nonempty :=
    mem_closure_iff.1 hcl _ hU htU
  have hD : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
  obtain ⟨x, hxr, hxO⟩ := hD.exists_mem_open (hU.inter isOpen_Ioo) hne
  obtain ⟨q, rfl⟩ := hxr
  exact ⟨q, Ioo_subset_Icc_self hxO.2, hxO.1⟩

/-- **Witness bound for `c_B`.** If every vertex of `B` has its cell meeting the open ball `ball z r`, then
`c_B = cRad ε η B < r` (chat 239 §2; the infimum in `capRadius` is over rational centres). Proof: pick a rational
parameter `Q v` per vertex with `dist (η (Q v)) z < r`; the largest of these distances is `< r`; a rational centre `w`
within `δ/2` of `z` (where `δ = r - max`) has `dist (w, η (Q v)) < r - δ/2` for every `v`. The empty case gives
`cRad ∅ = 0` (`capRadius ∅ = ⨅ z, 0`). -/
theorem cRad_lt_of_subset_cellVertices_ball {ε r : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε) (hr : 0 < r)
    {z : ℂ} {B : Finset ℤ} (hsub : (↑B : Set ℤ) ⊆ cellVertices ε η (Metric.ball z r)) :
    cRad ε η B < r := by
  by_cases hB : B.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hB
    subst hB
    simp [cRad, capRadius, hr]
  have hQ : ∀ v ∈ B, ∃ q : ℚ, q ∈ ratInt ε v ∧ dist (η q) z < r :=
    fun v hv => exists_ratInt_mem_ball_of_cell hη hε (hsub hv)
  choose! Q hQI hQd using hQ
  obtain ⟨v0, hv0, hmax⟩ := B.exists_max_image (fun v => dist (η (Q v)) z) hB
  set δ : ℝ := r - dist (η (Q v0)) z with hδdef
  have hδpos : 0 < δ := by
    have := hQd v0 hv0
    linarith
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - δ / 4 < z.re + δ / 4 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - δ / 4 < z.im + δ / 4 by linarith)
  have hwz : dist (Complex.mk (a : ℝ) (b : ℝ)) z < δ / 2 := by
    rw [Complex.dist_eq_re_im, Real.sqrt_lt' (by linarith)]
    simp only
    nlinarith [mul_pos (sub_pos.2 ha1) (sub_pos.2 ha2), mul_pos (sub_pos.2 hb1) (sub_pos.2 hb2),
      mul_pos hδpos hδpos]
  have hcap : capRadius ε η B ≤ ENNReal.ofReal (r - δ / 2) := by
    unfold capRadius
    refine (iInf_le _ ((a, b) : ℚ × ℚ)).trans ?_
    refine iSup_le fun v => ?_
    refine (iInf_le _ (⟨Q v.1, hQI v.1 v.2⟩ : ratInt ε v.1)).trans ?_
    show edist (Complex.mk (a : ℝ) (b : ℝ)) (η (Q v.1)) ≤ ENNReal.ofReal (r - δ / 2)
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have h1 := dist_triangle (Complex.mk (a : ℝ) (b : ℝ)) z (η (Q v.1))
    have h2 : dist (η (Q v.1)) z ≤ dist (η (Q v0)) z := hmax v.1 v.2
    have h3 : dist z (η (Q v.1)) = dist (η (Q v.1)) z := dist_comm _ _
    linarith
  have hlt : capRadius ε η B < ENNReal.ofReal r :=
    lt_of_le_of_lt hcap ((ENNReal.ofReal_lt_ofReal_iff hr).2 (by linarith))
  exact ENNReal.toReal_lt_of_lt_ofReal hlt

open scoped Classical in
/-- **The leaf binder `hL68` at one environment `ω`, for every radius `r > 0` (no `hcap`).** At `ω` with the
continuous curve `S.η ω`, `FullAdmAt (sparsityS₁ γ)` at `r` gives the sparsity clause of `Admissible` at
`(sparsityS₁ γ, (2+γ)²/2+1)`; the rewrites `hK1`, `hK2` identify these with `(K.s1, K.βm)` (for `K = shellK68 …`,
`shellK68_params`, ShellHoneInst68.lean). The cap-radius input of `hL68_of_clause` is supplied by
`cRad_lt_of_subset_cellVertices_ball`, applied to the filtered set `A.filter (· ∈ cellVertices ε η (ball z r))`. -/
theorem hL68_fixedOmega' {γ ρ s₀ ε : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (K : Constants68 γ ρ) (hK1 : K.s1 = Lemma68Config.sparsityS1 γ)
    (hK2 : K.βm = (2 + γ) ^ 2 / 2 + 1) (hε : 0 < ε) (ω : Ω) (hηω : Continuous (S.η ω))
    (i : Lemma68Config.Config68) :
    ∀ r : ℝ, 0 < r → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, (((↑i.A : Set ℤ) ∩ cellVertices ε (S.η ω) (Metric.ball z r)).ncard : ℝ)
        < K.s1 * r ^ (2 * K.βm) / ε := by
  intro r hr hFA
  have hs1 : 0 < K.s1 := by
    rw [hK1]
    exact Lemma68Config.sparsityS1_pos γ
  have hcl : ∀ B ⊆ i.A, B.Nonempty →
      r ≤ cRad ε (S.η ω) B ∨ tRad ε K.s1 K.βm B < r := by
    have h := hFA.2.2.2
    rw [hK1, hK2]
    exact h
  have hcapz : ∀ z : ℂ, cRad ε (S.η ω) (i.A.filter (fun v => v ∈ cellVertices ε (S.η ω) (Metric.ball z r))) < r :=
    fun z => cRad_lt_of_subset_cellVertices_ball hηω hε hr
      (fun v hv => (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2)
  exact fun z => hL68_of_clause K i.A hε hr hs1 hcl hcapz z

end Lemma68HoneSetup239
end MatedCRT

#print axioms MatedCRT.Lemma68HoneSetup239.exists_ratInt_mem_ball_of_cell
#print axioms MatedCRT.Lemma68HoneSetup239.cRad_lt_of_subset_cellVertices_ball
#print axioms MatedCRT.Lemma68HoneSetup239.hL68_fixedOmega'
