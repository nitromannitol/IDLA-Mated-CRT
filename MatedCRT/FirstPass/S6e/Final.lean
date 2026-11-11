import Mathlib
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.OfSteps
import MatedCRT.FirstPass.S6e.Cutoff
import MatedCRT.FirstPass.S6e.Admissible

/-!
# FIRST PASS: the final event of LEMMA68 (D2, bridge §2)

Sources: the D2 step of the Lemma 6.8 open parts (lines 957-989 of that write-up), and the bridge argument
§2.1 (admissibility guard, lines 95-135) and §2.2 (mesh argument,
lines 136-177). The configuration quantity `exitF ε ω r i` (the quenched exit probability `exitQ` of bridge §1) and
its admissibility guard `Adm ε ω r i` are parameters: they are instantiated in `FirstPass/S6h.lean`.

The quantifier order of D2 is kept: first `ε`, then every `r ∈ [α ε, dd ω]` and every configuration `i`, on
`E ε ∩ G`. The scalar `Q` depends on the mesh `ε` (bridge §2.2). Outside the guard `Adm` the scalar is `0`
(bridge §2.1): the guard is essential, since the raw exit probability of the empty configuration is `1`.
-/

open MeasureTheory Filter Topology Set

namespace MatedCRT

namespace Lemma68Final

open Classical in
/-- (bridge §2.1) The guarded scalar: the zero extension of `exitF` outside the admissible configurations `Adm`. -/
noncomputable def guardedExit {Ω ι : Type*} (Adm : ℝ → Ω → ℝ → ι → Prop) (exitF : ℝ → Ω → ℝ → ι → ℝ) :
    ℝ → Ω → ℝ → ι → ℝ :=
  fun ε ω r i => if Adm ε ω r i then exitF ε ω r i else 0

lemma guardedExit_of_adm {Ω ι : Type*} {Adm : ℝ → Ω → ℝ → ι → Prop} {exitF : ℝ → Ω → ℝ → ι → ℝ}
    {ε : ℝ} {ω : Ω} {r : ℝ} {i : ι} (h : Adm ε ω r i) :
    guardedExit Adm exitF ε ω r i = exitF ε ω r i := by
  simp [guardedExit, h]

lemma guardedExit_of_not_adm {Ω ι : Type*} {Adm : ℝ → Ω → ℝ → ι → Prop} {exitF : ℝ → Ω → ℝ → ι → ℝ}
    {ε : ℝ} {ω : Ω} {r : ℝ} {i : ι} (h : ¬ Adm ε ω r i) :
    guardedExit Adm exitF ε ω r i = 0 := by
  simp [guardedExit, h]

/-- (D2, mesh-indexed form; bridge §2.2) If `E` has probability tending to one (`ProbTendsToOne`), the field event `G`
has probability one, and on `E ε ∩ G` every quenched configuration bound of (C17) holds for all admissible radii
`r ∈ [α ε, dd ω]`, with the scalar `Q ε ω r i` depending on the mesh `ε`, then the uniform bound `≤ 1/2` of the printed
Lemma 6.8 (`s₂ = 1/2`) holds with probability tending to one. -/
theorem probTendsToOne_uniform_half {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (hE : ProbTendsToOne P E) {G : Set Ω} (hG : P Gᶜ = 0)
    {α : ℝ → ℝ} (hα : ∀ ε, 0 < ε → 0 < α ε)
    {dd : Ω → ℝ} {R : ℝ} (hdd : ∀ ω, dd ω ≤ R) {ζ q0 : ℝ} (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ : 0 < ζ)
    (hζ' : ζ < 1 / 2) (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ) (Q : ℝ → Ω → ℝ → ι → ℝ)
    (hpt : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι,
      ∃ N : ℕ, r ^ (-ζ) / 200 ≤ (N : ℝ) ∧ Q ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N) :
    ProbTendsToOne P (fun ε => {ω | ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι, Q ε ω r i ≤ 1 / 2}) := by
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hG
  have hGa : ProbTendsToOne P (fun _ => G) := probTendsToOne_of_ae hGae
  refine (hE.inter hGa).mono_pos ?_
  intro ε hε ω hω r hαr hrd i
  obtain ⟨N, hN, hQ⟩ := hpt ε hε ω hω r hαr hrd i
  have hr0 : 0 < r := (hα ε hε).trans_le hαr
  have hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ := (hrd.trans (hdd ω)).trans hR
  exact hQ.trans (Lemma68Cutoff.D1_le_half hq0 hq1 hζ hζ' hr0 hrA hN)

/-- (D2 with the guard; bridge §2.1 and §2.2) The bound `hpt` is needed only on the admissible configurations `Adm`;
outside `Adm` the guarded scalar is `0` and the witness `N = ⌈r^(-ζ)/200⌉₊` works, since `1 - q0/(1+log(1/r))² ≥ 0`
for `0 < r ≤ 1`. The conclusion is the guarded uniform bound of the printed Lemma 6.8. -/
theorem probTendsToOne_uniform_half_guarded {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (hE : ProbTendsToOne P E) {G : Set Ω} (hG : P Gᶜ = 0)
    {α : ℝ → ℝ} (hα : ∀ ε, 0 < ε → 0 < α ε)
    {dd : Ω → ℝ} {R : ℝ} (hdd : ∀ ω, dd ω ≤ R) {ζ q0 : ℝ} (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ : 0 < ζ)
    (hζ' : ζ < 1 / 2) (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ)
    (Adm : ℝ → Ω → ℝ → ι → Prop) (exitF : ℝ → Ω → ℝ → ι → ℝ)
    (hpt : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι, Adm ε ω r i →
      ∃ N : ℕ, r ^ (-ζ) / 200 ≤ (N : ℝ) ∧ exitF ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N) :
    ProbTendsToOne P (fun ε => {ω | ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : ι,
      guardedExit Adm exitF ε ω r i ≤ 1 / 2}) := by
  refine probTendsToOne_uniform_half hE hG hα hdd hq0 hq1 hζ hζ' hR (guardedExit Adm exitF) ?_
  intro ε hε ω hω r hαr hrd i
  by_cases hA : Adm ε ω r i
  · rw [guardedExit_of_adm hA]
    exact hpt ε hε ω hω r hαr hrd i hA
  · rw [guardedExit_of_not_adm hA]
    have hr0 : 0 < r := (hα ε hε).trans_le hαr
    have hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ := (hrd.trans (hdd ω)).trans hR
    have hA1 : Lemma68Cutoff.rAmp q0 ζ ≤ 1 := min_le_left _ _
    have hr1 : r ≤ 1 := hrA.trans hA1
    have hlog : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr0 hr1)
    have hbase : 0 ≤ 1 - q0 / (1 + Real.log (1 / r)) ^ 2 := by
      have h1 : q0 ≤ (1 + Real.log (1 / r)) ^ 2 := by nlinarith
      have h2 : q0 / (1 + Real.log (1 / r)) ^ 2 ≤ 1 :=
        (div_le_one (pow_pos (by linarith) 2)).2 h1
      linarith
    exact ⟨⌈r ^ (-ζ) / 200⌉₊, Nat.le_ceil _, pow_nonneg hbase _⟩

/-- `ENNReal.ofReal (1/2) = 1/2`, the value of the probability threshold `s₂` in the extended scale. -/
lemma ofReal_half : ENNReal.ofReal (1 / 2) = 1 / 2 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- (write-up (11), bridge §5) For a finite measure, a real bound `P.real s ≤ 1/2` gives the extended bound
`P s ≤ 1/2`; finiteness is what makes `P s = ENNReal.ofReal (P.real s)`. -/
lemma measure_le_half_of_real_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {s : Set Ω}
    (h : P.real s ≤ 1 / 2) : P s ≤ 1 / 2 := by
  have hfin : P s ≠ ⊤ := measure_ne_top P s
  calc P s = ENNReal.ofReal (P.real s) := (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal h
    _ = 1 / 2 := ofReal_half

/-- (bridge §5, `s₂ = 1/2`) The predicate `Phi` of `Lemma68Admissible` holds as soon as the real quenched exit
probability `P.real (exitEvent (killed ε η Θ F0 x) A)` is at most `1/2` (write-up §6 Step 2, B1 exit event). -/
theorem phi_of_real_le {ε : ℝ} {η : ℝ → ℂ} {Θ F0 A : Finset ℤ} {a : ℤ} {s1 βm x : ℝ} {P : Measure (ℕ → ℤ)}
    [IsFiniteMeasure P]
    (h : P.real (Lemma68Walk.exitEvent (Lemma68Admissible.killed ε η Θ F0 x) (↑A : Set ℤ)) ≤ 1 / 2) :
    Lemma68Admissible.Phi ε η Θ F0 A a s1 βm P x :=
  fun _ => measure_le_half_of_real_le h

open Classical in
/-- (exit time) If every position `x k`, `k ≤ n`, lies in `W`, then `n` is strictly before the exit time from `W`
(`vExitTime W x` is the first time `x` leaves `W`, `Defs/RandomWalk.lean`). -/
lemma lt_vExitTime_of_forall {W : Set ℤ} {x : ℕ → ℤ} {n : ℕ} (h : ∀ k ≤ n, x k ∈ W) :
    (n : ENat) < vExitTime W x := by
  unfold vExitTime
  split_ifs with hex
  · have hlt : n < Nat.find hex := by
      by_contra hle
      have hle' : Nat.find hex ≤ n := not_lt.1 hle
      exact (Nat.find_spec hex) (h _ hle')
    exact_mod_cast hlt
  · exact ENat.natCast_lt_top n

/-- (relation to `UniformConstantOrderLowerBoundStmt`, bridge §5: the complement step of the Lemma 6.8-to-6.7 reduction)
If `U ⊆ W`, `U \ A ⊆ Z` and the exit event `exitEvent U A` has probability at most `1/2`, then with probability at least
`1/2` the walk visits `Z` before it leaves `W`. Its complement is a visit to `U \ A` before the exit from `U`. -/
theorem visit_half_of_exit_le {P : Measure (ℕ → ℤ)} [IsProbabilityMeasure P] {U A W Z : Set ℤ}
    (hUW : U ⊆ W) (hZ : U \ A ⊆ Z) (h : P (Lemma68Walk.exitEvent U A) ≤ 1 / 2) :
    ENNReal.ofReal (1 / 2) ≤ P {x | ∃ n : ℕ, (n : ENat) < vExitTime W x ∧ x n ∈ Z} := by
  rw [ofReal_half]
  have hsub : (Lemma68Walk.exitEvent U A)ᶜ ⊆ {x | ∃ n : ℕ, (n : ENat) < vExitTime W x ∧ x n ∈ Z} := by
    intro x hx
    have hx' : ∃ n : ℕ, (∀ k ≤ n, x k ∈ U) ∧ x n ∉ A := by
      by_contra hc
      exact hx fun n hn => not_not.1 fun h => hc ⟨n, hn, h⟩
    obtain ⟨n, hn, hnA⟩ := hx'
    exact ⟨n, lt_vExitTime_of_forall fun k hk => hUW (hn k hk), hZ ⟨hn n le_rfl, hnA⟩⟩
  have hunion : (1 : ENNReal) ≤ P (Lemma68Walk.exitEvent U A) + P (Lemma68Walk.exitEvent U A)ᶜ := by
    calc (1 : ENNReal) = P univ := measure_univ.symm
      _ = P (Lemma68Walk.exitEvent U A ∪ (Lemma68Walk.exitEvent U A)ᶜ) := by rw [union_compl_self]
      _ ≤ _ := measure_union_le _ _
  have h1 : 1 - P (Lemma68Walk.exitEvent U A) ≤ P (Lemma68Walk.exitEvent U A)ᶜ :=
    tsub_le_iff_right.2 (by rw [add_comm]; exact hunion)
  have h2 : 1 - 1 / 2 ≤ 1 - P (Lemma68Walk.exitEvent U A) := tsub_le_tsub_left h 1
  have h3 : (1 : ENNReal) - 1 / 2 = 1 / 2 := by
    rw [one_div, ENNReal.one_sub_inv_two]
  calc (1 / 2 : ENNReal) = 1 - 1 / 2 := h3.symm
    _ ≤ P (Lemma68Walk.exitEvent U A)ᶜ := h2.trans h1
    _ ≤ _ := measure_mono hsub

/-- (relation to `UniformConstantOrderLowerBoundStmt`, bridge §5) With `U = W \ Θ` and `A = S' \ Θ`, the boundary-start
exit bound gives the visit bound `ENNReal.ofReal (1/2) ≤ P(∃ n < τ_W, x n ∈ W \ (S' ∪ Θ))` of that statement. -/
theorem visit_half_of_exit_le_target {P : Measure (ℕ → ℤ)} [IsProbabilityMeasure P] {W Θ S' : Set ℤ}
    (h : P (Lemma68Walk.exitEvent (W \ Θ) (S' \ Θ)) ≤ 1 / 2) :
    ENNReal.ofReal (1 / 2) ≤ P {x | ∃ n : ℕ, (n : ENat) < vExitTime W x ∧ x n ∈ W \ (S' ∪ Θ)} :=
  visit_half_of_exit_le Set.sdiff_subset
    (by
      rintro x ⟨⟨hxW, hxΘ⟩, hxA⟩
      exact ⟨hxW, fun hu => hu.elim (fun hS => hxA ⟨hS, hxΘ⟩) fun hT => hxΘ hT⟩) h

end Lemma68Final

end MatedCRT
