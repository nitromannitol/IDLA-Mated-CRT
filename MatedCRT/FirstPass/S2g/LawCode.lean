import MatedCRT.Defs.Setting
import Mathlib.Data.Rat.Denumerable

/-! # Countable codes of space-time processes (q1, fp-S2g; law encoding of Lemmas 2.5 and 2.6)

Lemmas 2.5 and 2.6 are stated as equalities in law of (circle process, family code), not of raw processes.
The code of a `Prop`-valued space-time process `F : ℝ × ℂ → Prop` is its restriction to the countable set
`{(q_i, z_j)}` of rational times and rational-complex points, a `Bool`-valued sequence on `ℕ × ℕ` with the product
σ-algebra. The code of a family is the code of its process; a code determines the process on the countable set,
and the decoder for the full family is in the notes (`notes/fp-gaps/CHATGPT-idla-2-5-2-6-law-encoding.md` Section 3).

Enumerations: `ratTime` lists all of `ℚ` (times `≤ 0` are excluded in the code by the decision `0 < q`, as in
`globalFamilyProcess`), and `ratPoint` lists the dense set `ℚ + iℚ` of `ℂ`. -/

namespace MatedCRT

open MeasureTheory

/-- Enumeration of the rational numbers, as real times. -/
noncomputable def ratTime (i : ℕ) : ℝ :=
  ((Denumerable.ofNat ℚ i : ℚ) : ℝ)

/-- Enumeration of the dense countable set `ℚ + iℚ` of `ℂ`. -/
noncomputable def ratPoint (j : ℕ) : ℂ :=
  let p : ℚ × ℚ := Denumerable.ofNat (ℚ × ℚ) j
  (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

open Classical in
/-- The countable code of a `Prop`-valued space-time process: its values on `{(q_i, z_j)}`. -/
noncomputable def processCode (F : ℝ × ℂ → Prop) : (ℕ × ℕ) → Bool :=
  fun ij => decide (F (ratTime ij.1, ratPoint ij.2))

/-- The global code of a family `{Λ_t}_{t > 0}` (Lemma 2.6): the code of the process `globalFamilyProcess Λ`. -/
noncomputable def globalCode (Λ : ℝ → Set ℂ) : (ℕ × ℕ) → Bool :=
  processCode (globalFamilyProcess Λ)

/-- The stopped code of a family stopped at `T` (Lemma 2.5): the lifetime `T` together with the code of the masked
process `familyProcess Λ T`, which records the sets `Λ_t` for `0 < t < T` only. -/
noncomputable def stoppedCode (T : ℝ) (Λ : ℝ → Set ℂ) : ℝ × ((ℕ × ℕ) → Bool) :=
  (T, processCode (familyProcess Λ T))

open Classical in
/-- The code map is measurable: each coordinate is the evaluation at one point followed by `decide`. -/
theorem measurable_processCode : Measurable processCode := by
  refine Measurable.of_eval fun ij => ?_
  have hdec : Measurable (fun b : Prop => decide b) :=
    measurable_to_countable' fun _ => MeasurableSpace.measurableSet_top
  exact hdec.comp (measurable_pi_apply (ratTime ij.1, ratPoint ij.2))

/-- The map `(x, F) ↦ (x, code F)` is measurable on a product with the process space. -/
theorem measurable_prod_processCode {X : Type*} [MeasurableSpace X] :
    Measurable (fun p : X × (ℝ × ℂ → Prop) => (p.1, processCode p.2)) :=
  measurable_fst.prodMk (measurable_processCode.comp measurable_snd)

/-- The map `(T, F) ↦ (T, code F)` is measurable: the stopped code is a measurable function of the lifetime and the
masked process. -/
theorem measurable_stoppedCode_map :
    Measurable (fun p : ℝ × (ℝ × ℂ → Prop) => (p.1, processCode p.2)) :=
  measurable_fst.prodMk (measurable_processCode.comp measurable_snd)

end MatedCRT
