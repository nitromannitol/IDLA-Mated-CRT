# Sections 3 and 5: partial statement audit (2026-11-06)

This is not a sealed audit. `FROZEN.md:1` says the freeze is not in force;
there is no manifest binding declaration bytes, source hashes, versions and
providers. The remaining binder, definition-body, consumption and axiom audits
are not complete. No statement here is certified faithful.

* **3.1 — WRONG** (Draft/Section3.lean:42): the corrected paper:977 permits
  every connected set; the draft's compact test permits a closed segment.
  `Audit.Refutations.not_discretePotentialTightnessStmt` (Refutations.lean:317)
  proves its negation assuming `MepsScalingInput` and a valid environment.
  Corrected form requires an open domain and polynomially summable deterministic
  scale range, and scales boundary data by ε⁻¹ (Steps/Sec3/DiscretePotentialTightness.lean:102).
  Its implication to the common restricted form is checked in
  `Audit/StatementsSec3Sec5M1.lean`; this does not establish the Draft.
* **3.2 — MISMATCH, corrected form**: the current corrected paper:1001–1014
  chooses ξ' after χ and before C', requires ξ' ≤ χ. Draft/Section3.lean:76
  has this scope and condition. The corrected Step at
  Steps/Sec3/DiscretePotentialTightness.lean:71 chooses ξ' after C' and does
  not require ξ' ≤ χ; it is weaker. Lean checks Draft ⇒ Step. Consequently
  `CORRECTED-FORMS.md:61` describes an earlier Draft when it says the current
  Draft is false because χ can be less than a previously selected ξ. That
  argument does not apply to the current Draft. No converse is established.
* **5.2 — relation checked, source fidelity pending**: the relaxed form
  implies the Draft by `generalIDLALowerBound_of_relaxed`; this does not
  discharge the relaxed form's cited inputs or audit definitions.

Remaining: independent complete audits of 3.3–3.7, 5.1, 5.3–5.4, all
expanded binders and definition bodies, and term-level checks of final forms.
