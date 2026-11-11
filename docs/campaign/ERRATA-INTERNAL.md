# Internal errata record: Internal DLA on mated-CRT maps

Not for the coauthor. Moved from docs/campaign/ERRATA-for-Ewain.md on 2026-11-11 (the INTERNAL section of that file, unchanged in content).

One line each, with the reason. Nothing below is an error of the printed paper.

- [C22]: superseded by [C26]; its Step 3 covering estimate is replaced, and the corrected draft carries no [C22] marker.
- [C21] editorial lines at corrected tex:2326 and 2350 (two sentences of surrounding exposition): wording only, covered by the [C21] item.
- [C13] boundary-stability consequence in the proof of Lemma 4.8 (corrected tex:2132-2135: the polynomial boundary data differ from their projected values by $o(m_\varepsilon)$): marked [C13] on 2026-11-11; source fp-gaps/CHATGPT-idla-printed-3-5.md (boundary-stability step, consequence of [C13]); unconfirmed as an error: paper/idla_mated_crt-corrected.tex:2132.
- [C48], [C49] (fp-gaps tags): Harmonic-Balls results (HB Lemma 10.5, Proposition 10.6), not corrections of this paper.
- Reading R1 (vertex 0 versus $a^\varepsilon_0$): literal reading at each place, a convention of the formalization; no change to the paper.
- S1 (Lemmas 2.5, 2.6): field through its circle-average process; statement convention only.
- S2 (frozen Lemmas 3.5, 3.6): Hölder data on a neighbourhood of $\overline{B_r(z)}$; statement convention; the successor with continuous data is [C13].
- S3 (Lemma 4.8, item 1): off the pole; statement scope only.
- S4 (Lemma 7.4): stopped odometer on its own cluster; statement scope only.
- S5 (annealed probability): outer integral / outer measure convention.
- S6 (Lemma 3.1): $u^\varepsilon$ is $\sigma(h,\eta)$-measurable; formalization convention.
- S7 (literature inputs in MatedCRT/External: SLE-model inputs, quantum cone scaling): input conventions, not paper errors.

- [C29] (translated application of Lemma 6.6 in the proof of Lemma 6.8; marker at corrected tex:3003): moved out of the email tag "(C26 to C31)" on 2026-11-11. The translation is described in the Lemma 6.4 item of the email.
- Removed from the paper body on 2026-11-11 (AUDIT-R2 M5): the subsection "Uses of Lemma 3.6 in the paper" (git history of paper/idla_mated_crt-corrected.tex before the AUDIT-R2 M5 commit). It listed the uses in the Lemma 3.5 proof, the normalized-exit-time argument, odometer compactness and the subsequential properties, and it stated: the Lemma 3.5 Step 3 limit has Laplacian -lambda_0 mu_h, not the displayed -1, and the zero-boundary control comes from the lens comparison at corrected tex:1144-1172. The Step 3 point is routed as M7 (MQ-li-7b-d), not closed here.
- Removed from Appendix B and appendix-occupation-C16.tex on 2026-11-11 (AUDIT-R2 M5): the coefficient-2 counterexample. It is now in the email Lemma 3.4 item.
- Removed from Appendix C (appendix-lemma36-C13.tex, former lines 42-59) on 2026-11-11 (AUDIT-R2 M5): the three issues (i)-(iii) and the notation remark. They are now in the email Lemma 3.6 item.
- Email tag "(C26 to C31)" changed to "(C26 to C28, C30, C31)" on 2026-11-11 (AUDIT-R2 M6).
- Reuse of kappa as a constant (kappa is also the SLE parameter): left as is, notation only (AUDIT-R2 IDLA (A)).
