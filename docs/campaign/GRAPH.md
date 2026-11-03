# Proof graph of arXiv:2211.04891 (corrected draft paper/idla_mated_crt-corrected.tex)

For each numbered result: the proof location (tex lines) and the results and literature facts its printed proof uses,
with the tex line of first use. Extracted from the `\ref`/`\cite` commands of each proof and checked against the text;
"max principle" and similar unreferenced standard facts are listed when the text names them. Numbers follow
docs/campaign/INVENTORY.tsv. Abbreviations: BG20 = Berestycki-Gwynne, Random walks on mated-CRT planar maps and
Liouville Brownian motion (berestycki2020random); HB22 = Bou-Rabee-Gwynne, Harmonic balls in LQG (bou2022harmonic);
GMS19 = Gwynne-Miller-Sheffield, Harmonic functions on mated-CRT maps (gwynne2019harmonic); LL10 = Lawler-Limic,
Random walk: a modern introduction; LBG92 = Lawler-Bramson-Griffeath (lawler1992internal); LP09 = Levine-Peres,
Strong spherical asymptotics (levine2009strong); DF91 = Diaconis-Fulton (diaconis1991growth); DMS14 =
Duplantier-Miller-Sheffield (duplantier2014liouville); DS11 = Duplantier-Sheffield (duplantier2011liouville);
SW16 = Sheffield-Wang (sheffield2016field).

## Section 1
- Thm 1.4 (251), Thm 1.6 (283): proof Section 8.1 (3280-3336): Lemma 2.6 @3288 (scale invariance, to remove the
  restriction t < T), Prop 8.1 @3298.

## Section 2
- Fact 2.2 (474): literature (lines 490-492): I-III from the definition (eq:measure-lim; DS11), IV DS11 Prop 2.1 (fixed
  map), SW16 (all maps simultaneously).
- Thm 2.3 (509): proof 587-594: Lemma 2.5 @590, Lemma 2.4 @593 (and T^b =d T, T > 0).
- Lemma 2.4 (533): proof 540-545: eq (gff) restriction to B_1 = whole-plane GFF - gamma log; HB22 Prop 1.3 (locality),
  HB22 Thms 1.1, 5.5, Lemma 3.2 @542; HB22 Prop 5.6 (uniqueness, "proof still works up to fixed time") @543.
- Lemma 2.5 (548): proof 565-585: eq (quantum-cone-scaling) = DMS14 Prop 4.13(i) (line 453); Lemma 2.4 @570; Fact 2.2
  (coordinate change + Weyl scaling) @578; HB22 Prop 5.6 @584.
- Lemma 2.6 (597): proof = "proof of Lemma 2.5 applied to the infinite family of Theorem 2.3" (line 596).
- Lemmas 2.7, 2.8, 2.9, 2.10, Thm 2.11, Lemmas 2.14, 2.15, 2.16, 2.18: cited (BG20 Lemma A.1, Lemma 2.4, Lemma A.4,
  Cor A.6, Thm 1.2, Lemma 5.4, Lemma 5.6, Lemma 4.4, Prop 5.1); eq (meps-scaling) = BG20 (1.8) (line 733).
- Lemma 2.13 (824): proof 830-833: elementary (neighbour with larger value).
- Lemma 2.17 (888): proof 900-913: BG20 Lemma A.3 @903 + Borel-Cantelli; Step 2 = BG20 (5.3) in the proof of BG20 Cor 5.2.
- Lemma 2.19 (933): proof 945-947: Lemma 2.17 (with rho' in (rho,1)) @946, Lemma 2.18 @946.

## Section 3
- Lemma 3.1 (973): proof 1013-1083: Lemma 2.8 @1014, Lemma 2.19 @1014, Lemma 3.2 @1014, Lemma 2.13 @1039; Arzela-Ascoli.
- Lemma 3.2 (997): cited GMS19 Thm 3.9.
- Lemma 3.3 (1106): proof 1179-1229: Lemma 2.10 @1183, Lemma 3.4 @1184, Lemma 2.14 @1186, Lemma 2.8 @1187, Lemma 3.1
  @1191, Lemma 2.13 @1221.
- Lemma 3.4 (1119): proof 1128-1175: Lemma 2.19 @1131, Lemma 2.8 @1131, Thm 2.11 @1140, Lemma 2.17 @1155, Lemma 2.18
  @1155; continuum: E_y[int_0^tau f(LBM)] = int G f dmu_h.
- Lemma 3.5 (1233): proof 1298-1376: LL10 Cor 6.2.4 @1316, Lemma 3.6 @1317, Lemma 3.4 @1317, Lemma 2.13 @1339,
  Lemma 2.19 @1345, Lemma 3.1 @1346, HB22 Prop 2.5 @1374, Lemma 3.3 @1375.
- Lemma 3.6 (1254): proof 1268-1291: Lemma 3.4 (method) @1269, Thm 2.11 @1280, Lemma 2.8 @1286.
- Lemma 3.7 (1391): proof 1404-1531: Lemma 3.3 @1409, Lemma 2.9 @1410, Lemma 2.19 @1410, Lemma 3.5 @1411, Lemma 3.1
  @1419, Lemma 3.2 @1466, Lemma 2.8 @1476, Lemma 2.17 @1525.

## Section 4
- Thm 4.1 (1594): proof Section 4.4 (1905-1951): Thm 2.3 @1906, Lemma 4.8 @1910, Lemma 4.6 @1910 (uniqueness of the
  obstacle problem: the subsequential limit is (m0/6) w_t^{B_rho}).
- Prop 4.2 (1611): proof 1618-1670 (assuming Thm 4.1): Thm 4.1 @1618, Thm 2.3 @1621, Lemma 2.13 @1630, Lemma 3.3 @1640,
  Lemma 2.8 @1648.
- Lemmas 4.3, 4.4, 4.5 (1679, 1697, 1705): special cases of Lemmas A.2, A.3, A.4 via the map of lines 3398-3407.
- Lemma 4.6 (1720): proof 1751-1754: Lemma 4.7, Lemma 4.4, Lemma 3.1, Lemma 3.5 @1752-1753.
- Lemma 4.7 (1729): proof 1736-1749: Lemma 4.3 @1737, Lemma 2.18 @1741, Lemma 2.17 @1747.
- Lemma 4.8 (1761): proof 1773-1902: Lemma 3.3 @1774, Lemma 3.5 @1777, Lemma 3.7 @1780, Lemma 4.6 @1781, Lemma 4.3
  @1785, Lemma 4.4 @1805, Lemma 2.13 @1806.

## Section 5
- Prop 5.1 (1959): proof 2015-2032: Lemmas 5.2, 5.3, 5.4 @2015, Lemma 2.8 @2022, Prop 4.2 @2027.
- Lemma 5.2 (1974): proof 2132-2229: LL10 Lemma 4.6.1 @2176, LBG92 Lemma 3.3 @2211 (reformulation of LBG92 Section 3).
- Lemma 5.3 (1995): proof 2067-2127: Lyons-Peres Exercise 2.1 @2069, Remark 2.12 @2077, Lemma 4.4 @2095, Lemma 2.13
  @2109, Thm 4.1 @2114, Lemma 3.3 @2114, Lemma 2.18 @2120.
- Lemma 5.4 (2005): proof 2037-2063: Lemma 2.15 @2039, Lemma 2.16 @2058, Lemma 2.9 @2058.

## Section 6
- Prop 6.1 (2236): proof 2834-2905: Lemma 6.10 @2835, Thm 2.3 @2836, Prop 5.1 @2850, Lemma 2.9 @2867, Lemma 6.3 @2889.
- Lemma 6.3 (2289): cited DF91 Section 4.
- Lemma 6.4 (2318): proof 2387-2400: Lemma 6.6 @2392, Lemma 6.5 @2399.
- Lemma 6.5 (2333): proof 2343-2368: Fact 2.2 @2355, @2367 (Weyl scaling, coordinate change; absolute continuity of h
  on annuli).
- Lemma 6.6 (2371): cited Gwynne-Miller (gwynne2020local), no theorem number printed.
- Lemma 6.7 (2410): proof 2449-2461 (assuming Lemma 6.8): Lemma 6.8 @2449, Lemma 2.8 @2450.
- Lemma 6.8 (2438): proof 2476-2604: Lemma 2.16 @2477, Lemma 2.7 @2479, Lemma 2.9 @2479, Lemma 6.4 @2482, Lemma 2.18
  @2489.
- Lemma 6.9 (2626): proof 2637-2666: Lemma 6.7 @2638-2649 (Chernoff-type bound).
- Lemma 6.10 (2679): proof 2691-2821: Lemma 6.9 @2692, Lemma 6.3 @2695, Lemma 2.7 @2698, Definition 6.2 @2706,
  Lemma 2.8 @2735.

## Section 7
- Prop 7.1 (2917): proof 3098-3265: Thm 2.3 @3099, Lemma 6.8 @3102, Lemma 2.7 @3102, Lemma 7.2 @3106, Thm 4.1 @3110,
  Lemma 3.3 @3110, Lemma 2.8 @3134, Lemma 7.3 @3186, Lemma 7.4 @3236.
- Lemma 7.2 (2974): proof 2983-3015: Lemma 2.16 @2984, Lemma 2.8 @2984; maximum principle (2986).
- Lemma 7.3 (3018): proof 3025-3047: maximum principle (3046).
- Lemma 7.4 (3058): proof 3068-3086: GMS19 Lemma 2.6 @3069, Lemma 4.5 @3085.

## Section 8
- Prop 8.1 (3270): proof 3282-3336 (with Thms 1.4, 1.6): Prop 4.2, Prop 5.1, Prop 6.1, Prop 7.1 (lower and upper bounds
  for both clusters, restricted to {t < T}).

## Appendix A
- Lemma A.1 (3347): proof 3354-3356: Telcs 2006 eq (2.17), BG20 Lemma 3.6 (summation by parts).
- Lemma A.2 (3413): proof 3420-3445: elementary (comparison, maximum principle).
- Lemma A.3 (3448): proof 3453-3525: Lemma A.2 @3455, @3495, @3522.
- Lemma A.4 (3528): proof 3536-3556: Lemma A.3 @3541, Lemma A.1 @3544, Lemma A.2 @3548.

## Literature cited inside proofs (exact sources)
BG20 Lemma A.1, Lemma 2.4, Lemma A.4, Cor A.6, Thm 1.2, Lemma 5.4, Lemma 5.6, Lemma 4.4, Prop 5.1, Lemma A.3, (5.3) in
Cor 5.2, (1.8), Lemma 3.6; HB22 Thm 1.1, Thm 5.5, Lemma 3.2, Prop 1.3, Prop 5.6, Prop 2.5; DMS14 Prop 4.13(i), Lemma 8.8
(equivalence of Definitions 1.1 and 1.2); DS11 Prop 2.1 and Section 3.1; SW16; GMS19 Thm 3.9, Lemma 2.6; LL10 Prop 6.2.3,
Cor 6.2.4, Lemma 4.6.1; LBG92 Section 3, Lemma 3.3; LP09 Lemma 3.2 (least action principle), Lemma 4.2; DF91 Section 4;
Lyons-Peres Exercise 2.1; Telcs 2006 (2.17); Gwynne-Miller (gwynne2020local).
