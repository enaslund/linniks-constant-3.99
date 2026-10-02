# Verification log for `references.bib`

Paper: *Linnik's constant is at most 3.99*. Compiled 2026-09-30.

`references.bib` has **149 entries**. Each one was checked against at least one
authoritative online record, and the URLs used are listed in the entry's `note`
field and in the tables below. No field was filled in from memory. Where two
authoritative records disagree, the entry follows the publisher (Crossref/DOI)
or MathSciNet, and the disagreement is recorded here.

## How the entries were verified

| Source | Access used | Used for |
|---|---|---|
| zbMATH Open | REST API `api.zbmath.org/v1/document/_search` (Zbl and JFM records, including review texts) | bibliographic data, reviews stating the admissible Linnik exponents |
| Crossref | REST API `api.crossref.org/works/<doi>` and bibliographic search | DOI, title, volume, issue, pages, dates; every DOI in the file resolves in Crossref |
| MathSciNet | public MRef / MR Lookup tools (`mathscinet.ams.org/mathscinet-mref`, `/mrlookup`) | MR numbers and data for older papers, Graham's thesis, Weil 1952, Tenenbaum's translation note |
| arXiv | API `export.arxiv.org/api/query` | preprints: title, authors, dates, abstracts (Xylouris 2009 value 5.2, Zhao, Meng, MMT) |
| Publisher and repository pages | Peking University journal platform, Pers&eacute;e, Numdam, Cambridge Core, Bonn repository (bonndoc), NIST DLMF bibliography | items not (fully) covered above |
| GitHub API and repository files | `api.github.com/repos/...`, raw README and source files | Lean and mathlib software entries |

An automated cross-check compared every entry that has a DOI with its Crossref record (title words, first
author, volume, first page). The only mismatches were the known Crossref defects listed under
"Discrepancies" below.

The file compiles cleanly with BibTeX (`alpha` style, `\nocite{*}`). BibTeX gives no warnings.
Non-standard fields (`mrnumber`, `zbl`, `language`, `eprint`, `archivePrefix`, `primaryClass`) are
ignored by classic `.bst` styles and used by biblatex. Every entry's `note` has the form
"Verified: <url>; <url>". **Delete these notes, or switch them off, before the bibliography is typeset
for the paper.**

Citation keys follow `AuthorYYYYword`. The exceptions are group or software authors: `mathlib2020lean`,
`mpmath2023library`, `LeanFRO2025comparator`, `KontorovichTao2024pnt`. The Chen-Liu series has
part-numbered keys: `ChenLiu1989III`, `ChenLiu1989IV` and `ChenLiu1991V`.

Chinese names follow zbMATH (`Chen, Jingrun`, `Liu, Jianmin`, `Pan, Chengdong`); MathSciNet writes
`Chen, Jing Run`, `Liu, Jian Min`, `Pan, Cheng Dong`. Linnik is given as `Yu. V.` (zbMATH); MathSciNet
prints `U. V.`.

### Entries by section

| Section | Entries |
|---|---:|
| 1. Linnik's theorem: origin, history of the constant, surveys | 36 |
| 2. Conditional bounds, exceptional zeros and the least prime, lower bounds, computation, other methods | 15 |
| 3. Zero-free regions and exceptional zeros | 16 |
| 4. Zero-density and log-free density estimates | 15 |
| 5. Sieve methods and the large sieve | 10 |
| 6. Character sums, subconvexity, special moduli | 13 |
| 7. Standard texts and surveys | 13 |
| 8. Explicit formula, zero detection and analytic tools | 4 |
| 9. Verified computation, interval arithmetic and linear programming | 18 |
| 10. Formal proof and Lean | 9 |
| **Total** | **149** |

## Verified timeline of admissible values of Linnik's constant L

This table covers unconditional results for all moduli: `P(a,q) << q^L`, or `P(a,q) <= C q^L`, for
every coprime pair. Each value comes from a zbMATH review or summary, from the paper's own abstract or
theorem, or from Table 1 of Xylouris 2011. That table is published in Acta Arith. and reproduces
Heath-Brown 1992, p. 266, "supplemented by three additional references".

| Year | Author(s) | L | Key | Where the value was verified |
|---|---|---|---|---|
| 1944 | Yu. V. Linnik | an absolute L exists (no value) | `Linnik1944least`, `Linnik1944deuring` | zbMATH review of Pan 1957 (Zbl 0083.26203): the proofs give only the existence of C, no bound |
| 1957 | Pan Chengdong | 10000 (announced without proof) | `Pan1957least` | Zbl 0083.26203 review: the author only claims C <= 10^4, no proofs; Zbl 1248.11067 review; Xylouris 2011, Table 1 |
| 1958 | Pan Chengdong | 5448 | `Pan1958least` | Zbl 0621.10029 (review of Wang 1986): "gave the first effective estimate C <= 5448"; Xylouris 2011, Table 1 |
| 1965 | Chen Jingrun | 777 | `Chen1965least` | Zbl 0203.35404 (review of Jutila 1970); Xylouris 2011, Table 1 |
| 1970 | M. Jutila | 550 | `Jutila1970new` | Zbl 0203.35404 review; Zbl 0367.10039 review |
| 1971 | M. Jutila, reported in Tur&aacute;n's survey | 630 | `Turan1971recent` | Xylouris 2011, Table 1, citing Tur&aacute;n 1971, p. 370. Weaker than 550; listed only because Heath-Brown's table lists it |
| 1977 | Chen Jingrun | 168 | `Chen1977least` | Zbl 0367.10039 review |
| 1977 | M. Jutila | 80 | `Jutila1977linnik` | Zbl 0367.10039 and Zbl 0379.10028 reviews |
| 1977 | S. W. Graham (Ph.D. thesis) | 36 | `Graham1977thesis` | Xylouris 2011, Table 1 (from Heath-Brown 1992, p. 266). Not stated in MR2627480 |
| 1979 | Chen Jingrun | 17 | `Chen1979least` | Zbl 0684.10040 and Zbl 0379.10028 reviews |
| 1981 | S. W. Graham | 20 | `Graham1981linnik` | Zbl 0379.10028 review: submitted before Chen's 17 appeared |
| 1986 | Wang Wei | 16 | `Wang1986least` | Zbl 0621.10029 review |
| 1989 | Chen Jingrun, Liu Jianmin | 13.5 | `ChenLiu1989III`, `ChenLiu1989IV` | Zbl 0684.10040 review |
| 1991 | Chen Jingrun, Liu Jianmin | 11.5 | `ChenLiu1991V` | Zbl 0860.11052 review |
| 1991 | Wang Wei | 8 | `Wang1991least` | Zbl 0742.11044 review |
| 1992 | D. R. Heath-Brown | 5.5 | `HeathBrown1992zero` | Zbl 0739.11033 review (11/2) |
| 2009 | T. Xylouris (Diplomarbeit, arXiv) | 5.2 | `Xylouris2009linnik` | arXiv:0906.2749 abstract |
| 2011 | T. Xylouris | 5.18 | `Xylouris2011least` | Theorem 1.1 of the paper; Zbl 1248.11067 review |
| 2011 | T. Xylouris (Dissertation, Bonner Math. Schriften 404) | 5 | `Xylouris2011nullstellen` | Zbl 1339.11080 summary. The review of Friedlander-Iwaniec 2023 (Zbl 1554.11095) also calls L = 5 the record |
| 2018 | T. Xylouris (journal summary of the dissertation) | 5 | `Xylouris2018linnik` | Zbl 1439.11244 summary. Despite the title, the displayed theorem is P(a,q) < Cq^5 |

The table is in publication order. Graham's 20 (1981) is weaker than Chen's 17 (1979); the zbMATH
review of Graham 1981 says the paper was submitted before Chen's appeared.

Values that were announced but not published appear only in zbMATH reviews and are left out of the table:
* Chen announced C <= 15 (footnote in Wang 1986, reported in Zbl 0621.10029).
* Chen claimed 13.4 in a private communication to the reviewer of Wang 1986.
* Chen claimed 14 in a written communication to Graham (Zbl 0379.10028).

### Related results: conditional, restricted moduli, other methods (for context, not improvements of L)

| Year | Author(s) | Result | Scope | Key | Verified at |
|---|---|---|---|---|---|
| 1990 | Heath-Brown | P(a,q) <= q^(3+delta) effectively; q^(2+delta) ineffectively | if a Siegel zero 1 - 1/(eta log q) with eta >= eta(delta) exists | `HeathBrown1990siegel` | Zbl 0715.11049 review |
| 2010 | Z. Meng | P(a,q) << q^4.5 | q with bounded cubic part; arXiv preprint | `Meng2010note` | arXiv:1010.3544 abstract |
| 2014 | M.-C. Chang | P < q^(12/5 + o(1)) | q with log p = o(log q) for every p dividing q | `Chang2014short` | arXiv:1201.0299, Corollary 11 |
| 2023 | Friedlander, Iwaniec | L = 75,744,000 | all q; sieve method without log-free density or zero repulsion | `FriedlanderIwaniec2023sifting` | arXiv:2303.06122v1, Theorem 7.2 (value stated in the text of v1) |
| 2024 | Matom&auml;ki, Merikoski, Ter&auml;v&auml;inen | p << q^350 | all q; no L-functions; arXiv preprint | `MatomakiMerikoskiTeravainen2024primes` | arXiv:2401.17570 abstract |
| 2025 | G. Zhao | P(q) = O(q^5) | all q; arXiv preprint | `Zhao2025exceptional` | arXiv:2511.05631 abstract |
| &mdash; | under GRH | p << (q log q)^2 | conditional | `BachSorenson1996explicit`, `LamzouriLiSoundararajan2015conditional`, `CarneiroMilinovichQuesadaHerreraRamos2025fourier` | stated in the Zbl 1554.11095 review. The explicit constants of these papers were not transcribed here |

## Discrepancies found

Discrepancies between sources:
1. **Friedlander-Iwaniec, "Selberg's sieve of irregular density".** Crossref and zbMATH give Acta Arith. **209** (2023), **385-396**. The repository's `literature/README.md` gives "Acta Arith. 207 (2023) 201-215", which is wrong.
2. **Banks-Shparlinski 2019.**
   * The published title is "Bounds on short character sums and L-functions with characters to a **powerful** modulus". The arXiv and repository title is "... for characters with a smooth modulus".
   * `research/notes/literature-2026-09-28.md` credits them with a Linnik exponent below 2.1115 for powers of a fixed prime. The paper (arXiv v2, §1.2) says: "We do not improve the Linnik exponent on the least prime in an arithmetic progression of this type". That credit should be checked before it is cited.
3. **Ingham 1940.** The publisher's Crossref record gives Q. J. Math. 11, pp. **201-202**, doi:10.1093/qmath/os-11.1.201. zbMATH and JFM give 291-292.
4. **Gronwall 1913.** JFM 44.0312.02 links doi:10.1007/BF03015593, which is a different Gronwall paper (pp. 95-102). The correct DOI is 10.1007/BF03015596 (pp. 145-159). Crossref garbles the author as "wall, T. H. Gron".
5. **de la Vall&eacute;e Poussin 1896.**
   * NIST DLMF gives Ann. Soc. Sci. Bruxelles **20**, pp. 183-256 and 281-397, and vol. 20 is used here.
   * JFM prints "21 B". JFM also puts the 1897 continuation in "21 B" at overlapping pages, so its volume is probably a slip.
6. **Pan 1958.**
   * Usually cited as "Acta Sci. Natur. Univ. Pekinensis 4 (1958), 1-34".
   * The Peking University platform shows 1958, issue 01, pp. **3-36**, no volume number, and a Chinese title. The platform data are used.
   * The value 5448 is not in the platform abstract. It comes from secondary reviews.
7. **Xylouris dissertation.** zbMATH 1339.11080 links arXiv:0709.4676. That is a different paper by Xylouris: "Binomial Coefficients and the Distribution of the Primes".
8. **Xylouris 2018.** The German title "Linniks Konstante ist kleiner als 5" is used, with the journal's own "for citation" line: 2018, vol. 19, no. 3, pp. 80-94.
   * Crossref gives the Russian title "Константа Линника не превосходит 5" and the date 2019-01-09.
   * The printed Russian title is "Константа Линника меньше 5".
9. **Wang 1991.** The last page is 289 in zbMATH and 288 in Crossref. Crossref also inverts the name ("Wei, Wang").
10. **Linnik 1944 II.** The subtitle is "The Deuring-Heilbronn phenomenon" in MathSciNet (used) and "The Deuring-Heilbronn theorem" in zbMATH.
11. **Jutila, "On two theorems of Linnik ..."** (verified, then omitted). MathSciNet gives 1969; zbMATH gives 1970.
12. **Year and volume slips in zbMATH reviews.** The records themselves are correct:
    * Chen 1965 appears as 1964.
    * Graham 1981 appears as "Acta Arith. 34"; it is vol. 39.
    * Liu-Wang 1998 appears as "Acta Arith. 84"; it is vol. 86.
    * Chen 1979 appears as "ibid. 22, 1-31"; the pages are 859-889.
13. **Dates and pages that differ between Crossref and the usual citation:**
    * Huxley, Invent. Math. 15: Crossref 1971, usual 1972.
    * Montgomery-Vaughan I: Crossref 2006, zbMATH 2007.
    * Knapowski 1962: Crossref gives 2022, the DOI registration date.
    * Tatuzawa: MathSciNet prints "(1952)".
    * Granville-Pomerance: zbMATH gives the title in the singular, "progression".
    * Phragm&eacute;n: Crossref misspells the name "Pharagm&eacute;n".
    * Friedlander-Iwaniec IMRN 2003: Crossref has no title.
14. **Online-first versus volume year.** Entries use the volume year:
    * Tao-Trudgian-Yang: online 2025-11-06, Math. Comp. 95 (2026).
    * Benli-Goel-Twiss-Zaman: online 2025-12-15, Proc. AMS 154 (2026).
    * Thorner-Zaman: Forum Math. 36 (2024); Crossref's online-first record has volume 0.
    * Carneiro-Milinovich-Quesada-Herrera-Ramos: Math. Comp., online 2025-12-02, no volume or pages yet.
15. **Davenport, 3rd edition (2000).** The Springer DOI 10.1007/978-1-4757-5927-3 belongs to the 1980 second edition, so no DOI is attached.
16. **Dirichlet.** Cited through his *Werke* (vol. 1, 1889, pp. 313-342, Cambridge reissue DOI). The original 1837 Berlin Academy printing was not checked against a primary record, so its page numbers are not given.
17. **Scope note: Iwaniec 1974.** The repository notes credit it with "2.4 for q built from a fixed set of primes". The zbMATH review describes only a zero-free region. The Linnik value was not verified, and no claim about it is made here.

## Per-entry verification

Each row gives the URLs used to verify the entry. "Discrepancies / notes" records conflicts between sources and, where relevant, the result the entry is cited for.

### 1. Linnik's theorem: origin, history of the constant, surveys (36)

| Key | Reference | Verified at | Discrepancies / notes |
|---|---|---|---|
| `Dirichlet1889beweis` | Dirichlet (1889), *Beweis des Satzes, dass jede unbegrenzte arithmetische Progression, deren erstes Glied und Differenz ganze Zahlen ohne gemeinschaftlichen Factor sind, unendlich viele Primzahlen enthält*, G. Lejeune Dirichlet's Werke, Vol. 1, 313–342 | https://doi.org/10.1017/CBO9781139237338.023<br>https://zbmath.org/?q=an:21.0016.01<br>https://zbmath.org/?q=an:1247.01055 | Cited through the Werke (verified: Cambridge Core chapter DOI, pp. 313-342; volume 1 per the ISBN 978-1-108-05040-1 = v.1 in Zbl 1247.01055; JFM 21.0016.01 for the 1889 Reimer edition, x+641 pp.). The original 1837 Berlin Academy printing (usually cited as Abh. Akad. Wiss. Berlin 1837, 45-81) was NOT checked against a primary record and is not given in the entry. |
| `Linnik1944deuring` | Linnik (1944), *On the least prime in an arithmetic progression. II. The Deuring–Heilbronn phenomenon*, Rec. Math. [Mat. Sbornik] N.S. 15(57), 347–368 | https://mathscinet.ams.org/mathscinet-getitem?mr=12112<br>https://zbmath.org/?q=an:0063.03585 | Subtitle: MathSciNet 'The Deuring-Heilbronn phenomenon'; zbMATH 'The Deuring--Heilbronn theorem'. MathSciNet form used. |
| `Linnik1944least` | Linnik (1944), *On the least prime in an arithmetic progression. I. The basic theorem*, Rec. Math. [Mat. Sbornik] N.S. 15(57), 139–178 | https://mathscinet.ams.org/mathscinet-getitem?mr=12111<br>https://zbmath.org/?q=an:0063.03584 | Author as in zbMATH ('Linnik, Yu. V.'); MathSciNet prints 'Linnik, U. V.'. |
| `Rodosskii1954least` | Rodosskiĭ (1954), *On the least prime number in an arithmetic progression*, Mat. Sbornik N.S. 34(76), 331–356 | https://mathscinet.ams.org/mathscinet-getitem?mr=62156<br>https://zbmath.org/?q=an:0056.27102 | Simplified proof of Linnik's theorem (zbMATH review of Pan 1957, Zbl 0083.26203). |
| `Pan1957least` | Pan (1957), *On the least prime in an arithmetical progression*, Sci. Record (N.S.) 1, 311–313 | https://mathscinet.ams.org/mathscinet-getitem?mr=105398<br>https://zbmath.org/?q=an:0083.26203 | Announcement: the zbMATH review states the author only claims C <= 10^4 and gives no proofs. zbMATH spells the author 'Pan, Chengdong'. |
| `Pan1958least` | Pan (1958), *On the least prime in an arithmetical progression*, Acta Sci. Natur. Univ. Pekinensis, 3–36 | https://ccj.pku.edu.cn/article/info?aid=271021302<br>https://zbmath.org/?q=an:0621.10029 | Not indexed as a record in zbMATH or MathSciNet (MR Lookup by author/year and by title found only the 1957 note). Verified on the Peking University journal platform: Chinese title '论算术级数中之最小素数', 1958, issue 01, pp. 3-36; its abstract states an unconditional bound P_min(D,l) < D^A and, under GRH, D^(2+eps). The value 5448 is not in that abstract; it is attributed to this paper by the zbMATH review of Wang 1986 (Zbl 0621.10029) and by Table 1 of Xylouris 2011 (from Heath-Brown 1992, p. 266). DISCREPANCY: the paper is usually cited as 'Acta Sci. Natur. Univ. Pekinensis 4 (1958), 1-34'; the platform shows issue 1 and pp. 3-36 and no volume number. English title is the one used in the literature (a translation of the Chinese title). |
| `Turan1961density` | Turán (1961), *On a density theorem of Yu. V. Linnik*, Magyar Tud. Akad. Mat. Kutató Int. Közl. 6, 165–179 | https://mathscinet.ams.org/mathscinet-getitem?mr=146155<br>https://zbmath.org/?q=an:0146.05802 | zbMATH names the journal 'Publ. Math. Inst. Hung. Acad. Sci., Ser. A'. |
| `Knapowski1962linnik` | Knapowski (1962), *On Linnik's theorem concerning exceptional L-zeros*, Publ. Math. Debrecen 9, 168–178 | https://doi.org/10.5486/PMD.1962.9.1-2.18<br>https://zbmath.org/?q=an:0141.04602 | Crossref records the DOI registration date (2022) as the issue date; the article is from 1962. |
| `Chen1965least` | Chen (1965), *On the least prime in an arithmetical progression*, Sci. Sinica 14, 1868–1871 | https://mathscinet.ams.org/mathscinet-getitem?mr=188172<br>https://zbmath.org/?q=an:0146.27502 | L < 777 per the zbMATH review of Jutila 1970 (Zbl 0203.35404). The zbMATH review of Wang 1986 gives the year as 1964; the records say 1965. |
| `Fogels1965zeros` | Fogels (1965), *On the zeros of L-functions*, Acta Arith. 11, 67–96 | https://doi.org/10.4064/aa-11-1-67-96<br>https://zbmath.org/?q=an:0136.03004 | A corrigendum appeared in Acta Arith. 14 (1968), 435 (Zbl 0179.34802). |
| `Jutila1970new` | Jutila (1970), *A new estimate for Linnik's constant*, Ann. Acad. Sci. Fenn. Ser. A I 471 | https://mathscinet.ams.org/mathscinet-getitem?mr=271056<br>https://zbmath.org/?q=an:0203.35404 | L < 550 (zbMATH review). |
| `Turan1971recent` | Turán (1971), *On some recent results in the analytical theory of numbers*, 1969 Number Theory Institute (Proc. Sympos. Pure Math., Vol. XX, State Univ. New York, Stony Brook, N.Y., 1969) 20, 359–374 | https://mathscinet.ams.org/mathscinet-getitem?mr=316400<br>https://zbmath.org/?q=an:0216.31001 | Source for Jutila's value 630 in the table of Heath-Brown 1992, p. 266, as reproduced in Xylouris 2011, Table 1 ('[17, p. 370]'). |
| `Iwaniec1974zeros` | Iwaniec (1974), *On zeros of Dirichlet's L series*, Invent. Math. 23, 97–104 | https://doi.org/10.1007/BF01405163<br>https://zbmath.org/?q=an:0275.10024 | Postnikov-Gallagher method for general moduli; zero-free region depending on the product of the distinct primes dividing q (zbMATH review). |
| `Motohashi1975density` | Motohashi (1975), *On a density theorem of Linnik*, Proc. Japan Acad. 51, 815–817 | https://doi.org/10.3792/pja/1195518441<br>https://zbmath.org/?q=an:0361.10037 | Crossref gives issue 'S1' and no pages; pages from zbMATH (which dates the review volume 1976). |
| `Chen1977least` | Chen (1977), *On the least prime in an arithmetical progression and two theorems concerning the zeros of Dirichlet's L-functions*, Sci. Sinica 20, 529–562 | https://mathscinet.ams.org/mathscinet-getitem?mr=476668<br>https://zbmath.org/?q=an:0367.10039 | L <= 168 (zbMATH review by Jutila). |
| `Graham1977thesis` | Graham (1977), *Applications of Sieve Methods*, University of Michigan | https://mathscinet.ams.org/mathscinet-getitem?mr=2627480 | Verified in MathSciNet (MR2627480; title printed in capitals there). L = 36 per Heath-Brown 1992, p. 266, as reproduced in Xylouris 2011, Table 1. Advisor H. L. Montgomery (zbMATH review of Graham 1981). |
| `Jutila1977linnik` | Jutila (1977), *On Linnik's constant*, Math. Scand. 41, 45–62 | https://doi.org/10.7146/math.scand.a-11701<br>https://zbmath.org/?q=an:0363.10026 | L <= 80 (zbMATH reviews of Chen 1977 and Graham 1981). Crossref lists only the first page (45). |
| `Motohashi1978primes` | Motohashi (1978), *Primes in arithmetic progressions*, Invent. Math. 44, 163–178 | https://doi.org/10.1007/BF01390349<br>https://zbmath.org/?q=an:0367.10040 |  |
| `Chen1979least` | Chen (1979), *On the least prime in an arithmetical progression and theorems concerning the zeros of Dirichlet's L-functions. II*, Sci. Sinica 22, 859–889 | https://mathscinet.ams.org/mathscinet-getitem?mr=549597<br>https://zbmath.org/?q=an:0417.10038 | L <= 17 (zbMATH reviews of Chen-Liu 1989 and Graham 1981). The review of Chen-Liu 1989 also cites 'ibid. 22, 1-31' for Part II; the records give 859-889. |
| `Graham1981linnik` | Graham (1981), *On Linnik's constant*, Acta Arith. 39, 163–179 | https://doi.org/10.4064/aa-39-2-163-179<br>https://zbmath.org/?q=an:0379.10028 | L <= 20; submitted before Chen's 1979 value 17 (zbMATH review by Graham). Some zbMATH reviews cite it as 'Acta Arith. 34'; the record and Crossref give 39. |
| `Wang1986least` | Wang (1986), *On the least prime in an arithmetic progression*, Acta Math. Sinica 29, 826–836 | https://mathscinet.ams.org/mathscinet-getitem?mr=888852<br>https://zbmath.org/?q=an:0621.10029 | L <= 16 (zbMATH review by Heath-Brown). |
| `ChenLiu1989III` | Chen & Liu (1989), *On the least prime in an arithmetical progression. III*, Sci. China Ser. A 32, 654–673 | https://mathscinet.ams.org/mathscinet-getitem?mr=1056044<br>https://zbmath.org/?q=an:0684.10040 | L <= 13.5 with Part IV (zbMATH review of the joint record Zbl 0684.10040). |
| `ChenLiu1989IV` | Chen & Liu (1989), *On the least prime in an arithmetical progression. IV*, Sci. China Ser. A 32, 792–807 | https://mathscinet.ams.org/mathscinet-getitem?mr=1058000<br>https://zbmath.org/?q=an:0684.10040 | Parts III and IV share one zbMATH record. |
| `ChenLiu1991V` | Chen & Liu (1991), *On the least prime in an arithmetical progression and theorems concerning the zeros of Dirichlet's L-functions (V)*, International Symposium in Memory of Hua Loo Keng, Vol. I: Number Theory, 19–42 | https://doi.org/10.1007/978-3-662-07981-2_3<br>https://zbmath.org/?q=an:0860.11052 | L <= 11.5 (zbMATH review). |
| `Wang1991least` | Wang (1991), *On the least prime in an arithmetic progression*, Acta Math. Sinica (N.S.) 7, 279–289 | https://doi.org/10.1007/BF02583005<br>https://zbmath.org/?q=an:0742.11044 | L <= 8 (zbMATH review). DISCREPANCY: last page 289 (zbMATH) vs 288 (Crossref); Crossref also inverts the name as 'Wei, Wang'. |
| `HeathBrown1992zero` | Heath-Brown (1992), *Zero-free regions for Dirichlet L-functions, and the least prime in an arithmetic progression*, Proc. London Math. Soc. (3) 64, 265–338 | https://doi.org/10.1112/plms/s3-64.2.265<br>https://zbmath.org/?q=an:0739.11033 | L = 5.5; zero-free region constant 0.348; at most one character (with conjugate) with a zero in sigma >= 1-0.702/log q (zbMATH review). |
| `LiuWang1998numerical` | Liu & Wang (1998), *A numerical bound for small prime solutions of some ternary linear equations*, Acta Arith. 86, 343–383 | https://doi.org/10.4064/aa-86-4-343-383<br>https://zbmath.org/?q=an:0918.11053 | Zero-free region constant 0.364 apart from an exceptional zero (zbMATH review by Heath-Brown; Xylouris 2011, remark after Thm 1.2). The zbMATH review of the sequel (Zbl 1014.11061) cites this paper as 'Acta Arith. 84'; the record gives 86. |
| `Xylouris2009linnik` | Xylouris (2009), *On Linnik's constant*, arXiv:0906.2749 | https://arxiv.org/abs/0906.2749 | arXiv abstract: admissible L = 5.2. 86 pages, Diplomarbeit, in German; supervisor B. Z. Moroz (Bonn) per the title page. |
| `Meng2010note` | Meng (2010), *A note on the Linnik's constant*, arXiv:1010.3544 | https://arxiv.org/abs/1010.3544 | Preprint (not refereed as far as found). Abstract: P(a,q) << q^4.5 when q has bounded cubic part. |
| `Xylouris2011least` | Xylouris (2011), *On the least prime in an arithmetic progression and estimates for the zeros of Dirichlet L-functions*, Acta Arith. 150, 65–91 | https://doi.org/10.4064/aa150-1-4<br>https://zbmath.org/?q=an:1248.11067 | L = 5.18 (Theorem 1.1; zbMATH review). zbMATH links arXiv:0906.2749 (the Diplomarbeit). |
| `Xylouris2011nullstellen` | Xylouris (2011), *Über die Nullstellen der Dirichletschen L-Funktionen und die kleinste Primzahl in einer arithmetischen Progression*, Bonner Mathematische Schriften | https://hdl.handle.net/20.500.11811/5074<br>https://zbmath.org/?q=an:1339.11080 | L = 5 (zbMATH summary). Bonn record: issued 2011-11-23, URN urn:nbn:de:hbz:5N-27156, 110 pp. DISCREPANCY: zbMATH links arXiv:0709.4676, which is a different paper by the same author ('Binomial Coefficients and the Distribution of the Primes'). |
| `Xylouris2018linnik` | Xylouris (2018), *Linniks Konstante ist kleiner als 5*, Chebyshevskiĭ Sb. 19, 80–94 | https://doi.org/10.22405/2226-8383-2018-19-3-80-94<br>https://zbmath.org/?q=an:1439.11244 | L = 5 (summary of the dissertation). DISCREPANCIES: Crossref gives the Russian title 'Константа Линника не превосходит 5' and issue date 2019-01-09; the printed Russian title is 'Константа Линника меньше 5'; the journal's own citation line gives 2018, vol. 19, no. 3, pp. 80-94 (used). zbMATH gives issue as No. 3(67). |
| `FriedlanderIwaniec2023sifting` | Friedlander & Iwaniec (2023), *Sifting for small primes from an arithmetic progression*, Sci. China Math. 66, 2715–2730 | https://doi.org/10.1007/s11425-022-2123-2<br>https://zbmath.org/?q=an:1554.11095<br>https://arxiv.org/abs/2303.06122 | Sieve proof of Linnik's theorem without log-free density or zero repulsion. arXiv v1, Theorem 7.2: L = 75744000. |
| `Sachpazis2023pretentious` | Sachpazis (2023), *A pretentious proof of Linnik's estimate for primes in arithmetic progressions*, Mathematika 69, 879–902 | https://doi.org/10.1112/mtk.12211<br>https://zbmath.org/?q=an:1539.11122 |  |
| `MatomakiMerikoskiTeravainen2024primes` | Matomäki & Merikoski & Teräväinen (2024), *Primes in arithmetic progressions and short intervals without L-functions*, arXiv:2401.17570 | https://arxiv.org/abs/2401.17570 | Preprint. Abstract: L-function-free proof of Linnik's theorem with p << q^350. |
| `Zhao2025exceptional` | Zhao (2025), *The exceptional set of Goldbach problem and Linnik's constant*, arXiv:2511.05631 | https://arxiv.org/abs/2511.05631 | Preprint (v1 2025-11-07, v2 2026-01-23). Abstract: P(q) = O(q^5). |

### 2. Conditional bounds, exceptional zeros and the least prime, lower bounds, computation, other methods (15)

| Key | Reference | Verified at | Discrepancies / notes |
|---|---|---|---|
| `Titchmarsh1930divisor` | Titchmarsh (1930), *A divisor problem*, Rend. Circ. Mat. Palermo 54, 414–429 | https://doi.org/10.1007/BF03021203<br>https://zbmath.org/?q=an:56.0891.01 | Correction: Rend. Circ. Mat. Palermo 57 (1933), 478-479 (JFM 59.0948.03, doi:10.1007/BF03017588). |
| `Chowla1934least` | Chowla (1934), *On the least prime in an arithmetical progression*, J. Indian Math. Soc. (N.S.) 1, 1–3 | https://zbmath.org/?q=an:0009.00802<br>https://zbmath.org/?q=an:60.0144.01 |  |
| `Wagstaff1979greatest` | Wagstaff (1979), *Greatest of the least primes in arithmetic progressions having a given modulus*, Math. Comp. 33, 1073–1080 | https://doi.org/10.1090/S0025-5718-1979-0528061-7<br>https://zbmath.org/?q=an:0407.10034 | zbMATH links the JSTOR DOI 10.2307/2006082; the AMS DOI is used here. |
| `Pomerance1980note` | Pomerance (1980), *A note on the least prime in an arithmetic progression*, J. Number Theory 12, 218–223 | https://doi.org/10.1016/0022-314X(80)90056-6<br>https://zbmath.org/?q=an:0436.10020 |  |
| `GranvillePomerance1990least` | Granville & Pomerance (1990), *On the least prime in certain arithmetic progressions*, J. London Math. Soc. (2) 41, 193–200 | https://doi.org/10.1112/jlms/s2-41.2.193<br>https://zbmath.org/?q=an:0658.10049 | zbMATH title reads 'certain arithmetic progression' (singular); Crossref (publisher) has 'progressions'. |
| `HeathBrown1990siegel` | Heath-Brown (1990), *Siegel zeros and the least prime in an arithmetic progression*, Quart. J. Math. Oxford Ser. (2) 41, 405–418 | https://doi.org/10.1093/qmath/41.4.405<br>https://zbmath.org/?q=an:0715.11049 | With a Siegel zero beta = 1 - 1/(eta log q), eta >= eta(delta): P(a,q) <= q^(2+delta) ineffectively, q^(3+delta) effectively (zbMATH review). Issue 4 per Crossref/DOI; zbMATH gives the whole number 164. |
| `BachSorenson1996explicit` | Bach & Sorenson (1996), *Explicit bounds for primes in residue classes*, Math. Comp. 65, 1717–1735 | https://doi.org/10.1090/S0025-5718-96-00763-6<br>https://zbmath.org/?q=an:0853.11077 | An announcement with the same title appeared in Proc. Sympos. Appl. Math. 48 (1994), 535-539 (Zbl 0819.11034). |
| `FriedlanderIwaniec2003exceptional` | Friedlander & Iwaniec (2003), *Exceptional characters and prime numbers in arithmetic progressions*, Int. Math. Res. Not. 2003, 2033–2050 | https://doi.org/10.1155/S1073792803130784<br>https://zbmath.org/?q=an:1038.11060 | Crossref metadata lacks the title; title and last page from zbMATH. |
| `Iwaniec2006conversations` | Iwaniec (2006), *Conversations on the exceptional character*, Analytic Number Theory: Lectures given at the C.I.M.E. Summer School held in Cetraro, Italy, July 11–18, 2002 1891, 97–132 | https://doi.org/10.1007/978-3-540-36364-4_3<br>https://zbmath.org/?q=an:1147.11047 |  |
| `LamzouriLiSoundararajan2015conditional` | Lamzouri & Li & Soundararajan (2015), *Conditional bounds for the least quadratic non-residue and related problems*, Math. Comp. 84, 2391–2412 | https://doi.org/10.1090/S0025-5718-2015-02925-1<br>https://doi.org/10.1090/mcom/3261<br>https://zbmath.org/?q=an:1326.11058 |  |
| `Zaman2016least` | Zaman (2016), *On the least prime ideal and Siegel zeros*, Int. J. Number Theory 12, 2201–2229 | https://doi.org/10.1142/S1793042116501335<br>https://zbmath.org/?q=an:1352.11096 |  |
| `LiPrattShakan2017lower` | Li & Pratt & Shakan (2017), *A lower bound for the least prime in an arithmetic progression*, Quart. J. Math. 68, 729–758 | https://doi.org/10.1093/qmath/hax001<br>https://zbmath.org/?q=an:1426.11091 |  |
| `BennettMartinOBryantRechnitzer2018explicit` | Bennett et al. (2018), *Explicit bounds for primes in arithmetic progressions*, Illinois J. Math. 62, 427–532 | https://doi.org/10.1215/ijm/1552442669<br>https://zbmath.org/?q=an:1440.11180 | Crossref has no pages; pages from zbMATH. |
| `ThornerZaman2024refinements` | Thorner & Zaman (2024), *Refinements to the prime number theorem for arithmetic progressions*, Math. Z. 306, Paper No. 54 | https://doi.org/10.1007/s00209-023-03414-3<br>https://zbmath.org/?q=an:1546.11120<br>https://arxiv.org/abs/2108.10878 | Article number 54 (14 pp., zbMATH). |
| `CarneiroMilinovichQuesadaHerreraRamos2025fourier` | Carneiro et al. (2025), *Fourier optimization, the least quadratic non-residue, and the least prime in an arithmetic progression*, Math. Comp., arXiv:2404.08380 | https://doi.org/10.1090/mcom/4154<br>https://arxiv.org/abs/2404.08380 | Crossref: online 2025-12-02, no volume/issue/pages; the DOI resolves to an AMS 'S0025-5718-2025-04154-1' page under '0000-000-00' (not yet in an issue). Improves GRH-conditional bounds. |

### 3. Zero-free regions and exceptional zeros (16)

| Key | Reference | Verified at | Discrepancies / notes |
|---|---|---|---|
| `delaValleePoussin1896recherches` | de la Vallée Poussin (1896), *Recherches analytiques sur la théorie des nombres premiers*, Ann. Soc. Sci. Bruxelles 20, 183–256, 281–397 | https://dlmf.nist.gov/bib/D<br>https://zbmath.org/?q=an:27.0155.03 | Parts: 'Première partie. La fonction zeta(s) de Riemann et les nombres premiers en général' (pp. 183-256) and 'Deuxième partie. Les fonctions de Dirichlet et les nombres premiers de la forme linéaire Mx+N' (pp. 281-397), per the NIST DLMF bibliography. DISCREPANCY: JFM 27.0155.03 prints the volume as 'Brux. S. sc. 21 B' with pages 183-256, 281-362, 363-397; the continuation (JFM 28.0178.02) is also listed in '21 B' at pp. 251-342, 343-368, which would overlap. Volume 20 (DLMF, and the usual citation) is used. |
| `delaValleePoussin1899fonction` | de la Vallée Poussin (1899), *Sur la fonction ζ(s) de Riemann et le nombre des nombres premiers inférieurs à une limite donnée*, Mém. Couronnés et Autres Mém. Publ. Acad. Roy. Sci. Lett. Beaux-Arts Belg. 59, 1–74 | https://doi.org/10.3406/marb.1899.2449<br>https://www.persee.fr/doc/marb_0770-8459_1899_num_59_1_2449<br>https://zbmath.org/?q=an:30.0193.03 | Persée/Crossref: 'Mémoires couronnés et autres mémoires publiés par l'Académie royale des sciences, des lettres et des beaux-arts de Belgique. Collection in-8°', tome 59, 1899, pp. 1-74 (JFM: 'Belg. Mém. 59, 74 p.'). Classical zero-free region for zeta. |
| `Gronwall1913series` | Gronwall (1913), *Sur les séries de Dirichlet correspondant à des caractères complexes*, Rend. Circ. Mat. Palermo 35, 145–159 | https://doi.org/10.1007/BF03015596<br>https://zbmath.org/?q=an:44.0312.02 | DISCREPANCY: the JFM record links doi:10.1007/BF03015593, which Crossref resolves to a different Gronwall paper ('Sur la fonction zeta(s) de Riemann au voisinage de sigma = 1', pp. 95-102). The correct DOI 10.1007/BF03015596 was found by Crossref search (Crossref garbles the author as 'wall, T. H. Gron'). |
| `Landau1918imaginar` | Landau (1918), *Über imaginär-quadratische Zahlkörper mit gleicher Klassenzahl*, Nachr. Ges. Wiss. Göttingen, Math.-Phys. Kl., 277–284 | https://zbmath.org/?q=an:46.0258.03<br>https://eudml.org/doc/59027 | Cited for Landau's theorem on the exceptional zero (e.g. Lu-Zaman-Zhao, arXiv:2602.03626, ref. [Lan18]). |
| `Deuring1933imaginare` | Deuring (1933), *Imaginäre quadratische Zahlkörper mit der Klassenzahl 1*, Math. Z. 37, 405–415 | https://doi.org/10.1007/BF01474583<br>https://zbmath.org/?q=an:0007.29602 |  |
| `Heilbronn1934class` | Heilbronn (1934), *On the class-number in imaginary quadratic fields*, Quart. J. Math. Oxford Ser. 5, 150–160 | https://doi.org/10.1093/qmath/os-5.1.150<br>https://zbmath.org/?q=an:0009.29602 |  |
| `Page1935number` | Page (1935), *On the number of primes in an arithmetic progression*, Proc. London Math. Soc. (2) 39, 116–141 | https://doi.org/10.1112/plms/s2-39.1.116<br>https://zbmath.org/?q=an:0011.14905 |  |
| `Siegel1935classenzahl` | Siegel (1935), *Über die Classenzahl quadratischer Zahlkörper*, Acta Arith. 1, 83–86 | https://doi.org/10.4064/aa-1-1-83-86<br>https://zbmath.org/?q=an:61.0170.02 | Author as in zbMATH/JFM ('Siegel, C. L.'); Crossref gives 'Siegel, Carl'. |
| `Tatuzawa1951theorem` | Tatuzawa (1951), *On a theorem of Siegel*, Jpn. J. Math. 21, 163–178 | https://doi.org/10.4099/jjm1924.21.0_163<br>https://mathscinet.ams.org/mathscinet-getitem?mr=51262<br>https://zbmath.org/?q=an:0054.02302 | MathSciNet prints the pages as '163--178 (1952)'; Crossref and zbMATH give 1951. |
| `Pintz1977elementaryV` | Pintz (1977), *Elementary methods in the theory of L-functions, V. The theorems of Landau and Page*, Acta Arith. 32, 163–171 | https://doi.org/10.4064/aa-32-2-163-171<br>https://zbmath.org/?q=an:0331.10020 |  |
| `Pintz1977elementaryVIII` | Pintz (1977), *Elementary methods in the theory of L-functions, VIII. Real zeros of real L-functions*, Acta Arith. 33, 89–98 | https://doi.org/10.4064/aa-33-1-89-98<br>https://zbmath.org/?q=an:0331.10023 |  |
| `McCurley1984explicit` | McCurley (1984), *Explicit zero-free regions for Dirichlet L-functions*, J. Number Theory 19, 7–32 | https://doi.org/10.1016/0022-314X(84)90089-1<br>https://zbmath.org/?q=an:0536.10035 |  |
| `Kadiri2005region` | Kadiri (2005), *Une région explicite sans zéros pour la fonction ζ de Riemann*, Acta Arith. 117, 303–339 | https://doi.org/10.4064/aa117-4-1<br>https://zbmath.org/?q=an:1101.11029 |  |
| `MossinghoffTrudgian2015nonnegative` | Mossinghoff & Trudgian (2015), *Nonnegative trigonometric polynomials and a zero-free region for the Riemann zeta-function*, J. Number Theory 157, 329–349 | https://doi.org/10.1016/j.jnt.2015.05.010<br>https://zbmath.org/?q=an:1334.11070 |  |
| `Kadiri2018explicit` | Kadiri (2018), *Explicit zero-free regions for Dirichlet L-functions*, Mathematika 64, 445–474 | https://doi.org/10.1112/S0025579318000037<br>https://zbmath.org/?q=an:1412.11096 | zbMATH links arXiv:math/0510570. |
| `BenliGoelTwissZaman2026explicit` | Benli et al. (2026), *Explicit Deuring–Heilbronn phenomenon for Dirichlet L-functions*, Proc. Amer. Math. Soc. 154, 509–525 | https://doi.org/10.1090/proc/17450<br>https://arxiv.org/abs/2410.06082 | Published online 2025-12-15 (Crossref); volume 154 is the 2026 volume. Not yet in zbMATH as a reviewed record. |

### 4. Zero-density and log-free density estimates (15)

| Key | Reference | Verified at | Discrepancies / notes |
|---|---|---|---|
| `Ingham1940estimation` | Ingham (1940), *On the estimation of N(σ,T)*, Quart. J. Math. Oxford Ser. 11, 201–202 | https://doi.org/10.1093/qmath/os-11.1.201<br>https://zbmath.org/?q=an:0025.02704 | DISCREPANCY: zbMATH and JFM give pp. 291-292; the publisher's Crossref record gives pp. 201-202 (used). |
| `Gallagher1970large` | Gallagher (1970), *A large sieve density estimate near σ=1*, Invent. Math. 11, 329–339 | https://doi.org/10.1007/BF01403187<br>https://zbmath.org/?q=an:0219.10048 |  |
| `Montgomery1971topics` | Montgomery (1971), *Topics in Multiplicative Number Theory*, Lecture Notes in Math. 227 | https://doi.org/10.1007/BFb0060851<br>https://zbmath.org/?q=an:0216.03501 |  |
| `Huxley1972difference` | Huxley (1972), *On the difference between consecutive primes*, Invent. Math. 15, 164–170 | https://doi.org/10.1007/BF01418933<br>https://zbmath.org/?q=an:0241.10026 | DISCREPANCY: Crossref dates the issue June 1971; zbMATH and the usual citation give 1972 (used). |
| `Jutila1972density` | Jutila (1972), *On a density theorem of H. L. Montgomery for L-functions*, Ann. Acad. Sci. Fenn. Ser. A I 520 | https://mathscinet.ams.org/mathscinet-getitem?mr=327681<br>https://zbmath.org/?q=an:0243.10033 |  |
| `HeathBrown1978hybrid` | Heath-Brown (1978), *Hybrid bounds for Dirichlet L-functions*, Invent. Math. 47, 149–170 | https://doi.org/10.1007/BF01578069<br>https://zbmath.org/?q=an:0362.10035 |  |
| `HeathBrown1979density` | Heath-Brown (1979), *The density of zeros of Dirichlet's L-functions*, Canad. J. Math. 31, 231–240 | https://doi.org/10.4153/CJM-1979-024-0<br>https://zbmath.org/?q=an:0362.10034 |  |
| `Bombieri1987grand` | Bombieri (1987), *Le grand crible dans la théorie analytique des nombres*, Astérisque 18 | https://zbmath.org/?q=an:0618.10042<br>https://zbmath.org/?q=an:0292.10035<br>https://www.numdam.org/item/AST_1987__18__1_0/ | Second edition (1987, 103 pp., Zbl 0618.10042); first edition Astérisque 18 (1974), 87 pp. (Zbl 0292.10035). The Numdam scan (item AST_1987__18__1_0) labels its cover 'Astérisque, tome 18 (1974)'; page references should state which edition is used. |
| `Pintz2018new` | Pintz (2018), *A new explicit formula in the additive theory of primes with applications II. The exceptional set in Goldbach's problem*, arXiv:1804.09084 | https://arxiv.org/abs/1804.09084 | Preprint (v2 2018-04-30). Author name as on arXiv ('Janos'). |
| `Pintz2019some` | Pintz (2019), *Some new density theorems for Dirichlet L-functions*, Banach Center Publ. 118, 231–244 | https://doi.org/10.4064/bc118-14<br>https://zbmath.org/?q=an:1443.11188 | In: Number Theory Week 2017 (Poznań), Banach Center Publications 118. |
| `SoundararajanThorner2019weak` | Soundararajan & Thorner (2019), *Weak subconvexity without a Ramanujan hypothesis*, Duke Math. J. 168, 1231–1268 | https://doi.org/10.1215/00127094-2018-0065<br>https://zbmath.org/?q=an:1426.11053 | Crossref has no pages; pages from zbMATH. |
| `ThornerZaman2024explicit` | Thorner & Zaman (2024), *An explicit version of Bombieri's log-free density estimate and Sárközy's theorem for shifted primes*, Forum Math. 36, 1059–1080 | https://doi.org/10.1515/forum-2023-0091<br>https://zbmath.org/?q=an:1555.11124 | Crossref (online-first record) has no volume or pages; they are from zbMATH. |
| `ChenGuptaLi2025large` | Chen & Gupta & Li (2025), *Large value estimates for Dirichlet polynomials with characters and zero density of Dirichlet L-functions*, arXiv:2507.08296 | https://arxiv.org/abs/2507.08296 | Preprint (v1 2025-07-11; v2 2026-07-27). |
| `GuthMaynard2026new` | Guth & Maynard (2026), *New large value estimates for Dirichlet polynomials*, Ann. of Math. (2) 203, 623–675 | https://doi.org/10.4007/annals.2026.203.2.6<br>https://zbmath.org/8212560<br>https://arxiv.org/abs/2405.20552 | Crossref has no pages; pages from the zbMATH record https://zbmath.org/8212560 (no Zbl number assigned yet when checked). |
| `TaoTrudgianYang2026new` | Tao & Trudgian & Yang (2026), *New exponent pairs, zero density estimates, and zero additive energy estimates: a systematic approach*, Math. Comp. 95, 2941–2990 | https://doi.org/10.1090/mcom/4138<br>https://zbmath.org/8241967<br>https://arxiv.org/abs/2501.16779 | Published online 2025-11-06 (Crossref); volume 95 is the 2026 volume (zbMATH record https://zbmath.org/8241967 gives 2026). |

### 5. Sieve methods and the large sieve (10)

| Key | Reference | Verified at | Discrepancies / notes |
|---|---|---|---|
| `Selberg1947elementary` | Selberg (1947), *On an elementary method in the theory of primes*, Norske Vid. Selsk. Forh., Trondhjem 19, 64–67 | https://mathscinet.ams.org/mathscinet-getitem?mr=22871<br>https://zbmath.org/?q=an:0041.01903 |  |
| `MontgomeryVaughan1973large` | Montgomery & Vaughan (1973), *The large sieve*, Mathematika 20, 119–134 | https://doi.org/10.1112/S0025579300004708<br>https://zbmath.org/?q=an:0296.10023 |  |
| `HalberstamRichert1974sieve` | Halberstam & Richert (1974), *Sieve Methods*, London Math. Soc. Monogr. 4 | https://zbmath.org/?q=an:0298.10026 |  |
| `Graham1978asymptotic` | Graham (1978), *An asymptotic estimate related to Selberg's sieve*, J. Number Theory 10, 83–94 | https://doi.org/10.1016/0022-314X(78)90010-0<br>https://zbmath.org/?q=an:0382.10031 |  |
| `Iwaniec1982brun` | Iwaniec (1982), *On the Brun–Titchmarsh theorem*, J. Math. Soc. Japan 34, 95–123 | https://doi.org/10.2969/jmsj/03410095<br>https://zbmath.org/?q=an:0486.10033 | Crossref has no pages; pages from zbMATH. |
| `Motohashi1983lectures` | Motohashi (1983), *Lectures on Sieve Methods and Prime Number Theory*, Tata Inst. Fund. Res. Lectures on Math. and Phys. 72 | https://zbmath.org/?q=an:0535.10001 | zbMATH: 'Lectures on Mathematics and Physics, Mathematics 72. Tata Institute of Fundamental Research. Berlin-Heidelberg-New York: Springer-Verlag. xii, 205 p.' |
| `Selberg1991lectures` | Selberg (1991), *Lectures on sieves*, Collected Papers, Vol. II, 65–247 | https://zbmath.org/?q=an:0729.11001 | Item No. 45 of the Collected Papers; pages from the zbMATH review of Vol. II. |
| `FriedlanderIwaniec2010opera` | Friedlander & Iwaniec (2010), *Opera de Cribro*, Amer. Math. Soc. Colloq. Publ. 57 | https://doi.org/10.1090/coll/057<br>https://zbmath.org/?q=an:1226.11099 | Chapter 24, 'The least prime in an arithmetic progression', pp. 453-473 (Crossref chapter DOI 10.1090/coll/057/24). |
| `Maynard2013brun` | Maynard (2013), *On the Brun–Titchmarsh theorem*, Acta Arith. 157, 249–296 | https://doi.org/10.4064/aa157-3-3<br>https://zbmath.org/?q=an:1321.11099 |  |
| `FriedlanderIwaniec2023selberg` | Friedlander & Iwaniec (2023), *Selberg's sieve of irregular density*, Acta Arith. 209, 385–396 | https://doi.org/10.4064/aa220719-5-10<br>https://zbmath.org/?q=an:1540.11118 | DISCREPANCY with the repository notes: literature/README.md cites 'Acta Arith. 207 (2023) 201-215'; Crossref and zbMATH give 209 (2023), 385-396. |

### 6. Character sums, subconvexity, special moduli (13)

| Key | Reference | Verified at | Discrepancies / notes |
|---|---|---|---|
| `Polya1918verteilung` | Pólya (1918), *Über die Verteilung der quadratischen Reste und Nichtreste*, Nachr. Ges. Wiss. Göttingen, Math.-Phys. Kl., 21–29 | https://zbmath.org/?q=an:46.0265.02<br>https://eudml.org/doc/59009 |  |
| `Vinogradov1918distribution` | Vinogradov (1918), *Sur la distribution des résidus et des nonrésidus des puissances*, J. Soc. Phys.-Math. Univ. Perm 1, 94–98 | https://zbmath.org/?q=an:48.1352.04 | JFM 48.1352.04 is a combined record of three Vinogradov papers; this one is given as 'ibid. 1, 94-98 (1918)'. Often cited as pp. 94-96. |
| `Burgess1962character` | Burgess (1962), *On character sums and L-series*, Proc. London Math. Soc. (3) 12, 193–206 | https://doi.org/10.1112/plms/s3-12.1.193<br>https://zbmath.org/?q=an:0106.04004 |  |
| `Burgess1962primitive` | Burgess (1962), *On character sums and primitive roots*, Proc. London Math. Soc. (3) 12, 179–192 | https://doi.org/10.1112/plms/s3-12.1.179<br>https://zbmath.org/?q=an:0106.04003 |  |
| `Burgess1963character` | Burgess (1963), *On character sums and L-series. II*, Proc. London Math. Soc. (3) 13, 524–536 | https://doi.org/10.1112/plms/s3-13.1.524<br>https://zbmath.org/?q=an:0123.04404 |  |
| `BarbanLinnikChudakov1964prime` | Barban & Linnik & Chudakov (1964), *On prime numbers in an arithmetic progression with a prime-power difference*, Acta Arith. 9, 375–390 | https://doi.org/10.4064/aa-9-4-375-390<br>https://zbmath.org/?q=an:0127.26901 | Crossref transliterates the third author as 'Tshudakov'; zbMATH as 'Chudakov'. |
| `Gallagher1972primes` | Gallagher (1972), *Primes in progressions to prime-power modulus*, Invent. Math. 16, 191–201 | https://doi.org/10.1007/BF01425492<br>https://zbmath.org/?q=an:0246.10030 |  |
| `Burgess1986character` | Burgess (1986), *The character sum estimate with r=3*, J. London Math. Soc. (2) 33, 219–226 | https://doi.org/10.1112/jlms/s2-33.2.219<br>https://zbmath.org/?q=an:0593.10033 |  |
| `HeathBrown2013burgess` | Heath-Brown (2013), *Burgess's bounds for character sums*, Number Theory and Related Fields: In Memory of Alf van der Poorten 43, 199–213 | https://doi.org/10.1007/978-1-4614-6642-0_10<br>https://zbmath.org/?q=an:1328.11088 |  |
| `Chang2014short` | Chang (2014), *Short character sums for composite moduli*, J. Anal. Math. 123, 1–33 | https://doi.org/10.1007/s11854-014-0012-y<br>https://zbmath.org/?q=an:1372.11087<br>https://arxiv.org/abs/1201.0299 | arXiv version, Corollary 11: if log p = o(log q) for every p / q, there is a prime P = a (mod q) with P < q^(12/5+o(1)). |
| `BanksShparlinski2019bounds` | Banks & Shparlinski (2019), *Bounds on short character sums and L-functions with characters to a powerful modulus*, J. Anal. Math. 139, 239–263 | https://doi.org/10.1007/s11854-019-0060-4<br>https://zbmath.org/?q=an:1460.11110<br>https://arxiv.org/abs/1605.07553 | DISCREPANCY: the arXiv/repository title reads '... for characters with a smooth modulus'; the published title (Crossref, zbMATH) is used. NOTE on scope: the arXiv v2 introduction states 'We do not improve the Linnik exponent on the least prime in an arithmetic progression of this type'; research/notes/literature-2026-09-28.md attributes a Linnik exponent below 2.1115 to Banks-Shparlinski, which this paper does not claim. |
| `Kerr2019moments` | Kerr (2019), *Moments of character sums to composite modulus*, arXiv:1904.04578 | https://arxiv.org/abs/1904.04578 | Preprint (v1 2019-04-09); no journal version found in zbMATH (listed there only as an arXiv preprint). |
| `PetrowYoung2020weyl` | Petrow & Young (2020), *The Weyl bound for Dirichlet L-functions of cube-free conductor*, Ann. of Math. (2) 192, 437–486 | https://doi.org/10.4007/annals.2020.192.2.3<br>https://zbmath.org/?q=an:1460.11111 | Crossref has no pages; pages from zbMATH. |

### 7. Standard texts and surveys (13)

| Key | Reference | Verified at | Discrepancies / notes |
|---|---|---|---|
| `Ingham1932distribution` | Ingham (1932), *The Distribution of Prime Numbers*, Cambridge Tracts in Mathematics and Mathematical Physics 30 | https://zbmath.org/?q=an:0006.39701 | Reissued in the Cambridge Mathematical Library, 1990 (Zbl 0715.11045). |
| `Titchmarsh1939theory` | Titchmarsh (1939), *The Theory of Functions*, Oxford University Press | https://zbmath.org/?q=an:65.0302.01<br>https://zbmath.org/?q=an:0005.21004 | First edition 1932 (Zbl 0005.21004); second edition 1939 (JFM 65.0302.01), x+454 pp. Standard source for the Phragmén-Lindelöf principle. |
| `Widder1941laplace` | Widder (1941), *The Laplace Transform*, Princeton Mathematical Series 6 | https://zbmath.org/?q=an:0063.08245 |  |
| `Prachar1957primzahlverteilung` | Prachar (1957), *Primzahlverteilung*, Grundlehren der Mathematischen Wissenschaften 91 | https://zbmath.org/?q=an:0080.25901 | Chapter X contains Linnik's theorem (zbMATH review of Pan 1957, Zbl 0083.26203). Reprinted 1978 (Zbl 0394.10001). |
| `Turan1984new` | Turán (1984), *On a New Method of Analysis and its Applications*, John Wiley & Sons | https://zbmath.org/?q=an:0544.10045 | zbMATH: 'A Wiley-Interscience Publication. New York etc.: John Wiley & Sons. XVI, 584 p.' |
| `Titchmarsh1986theory` | Titchmarsh (1986), *The Theory of the Riemann Zeta-Function*, Clarendon Press | https://zbmath.org/?q=an:0601.10026 |  |
| `Karatsuba1993basic` | Karatsuba (1993), *Basic Analytic Number Theory*, Springer-Verlag | https://doi.org/10.1007/978-3-642-58018-5<br>https://zbmath.org/?q=an:0767.11001 | Crossref lists the translator M. B. Nathanson as a second author; zbMATH lists Karatsuba alone with the translation note (used). |
| `Montgomery1994ten` | Montgomery (1994), *Ten Lectures on the Interface between Analytic Number Theory and Harmonic Analysis*, CBMS Regional Conference Series in Mathematics 84 | https://doi.org/10.1090/cbms/084<br>https://zbmath.org/?q=an:0814.11001 |  |
| `Davenport2000multiplicative` | Davenport (2000), *Multiplicative Number Theory*, Graduate Texts in Mathematics 74 | https://zbmath.org/?q=an:1002.11001 | The DOI 10.1007/978-1-4757-5927-3 belongs to the 1980 second edition and is deliberately not attached. |
| `Narkiewicz2000development` | Narkiewicz (2000), *The Development of Prime Number Theory: From Euclid to Hardy and Littlewood*, Springer Monographs in Mathematics | https://doi.org/10.1007/978-3-662-13157-2<br>https://zbmath.org/?q=an:0942.11002 |  |
| `IwaniecKowalski2004analytic` | Iwaniec & Kowalski (2004), *Analytic Number Theory*, Amer. Math. Soc. Colloq. Publ. 53 | https://doi.org/10.1090/coll/053<br>https://zbmath.org/?q=an:1059.11001 | Chapter 18, 'The least prime in an arithmetic progression', pp. 427-442 (Crossref chapter DOI 10.1090/coll/053/19). |
| `MontgomeryVaughan2007multiplicative` | Montgomery & Vaughan (2007), *Multiplicative Number Theory I. Classical Theory*, Cambridge Stud. Adv. Math. 97 | https://doi.org/10.1017/CBO9780511618314<br>https://zbmath.org/?q=an:1142.11001 | DISCREPANCY: Crossref dates the print edition 2006-11-16; zbMATH (and the usual citation) give 2007 (used). |
| `Tenenbaum2015introduction` | Tenenbaum (2015), *Introduction to Analytic and Probabilistic Number Theory*, Graduate Studies in Mathematics 163 | https://doi.org/10.1090/gsm/163<br>https://mathscinet.ams.org/mathscinet-getitem?mr=3363366<br>https://zbmath.org/?q=an:1336.11001 | Translation note as in MathSciNet MR3363366 ('Translated from the 2008 French edition by Patrick D. F. Ion'); zbMATH: 'Transl. from the 3rd French edition'. |

### 8. Explicit formula, zero detection and analytic tools (4)

| Key | Reference | Verified at | Discrepancies / notes |
|---|---|---|---|
| `PhragmenLindelof1908extension` | Phragmén & Lindelöf (1908), *Sur une extension d'un principe classique de l'analyse et sur quelques propriétés des fonctions monogènes dans le voisinage d'un point singulier*, Acta Math. 31, 381–406 | https://doi.org/10.1007/BF02415450<br>https://zbmath.org/?q=an:39.0465.01 | Crossref misspells the first author as 'Pharagmén'. |
| `Weil1952formules` | Weil (1952), *Sur les "formules explicites" de la théorie des nombres premiers*, Comm. Sém. Math. Univ. Lund [Medd. Lunds Univ. Mat. Sem.] 1952, 252–265 | https://mathscinet.ams.org/mathscinet-getitem?mr=53152<br>https://zbmath.org/?q=an:0049.03205 | Journal form from MathSciNet; zbMATH: 'Meddel. Lunds Univ. Mat. Sem., Suppl.-band M. Riesz, 252-265 (1952)' (volume dedicated to M. Riesz). |
| `Sion1958general` | Sion (1958), *On general minimax theorems*, Pacific J. Math. 8, 171–176 | https://doi.org/10.2140/pjm.1958.8.171<br>https://zbmath.org/?q=an:0081.11502 |  |
| `RosserSchoenfeld1962approximate` | Rosser & Schoenfeld (1962), *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6, 64–94 | https://doi.org/10.1215/ijm/1255631807<br>https://zbmath.org/?q=an:0122.05001 | Crossref has no pages; pages from zbMATH. |

### 9. Verified computation, interval arithmetic and linear programming (18)

| Key | Reference | Verified at | Discrepancies / notes |
|---|---|---|---|
| `Moore1966interval` | Moore (1966), *Interval Analysis*, Prentice-Hall Series in Automatic Computation | https://zbmath.org/?q=an:0176.13301 |  |
| `Chvatal1983linear` | Chvátal (1983), *Linear Programming*, A Series of Books in the Mathematical Sciences | https://zbmath.org/?q=an:0537.90067 |  |
| `Schrijver1986theory` | Schrijver (1986), *Theory of Linear and Integer Programming*, Wiley-Interscience Series in Discrete Mathematics | https://zbmath.org/?q=an:0665.90063 |  |
| `Jansson2004rigorous` | Jansson (2004), *Rigorous lower and upper bounds in linear programming*, SIAM J. Optim. 14, 914–935 | https://doi.org/10.1137/S1052623402416839<br>https://zbmath.org/?q=an:1073.90022 |  |
| `NeumaierShcherbina2004safe` | Neumaier & Shcherbina (2004), *Safe bounds in linear and mixed-integer linear programming*, Math. Program. 99, 283–296 | https://doi.org/10.1007/s10107-003-0433-3<br>https://zbmath.org/?q=an:1098.90043 |  |
| `ApplegateCookDashEspinoza2007exact` | Applegate et al. (2007), *Exact solutions to linear programming problems*, Oper. Res. Lett. 35, 693–699 | https://doi.org/10.1016/j.orl.2006.12.010<br>https://zbmath.org/?q=an:1177.90282 |  |
| `MooreKearfottCloud2009introduction` | Moore & Kearfott & Cloud (2009), *Introduction to Interval Analysis*, Society for Industrial and Applied Mathematics (SIAM) | https://doi.org/10.1137/1.9780898717716<br>https://zbmath.org/?q=an:1168.65002 |  |
| `ObuaNipkow2009flyspeck` | Obua & Nipkow (2009), *Flyspeck II: the basic linear programs*, Ann. Math. Artif. Intell. 56, 245–272 | https://doi.org/10.1007/s10472-009-9168-z<br>https://zbmath.org/?q=an:1184.68465 |  |
| `Rump2010verification` | Rump (2010), *Verification methods: rigorous results using floating-point arithmetic*, Acta Numer. 19, 287–449 | https://doi.org/10.1017/S096249291000005X<br>https://zbmath.org/?q=an:1323.65046 |  |
| `SolovyevHales2011efficient` | Solovyev & Hales (2011), *Efficient formal verification of bounds of linear programs*, Intelligent Computer Mathematics (Calculemus 2011 and MKM 2011, Bertinoro, Italy) 6824, 123–132 | https://doi.org/10.1007/978-3-642-22673-1_9<br>https://zbmath.org/?q=an:1335.68238 |  |
| `Tucker2011validated` | Tucker (2011), *Validated Numerics: A Short Introduction to Rigorous Computations*, Princeton University Press | https://doi.org/10.1515/9781400838974<br>https://zbmath.org/?q=an:1231.65077 |  |
| `Helfgott2015ternary` | Helfgott (2015), *The ternary Goldbach problem*, arXiv:1501.05438 | https://arxiv.org/abs/1501.05438 | arXiv v2 (2015-01-27). zbMATH links it from the ICM 2014 survey of the same title (Zbl 1373.11074). |
| `Platt2016numerical` | Platt (2016), *Numerical computations concerning the GRH*, Math. Comp. 85, 3009–3027 | https://doi.org/10.1090/mcom/3077<br>https://zbmath.org/?q=an:1345.11064 |  |
| `Hales2017formal` | Hales et al. (2017), *A formal proof of the Kepler conjecture*, Forum Math. Pi 5, e2 | https://doi.org/10.1017/fmp.2017.1<br>https://zbmath.org/?q=an:1379.52018 | Article e2, 29 pp. (zbMATH); 22 authors as in Crossref and zbMATH. |
| `HuangfuHall2018parallelizing` | Huangfu & Hall (2018), *Parallelizing the dual revised simplex method*, Math. Program. Comput. 10, 119–142 | https://doi.org/10.1007/s12532-017-0130-5<br>https://zbmath.org/?q=an:1402.90084 | Standard citation for the HiGHS solver (used through scipy.optimize.linprog, method='highs'). |
| `Virtanen2020scipy` | Virtanen et al. (2020), *SciPy 1.0: fundamental algorithms for scientific computing in Python*, Nature Methods 17, 261–272 | https://doi.org/10.1038/s41592-019-0686-2 | Crossref lists 112 author entries including the group 'SciPy 1.0 Contributors'; the first ten are given, then 'others'. computations/near/PROVENANCE.json pins scipy 1.17.0 (released 2026-01-10). |
| `PlattTrudgian2021riemann` | Platt & Trudgian (2021), *The Riemann hypothesis is true up to 3· 10^12*, Bull. Lond. Math. Soc. 53, 792–797 | https://doi.org/10.1112/blms.12460<br>https://zbmath.org/?q=an:1482.11111 |  |
| `mpmath2023library` | The mpmath development team (2023), *mpmath: a Python library for arbitrary-precision floating-point arithmetic (version 1.3.0)*,  | https://mpmath.org/<br>https://pypi.org/project/mpmath/1.3.0/ | Form follows the citation recommended on mpmath.org (which shows version 1.4.0, 2026); version 1.3.0 (released 2023-03-07 on PyPI) is the version pinned in computations/near/PROVENANCE.json. Adjust the version if a different one is used. |

### 10. Formal proof and Lean (9)

| Key | Reference | Verified at | Discrepancies / notes |
|---|---|---|---|
| `AvigadDonnellyGrayRaff2007formally` | Avigad et al. (2007), *A formally verified proof of the prime number theorem*, ACM Trans. Comput. Log. 9, Art. 2 | https://doi.org/10.1145/1297658.1297660<br>https://zbmath.org/?q=an:1367.68244 | Article No. 2, 23 pp. (zbMATH). |
| `Harrison2009formalizing` | Harrison (2009), *Formalizing an analytic proof of the prime number theorem*, J. Automat. Reason. 43, 243–261 | https://doi.org/10.1007/s10817-009-9145-6<br>https://zbmath.org/?q=an:1185.68624 |  |
| `Bailey2020nanoda` | Bailey (2020), *nanoda_lib*, GitHub repository ammkrn/nanoda_lib | https://github.com/ammkrn/nanoda_lib<br>https://api.github.com/users/ammkrn | GitHub account ammkrn = 'Chris Bailey' (GitHub API); repository created 2020-02-11; README: 'This is an external type checker for the Lean 4 programming language and theorem prover.' |
| `mathlib2020lean` | The mathlib Community (2020), *The Lean mathematical library*, Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020), 367–381, arXiv:1910.09336 | https://doi.org/10.1145/3372885.3373824<br>https://arxiv.org/abs/1910.09336 |  |
| `deMouraUllrich2021lean` | de Moura & Ullrich (2021), *The Lean 4 theorem prover and programming language*, Automated Deduction – CADE 28 12699, 625–635 | https://doi.org/10.1007/978-3-030-79876-5_37<br>https://zbmath.org/?q=an:1540.68264 |  |
| `Avigad2024mathematics` | Avigad (2024), *Mathematics and the formal turn*, Bull. Amer. Math. Soc. (N.S.) 61, 225–240 | https://doi.org/10.1090/bull/1832<br>https://zbmath.org/?q=an:1565.68005 |  |
| `KontorovichTao2024pnt` | Kontorovich & Tao & others (2024), *Prime Number Theorem And łdots*, GitHub repository AlexKontorovich/PrimeNumberTheoremAnd and blueprint (the PNT+ project) | https://github.com/AlexKontorovich/PrimeNumberTheoremAnd<br>https://alexkontorovich.github.io/PrimeNumberTheoremAnd/blueprint/<br>https://mathstodon.xyz/@tao/111847680248482955 | Repository created 2024-01-09 (GitHub API); described on GitHub as 'Blueprint for the PNT+ Project'; T. Tao's announcement calls it 'a new Lean formalization project led by Alex Kontorovich and myself'. Community project: cite with an access date. |
| `Stoll2024dirichlet` | Stoll (2024), *Dirichlet's theorem on primes in arithmetic progression*, Lean 4 Mathlib source file Mathlib/NumberTheory/LSeries/PrimesInAP.lean | https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/PrimesInAP.html<br>https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/LSeries/PrimesInAP.lean | Header: 'Copyright (c) 2024 Michael Stoll ... Authors: Michael Stoll'; module docstring title 'Dirichlet's Theorem on primes in arithmetic progression'. |
| `LeanFRO2025comparator` | Lean FRO (2025), *Comparator*, GitHub repository leanprover/comparator | https://github.com/leanprover/comparator | Repository created 2025-06-06 under the leanprover organization; README: 'Comparator is a trustworthy judge for Lean proofs'. The author string 'Lean FRO' is inferred from the organization and FORMALIZATION.md ('the Lean FRO Comparator'); the repository names no individual authors. |


## Candidates not verified (excluded)

These were considered but are **not** in `references.bib`. None of them could be verified against a
primary authoritative record, or the only records found conflict on a detail that could not be settled.

| Candidate | Reason |
|---|---|
| Dirichlet, original printing in Abh. K&ouml;nigl. Preuss. Akad. Wiss. Berlin (1837), "pp. 45-81" | Only secondary citations were found. The paper is cited through the verified *Werke* reprint (`Dirichlet1889beweis`) |
| Walfisz 1936 (Siegel-Walfisz theorem) | The search returned only "Zur additiven Zahlentheorie" in Prace Mat.-Fiz. 43 (1936), with conflicting pages: 81-118 in Zbl 0013.00603 and 81-114 in JFM 62.0151.02. The Math. Z. paper usually cited was not looked up |
| Kadiri's 2023 survey notes on zero-free regions (mentioned in `research/notes/literature-2026-09-28.md`) | No publication record found |
| K. Buzzard, survey on formalization (e.g. ICM 2022) | No record was confirmed (the zbMATH record found is licence-blocked); not pursued |
| G. Gonthier, "Formal proof - the four-color theorem", Notices AMS 2008 | Not checked; related zbMATH records found only for other Gonthier items |
| S. B. Stechkin (zero-free regions); Bordignon and Morrill-Trudgian (explicit Siegel-zero bounds); Mossinghoff-Trudgian-Yang (explicit zeta zero-free region, 2024); Kadiri-Ng (explicit density) | Not checked in this pass, so not included |
| IEEE Std 754-2019 (floating-point arithmetic) | The Crossref record (doi:10.1109/IEEESTD.2019.8766229) has no date or author metadata. The IEEE landing page was not checked, so it is not included |
| Iwaniec 1974, Linnik exponent "2.4" for special moduli (repository note) | The bibliographic record is verified and included (`Iwaniec1974zeros`); the numerical claim is not |
| Banks-Shparlinski, Linnik exponent "< 2.1115" (repository note) | Contradicted by the paper's own statement (see Discrepancies, item 2) |

## Verified but omitted to keep the list at 110-150 entries

Each of these was verified as described in its row, and each can be added unchanged. The generator
`build.py` in the scratchpad holds complete BibTeX data for them; remove a key from `DROP` to include it.

| Key | Reference | Verified at |
|---|---|---|
| `Landau1909handbuch` | Landau (1909), *Handbuch der Lehre von der Verteilung der Primzahlen*, B. G. Teubner | https://zbmath.org/?q=an:40.0232.08<br>https://zbmath.org/?q=an:40.0232.09 |
| `Turan1937primzahlen` | Turán (1937), *Über die Primzahlen der arithmetischen Progression*, Acta Litt. Sci. Szeged 8, 226–235 | https://zbmath.org/?q=an:0016.39104<br>https://zbmath.org/?q=an:63.0138.03 |
| `Linnik1941large` | Linnik (1941), *The large sieve*, C. R. (Doklady) Acad. Sci. URSS (N.S.) 30, 292–294 | https://mathscinet.ams.org/mathscinet-getitem?mr=4266<br>https://zbmath.org/?q=an:0024.29302 |
| `Selberg1946contributions` | Selberg (1946), *Contributions to the theory of Dirichlet's L-functions*, Skr. Norske Vid.-Akad. Oslo I 1946, 1–62 | https://mathscinet.ams.org/mathscinet-getitem?mr=22872<br>https://zbmath.org/?q=an:0061.08404 |
| `Bombieri1965large` | Bombieri (1965), *On the large sieve*, Mathematika 12, 201–225 | https://doi.org/10.1112/S0025579300005313<br>https://zbmath.org/?q=an:0136.33004 |
| `HalaszTuran1969distribution` | Halász & Turán (1969), *On the distribution of roots of Riemann zeta and allied functions, I*, J. Number Theory 1, 121–137 | https://doi.org/10.1016/0022-314X(69)90031-6<br>https://zbmath.org/?q=an:0174.08101 |
| `Jutila1969two` | Jutila (1969), *On two theorems of Linnik concerning the zeros of Dirichlet's L-functions*, Ann. Acad. Sci. Fenn. Ser. A I 458 | https://mathscinet.ams.org/mathscinet-getitem?mr=276182<br>https://zbmath.org/?q=an:0186.36303 |
| `Montgomery1969zeros` | Montgomery (1969), *Zeros of L-functions*, Invent. Math. 8, 346–354 | https://doi.org/10.1007/BF01404638<br>https://zbmath.org/?q=an:0204.37401 |
| `Huxley1975large` | Huxley (1975), *Large values of Dirichlet polynomials, III*, Acta Arith. 26, 435–444 | https://doi.org/10.4064/aa-26-4-435-444<br>https://zbmath.org/?q=an:0268.10026 |
| `Jutila1977zero` | Jutila (1977), *Zero-density estimates for L-functions*, Acta Arith. 32, 55–62 | https://doi.org/10.4064/aa-32-1-55-62<br>https://zbmath.org/?q=an:0307.10045 |
| `HeathBrown1978almost` | Heath-Brown (1978), *Almost-primes in arithmetic progressions and short intervals*, Math. Proc. Cambridge Philos. Soc. 83, 357–375 | https://doi.org/10.1017/S0305004100054657<br>https://zbmath.org/?q=an:0375.10027 |
| `HeathBrown1979zero` | Heath-Brown (1979), *Zero density estimates for the Riemann zeta-function and Dirichlet L-functions*, J. London Math. Soc. (2) 19, 221–232 | https://doi.org/10.1112/jlms/s2-19.2.221<br>https://zbmath.org/?q=an:0393.10043 |
| `LagariasMontgomeryOdlyzko1979bound` | Lagarias & Montgomery & Odlyzko (1979), *A bound for the least prime ideal in the Chebotarev density theorem*, Invent. Math. 54, 271–296 | https://doi.org/10.1007/BF01390234<br>https://zbmath.org/?q=an:0401.12014 |
| `Iwaniec1980rosser` | Iwaniec (1980), *Rosser's sieve*, Acta Arith. 36, 171–202 | https://doi.org/10.4064/aa-36-2-171-202<br>https://zbmath.org/?q=an:0435.10029 |
| `Chen1983exceptional` | Chen (1983), *The exceptional set of Goldbach numbers. II*, Sci. Sinica Ser. A 26, 714–731 | https://zbmath.org/?q=an:0513.10045 |
| `HeathBrown1983prime` | Heath-Brown (1983), *Prime twins and Siegel zeros*, Proc. London Math. Soc. (3) 47, 193–224 | https://doi.org/10.1112/plms/s3-47.2.193<br>https://zbmath.org/?q=an:0517.10044 |
| `RamareRumely1996primes` | Ramaré & Rumely (1996), *Primes in arithmetic progressions*, Math. Comp. 65, 397–425 | https://doi.org/10.1090/S0025-5718-96-00669-2<br>https://zbmath.org/?q=an:0856.11042 |
| `Hales2005proof` | Hales (2005), *A proof of the Kepler conjecture*, Ann. of Math. (2) 162, 1065–1185 | https://doi.org/10.4007/annals.2005.162.1065<br>https://zbmath.org/?q=an:1096.52010 |
| `LiuYe2005distribution` | Liu & Ye (2005), *Distribution of zeros of Dirichlet L-functions and the least prime in an arithmetic progression*, Acta Arith. 119, 13–38 | https://doi.org/10.4064/aa119-1-2<br>https://zbmath.org/?q=an:1078.11056 |
| `HelfgottPlatt2013numerical` | Helfgott & Platt (2013), *Numerical verification of the ternary Goldbach conjecture up to 8.875· 10^30*, Exp. Math. 22, 406–409 | https://doi.org/10.1080/10586458.2013.831742<br>https://zbmath.org/?q=an:1296.11128 |
| `Johansson2017arb` | Johansson (2017), *Arb: efficient arbitrary-precision midpoint-radius interval arithmetic*, IEEE Trans. Comput. 66, 1281–1292 | https://doi.org/10.1109/TC.2017.2690633<br>https://zbmath.org/?q=an:1388.65037 |
| `ThornerZaman2017explicit` | Thorner & Zaman (2017), *An explicit bound for the least prime ideal in the Chebotarev density theorem*, Algebra Number Theory 11, 1135–1197 | https://doi.org/10.2140/ant.2017.11.1135<br>https://zbmath.org/?q=an:1432.11167 |
| `PetrowYoung2023fourth` | Petrow & Young (2023), *The fourth moment of Dirichlet L-functions along a coset and the Weyl bound*, Duke Math. J. 172, 1879–1960 | https://doi.org/10.1215/00127094-2022-0069<br>https://zbmath.org/?q=an:1544.11068 |
| `Carneiro2024lean4lean` | Carneiro (2024), *Lean4Lean: Verifying a typechecker for Lean, in Lean*, arXiv:2403.14064 | https://arxiv.org/abs/2403.14064 |
| `Fiori2024least` | Fiori (2024), *The least prime in arithmetic an progression*, arXiv:2404.02329 | https://arxiv.org/abs/2404.02329 |
| `FordMaynard2024theory` | Ford & Maynard (2024), *On the theory of prime producing sieves*, arXiv:2407.14368 | https://arxiv.org/abs/2407.14368 |
| `Bruna2026conditional` | Bruna (2026), *A conditional bound for the least prime in an arithmetic progression*, arXiv:2603.25612 | https://arxiv.org/abs/2603.25612 |
| `LuZamanZhao2026numerical` | Lu & Zaman & Zhao (2026), *Numerical computations concerning Landau–Siegel zeros*, arXiv:2602.03626 | https://arxiv.org/abs/2602.03626 |

Further verified items with no BibTeX prepared:
* NumPy (Harris et al., Nature 585 (2020) 357-362, doi:10.1038/s41586-020-2649-2);
* Dantzig, *Linear Programming and Extensions* (Princeton 1963, Zbl 0108.33103, doi:10.1515/9781400884179);
* Montgomery-Vaughan, *Multiplicative Number Theory II. Primes and Sieves* (CUP 2026, doi:10.1017/9781009445030);
* Hadamard, Bull. SMF 24 (1896) 199-220 (doi:10.24033/bsmf.545);
* Bombieri-Friedlander-Iwaniec, Acta Math. 156 (1986) 203-251 (doi:10.1007/BF02399204);
* Huxley-Jutila, Acta Arith. 32 (1977) 297-312;
* Postnikov, J. Indian Math. Soc. 20 (1956) 217-226 (MR84010);
* Friedlander-Iwaniec, Selecta Math. 10 (2004) 61-69;
* Motohashi, Proc. Steklov Inst. Math. 280 (2013) S56-S64 ("An extension of the Linnik phenomenon").

