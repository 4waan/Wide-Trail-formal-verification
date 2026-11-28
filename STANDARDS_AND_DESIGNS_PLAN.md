# Implementation plan: standards (item 7) and new designs (item 8)

Prepared 2026-11-26 and revised 2026-11-27 after an adversarial review, for the WideTrail library
in this repository. Lean `v4.33.1`, Mathlib `v4.33.1`, rev
`0df444a360eaa60ab8c11dca51a86af692955474`.

Repository state on 2026-11-27 at 03:46 UTC:

* HEAD `d6a3907` on branch `proxy/gifted-ramanujan-397jqj`, which is pushed
  (`origin/proxy/gifted-ramanujan-397jqj` = `d6a3907`).
* `origin/main` is `2ae6391`. The nine commits `cba2cf8` … `d6a3907` are not on it, so
  `origin/main` has neither the `WideTrailHeavy` library (`git show origin/main:lakefile.toml`
  has no `WideTrailHeavy`) nor the Diag work.
* Uncommitted edits in `WideTrail/Poseidon2/PicoKoalaBear.lean` and
  `WideTrail/Poseidon2/Checks/PicoKoalaBear.lean`, since committed as `be3e05f`.

The plan is built from five research notes, each in its own directory under
`research/standards-and-designs/`:
`nist-rijndael256`, `skinny-gift`, `aes-zktls`, `new-designs` and `keccak`. It also draws on the
review material in `adversarial-review/` and the re-verification in `revision/` (log:
`research/standards-and-designs/revision/notes/VERIFICATION.txt`).

* Every statement about the repository was rechecked against the working tree on 2026-11-27.
* Status claims re-fetched on 2026-11-27 say so. The others keep their 2026-11-26 fetch date.
* On 2026-11-27 every one of the 72 distinct full SHA-256 values cited below was matched against
  a local file. The exception is the abbreviated hashes of live web pages, which change on every
  fetch (see the SP 800-197 entry).

**Where the research material is.** Paths under `research/standards-and-designs/` name the
material collected for this plan: downloaded sources, their extracted text, scripts, kernel
probes and SHA-256 manifests. Only the manifests are in this repository
(`research/standards-and-designs/`). The sources themselves are not, because several of them
may not be redistributed (Section 6, Q4 and Q12); the SHA-256 values cited below pin each one.
The scripts and probes are not committed either, since some of them embed third-party test
vectors.

Conventions.

* Effort: **S** less than a day, **M** a few days, **L** one to two weeks, **XL** open research
  with no schedule. Work longer than one L block is written as "2 × L".
* "Independent-key model" means the library's existing sample space: a probability is averaged
  over an additional independent uniform key added before each round
  (`Differential/Markov.lean`, `Differential/Scheduled.lean`, `Differential/Hull.lean`). Every
  probability in this plan is in that model unless it says otherwise.
* "Every trail" means every pattern sequence `T` with `WideTrailSpec.IsTrail S T r`
  (`Propagation/Cipher.lean:158`), which is what a real differential trail satisfies.
  "Functional trail" means `WideTrailSpec.trail a` (`Cipher.lean:111`), the orbit of one fixed
  S-box map. A bound for every functional trail does not cover every differential trail.
* "Merged" means merged into `origin/main`.
* "UNVERIFIED" marks a claim whose primary source could not be opened. A dated status claim
  gives the date the page was fetched.
* Lean names written in `code` that are not marked "(exists)" are proposals. None of them is in
  the repository today.
* Kernel timings are wall-clock on a 4-core / 15 GB profile with `decide +kernel`, including
  about 1 s of Lean start-up.

---

## 0. Repository facts rechecked for this plan (2026-11-27)

1. **The Rijndael-256 bounds are conditional, and they cover functional trails only (exists).**
   * `rijndael_four_round`, `rijndael_rounds`, `rijndael256_fourteen_round` and
     `rijndael256_fourteen_round_naive` take `hmix₈ : IsColBranchBound (gridCol 4 8) mix₈ 5`
     and `hnd₈ : NonDegenerate mix₈` as hypotheses (`WideTrail/Propagation/Rijndael.lean:244-300`,
     sections `Rijndael` and `Instances256`).
   * They bound `(rijndaelSpec …).trail a` and `trailWeight a r`, that is, functional trails.
     The form for every differential trail already exists generically:
     `WideTrailSpec.IsTrail.four_round` and `IsTrail.bound_rounds` (`Cipher.lean:190, 230`).
     `isTrail_of_trailKeyCount_ne_zero` (`Differential/TrailProb.lean:118`) links it to
     probabilities.
   * The concrete `aesMixColumns`, `aesMixColumns_isColBranchBound`, `_add` and
     `_nondegenerate` are defined only on `SquareIdx 4 = GridIdx 4 4`
     (`WideTrail/Algebra/AESMix.lean:139-184`).
   * The `WideTrailSpec` round applies MixColumns in every round, so the real final round, which
     has no MixColumns, is not modelled.
   * The S-box field of a spec is a placeholder: `aesLinSpec` uses `id`
     (`Differential/AESProb.lean:41-63`), because `AES.sbox 0 = 0x63` does not preserve support
     as a value map.
2. **The two-round differential bound exists, but nothing uses it for AES or Rijndael.**
   * `Scheduled.bricklayer_two_round_bound` and `Scheduled.diffKeyCount_bound_of_two_rounds` are
     in `WideTrail/Differential/Hull.lean:574, 587`.
   * Outside that file they are used only in `Hades/Hull.lean:89` and
     `Differential/Checks/Hull.lean` (grep, 2026-11-27).
   * The bound `(4/256)^4 = 2^-24` for AES-128 is therefore also new work, of size S. It is
     coarse; see 7a.
3. **No linear-cryptanalysis result exists.** `WideTrail/Algebra/Transpose.lean:13-19` says the
   linear branch number "is taken as the definition here and is not proved", because
   correlations are not formalised. The convention there propagates masks backwards: an output
   mask `v` corresponds to the input mask `Aᵀ v` (`Transpose.lean:13-14`).
4. **Branch and commit state.**
   * `WideTrailHeavy` was committed in `500a3f5`, on the feature branch only.
   * Engineering target 1, the `Diag` layer for an arbitrary internal diagonal:
     * committed in `4a37d31` (2026-11-26T23:46Z) and revised in `f483e67` (2026-11-27T03:12Z);
     * `d6a3907` (2026-11-27T03:34Z) adds `WideTrail/Poseidon2/PicoKoalaBear.lean` and
       `Checks/PicoKoalaBear.lean`, which `WideTrail/Poseidon2.lean:14,17` import into the
       default library;
     * at 03:46Z the two Pico files had uncommitted edits again;
     * `Poseidon2.Plonky3.Diag` opens at `WideTrail/Poseidon2/Plonky3.lean:390`.
   * So target 1 is committed on a feature branch and still active. Work in this plan does not
     edit `WideTrail/Poseidon2/` until target 1 is merged and no Poseidon2 work is open.
5. **How heavy modules are wired.**
   * CI builds the heavy modules one at a time, by name (`.github/workflows/ci.yml:51-54`). A new
     heavy module must be added there and to `WideTrailHeavy.lean`.
   * It must pass `scripts/AuditAxiomsHeavy.lean` (`ci.yml:77`) as well as
     `scripts/AuditAxioms.lean` (`ci.yml:74`). Those scripts and `scripts/check_imports.py` then
     cover it with no further change.
   * This wiring exists on the feature branch only (item 4).
6. **`decide +kernel` is already used.**
   * Where: `WideTrail/Differential/Checks/Hull.lean:135`
     (`theorem toy_count_le … := by decide +kernel`; docstring at line 39), from commit `6def301`
     (2026-11-26T19:18Z).
   * The module is imported at `WideTrail/Differential.lean:19`, so it is in the default library
     and passes `scripts/AuditAxioms.lean`.
   * Using it more needs no new policy, only README wording. Every probe run for this plan
     reported the axioms `[propext, Quot.sound]`.
7. **Arithmetic and tables.**
   * `GF256.xtime : BitVec 8 → BitVec 8` (`WideTrail/Algebra/GF256.lean:86`) is the FIPS
     `xtime`. It sits in the `GF256` namespace opened at line 54, before `structure GF256`
     (line 270). A round constant therefore needs a wrapper:
     `rcon j := ⟨GF256.xtime^[j-1] 1#8⟩`, or `(2 : GF256) ^ (j-1)` with a lemma that the two
     agree.
   * `AES.sbox` (`Algebra/AESSbox.lean:48`) is the FIPS S-box. The aes-zktls note checked it
     against Table 4 in the kernel.
8. **Large enumerations do not finish in the kernel.**
   * `GF256.lean:20-23` records that even a `256²`-shaped commutativity `decide` timed out.
   * `Differential/Checks/ATTACKS.md:146-153` records that the AES DDT bound was therefore
     proved by a root count (`Sbox.inv_uniform`, `Differential/Polynomial.lean:33`).
   * This sets the cost of R5 (the LAT) and of SKINNY's S8.
9. **Names.**
   * The root-namespace `two_round` (`Propagation/Activity.lean:119`) is the deterministic
     statement, for one fixed map `γ` with `PreserveSupport γ`. There is no `Activity.two_round`.
   * For differential trails, use `WideTrailSpec.IsTrail.two_round` (`Cipher.lean:182`), or argue
     directly from `activePattern_eq_of_diffCount_ne_zero` (`Differential/Bricklayer.lean:66`)
     plus `isBranchBound`. The direct argument also works without a `WideTrailSpec`, as Keccak
     and Ascon need.
10. **Cell types.** `BitVec n` addition is addition modulo `2^n`, not XOR. 4-bit and 5-bit cells
    (SKINNY-64 nibbles, Keccak rows, Ascon columns) need an XOR wrapper, as `GF256` is for bytes.

---

## 1. Executive summary

**What to do, in order.**

1. **Make the existing Rijndael-256 results unconditional, state them for every differential
   trail, and turn them into probabilities (R0-R1, about 3-4 days).** Neither step uses the key
   schedule, so both survive any change NIST makes to it.
2. **Build one FIPS 197-shaped specification, parametric in `Nb, Nk ∈ {4,6,8}` (R2-R4, about
   1.5-2 weeks).**
   * It comes with a kernel runner, known-answer tests (KATs), key-schedule facts and a bridge to
     the trail model. This is the "full AES spec" that both 7a and 7c need.
   * The KATs come from FIPS 197 and CAVP first. The 3GPP/ETSI Rijndael-256 vectors are
     committed only after the licence question (Q4) is answered.
3. **Draft the NIST package (R8, S-M), but do not send it** until the owner has decided the
   name, channel and timing (Section 6, Q1-Q3). As of 2026-11-27 there is no FIPS 197 revision
   draft to comment on.
4. **In parallel, build two cheap foundations.**
   * Keccak (K0-K4, about 1.5 weeks): the FIPS 202 specification with KATs, the chi and theta
     facts, and a two-round bound that holds at every width.
   * Ascon (A0-A1, S-M): the SP 800-232 permutation's S-box and Σ facts and its two-round
     bound. It uses the same row and column activity argument as Keccak.
5. **Add a machine-checked ARX scope module (D0, S) now. Build the design-kit facade (D1, M)
   only after target 1 is merged and no Poseidon2 work is open.**
6. **Linear work.**
   * The AES S-box Walsh bound (R5a, M) can start before target 3, with a local Walsh
     definition. It carries the main kernel risk of R5.
   * After target 3 (the linear framework) is in: the remaining linear trail bounds for
     Rijndael-256 and AES (R5), SKINNY, Keccak and Ascon.
7. **Gate all certificate-heavy work on one kernel-throughput spike** (task 3 in Section 5). It
   covers the SKINNY truncated automaton, the Keccak small-width certificates and the Ascon
   3-round certificate. The spike must measure scaling curves, not single points.
8. **Treat the rest as research with no schedule:**
   * multi-round Keccak-f[1600] certificates;
   * GIFT beyond five rounds;
   * related-(twea)key differential bounds;
   * a checker for MILP certificates;
   * verification of deployed zkTLS circuits;
   * a kernel-checked multi-round MEDP bound in the style of Keliher and Sui (R9).

**What each step would let the project say publicly, and what it would not.**

| Step | Effort | Can say | Cannot say |
|---|---|---|---|
| R0-R1, Rijndael-256 bounds | S + S-M | With ShiftRows offsets (0,1,3,4) and the real MixColumns, every differential trail (`IsTrail`) of Rijndael-256 has at least 25 active S-boxes in 4 rounds and at least 80 in 14 rounds, kernel-checked. In the independent-key model: each 4-round trail ≤ 2^-150, each 14-round trail ≤ 2^-480 (also with a final round without MixColumns, and the same final-round form for AES-128/192/256). A coarse two-round key-averaged differential bound of 2^-24. | Anything about the real key schedule, a fixed key, differentials over more than two rounds, linear or related-key attacks, integral/Square or truncated attacks. That Rijndael-256 is secure. Any new cryptanalysis: the trail bounds are the designers' 1999 claims (proposal §8.2), now machine-checked. The 2^-24 figure is not informative on its own: the exact AES two-round MEDP 53/2^34 ≈ 2^-28.27 has been known since 2005 (Keliher-Sui). |
| R2-R4, spec, KATs, key schedule | L + S-M (about 1.5-2 weeks) | A FIPS 197-upd1-shaped Lean specification of the Rijndael family reproduces, in the kernel, FIPS 197 Appendices A and B and the 2001 Appendix C. Once Q4 allows, it also reproduces all 8 Rijndael-256-256 vectors of 3GPP TS 35.236 / ETSI TS 135 236 V19.0.0, with all 15 round keys of test 1. Decryption inverts encryption. For every key, the first 60 expanded words equal the AES-256 expansion. Nk = 8 needs Rcon[11..14] = 6c, d8, ab, 4d, beyond FIPS Table 5. | That any implementation is correct. That the key schedule adds security. That the probability bounds hold for the cipher with its expanded keys. |
| R8, NIST package | S-M | A comment that states each fact with its Lean name and its model, with a reproducible, hash-pinned artifact. | Anything a reader could take as a security endorsement. The 2^-24 two-round figure presented as informative. |
| R5a, then T3 and R5, linear | M (R5a), L (T3), then M (R5) | Every 4-round linear trail of Rijndael-256 or AES has \|correlation\| ≤ 2^-75 (the designers' §8.2.2 claim, machine-checked). The AES S-box has \|correlation\| ≤ 2^-3. | Linear-hull statements beyond what T3 proves. |
| K0-K4, Keccak foundation | M-L (about 1.5 weeks) | The Keccak-p[b, nr] specification reproduces the FIPS 202 examples and the XKCP intermediate values. At every width, every 2-round differential trail has weight at least 8 (tight). Chained over nr rounds, every trail has weight at least 8·⌊nr/2⌋ + 2·(nr mod 2). In the independent-key model, every 2-round differential has probability at most 2^-6. | Any bound beyond the chained two-round bound 8·⌊nr/2⌋ + 2·(nr mod 2). Anything about the security of SHA-3, ML-KEM or ML-DSA. |
| A0-A1, Ascon two rounds | S-M | The Ascon S-box of SP 800-232 has differential uniformity 8 (probability 2^-2) and differential branch number 3. Each Σi has branch number 4. Every 2-round differential trail of Ascon-p has at least 4 active S-boxes (the Table 12 value). In the independent-key model, each 2-round trail ≤ 2^-8 and each 2-round differential ≤ 2^-6. | The 3-round minima 15/13 (that needs A2). Anything for 4 or more rounds, where even the designers have only heuristic values. Anything about Ascon-AEAD128 or Ascon-Hash256 security. |
| D0, ARX scope | S | The wide-trail hypotheses (support preservation, bricklayer factorisation) provably fail for addition mod 2^n, and counting active words yields probability 1 per word. | Any bound for an ARX design. |
| D1-D2, design kit | M, plus S-M per obligation | From the parameters of a HADES-type design one gets a kernel-checked certificate: bijectivity, active S-boxes, the trail exponent, the 2-round differential exponent and the inactive dimensions. The four existing instances (BN254, SP1 KoalaBear, SP1 BabyBear, Pico KoalaBear) are re-derived through it. | Resistance to algebraic attacks, which sets the round counts of large-field designs. Designers' heuristics such as Poseidon's p^-t differential criterion. |
| SKINNY automaton (L0-L4, L7) | 2 × L (about 3-4 weeks), L3 gated by the spike | Single-key differential: at least 36 active S-boxes in 8 rounds, hence at least 180 over the 40 rounds of Skinny-128-384+ (Alfarano et al. give 200 by Matsui's algorithm). The same for linear activity, which the designers state also holds in the related-tweakey model (Table 7 caption). All kernel-checked. | Related-tweakey differential bounds. Exact full-round optima: the full 46.7M-edge ladder is out of kernel reach on the measured throughput. |
| Z1, gadget algebra | S-M | The identities behind the hinted-inverse, multiplexer-table, T-table and sparse base-9 AES gadgets hold, with their explicit side conditions. A per-block key check accepts a transcript produced with two different keys. | That any deployed circuit is sound. |

**Not worth doing:**

* Wide-trail counting for SHA-2 or BLAKE3. D0 replaces it with a proved scope statement.
* The 2^32-entry DDT of Saturnin's super-box in the kernel.
* A `Field` instance for GF(2^128), until some algebraic GHASH proof actually needs it.

**Effort for the minimum credible package.**

* For 7a, R0-R4 plus R8 is about 2-3 weeks.
* The Keccak foundation is about 1.5 weeks, and the Ascon two-round part is S-M.
* The ARX scope module and the facade together are M.
* Everything else is gated or research.

---

## 2. Items

### 7a. Rijndael-256 and the FIPS 197 revision

**State of the outside world (re-fetched 2026-11-27 unless stated).**

* **No draft text exists**, neither a FIPS 197 revision nor SP 800-197, and no Rijndael-256
  comment period is open.
  * The CSRC FIPS list shows "FIPS 197 (Final) 5/09/2023"
    (https://csrc.nist.gov/publications/fips).
  * "Drafts open for comment" lists no FIPS and no SP 800-197
    (https://csrc.nist.gov/publications/drafts-open-for-comment).
  * The CSRC 2026 news lists nothing on Rijndael. Its latest item is "NIST Will Revise SP 800-52
    Rev. 2", November 19, 2026 (https://csrc.nist.gov/news/2026).
  * A Federal Register API search for "Rijndael" returns only 01-30232 (2001-12-06, approval of
    FIPS 197) and 03-15189 (2003-06-17, export regulations).
* **2024-08-09.** M. Dworkin (NIST) on ciphermodes-forum: "One plausible option is for a version of
  Rijndael with 256-bit blocks and 256-bit keys ... The main technical questions are whether to
  revise the key schedule and, more generally, whether additional security vetting is necessary."
  (https://groups.google.com/a/list.nist.gov/g/ciphermodes-forum/c/D5qni2KDoms; confirmed by
  the review on 2026-11-27).
* **2024-12-23.** SP 800-197 pre-draft call for comments ("NIST Proposes to Standardize a Wider
  Variant of AES"; https://csrc.nist.gov/pubs/sp/800/197/iprd).
  * It covers Rijndael-256 with a single 256-bit key size. Fields re-read on 2026-11-27:
    * "Date Published: December 23, 2024";
    * "Comments Due: June 25, 2025 (public comment period is CLOSED)";
    * "Planning Note (07/07/2025)";
    * "Publication: No Download Available".
  * The announcement says "NIST plans to develop a draft standard for Rijndael-256 over the next
    year". That year has passed with no draft.
  * Comments went to `ciphermodes@nist.gov` (decoded from the page's obfuscated address) with the
    subject "Comments on Rijndael-256". NIST posted them with "Submitters' names and affiliations
    (when provided)".
  * On page hashes: the hash `dc72a90a13ee41c0bd90e1b541d3c6ec5481c46b8315ea889003d8111afa0820`
    identifies only the snapshot saved on 2026-11-26
    (`nist-rijndael256/SHA256SUMS.html-snapshots-2026-11-26.txt:1`). The live page hashes
    differently on every fetch (`62581ddb…` and `dd110e4b…` on 2026-11-27), while the cited
    fields stay the same.
  * The news item is dated December 24, 2024
    (https://csrc.nist.gov/news/2024/nist-proposes-to-standardize-wider-variant-of-aes).
* **2025-07-07/09.** NIST posted 10 comments; #4 was added on Jul 9
  (https://csrc.nist.gov/files/pubs/sp/800/197/iprd/docs/sp800-197-pre-draft-public-comments.pdf,
  p.1). They include:
  * NSA CCSS: "the eventual standardization of the published specification of Rijndael-256-256
    is a natural choice ... If NIST considers modifying Rijndael-256-256, the changes should
    admit simple analysis, such as ... a linear key schedule" (comment 6, pdf p.9).
  * NLNCSA (comment 8, pdf pp.21-22):
    * MILP minimum active S-boxes, single key, rounds 1..11 = 1, 5, 9, 25, 41, 50, 58, 65, 74,
      85, 93. These are uncertified optima.
    * "The probability of a related-key differential trail in Rijndael-256-256 is at most
      2^-288" (pdf p.22).
  * Zhang et al.: security margin "above 25% across all evaluated attack scenarios"
    (comment 5, pp.7-8).
  * Saarinen: "the first 7 of Rijndael-256's round keys have the same bytes as the first 14
    round keys of AES-256" (comment 7, pdf p.13).
  * Avanzi et al. oppose vanilla Rijndael-256 (comment 9, pp.26-28). Avanzi repeated this on
    the forum on 2026-07-30: "I am worried by the concept of standardizing vanilla
    Rijndael-256." (https://groups.google.com/a/list.nist.gov/g/ciphermodes-forum/c/V14PA3UOn0k,
    thread "Comments on Rijndael-256", post dated "Jul 30, 2026"; fetched 2026-11-27, HTTP 200,
    sha256 `1d4d7b30e8f88daa616850b5b1b34add3bb4acd808b4d78371d5fd0bbfbbb061`).
  * Do not confuse that post with item 11 of the SP 800-38D Rev. 1 second-pre-draft comments
    (Avanzi, July 30, 2026, p.37). That item is about naming the POLYVAL-like function MHASH
    (local text extraction `nist-rijndael256/text/sp800-38Dr1-2prd-comments-090126.txt`, lines
    23 and 1462-1470).
* **2025-06-06.** SP 800-197A pre-draft: "Acc256 ... (possibly Rijndael-256)"
  (https://csrc.nist.gov/pubs/sp/800/197/a/iprd).
* **2026-01-28.** NIST talk, slide p.10: "NIST plans to develop a revision of FIPS 197 to include
  Rijndael-256", "Rijndael with a 256-bit block size and fixed 256-bit key"
  (https://csrc.nist.gov/csrc/media/presentations/2026/mpts2026-3a1/images-media/mpts2026-3a1-slides-nist-symm-meltem.pdf,
  pp.10, 14). This is the only NIST source found that names FIPS 197 as the vehicle.
* **2026-06-01.** SP 800-38D Rev.1, second pre-draft, proposes wGCM "to support the Rijndael-256
  variant of AES". Comments were due 2026-07-31; 16 were posted on 2026-09-01
  (https://csrc.nist.gov/pubs/sp/800/38/d/r1/2prd).
* **Precedents for a comment period.**
  * The 2022 editorial update of FIPS 197 went through CSRC only, with no Federal Register
    notice found:
    * draft "updated December 19, 2022", "Comments Due: February 13, 2023" (56 days);
    * comments to `cryptopubreviewboard@nist.gov` with "Comments on Draft FIPS 197 Update" in
      the subject line (https://csrc.nist.gov/pubs/fips/197/ipd);
    * "No public comments were received on the proposal nor the draft"
      (https://csrc.nist.gov/news/2023/nist-updates-fips-197-advanced-encryption-standard,
      May 09, 2023);
    * Federal Register API searches since 2022-06-01, for "FIPS 197" and for "Advanced Encryption
      Standard" with agency NIST, return no notice for it (2026-11-27).
  * The FIPS 203-205 drafts, which added algorithms, had a Federal Register notice and 90 days:
    FR 2023-18197, published 2023-08-24, comments closed 2023-11-22
    (https://www.federalregister.gov/documents/2023/08/24/2023-18197/request-for-comments-on-draft-fips-203-draft-fips-204-and-draft-fips-205).
  * The 2001 AES draft FIPS also had a 90-day period
    (https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/archived-crypto-projects/aes-development).
  * A FIPS 197 revision that adds Rijndael-256 is a technical change, so the FIPS 203 pattern
    is the likelier one. This is an inference, not a NIST schedule.
* **The object to be standardised.**
  * Nb = 8, Nk = 8, Nr = 14, ShiftRows offsets 0, 1, 3, 4, and the unmodified 1999 key schedule.
  * That schedule needs Rcon[1..14]. FIPS 197-upd1 tabulates only Rcon[1..10] (§5.2, pdf p.25;
    https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf).
  * FIPS 197-upd1 §6.3 (pdf p.34) allows future parameter extensions.
* **The designers' evidence (1999 proposal, valid for all block lengths).**
  * §8.2.1: "no 4-round differential trails with a predicted prop ratio above 2^-150".
  * §8.2.2: "no 4-round linear trails with a correlation above 2^-75" (Rijndael-ammended.pdf,
    pdf pp.32-33).
  * These are trail bounds; the proposal makes no two-round differential claim.
  * NIST cites no analysis of its own (news item of Dec 24, 2024).
* **Known exact two-round values for AES (128-bit block), in the same key-averaged model.**
  * The 2-round MEDP is "53/2^34 ≈ 1.656 × 2^-29" (≈ 2^-28.27), and the 2-round MELP is
    "109,953,193/2^54 ≈ 1.638 × 2^-28".
  * For T ≥ 4 rounds this gives "(53/2^34)^4 ≈ 1.881 × 2^-114" (≈ 2^-113.1) and
    "(109,953,193/2^54)^4 ≈ 1.802 × 2^-110".
  * Source: Keliher and Sui, ePrint 2005/321, abstract (https://eprint.iacr.org/2005/321,
    fetched 2026-11-27, sha256
    `87686085a80c349ea39cb905b99e054f7d4d1da9b5a0e6415130f1ccee2a7f7c`). The paper body was not
    opened.
  * Rijndael-256's exact 2-round MEDP is UNVERIFIED.
* **Deployment.** 3GPP TS 35.235 V19.0.0 makes Rijndael-256-256 the kernel of MILENAGE-256
  (clause 8.4.1). TS 35.236 V19.0.0, clause 5.1.2, gives 8 test vectors, and test 1 lists all 15
  round keys.
* **TS 35.235 errata, now confirmed in the published PDF.** ETSI TS 135 235 V19.0.0 (2026-01)
  (https://www.etsi.org/deliver/etsi_ts/135200_135299/135235/19.00.00_60/ts_135235v190000p.pdf,
  sha256 `8e0cb013532fc8502e812185d01adc18341eedb46ef188336aa79665e9f39b0b`) carries both errata
  that the nist-rijndael256 note found in the docx text:
  * Clause 11.5 (pdf p.28, printed p.27) says "on column j, for j = 0, 1, 2, 3", for an 8-column
    state. The prose c(x) gives the x² coefficient as '0x0', where it should be '0x01'. The
    explicit equations that follow are correct.
  * Clause 11.7 (pdf p.30, printed p.29), row 0 uses "S-box[rk r-1,7,7]", while rows 1-3 use
    (2,7), (3,7), (0,7). By RotWord, row 0 should use rk r-1,1,7.

**Inputs gathered (local files, SHA-256 recomputed).**

* Rijndael proposal v2: Tables 1-2, KeyExpansion for Nk ≤ 6 and Nk > 6, §7.4-7.6, §8.2.
  `research/standards-and-designs/nist-rijndael256/downloads/rijndael-submission/Rijndael-ammended.pdf`,
  `53e07be3640a824ffaddb34921a8300d935c7a394fb4e7f0629e8729e863a7ea`.
* FIPS 197-upd1: Algs. 1-5, Tables 3-6, Appendices A and B.
  `research/standards-and-designs/nist-rijndael256/downloads/NIST.FIPS.197-upd1.pdf`,
  `62c86eb567f13edb8f71826e985da870b04ef6381634f303cdb16e84d47becd1`.
* FIPS 197 (2001), with the full Appendix C.1-C.3 traces of Cipher, InvCipher and EqInvCipher.
  `research/standards-and-designs/aes-zktls/downloads/nist/NIST.FIPS.197.pdf`,
  `251dfe0b5dc283abaf364adf586f7ec6dc4e495335d48dd5ee0fee6c5961da8a`.
* **Transcription source for the Rijndael-256 vectors:** ETSI TS 135 236 V19.0.0 (2026-01),
  clause 5.1.2, tests #1-#8, all legible.
  `research/standards-and-designs/adversarial-review/downloads/etsi/ts_135236v190000p.pdf`,
  `a5038db8d2d2ddfd886a71fe29f193a23f64f4da6d5c7e4320994435a5cf528e`.
  * Its notice (pdf p.2) reads: "No part may be reproduced or utilized in any form or by any
    means … except as authorized by written permission of ETSI" (Q4).
  * An independent model written from FIPS 197
    (`research/standards-and-designs/revision/scripts/r256check.py`,
    `d908343c0c0ea714be5fd3ac3d9d205bb30a90d2387225793e07085a738f155a`) reproduces, from the
    PDF's text, all 8 outputs and all 15 round keys of test 1. Byte order is n = i + 4j.
* The 3GPP archives of the same specifications (docx inside; the text layer of TS 35.236 is
  partly garbled), each carrying a 3GPP copyright notice (Q4):
  * TS 35.236 V19.0.0:
    `research/standards-and-designs/nist-rijndael256/downloads/3gpp/35236-j00.zip`,
    `6e5fc20e356aa700fbd4973ccea2cdfdeacfe152f683bc1fa4e5f6e814f9f925`.
  * TS 35.235 V19.0.0:
    `research/standards-and-designs/nist-rijndael256/downloads/3gpp/35235-j00.zip`,
    `9ffa7523a9b6ca8dfaddc22bd3eacb8103cbbe1616f01cbf9f949d282b2e02cb`.
* The Rijndael submission KATs, 128-bit block only. `ecb_iv.txt` gives AES-128 intermediates,
  for regressing the parametric spec at Nb = 4.
  `research/standards-and-designs/nist-rijndael256/downloads/rijndael-submission/rijndael-vals.zip`,
  `046e9235d4b2dffea79b76bb1e3a06a665e5a2130839278dd8c50b7762fe83bb`.
* SP 800-197 pre-draft comments (MILP target figures and the positions on the key schedule).
  `research/standards-and-designs/nist-rijndael256/downloads/sp800-197-pre-draft-public-comments.pdf`,
  `699dc8af8fec84208fad7ed0aa35b1465af59a9226be654a98f6aef9924d3f6b`.
* NIST slides of 2026-01-28.
  `research/standards-and-designs/nist-rijndael256/downloads/mpts2026-3a1-slides-nist-symm-meltem.pdf`,
  `94a69b7f493eaa5b95b5abea31396dcff0ad663b41bcf20919dc13215dfc10b2`.
* CAVP AES KATs: 2078 ECB vectors, all reproduced by the outside model.
  `research/standards-and-designs/aes-zktls/downloads/nist/KAT_AES.zip`,
  `a203b16c9246b2ebae31dee5de21a606be80cf78ceabaca37150236fa098eb60`.
* Outside cross-check model (Python, written from the 1999 proposal).
  * It reproduces all 8 TS 35.236 vectors, all 15 round keys of test 1, and FIPS 197 C.1-C.3.
  * It also gives regression values for Nk = 4 and 6 at Nb = 8, for which no published source
    was found (UNVERIFIED as published values).
  * Location:
    `research/standards-and-designs/nist-rijndael256/tools/`
    (hashes in
    `research/standards-and-designs/nist-rijndael256/SHA256SUMS.tools.txt`).
* Kernel measurement with a scratch List runner over the library's `GF256` and `AES.sbox`
  (`research/standards-and-designs/revision/spike/R256.lean`,
  `cb12c551a83f9585542462e9c6869a6ceaa0271d2ff4ebc8955e7b4d17fdb074`). Axioms
  `[propext, Quot.sound]`.

  | Run | Time | Peak RSS |
  |---|---|---|
  | TS 35.236 #3 | 20.3 s | 3.55 GB |
  | TS 35.236 #7 | 24.6 s | not measured |
  | #3 and #7 in one file | 41.0 s | 3.85 GB |
  | Review's runs: #3 / #7 | 24.1 s / 22.8 s | 3.7 GB |

  All 8 vectors in one default-library module should therefore take about 3 minutes.
* Full manifests:
  `research/standards-and-designs/nist-rijndael256/SHA256SUMS.downloads.txt`,
  `research/standards-and-designs/nist-rijndael256/SHA256SUMS.html-snapshots-2026-11-26.txt`,
  `research/standards-and-designs/adversarial-review/SHA256SUMS.downloads.txt`
  and
  `research/standards-and-designs/revision/SHA256SUMS.downloads.txt`.
* Lean parameters:
  * Nr = max(Nb, Nk) + 6.
  * The offsets are `shiftOff256 = ![0,1,3,4]` (exists) when Nb = 8, and (0,1,2,3) otherwise.
  * The expanded key has Nb·(Nr+1) words, and round key r is words Nb·r .. Nb·r + Nb - 1.
  * Rcon[1..14] = 01 02 04 08 10 20 40 80 1b 36 6c d8 ab 4d (recomputed 2026-11-27). Rcon is a
    `GF256` value built with a wrapper around `GF256.xtime` (Section 0, item 7).
  * At Nb = 8, Nk = 6 needs Rcon up to 19 and Nk = 4 up to 29. Since ord(0x02) = 51, these are
    distinct.
  * When Nk > 6, SubWord is also applied at i mod Nk = 4.
  * The final round has no MixColumns.

**Reuse (all exist).**

* **Propagation:** `GridIdx`, `gridCol`, `shiftRowsPerm`, `diffusionOptimal_shiftRowsPerm_iff`,
  `gridSpec`, `transpose`, `shiftOff256`, `shiftOff256_diffusionOptimal`,
  `card_diffusionOptimal_offsets_256` (= 1680), `shiftOff256naive_diffusionOptimal`,
  `shiftOff256_sq_not_diffusionOptimal`, `rijndaelSpec`, `rijndael_rounds`,
  `WideTrailSpec.IsTrail`, `IsTrail.four_round`, `IsTrail.bound_rounds`,
  `WideTrailSpec.trailWeight_bound_rounds`, `patternWeight`.
* **Algebra:** `GF256`, `GF256.xtime`, `AES.sbox`, `AES.sboxInv`, `AES.sboxEquiv`,
  `AES.affineEquiv`, `aesMatrix`, `aesMatrix_isMDS`, `isMDS_branch_bound`, `isMDS_injective`,
  `localWeight_sqCol_eq_weight` (to generalise from `sqCol` to `gridCol`), `isMDS_transpose_iff`.
* **Differential:** `bricklayer`, `trailKeyCount_le_of_spec`, `isTrail_of_trailKeyCount_ne_zero`,
  `linAddEquiv`, `card_gf256`, `aes_uniformity_clears`, `AES.sbox_uniform`,
  `Scheduled.trailKeyCount_eq_prod`, `Scheduled.run`, `Scheduled.diffKeyCount`,
  `Scheduled.bricklayer_two_round_bound`, `Scheduled.diffKeyCount_bound_of_two_rounds`.
  `aesLinSpec` and the `aes*_prob` theorems (AESProb.lean) are the template, including the `id`
  placeholder for the spec's S-box field.
* **Patterns:**
  * KATs: `Poseidon2/Plonky3Execution.lean` (runner plus refinement theorem) and
    `Poseidon2/Checks/Plonky3KAT.lean` (`kat_dense`, `kat_fails_*` negative controls).
  * Certificates: `PRODUCTION_CERTIFICATE.md` (sources, claims, boundary).
  * Prototype: the scratch file
    `research/standards-and-designs/aes-zktls/proto/AESProto.lean`
    (`e58dc18a544fe7da85959abfabeb42be9315eb1124a8479486682cfc6f2cfb47`) already decides
    FIPS 197 Appendix B, C.2 and C.3 and Table 4 over the library's `GF256`, in 38 s on 4 cores,
    with axioms `[propext, Quot.sound]`.

**Theorems to state (proposed signatures, in prose Lean).**

```
-- R0  WideTrail/Rijndael/MixColumns.lean
def  Rijndael.mixColumns (cols : ℕ) : (GridIdx 4 cols → GF256) → (GridIdx 4 cols → GF256)
theorem Rijndael.mixColumns_add, mixColumns_nondegenerate
theorem Rijndael.mixColumns_isColBranchBound (cols) [NeZero cols] :
    IsColBranchBound (gridCol 4 cols) (mixColumns cols) 5
theorem Rijndael.mixColumns_four : mixColumns 4 = aesMixColumns          -- regression
def rijndael256LinSpec := rijndaelSpec 8 shiftOff256 shiftOff256_injective id (mixColumns 8)
    (fun _ => rfl) (mixColumns_isColBranchBound 8) (mixColumns_nondegenerate 8)
    -- `id` placeholder as in aesLinSpec; IsTrail reads only the linear layer
-- headline form: every differential trail
theorem rijndael256_four_round_concrete {T} {n} (h : rijndael256LinSpec.IsTrail T (n + 4))
    (h0 : T 0 ≠ 0) : 25 ≤ weight (T n) + weight (T (n+1)) + weight (T (n+2)) + weight (T (n+3))
theorem rijndael256_rounds_concrete {T} {r} (h : rijndael256LinSpec.IsTrail T r) (h0 : T 0 ≠ 0) :
    r / 4 * 25 + (if 2 ≤ r % 4 then 5 else 0) ≤ patternWeight T r          -- IsTrail.bound_rounds
theorem rijndael256_fourteen_round_concrete : … IsTrail T 14 → T 0 ≠ 0 → 80 ≤ patternWeight T 14
theorem rijndael192_twelve_round_concrete  : … IsTrail T 12 → T 0 ≠ 0 → 75 ≤ patternWeight T 12
-- corollaries in the form of the existing theorems (functional trail)
theorem rijndael256_fourteen_round_concrete_trail (sbox) (hsbox : PreserveSupport sbox)
    (ha : a ≠ 0) : 80 ≤ (rijndaelSpec 8 shiftOff256 … sbox (mixColumns 8) …).trailWeight a 14
theorem Rijndael.lin_isBranchBound (cols) [NeZero cols] (off : Fin 4 → Fin cols) :
    isBranchBound id (mixColumns cols ∘ transpose (shiftRowsPerm 4 cols off)) 5
    -- no injectivity hypothesis: shiftRowsPerm is a permutation for every off (Grid.lean:64-69)

-- R1  WideTrail/Rijndael/Probability.lean
theorem card_state256 : Fintype.card (GridIdx 4 8 → GF256) = 2 ^ 256
theorem rijndael256_four_round_prob (hs : ∀ i, Injective (s i)) (hu : ∀ i, IsDiffUniform (s i) 4)
    (h0 : T 0 ≠ 0) (x) : trailKeyCount rijndael256Lin (bricklayer s) 4 T x * 2 ^ 150 ≤ (2 ^ 256) ^ 4
theorem rijndael256_eight_round_prob    … 8 …  * 2 ^ 300 ≤ (2 ^ 256) ^ 8   -- first r with exponent > 256
theorem rijndael256_fourteen_round_prob … 14 … * 2 ^ 480 ≤ (2 ^ 256) ^ 14
theorem rijndael256_two_round_differential (ha : a ≠ 0) (b x) :
    Scheduled.diffKeyCount (fun _ => rijndael256Lin) (fun _ => bricklayer fun _ => AES.sbox) 2 a b x
      * 2 ^ 24 ≤ (2 ^ 256) ^ 2
    -- docstring: coarse (4 of the 5 branch S-boxes charged at 2^-6); for AES-128 the exact
    -- two-round MEDP is 53/2^34 ≈ 2^-28.27 (Keliher-Sui, ePrint 2005/321)
theorem rijndael256_differential (R) (hR : 2 ≤ R) … : … R … * 2 ^ 24 ≤ (2 ^ 256) ^ R
theorem aes128_two_round_differential : the same at Nb = 4, also 2^-24      -- new for AES too
theorem rijndael256_fourteen_round_prob_final :
    Scheduled.trailKeyCount lamSched γSched 14 T x * 2 ^ 480 ≤ (2 ^ 256) ^ 14
    -- lamSched n = MixColumns ∘ ShiftRows for n < 13, lamSched 13 = ShiftRows alone
theorem aes128_ten_round_prob_final, aes192_twelve_round_prob_final,
        aes256_fourteen_round_prob_final                 -- the aes*_prob exponents 330/450/480,
                                                         -- with the real last round

-- R2  WideTrail/Rijndael/{Tables,Spec,Execution}.lean and Checks/
structure Rijndael.Params := (Nb Nk : ℕ) (hNb : Nb ∈ [4,6,8]) (hNk : Nk ∈ [4,6,8])
def Nr, offsets, subWord, rotWord
def rcon (j : ℕ) : GF256 := ⟨GF256.xtime^[j - 1] 1#8⟩        -- xtime acts on BitVec 8
def keyExpansion (P) (key : Fin (4 * P.Nk) → GF256) : Fin (P.Nb * (Nr P + 1)) → Word
def cipher, invCipher, eqInvCipher, keyExpansionEIC          -- FIPS 197-upd1 Algs. 1-5
theorem invCipher_cipher (P key x) : invCipher P key (cipher P key x) = x
theorem cipher_invCipher, eqInvCipher_eq_invCipher
theorem sbox_table4, sboxInv_table6, rcon_table5, invMatrix_mul_aesMatrix
theorem cipher_eq_exec (P key x) : cipher P key x = Exec.cipher P key x    -- runner refinement
theorem fips197_A1_A2_A3 (all expanded words), fips197_appendixB (every round state),
        fips197_2001_C1/C2/C3 (Cipher, InvCipher and EqInvCipher traces)
theorem ts35236_vector (n : Fin 8) : cipher ⟨8,8,…⟩ (key n) (X n) = Y n      -- only after Q4
theorem ts35236_test1_roundKeys : ∀ r : Fin 15, roundKey ⟨8,8,…⟩ key₁ r = RK₁ r   -- only after Q4
theorem kat_fails_offsets0123, kat_fails_rcon10, kat_fails_noSubWordAt4, kat_fails_finalMix
    -- each: the modified spec gives ≠ the published output on a stated vector

-- R3  WideTrail/Rijndael/KeySchedule.lean
theorem keyExpansion_prefix_aes256 (key) (i : ℕ) (hi : i < 60) :
    keyExpansion ⟨8,8,…⟩ key i = keyExpansion ⟨4,8,…⟩ key i        -- Saarinen's observation
theorem keyExpansion_window_determines (P) (j) (h : ∀ i ∈ [j, j + P.Nk), w key i = w key' i) :
    key = key'                                                      -- proposal §7.5 criterion
theorem rcon_values : rcon 11 = 0x6c ∧ rcon 12 = 0xd8 ∧ rcon 13 = 0xab ∧ rcon 14 = 0x4d
theorem rcon_injOn : Set.InjOn rcon (Set.Icc 1 29)
theorem rcon_maxIndex (P) : the largest Rcon index KeyExpansion reads is 14 / 19 / 29 at
    Nb = 8 with Nk = 8 / 6 / 4

-- R4  WideTrail/Rijndael/Bridge.lean
theorem cipher_eq_scheduledRun (P key x) :
    cipher P key x = Scheduled.run (lamSched P) (fun _ => subBytes) (Nr P) (roundKeys P key) x
                       + roundKey P key (Nr P)
    -- docstring: the probability theorems average over *all* key vectors, not over roundKeys

-- R5a (may start before T3, with a local `walsh`, later replaced by T3's)
theorem AES.sbox_walsh_le (a b) (hb : b ≠ 0) : |walsh AES.sbox a b| ≤ 32       -- |C| ≤ 2^-3
-- R5  (after target 3)
theorem rijndael256_four_round_linear : |trailCorrelation …| ≤ 2^-75 ; fourteen: ≤ 2^-240
```

**Staged plan.**

| Stage | Content | Effort | Main risk |
|---|---|---|---|
| R0 | `Rijndael.mixColumns` on `GridIdx 4 cols`. Generalise `localWeight_sqCol_eq_weight` to `gridCol`. Unconditional 25/80 (Nb = 8) and 75 (Nb = 6), stated over `IsTrail` via `IsTrail.bound_rounds`, with functional-trail corollaries. Whole-state branch number 5 (no injectivity hypothesis). Checks: axiom pins; a non-MDS mix over `GridIdx 4 8` that fails the hypothesis. | S | Low. |
| R1 | Probability at 4, 8 and 14 rounds. Two-round differential 2^-24 at Nb = 4 and Nb = 8, documented as coarse. A final-round variant in `Scheduled` with lam 13 = ShiftRows; the count needs only the 13 MixColumns transitions, and lam 13 is a bijection that relabels T 14. The same final-round variants for the existing `aes128_ten_round_prob`, `aes192_twelve_round_prob` and `aes256_fourteen_round_prob` (S). A sharpness check that the per-S-box exponent 6 cannot be raised by this arithmetic, as in the Poseidon2 checks. | S-M | Kernel arithmetic with 2^256 to the 14th power; copy the AESProb patterns. |
| R2 | Parametric spec, Nat-byte runner with a refinement proof for generic (Nb, Nk), InvCipher and the EqInvCipher equivalence (InvMixColumns linearity and the commuting lemmas), the table theorems, KATs, 4 negative controls (about 15 KAT statements). Default library: Appendices A and B, 2001 C.1-C.3, the CAVP ECB subset. After Q4: all 8 TS 35.236 vectors and the 15 round keys of test 1, in one default-library module (measured at about 20-25 s and 3.6-3.9 GB per vector with a scratch runner). | L (1-1.5 weeks) | The generic refinement proof. The index conventions (in[r+4c]), fixed by the KATs. The licence of the 3GPP/ETSI vectors (Q4). |
| R3 | Key-schedule facts. A docstring says explicitly that no trail theorem uses the key schedule. | S-M | Low. |
| R4 | Bridge lemma from the FIPS cipher to `Scheduled.run`. | S | Low. |
| R5a | The AES S-box Walsh bound, by one of two routes: (i) the trace-form lemma (every F2-linear functional on GF(2^8) is x ↦ Tr(αx)), the reduction of each Walsh value of inversion to a Kloosterman sum, the 255 Kloosterman sums of 256 terms each by `decide +kernel` in balanced recursion, and the affine layer's mask map; (ii) digit-packed tables with `decide +kernel`, as in lean-aes. A naive 256²-shaped enumeration will not finish (Section 0, item 8). | M | Kernel cost. lean-aes reports about 48 s for route (ii); UNVERIFIED in this repository. |
| R5 | Linear bounds: linear branch number 5 via `isMDS_transpose_iff`, 2^-75 per 4 rounds, 2^-240 per 14. If T3 keeps the backward convention of `Transpose.lean:13-14` (masks through Lᵀ = πᵀ∘θᵀ), each round applies θᵀ before πᵀ, the reverse of the `WideTrailSpec` shape `mix ∘ transpose disp` (`Cipher.lean:103-104`). The transposed specification must then be rebracketed: each πᵀ is regrouped with the next round's θᵀ across the S-box layer, which a byte permutation only relabels. With forward propagation through L⁻ᵀ = θ⁻ᵀ∘π⁻ᵀ the round keeps the mix∘permutation shape. | M, after target 3 and R5a | Depends on the T3 interface and its direction convention. |
| R6 | Tighter active-S-box counts: (a) a three-round bound of 9 (M); (b) 41 and 50 for 5 and 6 rounds, the MILP figures (L-XL); (c) a checker for MILP or branch-and-bound certificates (XL). | L-XL | Unknown certificate size; a 2^32 truncated state at 4×8. |
| R7 | Related-key truncated bounds (NLNCSA: 2^-288 for the full 14 rounds). | XL | Needs a truncated model of the key schedule. |
| R8 | Submission package, described after this table. | S-M | Timing, and a possible change to the key schedule (Q1-Q3). |
| R9 | A kernel-checked multi-round MEDP bound in the existing averaged-key model, following Keliher-Sui (exact 2-round MEDP 53/2^34 for AES; Rijndael-256's value UNVERIFIED). | XL | The 2-round MEDP computation is large; the paper body was not opened. |

R8, the submission package, consists of:

* `RIJNDAEL256_CERTIFICATE.md`;
* `WideTrail/Rijndael/Claims.lean`, with each claim as a named theorem with pinned axioms;
* `submission/rijndael256/`, with LETTER.md, PROVENANCE.md and REPRODUCE.md.

The letter states the model and the limits plainly. It presents the 2^-24 two-round figure only
as a coarse bound, next to the known exact value. It makes three suggestions to NIST:

* tabulate Rcon[11..14];
* publish Rijndael-256 intermediate values (the CSRC example-values page lists AES only,
  confirmed 2026-11-27);
* phrase the security claims as precise statements in the trail model.

Ordering risk: if NIST changes the key schedule, R2-R4 have to be redone, but R0-R1, R5a and R5
do not, because they never use it.

**Explicit non-goals for 7a:**

* Any claim that Rijndael-256 is secure or meets a stated security level.
* Any use of the real key schedule in a probability bound.
* Related-key, integral/Square or truncated-differential resistance (criteria 2-3 of proposal
  §7.4).
* Modes (wGCM, Accordion), implementations and side channels.
* Proposing a modified key schedule.
* New cryptanalysis.

### 7b. Design-rationale evidence for SKINNY and GIFT

**State of the outside world.**

* **Standards status.** Romulus (Skinny-128-384+) and GIFT-COFB (GIFT-128) were NIST
  lightweight-cryptography finalists. NIST selected Ascon in February 2023 and published
  SP 800-232 on August 13, 2025 (https://csrc.nist.gov/projects/lightweight-cryptography and
  https://csrc.nist.gov/pubs/sp/800/232/final; confirmed 2026-11-27). Ascon is treated in 8b,
  because its bound pipeline is the Keccak one.
* **Best attacks.** NIST IR 8454 (June 2023), Table 7: "KR of GIFT-128 (27 out of 40 rounds)",
  "RKR of Skinny-128-384+ (32 out of 40 rounds)"
  (https://nvlpubs.nist.gov/nistpubs/ir/2023/NIST.IR.8454.pdf, pdf p.20, printed p.9; sha256
  `0f89ee7b08f4670042a3f558fb911230af1f24fc0932fe3604cf2150a00db5eb`).
* **ISO.** ISO/IEC 18033-7:2022 reportedly specifies SKINNY variants (UNVERIFIED; iso.org
  returned 403 on 2026-11-27).
* **SKINNY designers' table.** The SKINNY-AEAD/Hash round-2 spec gives bounds from MILP and
  Matsui's algorithm
  (https://csrc.nist.gov/CSRC/media/Projects/lightweight-cryptography/documents/round-2/spec-doc-rnd2/SKINNY-spec-round2.pdf).
  * Table 7 (pdf p.37), SK rows 1-15: 1 2 5 8 12 16 26 36 41 46 51 55 58 61 66.
  * The body of §5.1 (pdf p.36) says "those bounds are for single characteristic only". The
    linear case uses only the single-key model "as there is no cancellation of active Sboxes in
    linear characteristics".
  * The Table 7 caption (pdf p.37) says "the bounds on the number of linear active Sboxes in the
    single-key model are also valid in the related-tweakey model".
  * Table 7 runs to 30 rounds. §5.3 (pdf p.39) says Alfarano et al. "computed the bounds for up
    to 40 rounds in the single-key setting, while the designers only gave bounds for up to 22
    rounds", and that Table 7 takes their values from round 23 on.
* **Alfarano et al.** (ToSC 2018(2)) extend the SK differential bounds to 40 rounds by Matsui's
  algorithm, with B(40) = 200 (https://tosc.iacr.org/index.php/ToSC/article/download/887/838,
  App. C.2, pdf p.28).
* **GIFT.**
  * The designers' CHES 2017 slides give BOGI and the claim ">= 7 active Sboxes in 5 rounds"
    (https://ches.iacr.org/2017/slides/ches2017s5t3.pdf, slides 26-34).
  * Sun, Wang and Wang (ToSC 2021(1)) give SAT optima for the full rounds, with no proof
    certificates (https://tosc.iacr.org/index.php/ToSC/article/download/8840/8443, Tables 4-5).
* **Inaccessible primary texts.** The ePrint PDFs of the SKINNY and GIFT papers (2016/660,
  2017/622) returned HTTP 403 on 2026-11-26 and again on 2026-11-27. The abstract pages are
  reachable. Their contents, including SKINNY-64 test vectors and the BOGI proof text, are
  UNVERIFIED.
* **Certificates.** No published DRAT, LRAT or VeriPB certificate was found for any
  active-S-box bound (search not exhaustive). arXiv 2609.20873 (Pandey, submitted 2026-09-16)
  names the same gap, the "refutation gap", for XOR-circuit minimality claims; it does not
  discuss active-S-box bounds (https://arxiv.org/abs/2609.20873, abstract, sha256
  `d956efbe06bff90f7b139af820bb0a201f7e251f6a21c7ee182429c2511692f1`).
* **Key technical finding** (skinny-gift note, recomputed there).
  * Classical wide trail gives only B² = 4 active S-boxes per 4 rounds for SKINNY and CRAFT,
    whose binary MixColumns has branch number 2 (SKINNY spec p.32). That is 40 over 40 rounds,
    against the true 200.
  * The fix is one generic object: a truncated-activity automaton over the 2^16 column
    patterns, sound over any XOR group (characteristic 2), with a DP certificate pruned at a
    threshold.
  * GIFT is bit-level and has no word-level mixing layer, so classical wide trail gives nothing
    for it.

**Inputs gathered.**

* SKINNY round-2 spec (Table 7, S8 table in App. A, KATs in App. B).
  `research/standards-and-designs/skinny-gift/downloads/nist/SKINNY-spec-round2.pdf`,
  `b0d2e3c7c6837168d32d4b746cd8bf07b4f903dca8c5bada66be9f1a89d2c71c`.
* Romulus v1.3 (Skinny-128-384+, its KAT with C = ff38d1d24c864c4352a853690fe36e5e).
  `research/standards-and-designs/skinny-gift/downloads/nist/romulus-spec-final.pdf`,
  `358113f30554ca19bfdb37e02e2f7459934b6bee0620c7e8707fb3efa699954f`.
* GIFT-COFB v1.1.
  `research/standards-and-designs/skinny-gift/downloads/nist/gift-cofb-spec-final.pdf`,
  `31e222d673dc587c621af5f0dd41aba213cc47e7fb6fe7225f01a75ebc30949f`.
* GIFT reference code and 6 KAT traces from giftcipher/gift at commit
  `f43c6b3e214e39c22dc0ae5efcc39297809d9b68`, in
  `research/standards-and-designs/skinny-gift/downloads/gift-repo/`.
  * `GIFT64-128_cipher.cpp`: `069a0ea08c4d10acfcdb7c18018eb9f6fd136c01e37f261bf893aab7e3277b2c`
  * `GIFT128-128_cipher.cpp`: `8a0a2e6385ea02567ecd82fd0c33bb67de3a05ea2bd4d2319d0f0cb76c004c84`
  * `GIFT64_test_vector_1.txt`: `226c9fa1b2a950bb5522b4982d619f5c94492be78758fdaa4f08c5770157b194`
  * `GIFT128_test_vector_1.txt`: `a8ebfb300cfa04274df974a1865e7d439be28f4815ff8c8441bedc5784f2b163`
  * The repository license is UNVERIFIED.
* Alfarano et al.
  `research/standards-and-designs/skinny-gift/downloads/tosc/alfarano2018.pdf`,
  `5de524546fa681c1c65fe7ac79d221de523fbeff2eee5a588b1d7b0c231da109`.
* Sun-Wang-Wang.
  `research/standards-and-designs/skinny-gift/downloads/tosc/sun-wang-wang-2021.pdf`,
  `b6ec593e7469964cc16dc40eab8745cfec62bb37905452658ed0f888db33ed01`.
* Delaune et al. (HAL), CRAFT (ToSC 2019) and the GIFT CHES 2017 slides are listed with their
  hashes in
  `research/standards-and-designs/skinny-gift/notes/SHA256SUMS.txt`.
* Tables ready for Lean:
  * SKINNY:
    * S4 = [c,6,9,0,1,a,2,b,3,8,5,d,4,e,7,f];
    * ShiftRows P = [0,1,2,3,7,4,5,6,10,11,8,9,13,14,15,12];
    * M = [[1,0,1,1],[1,0,0,0],[0,1,1,0],[1,0,1,0]];
    * (M⁻¹)ᵀ = [[0,0,0,1],[1,1,1,0],[0,1,0,0],[0,1,1,1]].
  * GIFT: GS = [1,a,4,c,6,f,3,9,2,d,b,7,5,0,8,e]; the P64 and P128 closed form.
  * Midori and CRAFT: Sb0 = [c,a,d,3,e,b,f,7,8,9,1,5,0,2,4,6]; CRAFT M and PN.
  * All with sources, in the skinny-gift note and in
    `research/standards-and-designs/skinny-gift/scripts/truncated_dp.py`
    (`5399338cc63f2aaa70423cc429d5a30f8df4f953271244854b6a931dae4f022e`).
* Reproduction outputs.
  * SKINNY SK differential B(1..40) and linear B(1..23) match the published tables.
  * The linear values for rounds 24-40 (110, 115, 121, 127, 130, 135, 141, 147, 153, 157, 160,
    166, 172, 177, 180, 186, 192) have no published confirmation that could be opened.
  * Measured pruned certificate sizes: the B(1..8) ladder needs about 2.48M edge checks, linear
    B(8) 0.34M, and B(1..40) 46.7M.
  * Files, all in
    `research/standards-and-designs/skinny-gift/notes/`:
    `truncated_dp_output.txt`, `pruned_cert_size_output.txt` and `ladder_cost_output.txt`.
* Kernel throughput baseline for L3, measured 2026-11-27 on a 2^16-leaf trie
  (`research/standards-and-designs/revision/spike/`,
  hashes in `revision/SHA256SUMS.scripts-spike.txt`):

  | Lookups per theorem | Time | Peak RSS |
  |---|---|---|
  | 200 | 1.4 s | not recorded |
  | 2,000 | 5.3 s | 0.97 GB |
  | 5,000 | 10.3 s | 1.7 GB |
  | 10,000 | 22.4 s | 2.85 GB |
  | 20,000 | 198.5 s | 5.1 GB |

  * So a lookup costs about 2 ms when a theorem holds at most about 10^4 lookups, and the cost
    blows up beyond that.
  * At that rate the B(1..8) ladder (2.48M edges) needs at least about 80 minutes single-core,
    split into hundreds to thousands of theorems. That is heavy-library only.
  * The 46.7M-edge ladder needs at least about 26 hours, which is out of reach.

**Reuse (all exist).**

* **Propagation:** `activePattern`, `weight`, `isBranchBound`, `PreserveSupport`, the root
  `two_round` (deterministic) and `WideTrailSpec.IsTrail.two_round` (for trails),
  `IsColBranchBound`, `DiffusionOptimal`, `transpose`, `WideTrailSpec`, `gridSpec`. These give
  the classical corollaries for SKINNY (B = 2), Midori (B = 4) and PHOTON.
* **Algebra:** `IsMDS`, `isMDS_branch_bound`, `isMDS_transpose_iff`, and `GF256` as the XOR group
  for SKINNY-128 cells.
* **Differential:**
  * `diffCount`, `IsDiffUniform` with its decidable instance, `diffCount_bricklayer_le`.
  * `trailKeyCount_bricklayer_le`. It takes any `lam : (Idx → K) ≃+ (Idx → K)`, so a GIFT bit
    permutation or SKINNY's MC∘SR plugs in.
  * `activePattern_eq_of_diffCount_ne_zero`, and `isTrail_of_trailKeyCount_ne_zero` as the
    template for the automaton bridge.
  * `Scheduled`, for round-dependent layers.
* **Not reusable as is:** `Hull.diffKeyCount_bound_of_two_rounds` charges only B - 1 = 1 for
  SKINNY, which is weak.

**Theorems to state (proposed).**

```
-- Algebra/XorBits.lean, Algebra/GF16.lean (X^4+X+1)
structure XorBits (n : ℕ) := (val : BitVec n)   -- AddCommGroup by XOR, Fintype, DecidableEq
abbrev Nibble := XorBits 4                       -- BitVec's own + is addition mod 2^n

-- SPN/Skinny/Sbox.lean, SPN/Gift/Sbox.lean
theorem Skinny.S4_bijective, Skinny.S4_uniform : IsDiffUniform Skinny.S4 4
theorem Skinny.S8_uniform : IsDiffUniform Skinny.S8 64            -- digit-packed table, M
theorem Gift.GS_uniform : IsDiffUniform Gift.GS 6
theorem Gift.GS_six_iff (a b) : diffCount Gift.GS a b = 6 ↔ (a, b) = (4, 7) ∨ (a, b) = (6, 3)
theorem Gift.bogi_ddt : oneBitDDT Gift.GS i j ≠ 0 → i = 0 ∧ j = 3   -- GI, GO, BI, BO sets
theorem Gift.GS_no_fixedPoint, Gift.bogi_identity (BO ⊆ GI, for the DDT and the LAT)

-- Search/Automaton.lean
def TruncRel (n) := Finset (Fin n) → Finset (Finset (Fin n))
def TruncRel.Sound (R) (M : (Fin n → G) → (Fin n → G)) := ∀ x, supp (M x) ∈ R (supp x)
def relOf (A : Matrix (Fin 4) (Fin 4) Bool) : TruncRel 4
    -- the support transitions realisable over (ZMod 2)^4; every characteristic-2 solution spans
    -- a subgroup of rank ≤ 4, so this covers every XOR group
theorem binaryMatrix_rel_sound (A : Matrix (Fin 4) (Fin 4) Bool) [AddCommGroup G]
    (h2 : ∀ g : G, g + g = 0) : (relOf A).Sound (A.actOn (G := G))
    -- h2 is needed: over ZMod 3, A = rows (1,1,0,0),(0,1,1,0),(1,0,1,0),(0,0,0,1) and
    -- x = (1,2,1,0) give supports {0,1,2} → {2}, impossible in an XOR group (6 such pairs)
theorem path_of_trailKeyCount_ne_zero : Scheduled.trailKeyCount … ≠ 0 → IsPath aut (patterns T)
theorem minWeight_superadditive : B (a + b) ≥ B a + B b
def check (aut) (R b : ℕ) (Bprev : Fin R → ℕ) : Bool        -- threshold-pruned forward DP
theorem check_sound (hB : ∀ r < R, ∀ p, IsPath aut p r → Bprev r ≤ weight p) :
    check aut R b Bprev = true → ∀ p, IsPath aut p R → b ≤ weight p
    -- without hB an inflated Bprev prunes every branch; alternatively `check` re-verifies the
    -- ladder Bprev itself and hB is dropped

-- SPN/Skinny/Bounds.lean
theorem skinny_sk_active_eight (T) (h : trailKeyCount skinnyLin (bricklayer S) 8 T x ≠ 0)
    (h0 : T 0 ≠ 0) : 36 ≤ Σ n < 8, weight (T n)
theorem skinny128_384plus_trail_prob : trailKeyCount … 40 T x * 2 ^ 360 ≤ (2 ^ 128) ^ 40
theorem skinny_lin_active_eight : 32 ≤ …          -- masks through (M⁻¹)ᵀ; correlation after T3
theorem skinny_classical_gap : the gridSpec route gives only 4 per 4 rounds (a Checks file)
theorem midori_four_round_classical : 16 ≤ …      -- B = 4, DiffusionOptimal ShuffleCell
theorem gift_five_round_active : 7 ≤ …            -- a small search certificate (7-12k nodes)
theorem skinny_kat_128_256, skinny_kat_128_384, skinny_kat_128_384plus, gift64_kat_1..3, gift128_kat_1..3
```

**Staged plan** (the order recommended by the skinny-gift note, merged with Section 3):

| Stage | Content | Effort | Risk |
|---|---|---|---|
| L0 | Spike, shared with task 3 of Section 5: kernel throughput on 2^16-leaf tries and automaton edges at three or more sizes, linear against balanced recursion, chunk size per theorem, and certificate data as a literal against recomputed in the kernel. Go/no-go for L3 only. | S-M | Kernel time and memory. In the kernel, lists cost O(n) per lookup, so the spike uses tries. The 2026-11-27 baseline (about 2 ms per lookup up to 10^4 per theorem) is above. |
| L1 | `XorBits`/`Nibble`, the S-box facts (SKINNY S4, Midori/CRAFT Sb0, GIFT GS with BOGI) by `decide`; SKINNY S8 with digit packing. | S, plus M for S8 | The S8 table cost (65,536 DDT cells; a 256²-shaped enumeration, see Section 0, item 8). |
| L2 | `Search/Automaton`: soundness for binary matrices over characteristic-2 groups, the path lemma, superadditivity, `check_sound` with the ladder hypothesis, and the bridge to `trailKeyCount`. Pure theory, not gated by the spike. | M | Low. |
| L3 | The verified checker, with certificates for SKINNY B(1..8), differential and linear. Then Skinny-128-384+ (≥180 over 40 rounds), Midori and CRAFT. | M-L, spike-gated | Certificate size: at least about 80 min of kernel time for B(1..8), heavy library. The full 40-round ladder (46.7M edges, at least about 26 h) is out of reach. |
| L4 | Classical-bound corollaries, as checks that show the gap. | S each | None. |
| L5 | Structural proofs: Midori's Prop. 4 (≥28 in 6 rounds), the GIFT BOGI 5-round bound. | M-L | The BOGI proof text is UNVERIFIED; a small certificate can replace it. |
| L6 | GIFT 6-7 rounds by certificate (3.8M and 11.5M nodes). | XL | Probably beyond the kernel. |
| L7 | Executable specs and KATs for SKINNY-128-256/384/384+ and GIFT-64/128. SKINNY-64 waits for vectors that could not be opened. | M each | Nibble and bitslice ordering (GIFT-COFB loads bits differently from the reference code). |
| L8 | Related-tweakey differential bounds. Linear activity needs only a small transfer lemma, since the designers state that single-key linear bounds also hold in the related-tweakey model (Table 7 caption). | XL (differential); S (linear transfer) | Counters per cell; out of kernel reach. |
| L9 | PHOTON256 (12,869 MDS minors over GF(2^4); the MDS property of Serial^8 is UNVERIFIED). Saturnin, shared with 8a. | M-L | Kernel cost of the minors. |

**Explicit non-goals for 7b:** related-tweakey differential certificates in the kernel; the AEAD
modes (Romulus, GIFT-COFB); GIFT bounds the kernel cannot certify; integral and
impossible-differential attacks; any claim about standards status beyond the cited pages.

### 7c. AES-in-circuit gadgets used in zkTLS

**State of the outside world.**

* **Provenance of the GitHub facts.** All repository revisions below are pinned, and source
  files were read on 2026-11-26. The GitHub-hosted facts (the TLSNotary release date and tag,
  Crema PR #7) could not be re-checked on 2026-11-27, because github.com and api.github.com
  returned 403 to this environment. They rest on the aes-zktls note of 2026-11-26.
* **Gadget families.**
  * Boolean (Bristol) circuits with Boyar-Peralta S-boxes, 32 AND gates each.
    * TLSNotary `v0.1.0-beta.1` (tag commit `40a0695`, release dated 14 Nov 2026) uses the mpz2
      circuits `AES128_KS` and `AES128_POST_KS` at rev
      `23e2cc08ed11ae86d71f72fb968f1273d70c9e88`.
    * It also uses GHASH by share conversion and QuickSilver.
  * Lookup tables: Reclaim gnark at `aa1ad6629be0cd84be16094a472ebafb33738187`;
    Barretenberg/Noir at `aztec-packages@6542e71b9cf40d819fe1d6efaf7aca923aefd80d`, with
    base-9 sparse XOR.
  * R1CS with a hinted inverse (Crema) or a constrained multiplexer table (Pluto, archived).
  * Underconstrained `<--` assignments: Electron Labs, and the circom copy inside Reclaim at
    `aa1ad66`, whose readme says "may be insecure".
* **Documented defects.**
  * Crema PR #7, merged 2024-09-11: unconstrained S-box outputs let "malicious provers to
    arbitrarily specify SBox output results"
    (https://github.com/crema-labs/aes-circom/pull/7; quotes relayed through a fetch tool, not
    byte-exact; not re-checked 2026-11-27).
  * Xie and Wang's report (undated): "Reclaim actually proves each AES block separately without
    ensuring that the encryption key remains consistent across all blocks"
    (https://hackmd.io/@-fI_Eu_rR8qs02aOhOPWNg/HkRyz5OF1g, lines 157-173). The fix status is
    UNVERIFIED.
* **GCM is not committing.**
  * DECO, arXiv 1909.00938v6 p.8.
  * "Proxying Is Enough" (AFT 2025, ePrint 2024/733 abstract) reports that AES-GCM fails context
    unforgeability.
* **Audits.**
  * No third-party audit of any zkTLS AES gadget was found. The search was not exhaustive
    (UNVERIFIED as complete).
  * The zkSecurity Reclaim audit of 2023-09-23 covered ChaCha20 only
    (https://reports.zksecurity.xyz/reports/reclaim/).
* **Lean circuit frameworks.**
  * zksecurity `clean`:
    * a tag `v4.33.1` (peeled commit `93c9d1ef45be9f687214625d7857889cf2485504`) pins exactly
      this library's Lean and Mathlib;
    * it offers `FormalCircuit`, `Soundness`, `Completeness` and static lookup tables, but no AES
      gadget;
    * its LLZK (circom) frontend is on its roadmap only.
  * zkLean (Lean v4.25.2) has an LLZK bridge; the toolchains do not match.
  * LNSym (Lean v4.35.0) has AES and GCM specs, useful as a cross-check.
* **Standards context.** NIST announced on 2024-03-05 that it will revise SP 800-38D
  (https://csrc.nist.gov/news/2024/nist-to-revise-sp-80038d-gcm-and-gmac-modes; confirmed
  2026-11-27).

**Inputs gathered.**

* NIST standards: FIPS 197-upd1, FIPS 197 (2001) and the CAVP AES KATs, as in 7a.
* SP 800-38D (2007).
  `research/standards-and-designs/aes-zktls/downloads/nist/NIST.SP.800-38D.pdf`,
  `d99f3921ccebca049e7522426553aba071dae14ec3d5b6041e8c111a6cb57bba`.
* AES_GCM.pdf examples.
  `research/standards-and-designs/aes-zktls/downloads/nist/AES_GCM.pdf`,
  `55e822592257799a4f895d6f3cb4c15515a065c008087105fc2063d2e757b5ef`.
* CAVP GCM vectors.
  `research/standards-and-designs/aes-zktls/downloads/nist/gcmtestvectors.zip`,
  `f9fc479e134cde2980b3bb7cddbcb567b2cd96fd753835243ed067699f26a023`.
* mpz2 Bristol files, in
  `research/standards-and-designs/aes-zktls/downloads/gh/mpz2/`.
  Evaluated in Python, KS reproduces the A.1 schedule and POST_KS reproduces Appendix B.
  * Key schedule: `52c267283198e4abee29f6069ca3e2b9a5d803b94b5eb7ae527851e573184514`
  * Post key schedule: `3368077b80c76c3a66d024ff558d47ce02e7b18d3c95295a95fa14e5758f1ec4`
  * Full circuit: `f6c2d8b2960f074628f3b5b46d870bdabd26d00f8635ee97a64cf489bfd2a043`
* Reclaim gnark files, in
  `research/standards-and-designs/aes-zktls/downloads/gh/reclaim/`.
  * `gnark_circuits_aesV2_common.go`: `cf90fe4567a80582278fdde5f138c2414832b448a210f5f0c8151841be022ca1`
  * `tables.go`: `57f3b73e2fe897d609845d8bfbf045ea97576e174fdb7285f9a2568cdc49ad7d`
  * The circom `aes_encrypt.circom` with the `<--` pattern: `bc2da94a21df688b26388b937ad781e1220a1191eadacd96287865fd03a646b8`
* Crema `finite_field.circom`, in
  `research/standards-and-designs/aes-zktls/downloads/gh/crema/`:
  `5fd7ca3cf120caac5a945eb0d41effac0b00f6fe8a54b9a2bf32c8b2c5a4eaab`.
* Barretenberg files, in
  `research/standards-and-designs/aes-zktls/downloads/gh/aztec/`.
  * `aes128_aes128.cpp`: `c68e4399539199c32dd98f58908d395e54d8a77e28060aa3961a801d50dce52c`
  * `plookup_tables_aes128.hpp`: `af5f94bf8c0b0b44c48ff58ba77ad8cfa69f747b2dfeccb320d9c9df6dc61d32`
* clean `Formal.lean` (`7db87890c317a4788d2629ed4232fe8dcf5b7f9d8a308c3bdd0059fb412fca08`) and
  the `v4.33.1` lakefile (`85ba60168e9445cc787f0590318b820e308d621e3ef2f10862756744b258333b`), in
  `research/standards-and-designs/aes-zktls/downloads/gh/lean/`.
* The Xie-Wang report.
  `research/standards-and-designs/aes-zktls/downloads/web/primus-zktls-report.md`,
  `e50c08f32e2926c3c7f5d05021b6e84452f71633bd39b2dc056dc3cd60b94672`.
* Scratch prototype of the gadget lemma.
  `research/standards-and-designs/aes-zktls/proto/GadgetProto.lean`
  (`79776f809d036f19b316b31892d73db95d2f38a9bfb1912e204b3783a23142b5`).
* Full manifest:
  `research/standards-and-designs/aes-zktls/manifest.sha256`.

**Reuse:** the Rijndael spec from R2 (this item depends on it); `GF256` as a `Field`; `AES.sbox`,
`AES.affine`, `AES.affineEquiv`; `GF256.xtime`; the KAT pattern from Plonky3KAT.

**Theorems to state (proposed).**

```
-- Circuits/AESGadgets.lean   (field level, needs no arithmetisation)
theorem hinted_inverse_sound (x y : GF256) : (x * y = 1 ∨ (x = 0 ∧ y = 0)) ↔ y = x⁻¹
theorem sbox_gadget_sound (h : x * y = 1 ∨ (x = 0 ∧ y = 0)) (hz : z = AES.affine y + 0x63) :
    z = AES.sbox x
theorem pluto_invTable_eq : ∀ x, plutoInvTable x = x⁻¹                         -- decide
theorem ttable_middleRound_eq (k s) : Rijndael.middleRound k s = ttableRound k s
    -- T_k x = rot_k (2·S x, S x, S x, 3·S x); the four lookups XOR the round key
theorem ttable_finalRound_eq, plookup_table_eq : ∀ x, aesPlookup x = (S x, S x + xtime (S x))
-- Circuits/Sparse9.lean
theorem sparse9_xor (xs : List (Fin 256)) (h : xs.length ≤ 8) :
    normalize9 (xs.map sparse9).sum = sparse9 (xs.foldl (· ^^^ ·) 0)
theorem sparse9_xor_fails_nine : normalize9 (9 • sparse9 0xff) ≠ sparse9 0xff   -- side condition is needed
-- Modes/GHASH.lean, Modes/GCM.lean   (SP 800-38D 2007, Algs. 1, 2, 4, 5; no Field instance)
def gf128Mul (X Y : BitVec 128) : BitVec 128, ghash, gctr, gcmAE, gcmAD
theorem gcm_example (n), gcm_cavp_subset (n) : by decide
-- Circuits/Bristol.lean
def Bristol.eval (c : Circuit) : List Bool → List Bool
theorem mpz2_ks_kat : Bristol.eval aes128KS (bits keyA1) = bits scheduleA1          -- pinned file hash
theorem mpz2_postks_kat : Bristol.eval aes128PostKS (bits (scheduleA1 ++ inputB)) = bits outputB
-- Circuits/Protocol.lean
theorem joint_implies_perBlock : (∃ K, ∀ i, C i = P i + E K (ctr i)) → ∀ i, ∃ K, C i = P i + E K (ctr i)
theorem perBlock_not_joint_toy : ∃ toy transcript, perBlock ∧ ¬ joint        -- toy cipher, decide
theorem aes_perBlock_accepts_two_keys : the per-block relation accepts a transcript whose two
    blocks were made with K₁ ≠ K₂     -- decide. That no single AES key explains it is *not* claimed:
                                      -- that is a statement over 2^128 keys and cannot be decided.
theorem gcm_not_committing : ∃ K K' N A C T, K ≠ K' ∧ gcmAD K N A C T ≠ none ∧ gcmAD K' N A C T ≠ none
    -- the witness is computed offline; the kernel only evaluates GCM twice
-- (Stage Z5, after semantics) theorem electron_ttable_underconstrained :
--   ∃ w₁ w₂, Sat cs w₁ ∧ Sat cs w₂ ∧ inputs w₁ = inputs w₂ ∧ outputs w₁ ≠ outputs w₂
```

**Staged plan.**

| Stage | Content | Effort | Risk |
|---|---|---|---|
| Z0 | Prerequisite: R2 (spec and KATs). | (in 7a) | — |
| Z1 | Gadget algebra: hinted inverse, the Pluto table, the T-table round equivalence, the plookup table, sparse base-9 with its counterexample. | S-M | Byte and bit conventions; each convention gets its own KAT. |
| Z2 | GHASH and GCM on `BitVec 128`, with the AES_GCM.pdf examples and a CAVP subset. Optional agreement on vectors with LNSym. | M | The bit-reflected convention; kernel cost of a bit-serial multiply. |
| Z3 | Bristol evaluator and the mpz2 KATs, with pinned file hashes. | M | Size of the circuit literal (about 28k gates); load the hash-pinned file through a generated Lean data file. |
| Z4 | Protocol statements: key consistency (per block versus joint) and GCM non-commitment. | M | Phrase the AES part honestly, as above. |
| Z5 | Constraint-system semantics. Option A: a separate Lake package that requires `clean@v4.33.1` and WideTrail. Option B: in-house R1CS over `ZMod p`. Then an AES-128 gadget as a `FormalCircuit` with Spec := `Rijndael.cipher`, and the underconstrained negative theorem. | L | Coupling to the dependency if `clean` moves past v4.33.1. The gap between a hand transcription and the deployed code. |
| Z6 | Verify deployed circom or gnark code through an importer (circom `.r1cs`, LLZK); full equivalence of a 30k-gate Bristol circuit without `bv_decide`. | XL | Tooling. |

**Explicit non-goals for 7c:**

* Soundness of lookup arguments or proof systems (logUp, plookup, Groth16, QuickSilver).
* Security of TLS, MPC or the notary protocols.
* A GF(2^128) `Field` instance (deferred until a GHASH-share proof needs it).
* Any statement about production deployments; which proving path Reclaim runs in production is
  UNVERIFIED.

### 8a. A design kit for new hash designs

**State of the outside world.**

* **Three families of designs** (new-designs note, checked 2026-11-26).
  1. **SPN or HADES designs with an MDS layer**, argued by counting active S-boxes.
     * Poseidon states its argument through "the wide trail strategy" (USENIX Security 2021,
       https://www.usenix.org/system/files/sec21-grassi.pdf, p.6).
     * Its full version, App. C.1.1, gives the activity formula
       (⌊s/2⌋+⌊r/2⌋)(t+1) + s mod 2 + r mod 2
       (https://eips.ethereum.org/assets/eip-5988/papers/poseidon_paper.pdf, p.21). That is
       exactly `Hades.hades_bound` with B = t + 1 (exists).
  2. **Non-SPN nonlinear layers:** Griffin, Arion, Monolith, Tip5 and others.
     * Griffin's slides: "No straightforward application for wide-trail strategy"
       (https://iacr.org/submit/files/slides/2023/crypto/crypto2023/86/slides.pdf, slide 14).
     * Arion assumes "the rounds of Arion are statistically independent" (arXiv 2303.04639v3,
       pp.9-10).
  3. **ARX and chi-based designs**, argued by computer search.
     * SPARKLE: "the only formal bounds available for ARX-based algorithms were obtained via
       computer search" (spec v1.2, p.33,
       https://csrc.nist.gov/CSRC/media/Projects/lightweight-cryptography/documents/finalist-round/updated-spec-doc/sparkle-spec-final.pdf).
     * BLAKE3: "The round reduction from 10 to 7 rounds is based on existent cryptanalysis"
       (BLAKE3-specs at `ac784c9f22a48327782f042ec2f4d8126b3b1744`, Sec. 4.4).
     * FIPS 180-4 Sec. 6.2.2 specifies addition modulo 2^32.
     * So the user's premise holds: wide-trail counting does not apply to SHA-2 or BLAKE3.
* **Demand signal.**
  * The Ashlar post of 2026-08-06 (https://ethresear.ch/t/25634):
    * under "Proven", a bound of at least 2(t+1) active S-boxes;
    * under "Assumed", round independence and single-trail bounds;
    * as its open item, "whether a hull argument changes the picture".
  * These map to `Hades.hades_mds_bound`, `hades_probability_exact` and
    `hades_differential_bound` (all exist).
  * A follow-up post on 2026-08-17 reclassifies Ashlar as pure research.
* **Round counts are set by algebraic attacks.**
  * For large-field arithmetisation-oriented (AO) designs, the statistical round count never
    decides the number of rounds. Poseidon fixes RF = 6 plus a margin, and the defaults of
    Rescue-Prime and Anemoi have no differential term.
  * A machine-checked statistical bound therefore matters most for small fields and classical
    SPNs (Saturnin).
* **No prior machine-checked work.** No Coq, Isabelle or Lean proof of an active-S-box, trail or
  hull bound was found for any surveyed design. The search was not exhaustive, and a
  self-published "aes-verification-suite" was not inspected (UNVERIFIED).
* **Access.** ePrint, ToSC and TCHES PDFs were blocked on 2026-11-26, so the paper-level claims
  for Poseidon2, Rescue(-Prime), RPO, XHash, Tip5, Monolith and others are UNVERIFIED. Their
  pinned code was read instead.

**Inputs gathered.** Full list and hashes in
`research/standards-and-designs/new-designs/SHA256SUMS.txt`;
quotes in
`research/standards-and-designs/new-designs/quotes.txt`.
The main ones:

* Poseidon full version.
  `research/standards-and-designs/new-designs/downloads/papers/poseidon_eip5988.pdf`,
  `90261afb0d57541781aa6a9be3b0b27671c5dde9c6cad248b4ab0a6bd8440566`.
* Poseidon2 reference parameter script, HorizenLabs/poseidon2 at `055bde3f`.
  `research/standards-and-designs/new-designs/downloads/pinned/HorizenLabs_poseidon2_055bde3f_poseidon2_rust_params.sage`,
  `c301c6d074b58cc27f117f59971f405a16c57d10e6140f1025643fa25ba75223`.
* Starknet Poseidon parameters (lambdaworks-crypto 0.13.0): t = 3, α = 3, RF = 8, RP = 83, mix
  diag(2,-2,-3) + J.
  `research/standards-and-designs/new-designs/downloads/crates/x_lwc/lambdaworks-crypto-0.13.0/src/hash/poseidon/starknet/parameters.rs`,
  `073a1d0b3e4a5c17800457f83dea29e0f428baa7246d2508db2be62f2e7ae44a`. This is an input for
  target 1 (see Section 4).
* RPO MDS (miden-crypto 0.36.5): a 12×12 circulant with first row
  [7,23,8,26,13,10,9,7,6,22,21,8], found MDS outside Lean after checking 2,704,155 minors.
  `research/standards-and-designs/new-designs/downloads/crates/x_miden-crypto-0.36.5/miden-crypto-0.36.5/src/hash/algebraic_sponge/rescue/mds/mod.rs`,
  `db5794ef3e88803577cdfe14867a380fd3b0be4ab463289ac29a6f5e731dff99`.
* Saturnin round-2 spec: S-boxes σ0 and σ1, M over F2[α], super-box claims.
  `research/standards-and-designs/new-designs/downloads/papers/saturnin_nist_round2.pdf`,
  `65ea333c39c7c3a91976d6ee8750cd783fc00933ce1706261b26219d28149532`.
* The Ashlar post.
  `research/standards-and-designs/new-designs/downloads/web/ashlar_ethresearch.json`,
  `39463e167d683051671eb6e128d8f410412d9c17bd983ff142a6674e1f974843`.
* The check scripts (RPO MDS, Saturnin, small matrices, ARX and Lipmaa-Moriai), in
  `research/standards-and-designs/new-designs/scripts/`.
* The four in-repository Poseidon2 certificates that D1 must re-derive (exist):

  | Instance | Trail exponent | Differential exponent | Source |
  |---|---|---|---|
  | BN254 | 8554 | 754 | `PRODUCTION_CERTIFICATE.md:137, 150` |
  | SP1 KoalaBear | 989 | 209 | `PRODUCTION_CERTIFICATE.md:277, 283` |
  | SP1 BabyBear | 906 | 198 | `PRODUCTION_CERTIFICATE.md:303, 309` |
  | Pico KoalaBear | 989 | 209 | `WideTrail/Poseidon2/PicoKoalaBear.lean:136-147`; built on `Plonky3.Diag` |

**Reuse (all exist).**

* **Hades:** `Hades.hades_bound`, `hades_mds_bound`, `outer_middle_bound`,
  `hades_probability_exact`, `hades_probability_with_middle_exact`, `mul_le_of_ratio`,
  `hades_differential_bound`, `inactiveSpace_ne_bot`, `finrank_inactiveSpace_singleton`,
  `inactiveSpace_diagPlusOnes_card_eq_bot_iff`, `finrank_inactiveSpace_diagPlusOnes`,
  `execute_bijective`.
* **Poseidon2 (target 1):** `Poseidon2.Plonky3.Diag` (`Plonky3.lean:390`), with
  `Diag.Conditions`, `Diag.permutation_bijective` and `Diag.inactiveSpace_internal`.
* **Algebra:** `isMDS_branch_bound`, `m4_isMDS_iff`, `m4Primes` (the minor-certificate pattern),
  `isBranchBound_blockMix`, `diagPlusOnesEquiv`, `Sbox.powerEquivOfFermat`.
* **Differential:** `Sbox.pow_uniform`, `decidableIsDiffUniform`.
* **Primality:** Mathlib `lucas_primality`, as used in `Poseidon2/*Primality.lean`.
* **Execution:** the runner template in `Poseidon2/Plonky3Execution.lean`.

**Theorems to state (proposed).**

```
-- DesignKit/Checks/ARX.lean   (by decide at n = 3..5)
theorem add_not_supportPreserving : ∃ x y a, bitWeight a = 1 ∧ bitWeight (((x ^^^ a) + y) ^^^ (x + y)) = 5
theorem add_msb_cancels : ∀ x y : BitVec 4, ((x ^^^ msb) + (y ^^^ msb)) ^^^ (x + y) = 0
theorem add_msb_passes  : ∀ x y : BitVec 4, ((x ^^^ msb) + y) ^^^ (x + y) = msb
theorem lipmaaMoriai_eq_count : ∀ a b g : BitVec 3, xdpCount a b g = lmFormula a b g
-- DesignKit/Hades.lean
structure HadesDesign (K Idx) where
  (mask boxes linear values r m s u B w) (hbij hunif hbranch hinactive : …)
theorem HadesDesign.certificate (D) :
    Bijective D.perm ∧ (∀ x ≠ y, D.activity ≤ chargedWeight D x y)
    ∧ D.trailBound ∧ D.differentialBound ∧ D.inactiveDims
-- obligations (in Algebra/ and Differential/, re-exported by DesignKit)
theorem IsDiffUniform.symm (e : K ≃ K) : IsDiffUniform e u → IsDiffUniform e.symm u   -- x^(1/α)
theorem hades_probability_perRound (u : ℕ → Idx → ℕ) …                               -- Tip5-like layers
theorem isMDS_of_intMinors (A : Matrix (Fin t) (Fin t) ℤ) (ps : List ℕ) (hA : minorPrimes A ⊆ ps)
    (hK : ∀ p ∈ ps, (p : K) ≠ 0) : IsMDS (A.map (↑))                     -- generalises m4Primes
theorem cauchy_isMDS (x y : Fin t → K) (hx : Injective x) (hy : Injective y)
    (hxy : ∀ i j, x i + y j ≠ 0) : IsMDS (Matrix.of fun i j => (x i + y j)⁻¹)
theorem vandermondeSystematic_isMDS …      -- Rescue-Prime; Mathlib `Matrix.det_vandermonde`
theorem IsMDS.submatrix_square …           -- RPO-M31 24×24 inside 32×32
theorem blockBranch_of_coordBranch : isBranchBound id L B → blockBranch L s ≥ ⌈B / s⌉
theorem PrattCert.check_sound : PrattCert.check c = true → Nat.Prime c.p
-- Designs/RPO.lean  (Goldilocks, t = 12, 7 rounds = 14 full S-box layers)
theorem rpo_bijective; theorem rpo_active (hB : isBranchBound id rpoMDS 13) : 91 ≤ …
    -- 7 · 13 from hades_bound; the branch hypothesis stays a hypothesis unless a structural
    -- MDS proof is found (2.7M minors are beyond the kernel)
```

**Staged plan.**

| Stage | Content | Effort | Risk |
|---|---|---|---|
| D0 | Scope statement (README SCOPE section) plus `DesignKit/Checks/ARX.lean`, citing SPARKLE p.6/p.33, BLAKE3 Sec. 4.4 and FIPS 180-4 Sec. 6.2.2. | S | None. |
| D1 | `HadesDesign` facade with one `certificate` theorem, wrapping `Poseidon2.Plonky3.Diag` for the width-16 instances. Acceptance: the four instances in the table above are re-derived through it with unchanged exponents. Start after target 1 is merged and no Poseidon2 work is open. | M | Elaboration cost of the exponent arithmetic; keep the existing style in which the type retains the arithmetic. Churn in `Diag` while target 1 is active. |
| D2 | Obligations (a)-(h): inverse uniformity (S), per-round uniformity (M), integer-minor certificates up to t ≈ 6-8 (M), Cauchy (M), Vandermonde/RS (M-L), MDS submatrices (S), coarsening to blocks (S), Pratt checker (M) with Goldilocks, M31, Stark252 and BLS12-381 instances (S each). | S-M each | Elaboration size of the Cauchy determinant. |
| D3 | `Designs/RPO.lean` (Goldilocks RPO-256): runner and outputs; MDS either structural or kept as a stated hypothesis. | M (XL if the MDS must be kernel-checked) | 1.35M determinants even using the symmetry. |
| D4 | Saturnin as the classical showcase (in `SPN/Saturnin/`), described after this table. | M-L | Getting the SR_slice/SR_sheet layout right. |
| D5 | Block S-boxes (Anemoi's Flystel, power maps over F_{p^3} for XHash12, Tip5 lookups). | L | The Flystel uniformity proof. Its paper (ePrint 2022/840) is UNVERIFIED. |
| D6 | Non-SPN layers: Arion's per-round GTDS bound (L), so that its Theorem 12 becomes a theorem in the independent-key model. Griffin, Monolith, Skyscraper, Reinforced Concrete (XL). | L-XL | — |
| D7 | Joins 8b (chi-based: Xoodoo) and an ARX composition theorem for the long-trail strategy (LTS), taking the ARX-box bound as a hypothesis (L). | L-XL | — |
| D8 | Linear outputs after target 3. Characters over F_p are needed for AO designs (L). | S-L | Depends on the T3 interface. |
| D9 | Author deliverable, `DESIGN_KIT.md`: a template file and a recipe. Fill in the record, discharge the obligations, and paste the theorem list, the exponents and the `#print axioms` output into the paper. Pilot it with one external author (Q11). | S | — |

D4, the Saturnin showcase, contains:

* `GF16`, and σ0/σ1 by decide;
* M by 69 minors;
* the super-box grid with 25 active super-boxes per 4 super-rounds;
* a two-level lemma giving ≥125 active nibbles per 8 rounds.

S16's uniformity of 80 stays a hypothesis.

**Explicit non-goals for 8a:**

* Resistance to algebraic, Gröbner or interpolation attacks.
* Sponge or indifferentiability security.
* Proving designers' heuristics, for example "differential ≤ p^-t if every characteristic
  ≤ p^-2t" (Poseidon full version, C.1.1). These are documented as outside the certificate.
* Wide-trail bounds for ARX.
* Any obligation whose check is infeasible in the kernel (the S16 DDT, minors at t ≥ 12), unless
  a structural proof replaces the computation.

### 8b. Keccak trail bounds (long-term target), with Ascon on the same pipeline

**State of the outside world.**

* **Every published Keccak lower bound comes from dedicated C++ tree searches** (KeccakTools,
  XooTools). Those tools output trail lists but no completeness certificate.
* **Small widths.** Keccak reference 3.0, Table 3.3 ("Minimum weight of w-symmetric trails", pdf
  p.41), gives lower bounds for Keccak-f[25w], w ≤ 8. They are exact minima only for some
  entries:
  * w = 1, 2: rounds 2-6;
  * w = 4, 8: rounds 2-4.

  The other entries are not bounds:
  * at w = 4, rounds 5-6 are "≤ 54 / ≤ 85" (DC) and "≤ 66 / ≤ 94" (LC), best-known trails that
    "do not provide bounds" (pdf p.40);
  * at w = 8, rounds 5-6 are blank.

  At b = 25 the differential minima for 2/3/4 rounds are 8/16/23
  (https://keccak.team/files/Keccak-reference-3.0.pdf).
* **Keccak-f[1600], differential.**
  * The 3-round minimum is 32 and tight (FSE 2012, https://keccak.team/files/KeccakDC.pdf).
  * Six rounds: ≥74 (FSE 2012), then ≥92 for b > 100 (ToSC 2017(1), p.348,
    https://keccak.team/files/NewTechniquesAndResultsForBoundingDifferentialTrailsInKeccak.pdf).
  * Twelve rounds: ≥184 (ToSC 2017, p.351).
  * Liu, Qiu and Tu (ToSC 2019(4)) claim 108 for six rounds; their abstract says exhaustiveness is
    "only experimentally verified" (https://tosc.iacr.org/index.php/ToSC/article/view/8470).
* **Published search costs** (ToSC 2017, sha256 `217ecbee…`):
  * App. A, Tables 5-6 (printed p.354): 3-round trail cores up to weight 45 took
    33h16m04s + 225h35m56s at b = 1600 (about 260 CPU-hours, backing the 6-round bound 92), and
    55h34m45s + 46h36m17s at b = 200 (about 102 CPU-hours).
  * App. D.2, Tables 10-11 (printed p.357): 3-round cores up to weight 36, enough for the 3-round
    bound 32, took 12m14s + 55m19s with the 2017 method, against "more than 20 days" with the
    FSE 2012 method.
* **Keccak-f[b], linear.** No published exhaustive bound beyond 2 rounds was found for b ≥ 400
  (UNVERIFIED as complete).
* **Xoodoo.** ToSC 2023(4): 4 rounds 80 (tight), 6 rounds ≥132, 12 rounds ≥264
  (https://tosc.iacr.org/index.php/ToSC/article/view/11285).
* **The case for machine checking.** On 2021-12-20 the Keccak team reported that an independent
  SAT search found two 3-round Xoodoo trails of weight 48 that XooTools had missed, "caused by a
  bug in our program XooTools" (https://keccak.team/2021/updated_bounds_xoodoo.html).
* **Slips in the reference document.** Keccak reference pdf pp.40-41 has three slips:
  * "268 for 8-symmetric trails in Keccak-f[1600]" should be 368 = 46 × 8;
  * "8 × 98 + 8 = 204" should be 2 × 98 + 8;
  * the linear bullet says "a 8-round differential trail has at least weight 48 + 50 = 98",
    where it means linear.

  The 99 and 98 derivations are also under-specified. A formalisation must recompute such
  numbers, not transcribe them.
* **The Matryoshka statement in the reference** (§2.4.2, pdf p.24) is in the existence
  direction: "a trail for a given width b implies a trail for all larger widths b′ … the weight
  must be multiplied by b′/b". It also says: "The existence of trails (both differential and
  linear) and their weight is independent of ι."
* **Where SHA-3 and SHAKE are used.** FIPS 203 Sec. 4.1 (ML-KEM: H, J, G, PRF and XOF from
  SHA3/SHAKE); FIPS 204 Sec. 3.7 (ML-DSA: H = SHAKE256, G = SHAKE128); FIPS 205 Sec. 11.1; RFC 9861
  (October 2025, TurboSHAKE and KangarooTwelve on Keccak-p[1600, 12]).
* **FIPS 202 status (re-fetched 2026-11-27).**
  * NIST decided on 2025-03-12 to update FIPS 202
    (https://csrc.nist.gov/News/2025/decision-to-update-fips-202-and-revise-sp-800-185). The
    update is mainly editorial: "NIST has decided to update FIPS 202 to improve its editorial
    quality", with the SHA-1 and Triple DES text updated. It is not only editorial: "NIST will
    also consider other technical changes proposed in the public comments".
  * The FIPS 202 history shows only the 08/04/15 final.
  * The SP 800-185r1 initial public draft is open for comments until 2026-12-07
    (https://csrc.nist.gov/pubs/sp/800/185/final; CSRC news of October 8, 2026).
* **Prior formal work** checks implementations and specifications only: s2n-bignum in HOL Light,
  HACL*, cryptol-specs, Jasmin/EasyCrypt (ePrint 2019/1155) and a Lean 4 SHA-3 (ePrint 2024/1880).
  None of it proves a trail bound.
* **Ascon (NIST SP 800-232, published 2025-08-13).** It is the most standards-relevant addition
  on the lightweight side, and it fits this pipeline.
  * The permutation is p = pL ∘ pS ∘ pC on five 64-bit words (SP 800-232 §3, pdf p.19):
    * the S-box acts on the 64 columns;
    * Σi acts within each word (eqs. 8-12, pdf p.21).
  * The S-box is χ with affine input and output maps (Ascon v1.2, p.25).
  * The S-box has differential and linear branch number 3, and each Σi has branch number 4
    (v1.2, p.29).
  * Minimum active S-boxes (v1.2, Table 12, pdf p.31):
    * DC: 1, 4, 15 for R = 1, 2, 3, then "≤ 44", "≤ 78";
    * LC: 1, 4, 13, then "≤ 43", "≤ 67".

    "Results for R ≥ 4 are from heuristic search." The spec does not say how the 3-round minima
    were established (UNVERIFIED method).
  * The 3-round minima would need a Search/Tree certificate of unknown size (UNVERIFIED).

**Inputs gathered.**

* FIPS 202.
  `research/standards-and-designs/keccak/downloads/nist/NIST.FIPS.202.pdf`,
  `1592607831ff0908cc590632ce371c6c95e94025bb1a0c8ae90a4d0ec1ed025e`. Note: pdftotext drops the
  minus sign in Alg. 1 and the superscript in Alg. 6, so read those from the PDF.
* FIPS 203.
  `research/standards-and-designs/keccak/downloads/nist/NIST.FIPS.203.pdf`,
  `fe1f12f32a7e44ec9fdebbf400cda843a40b506dee676725234dc6f7923b6cac`.
* SHA3-256 example with message length 0.
  `research/standards-and-designs/keccak/downloads/nist/SHA3-256_Msg0.pdf`,
  `72c5a5d37ed639058421b0a292775605a6be1631cfc4c156a2fb4739e68f8e9c`.
* XKCP intermediate values at `d789b57c26dd7d5f628f7527c2bd006bc33b6a93`, in
  `research/standards-and-designs/keccak/downloads/XKCP_d789b57/`.
  * KeccakF-1600: `db0947545a5d91c20b2105aac75fac430deafe0ccaecb660af60044244df30d4`
  * KeccakF-200: `5420859c01dfd1e0556389537b214a68ac14c68c06012827f796e4158d49acf5`
  * KeccakF-400: `3c36fb72247e0e3b3a2987c5d0622c1e91d72c4ea691a6c96de4a975f4fe983e`
  * KeccakF-800: `d41fe84eec7cdea65346888199b8b8c64385426239d1a3d60d06670d30076d8e`
  * ShortMsgKAT_SHA3-256: `bc2506ecea3d2ffc2ddfb53982327688ea429a668a98fec571ede949c913f0d0`
* Keccak reference 3.0.
  `research/standards-and-designs/keccak/downloads/files_Keccak-reference-3.0.pdf`,
  `834e74ed4b917b43a5f9cee932166161e09246a0cb90544539a0c81a04d748a5`.
* FSE 2012, `13761bb47225ac906d25345181568e4779c1b21b042645c81f8b47892b934b35`; ToSC 2017,
  `217ecbeeb4893b0c72c6aee7e86da662c29eefcb78a2cdccb947e9b6922c3e46`; Xoodoo ToSC 2023,
  `45e5750ad345dfb41a01948384ff6e08926be68ab2441003333bdd44d28ff954`. All in
  `research/standards-and-designs/keccak/downloads/`.
* KeccakTools trail cores at `3473478bf9c10bf95879cd8960c7409fee313162` (CC0), in
  `research/standards-and-designs/keccak/downloads/KeccakTools_3473478/`.
  * DCKeccakF-25: `02a6d3290bd5a18efa4558933ba5b9c7f4d223f8fef255a1500f7e8c0be59753`
  * LCKeccakF-25: `31e39b174a04119ecd7bae1dc376734b73ffcbca2f14c3921e0b7d000ee78380`
  * The 63 FSE 2012 cores: `c3c1b1ec25d24d955f6689f14a8b62f218eb7c1f4ef94dcfd9324be206b85fa7`
* XooTools trails at `b940a949ca822adb720cc09e4d47508e08205379`, in
  `research/standards-and-designs/keccak/downloads/XooTools_b940a94/`.
  * DC-3r: `65a2fc8f1dde6e0eb3a0529acd1c74b9216f563c8e2f8d9868c261ab1c47ad37`
  * LC-3r: `ccc999e22c5b21d827b65a0c0739498cc5bc72aa40745e94cea59d1c047bc93b`
  * The license is UNVERIFIED (Q12).
* Kernel probes, in
  `research/standards-and-designs/keccak/leantest/`.
  The Keccak-p[1600, 24] zero-input KAT checks in about 2 s and SHA3-256("") in about 1.5 s with
  `decide +kernel`; axioms: `propext`. A naive full-state weight evaluation costs about 0.2 s.
* The chi row-weight table (by row value) is
  [0,2,2,3,2,3,3,4,2,3,3,3,3,3,4,4,2,3,3,4,3,3,3,4,3,4,3,4,4,4,4,4]. Manifest:
  `research/standards-and-designs/keccak/SHA256SUMS.txt`.
* **Ascon inputs.**
  * NIST SP 800-232 (August 2025). Table 5 (round constants const0..const15) and eq. (7) (S-box
    algebraic normal form) are on pdf p.20; Table 6 (S-box lookup table) and eqs. (8)-(12) (Σi
    rotation amounts 19/28, 61/39, 1/6, 10/17, 7/41) are on pdf p.21; Table 10 gives the
    little-endian byte order.
    `research/standards-and-designs/revision/downloads/nist/NIST.SP.800-232.pdf`,
    `1be9bb9a5fef3665ee8b258babe54b8e500d667fcfbbcc99710fe6077c6bad27`
    (https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-232.pdf, fetched
    2026-11-27).
  * S-box = [04,0b,1f,14,1a,15,09,02,1b,05,08,12,1d,03,06,1c,1e,13,07,0e,00,0d,11,18,10,0c,01,
    19,16,0a,0f,17]; the input x = 1 is (x0..x4) = (0,0,0,0,1).
  * Recomputed by
    `research/standards-and-designs/revision/scripts/ascon_check.py`
    (`c564868b51318b9266e35203c7ebb19cb5467e0d52b0b691b7b5d6d7223d848b`):
    * Table 6 equals eq. (7), and the S-box is bijective;
    * DDT maximum 8 and differential branch number 3;
    * maximum |Walsh| 16 and linear branch number 3;
    * for each Σi and its transpose, min wt(x) + wt(Σx) over inputs of weight ≤ 3 is 4;
    * for comparison, the Keccak χ row also has maximum |Walsh| 16 and DDT maximum 8.
  * Ascon v1.2 submission (2021-05-31), Table 12 and the design rationale.
    `research/standards-and-designs/adversarial-review/downloads/pdf/ascon-spec-final.pdf`,
    `ebd9588c7a293e808bcb153b873f6c5a6bc49e9472bacc2908412249e82248d4`.
  * KATs: SP 800-232 §6 (pdf p.42) says "Example test vectors are available from the
    Cryptographic Algorithm Validation Program (CAVP)". Its reference [25] points to the
    ACVP-Server JSON files on github.com, which were not opened (UNVERIFIED; github.com returned
    403 on 2026-11-27).

**Reuse (all exist).**

* **Differential:** `diffCount`, `IsDiffUniform` (chi row: u = 8, |K| = 32, by decide),
  `diffCount_addKey`, `diffCount_addEquiv`, `bricklayer`, `diffCount_bricklayer`,
  `activePattern_eq_of_diffCount_ne_zero`, `Scheduled.trailKeyCount_eq_prod`,
  `Scheduled.bricklayer_two_round_bound`.
* **Propagation:** `isBranchBound`, and the root `two_round` as the deterministic analogue.
  There is no `Activity.two_round`; the two-round step for trails is argued from
  `activePattern_eq_of_diffCount_ne_zero` plus `isBranchBound`, because Keccak and Ascon have no
  `WideTrailSpec`.
* **Execution:** the Plonky3Execution runner pattern.
* **Not reusable:** the B² four-round machinery (`FourRound`, `Dispersion`, `Grid`). Keccak has no
  column or super-box structure. ToSC 2017 p.330 says such "compact proofs are out of reach for
  primitives with weak alignment such as Keccak-f".

**Theorems to state (proposed).**

```
-- Keccak/Constants.lean, Keccak/Spec.lean, Keccak/Execution.lean, Keccak/Sponge.lean
def rhoOffsets, roundConstants (from the Alg. 2 walk and the rc LFSR)
theorem rhoOffsets_table2, roundConstants_xkcp                        -- decide
def theta, rho, pi, chi, iota, rnd, keccakP (b nr)                    -- FIPS 202 Algs. 1-7
theorem keccakP_eq_exec (w) : keccakP … = Exec.keccakP …              -- for every w
theorem kat_keccakF1600_zero, kat_keccakF200/400/800, sha3_256_empty, shake128_empty
theorem kat_fails_rho0, kat_fails_noIota                              -- negative controls
-- Keccak/Chi.lean   (rows as XorBits 5)
theorem chiRow_bijective, chiRow_uniform : IsDiffUniform chiRow 8
theorem chiRow_affine (a) : the outputs compatible with a form an affine space of size 2^(wRow a),
    each reached 2^(5 - wRow a) times;  theorem wRow_table : wRow = ![0,2,2,3,…]
-- Keccak/Theta.lean
theorem theta_eq_id_of_kernel, theta_injective, thetaEffect_eq_zero_iff (h : Nat.gcd 5 w = 1)
theorem lambda_rowBranch (w) : isBranchBound id (lambdaOnRows w) 4
theorem lambda_rowBranch_tight (w) : ∃ b ≠ 0, activeRows b + activeRows (lambdaOnRows w b) = 4
-- Keccak/TwoRound.lean
theorem keccak_two_round_weight (w) (h0 : T 0 ≠ 0) (h : trailKeyCount … 2 T x ≠ 0) :
    trailKeyCount … 2 T x * 2 ^ 8 ≤ |X| ^ 2              -- ≥4 active rows at 2 bits each
theorem keccak_rounds_weight (nr) : … * 2 ^ (8 * (nr / 2) + 2 * (nr % 2)) ≤ |X| ^ nr
    -- 96 for 24 rounds, 48 for 12: the FSE 2012 trivial baseline, now proved
theorem keccak_two_round_differential (ha : a ≠ 0) : diffKeyCount … 2 a b x * 4 ^ 3 ≤ |X| ^ 2
    -- (8/32)^3 = 2^-6, a differential (hull) bound, a weaker number than the trail bound
-- Search/Tree.lean, Search/Chaining.lean (K5); Keccak/Small/F25.lean … F200 (K6)
theorem keccakF25_three_round : ∀ trail, 16 ≤ weight …
    -- the lower bound comes from the Search/Tree traversal; the DCKeccakF-25 cores are only
    -- witnesses that 16 is attained (the upper bound)
theorem matryoshka (w w') (hw : w ∣ w') :
    -- z-reduction is a bijection from the trails of Keccak-f[25w′] whose patterns all have
    -- z-period dividing w onto the trails of Keccak-f[25w], with
    -- weight (lift Q) = (w′ / w) * weight Q; ι is irrelevant for differences (reference §2.4.2).
    -- Lower bounds on symmetric 1600-bit trails use the "onto" direction.

-- SPN/Ascon/{Sbox,Linear,Spec,TwoRound}.lean   (A0-A3)
def Ascon.sbox : XorBits 5 → XorBits 5                -- SP 800-232 Table 6
theorem Ascon.sbox_table6_eq_anf : ∀ x, sbox x = anf x  -- eq. (7)
theorem Ascon.sbox_uniform : IsDiffUniform Ascon.sbox 8 ; theorem Ascon.sbox_diffBranch : 3
theorem Ascon.sigma_bitBranch (i : Fin 5) : ∀ x ≠ 0, 4 ≤ wt x + wt (Σ i x)
    -- structural: Σi is invertible; weight 1 → 3 output bits; weight 2 → ≥ 2 (parity)
theorem Ascon.pL_colBranch : isBranchBound id pL 4      -- bundles = the 64 columns
theorem ascon_two_round_active (h : trailKeyCount pL (bricklayer sbox) 2 T x ≠ 0) (h0 : T 0 ≠ 0) :
    4 ≤ weight (T 0) + weight (T 1)
theorem ascon_two_round_prob : trailKeyCount … 2 T x * 2 ^ 8 ≤ |X| ^ 2     -- 4 × 2^-2
theorem ascon_two_round_differential : diffKeyCount … 2 a b x * 4 ^ 3 ≤ |X| ^ 2   -- (8/32)^3
theorem ascon_three_round_active : 15 ≤ …                 -- A2, Search/Tree certificate
```

**Staged plan.**

| Stage | Content | Effort | Risk |
|---|---|---|---|
| K0 | Constants: rho offsets and round constants, computed and then checked against FIPS 202 Table 2 and XKCP. | S | None. |
| K1 | Spec on `Fin 5 × Fin 5 × Fin w`, a Nat-lane runner proved equal to it for every w, and KATs (XKCP at 200/400/800/1600; NIST SHA3-256 and SHAKE128 Msg0 through the optional sponge). | M | Bit and byte ordering (Sec. 3.1.2-3.1.3, App. B.1); the generic-w runner proof. |
| K2 | Chi row facts. Correlation weights wait for target 3. | S-M | Low. |
| K3 | Theta and the CP-kernel; facts about π∘ρ; `lambda_rowBranch`. The general-w proof has three cases (in the kernel; theta-gap > 0; all-odd parity). It is only a sketch in the research notes, and was checked exhaustively only for w = 1 (UNVERIFIED for w > 1). | M | The case "all-odd parity" may need the runs/theta-gap lemma. |
| K4 | The two-round corollaries via `activePattern_eq_of_diffCount_ne_zero` with `lambda_rowBranch`, and via `bricklayer_two_round_bound`. | S-M | Low. |
| K5 | `Search/Tree` (the ToSC 2017 ordered unit-list traversal with canonicity, Lemma 1) and `Search/Chaining` (the T2, 2·T3 + 2, T3 + 3 and T3 + 5 rules; Matryoshka as a weight-scaling bijection). Pure combinatorics. | M-L | Getting the abstraction right for GIFT, Xoodoo and Ascon reuse. |
| K6 | Certificates for the exact entries of Table 3.3 only, with KeccakTools lists as data (lower bounds by traversal, upper bounds by witness). The exact entries are w = 1, 2 at rounds 2-6 and w = 4, 8 at rounds 2-4. Then bounds on symmetric Keccak-f[1600] trails via the onto direction of Matryoshka. | L for b = 25 and for the 3-round entries (spike-gated); XL for the 4-round entries at b = 100 and 200 | b = 25 at 3 rounds needs about 2.5e3 cores and 4.8e5 extensions, so an optimised 25-bit encoding is needed. The only published b = 200 cost is about 102 CPU-hours of C++ for 3-round cores to weight 45 (ToSC 2017 Tables 5-6). A 4-round certificate at b = 200 needs a scan of comparable depth (inference). |
| K7 | Keccak-f[1600]: 3 rounds ≥ 32 (in-kernel trails first, the 63 FSE 2012 cores), then 6 rounds ≥ 74 and ≥ 92, then settle 108. | 3 rounds: L-XL, spike-gated; 6 rounds: XL | 3 rounds ≥ 32 took about 1 CPU-hour of C++ with the 2017 method (Tables 10-11). 6 rounds ≥ 92 took about 260 CPU-hours (Tables 5-6). Needs either a compact covering certificate or a separately labelled compiled tier (Q5). |
| X1 | Xoodoo with the same pipeline (weight is 2 per active column; affine sets): 3 rounds 36, 4 rounds 80, then ≥ 132. | L-XL | The license of the XooTools data. |
| A0 | Ascon S-box facts by `decide` (SP 800-232 Table 6 against eq. (7), bijectivity, uniformity 8, differential branch number 3), on `XorBits 5`; Σi constants; round constants against Table 5. | S | The column bit order (x0 is the most significant bit of the index). |
| A1 | Σi branch number 4 by a structural argument, lifted to column branch number 4 of pL; the two-round active-S-box, trail (2^-8) and differential (2^-6) theorems; checks that 5 active S-boxes and exponent 9 fail. | S-M | Low. |
| A2 | Three rounds: ≥ 15 (DC) by a `Search/Tree` certificate; ≥ 13 (LC) after target 3. | L, spike-gated | Search size UNVERIFIED; the method behind the designers' 15/13 is not stated. |
| A3 | Ascon-p spec, runner and KATs (CAVP/ACVP vectors once fetched and pinned), little-endian byte order per SP 800-232 Table 10. | M | The KAT source is UNVERIFIED until fetched. |

**Explicit non-goals for 8b:**

* Collision or preimage resistance of SHA-3; sponge indifferentiability.
* Implementation correctness, which is already done elsewhere (s2n-bignum, HACL*).
* Certificates for 3 or 6 rounds of Keccak-f[1600] within the first year.
* Linear trails before target 3.
* Any statement about the security of ML-KEM, ML-DSA or SLH-DSA.
* Ascon for 4 or more rounds, and any security claim for Ascon-AEAD128, Ascon-Hash256 or the
  XOFs.

---

## 3. Proposed library sector layout

```
WideTrail/
  Propagation/  Algebra/  Differential/  Hades/  Poseidon2/      (existing; unchanged except additions below)
  Algebra/      + XorBits.lean (Nibble = XorBits 4; 5-bit rows/columns), GF16.lean (X^4+X+1),
                  MinorCertificate.lean, Cauchy.lean, Vandermonde.lean, Pratt.lean   [7b, 8a, 8b]
  Differential/ + Inverse.lean (IsDiffUniform.symm), per-round uniformity variant [8a]
  Linear/       Correlation, Walsh, Masks, Trail, Hull, Checks/                  [target 3; prerequisite]
  Rijndael/     MixColumns, Probability, Tables, Spec, Execution, KeySchedule,
                Bridge, Claims; Checks/{Axioms, FIPS197, TS35236, Negative}      [7a; spec for 7c]
  Modes/        GHASH, GCM, CTR; Checks/{SP80038D, CAVP}                         [7c; wGCM later]
  Search/       Automaton, Checker, Superadditive, Tree, Chaining; Checks/       [7b, 8b; R6]
  SPN/          Skinny/, Midori/, Craft/, Gift/, Saturnin/, Photon/, Ascon/; Checks/   [7b; Saturnin for 8a; Ascon for 8b]
  Circuits/     AESGadgets, Sparse9, Bristol, Protocol, (R1CS if option B); Checks/  [7c]
  DesignKit/    Hades (facade), SPN (facade), Template; Checks/{ARX, Facade}     [8a]
  Designs/      RPO, then Anemoi, XHash12                                        [8a]
  Keccak/       Constants, Spec, Execution, Sponge, Chi, Theta, TwoRound, Small/; Checks/  [8b]
  Xoodoo/       (later)                                                          [8b]
WideTrail/{Linear,Rijndael,Modes,Search,SPN,Circuits,DesignKit,Designs,Keccak}.lean   aggregators
circuits/                 optional separate Lake package: requires WideTrail + clean@v4.33.1   [7c Z5]
submission/rijndael256/   LETTER.md, PROVENANCE.md, REPRODUCE.md (not Lean)             [7a R8]
RIJNDAEL256_CERTIFICATE.md, DESIGN_KIT.md, MECHANICS_SEARCH.md, MECHANICS_KECCAK.md,
README sections per layer and a SCOPE section
```

`Checks/TS35236` is created only after Q4 is answered.

**Design choices.**

* **No `Standards/` Lean namespace.** A standard is not a kind of mathematics, and the README's rule
  is that "the directories identify the kind of mathematics they contain". The NIST artifact is a
  `Claims.lean` index, a certificate document and a non-Lean `submission/` folder pinned to a
  release tag.
* **`Rijndael/` and not `AES/`.**
  * One specification covers AES (Nb = 4) and Rijndael-256 (Nb = 8).
  * NIST calls the new object Rijndael-256 and presents it as an extension of the AES family
    (slides, p.14).
  * FIPS-named abbreviations such as `AES.encrypt128` sit in the existing `AES` namespace.
  * `Propagation/Rijndael.lean` stays the abstract layer.
* **Ascon sits in `SPN/`.** It is an SPN with column S-boxes and a word-wise linear layer, so its
  two-round bound is a classical activity argument. Its three-round certificate uses
  `Search/Tree`, like Keccak.
* **`Search/` is one certified-search layer with two engines.** A pattern automaton (SKINNY,
  Midori, CRAFT, optionally truncated Rijndael) and an ordered tree (Keccak, Xoodoo, GIFT,
  Ascon). Both share `Checker` soundness and `Superadditive`.
* **The mathematics behind design-kit obligations lives where it belongs** (MDS certificates in
  `Algebra/`, uniformity in `Differential/`). `DesignKit/` only packages them into a facade and a
  template.
* **The `circuits/` package is separate** so that the default library does not depend on `clean`.
  Lake resolves every `require` of a package for every user, so this needs the owner's decision
  (Q7).

**Dependencies on existing layers.**

| New sector | Imports |
|---|---|
| Rijndael | Algebra (GF256, AESSbox, AESMix, MDS), Propagation (Grid, Rijndael, Cipher), Differential (Bricklayer, TrailProb, Scheduled, Hull, AESConcrete), Linear (R5) |
| Modes | Rijndael (KATs only); its own bit-serial GF(2^128) multiply |
| Search | Propagation (Activity), Differential (Markov, Scheduled) |
| SPN | Search, Algebra (XorBits, GF16, MDS), Propagation, Differential, Linear |
| Circuits | Rijndael, Modes; optionally the external clean package |
| DesignKit, Designs | Hades, Poseidon2 (after target 1 is merged, for the re-derivation tests), Algebra, Differential, Linear |
| Keccak, Xoodoo | Algebra (XorBits), Differential (Counts, Bricklayer, Scheduled, Hull), Propagation (Activity), Search (Tree), Linear |

**House rules, applied to every new sector.**

* No `sorry`, `native_decide` or `bv_decide`. `decide +kernel` is allowed; it is already used
  (`Differential/Checks/Hull.lean:135`).
* Only `propext`, `Classical.choice` and `Quot.sound` appear in axiom footprints. The
  full-declaration audits enforce this without change: `scripts/AuditAxioms.lean` for the default
  library, and `scripts/AuditAxiomsHeavy.lean` (`ci.yml:77`) for anything heavy.
* Each sector has `Checks/Axioms.lean` with `#guard_msgs` pins for its headline theorems.
* Each sector has adversarial checks: every hypothesis of a headline theorem gets a check showing
  it cannot be dropped. Every KAT file gets negative controls (`kat_fails_*`).
* Each certificate is tested against a deliberately wrong bound, which must fail to check.
* Every module is reachable from `WideTrail.lean` or `WideTrailHeavy.lean`
  (`scripts/check_imports.py`). A heavy module is also listed by name in
  `.github/workflows/ci.yml`, with its measured memory noted as in the README.
* Docstrings state:
  * the model ("averaged over an additional independent uniform key per round");
  * whether a bound covers every trail (`IsTrail`) or only functional trails;
  * what is not claimed;
  * the pinned source with its hash.

  A "What is not claimed" section follows the pattern of `Poseidon2/Checks/Plonky3.lean`.
* Data transcribed from outside sources records the URL, revision and SHA-256 in the module
  docstring. Data under a restrictive notice (3GPP/ETSI) is committed only after Q4.

---

## 4. Dependencies between items and the three current engineering targets

```
T1 (Plonky3 Diag; committed on the feature branch, still active) ─► D1 facade (wraps
                                    Poseidon2.Plonky3.Diag; re-derives the four instances)
T2 (more partial-round S-boxes) ─► D1 middle term (the facade takes the middle-round lemma as a
                                    parameter, so T2's improvement flows into every design)
T3 (linear framework) ─► R5 (Rijndael/AES linear; R5a may start earlier) ─► R8 (linear claims, optional)
                      ─► SPN linear (SKINNY/GIFT/Midori/CRAFT correlation; Saturnin; Ascon LC)
                      ─► Keccak linear (θᵀ, chi masks w_c, w_c_rev); Xoodoo linear
                      ─► D8 (Ashlar's linear half; Poseidon's "square correlation ≤ 2/p", needs F_p characters)
R0-R1 ─► R8;  R2 ─► R3, R4, R8, Z1-Z4 (7c), Modes KATs
Q4 ─► the TS 35.236 data commit inside R2
Kernel spike ─► L3 (SKINNY), K6 (Keccak small widths), A2 (Ascon 3 rounds), Z3 (Bristol);
                confirms the R2 placement already measured with a scratch runner
Search/Automaton ─► L3 (SKINNY, Midori, CRAFT), optional R6
Search/Tree ─► K6, K7, X1, A2, L5/L6 (GIFT)
SPN/Saturnin ─► D4 (SPN facade example)
```

**Target 1** (parametrised Plonky3 diagonal).

* State on 2026-11-27: committed on `proxy/gifted-ramanujan-397jqj`, not merged, and still
  changing. The commits are `4a37d31`, `f483e67` and `d6a3907`, plus uncommitted Pico edits at
  03:46Z.
* Start D1 only after T1 is merged and no Poseidon2 work is open, to avoid conflicts in
  `WideTrail/Poseidon2/`.
* **Pico KoalaBear is now an in-repository instance** (`d6a3907`): it is built on
  `Plonky3.Diag`, has exponents 989/209, and pins the Brevis Plonky3 fork at
  `da6ca12c71912ec213d3c5af68b14509d2099bc3` (`PicoKoalaBear.lean:11-24`).
* **Starknet is not a Plonky3 width-16 instance.**
  * It is a width-3 Poseidon (version 1) HADES permutation. The same matrix
    [[3,1,1],[1,-1,1],[1,1,-2]] = diag(2,-2,-3) + J serves full and partial rounds, and the
    partial S-box is on coordinate 2 (lambdaworks-crypto 0.13.0 `parameters.rs`,
    `mod.rs:27-56`).
  * It is covered by `Hades` together with `Algebra.DiagPlusOnes` and
    `inactiveSpace_diagPlusOnes_card_eq_bot_iff` (with a coordinate permutation), following the
    BN254 pattern, and not by the Plonky3 model.
* Its round constants come in an "optimized" 91-row layout. Proving that layout equivalent to the
  plain one is an obligation within T1's scope.
* No inputs were gathered in this research for OpenVM BabyBear or Aztec's BN254 parameters. The
  Barretenberg tree pinned for 7c (`aztec-packages@6542e71`) may also hold Aztec's Poseidon2
  parameters (UNVERIFIED). One pin for both would simplify provenance.

**Target 2** (partial-round S-boxes; projections of 35 for KoalaBear and 40 for BN254).

* It feeds only 8a. The `HadesDesign` record should take the middle-round count as a lemma
  argument rather than hard-coding `m / w`, so that D1 needs no rework when T2 lands. Ashlar-type
  authors are exactly the users who want this term.

**Target 3** (linear-cryptanalysis framework). Items 7 and 8 need the following from it.

1. **Correlation as an exact integer Walsh sum,** `walsh F a b = Σ_x (-1)^(a·x + b·F x)`, for
   maps on F2-vector spaces.
   * This covers `GF256`, `XorBits n` (nibbles, 5-bit Keccak rows and Ascon columns) and bit
     vectors, with decidable LAT bounds.
   * 8-bit S-boxes need a fast route: the trace form and Kloosterman structure for inversion
     (R5a), or digit-packed tables as in lean-aes at `b70ac45a1063c13621e2ee2b4edf211eb0ed70eb`,
     whose README reports about 48 s (not measured here). A naive 256²-shaped enumeration does
     not finish (Section 0, item 8).
   * R5a may define `walsh` locally first. T3 should adopt or replace that definition.
2. **Mask propagation through an `AddEquiv`,** which turns the convention in
   `Algebra/Transpose.lean` from a definition into a theorem.
   * The direction must be fixed: backward through Aᵀ, as `Transpose.lean:13-14` does today, or
     forward through A⁻ᵀ.
   * The backward choice applies θᵀ before πᵀ in each round. That forces a rebracketing of the
     transposed round in every `WideTrailSpec`-shaped linear bound (R5).
3. **Linear trails with key-dependent signs:** the trail correlation is ± the product of local
   correlations. The analogue of `trailKeyCount_le_of_spec`, stated combinatorially as
   `|C_trail| * 2^(c·W) ≤ 1`, with `c = 3` for AES and `c = 1` for the Ascon and Keccak 5-bit
   rows.
4. **The linear hull:** a key-averaged squared correlation as the sum of the trails' squared
   correlations, and a two-round bound mirroring `Scheduled.bricklayer_two_round_bound`.
5. **Room for characters over F_p,** to be added later for AO designs (D8). An F2-only first
   version is enough for 7a, 7b and 8b.

---

## 5. Ranked first concrete tasks

Each task takes a few days at most, except R2 (L). The common rules:

* All must pass `lake build`, `lake env lean scripts/AuditAxioms.lean` and
  `python3 scripts/check_imports.py`.
* Any task that adds a heavy module must also pass `lake env lean scripts/AuditAxiomsHeavy.lean`.
* None may touch `WideTrail/Poseidon2/` until target 1 is merged and no Poseidon2 work is open.

1. **R0: Rijndael MixColumns for any number of columns; unconditional Rijndael-256 bounds for
   every trail (S).** Acceptance:
   * `Rijndael.mixColumns_isColBranchBound cols`, and `mixColumns 4 = aesMixColumns`.
   * `rijndael256_four_round_concrete`, `rijndael256_rounds_concrete`,
     `rijndael256_fourteen_round_concrete` (80) and `rijndael192_twelve_round_concrete` (75).
     Each is stated over `IsTrail` (via `IsTrail.four_round` and `IsTrail.bound_rounds`), with
     no branch-number or non-degeneracy hypothesis.
   * Functional-trail corollaries in the shape of the existing `rijndael256_fourteen_round`.
   * `Rijndael.lin_isBranchBound` (whole-state branch number 5), with no injectivity hypothesis.
   * Pinned axioms; one adversarial check (a mix with branch number below 5 on `GridIdx 4 8`).
   * README and the `Propagation/Rijndael.lean` docstrings point to the new results.
2. **R1: Rijndael-256 probabilities, two-round differentials, final-round variants (S-M).**
   Acceptance:
   * `card_state256`.
   * `rijndael256_{four,eight,fourteen}_round_prob` with exponents 150, 300 and 480.
   * `rijndael256_two_round_differential` and `aes128_two_round_differential`, both 2^-24. Their
     docstrings say that the bound is coarse and cite the exact AES two-round MEDP 53/2^34
     (Keliher-Sui).
   * `rijndael256_fourteen_round_prob_final` in `Scheduled`, with the last linear map equal to
     ShiftRows alone, and the same final-round form of `aes128_ten_round_prob`,
     `aes192_twelve_round_prob` and `aes256_fourteen_round_prob`.
   * A check that the per-S-box exponent 7 fails the arithmetic (4·2^7 > 256).
   * Each docstring names the independent-key model.
3. **Kernel throughput spike (S-M), run on a branch or under `scripts/bench/`.**
   * Acceptance: a short note on a 4-core / 15 GB profile. For every probe it records time and
     peak memory at three or more sizes (a scaling curve), the recursion shape (linear or
     balanced), the chunk size per theorem, and the certificate-data encoding (a literal or
     recomputed in the kernel). The probes are:
     * (a) Rijndael-256 14-round encryptions by `decide +kernel` with the committed runner: one
       vector, then all 8 in one file;
     * (b) automaton edge checks with trie lookups at 10^3, 10^4 and 10^5 per theorem, linear
       against balanced recursion;
     * (c) 10^4 chi-weight evaluations on 25-bit Keccak states;
     * (d) one GHASH block multiply.
   * The 2026-11-27 baseline the spike starts from (scratch probes, not yet with committed code):

     | Probe | Size | Time | Peak RSS |
     |---|---|---|---|
     | Linear-recursion loop | 5,000 steps | 1.3 s | — |
     | Linear-recursion loop | 20,000 steps | 9.0 s | — |
     | Linear-recursion loop | 40,000 steps | over 11 min, killed (review) | — |
     | Balanced recursion | 2^14 steps | 1.7 s | — |
     | Balanced recursion | 2^16 steps | 5.1 s | 1.0 GB |
     | 2^16-leaf trie lookups | 2,000 | 5.3 s | 0.97 GB |
     | 2^16-leaf trie lookups | 10,000 | 22.4 s | 2.85 GB |
     | 2^16-leaf trie lookups | 20,000 | 198.5 s | 5.1 GB |
     | Rijndael-256 vector (List runner) | 1 | 20-25 s | 3.55-3.7 GB |
     | Rijndael-256 vectors, one file | 2 | 41 s | 3.85 GB |

   * The note ends with a go/no-go and a default-or-heavy placement for L3, K6, A2 and Z2, and
     confirms the R2 placement.
4. **R2: parametric Rijndael spec, runner and KATs (L, 1-1.5 weeks).** Acceptance:
   * `Rijndael.Params`, `keyExpansion`, `cipher`, `invCipher`, `eqInvCipher`, and
     `cipher_eq_exec`, proved for generic (Nb, Nk).
   * `invCipher_cipher`, `cipher_invCipher` and `eqInvCipher_eq_invCipher`.
   * KATs by kernel evaluation: FIPS 197-upd1 A.1-A.3 (all words) and Appendix B (all round
     states); 2001 C.1-C.3 (all three algorithms); a CAVP ECB subset.
   * **Q4 must be answered before any TS 35.236 data is committed.** Until then, only the
     citation and the SHA-256 of the ETSI PDF are committed. The check of tests 1-8 and the 15
     round keys of test 1 stays in an uncommitted local file. Once Q4 allows, all 8 vectors go
     into one default-library module.
   * Four negative controls that must fail: offsets (0,1,2,3), Rcon truncated at 10, no SubWord
     at i mod Nk = 4, MixColumns kept in the final round.
   * Heavy modules, if any, added to `WideTrailHeavy.lean` and to `ci.yml`, and passing
     `AuditAxiomsHeavy.lean`.
   * The source, revision and hash of every vector recorded in docstrings.
5. **R3 and R4: key-schedule facts and the bridge (S-M).** Acceptance:
   * `keyExpansion_prefix_aes256`, `keyExpansion_window_determines`, `rcon_values`, `rcon_injOn`
     (indices 1..29), `rcon_maxIndex`.
   * `cipher_eq_scheduledRun`.
   * A module docstring that says, in plain words, that no probability theorem uses the key
     schedule.
6. **T3 requirements note (S).** A one-page interface request from items 7 and 8 to the owner of
   the linear framework, covering points 1-5 of Section 4, including the mask direction.
   Acceptance: the owner of target 3 confirms or amends the signatures before R5, the SPN
   linear work or the Keccak linear work starts. R5a does not wait for it.
7. **D0: ARX scope module (S).** Acceptance: `DesignKit/Checks/ARX.lean` with the four
   `decide`-checked facts (bit-level support not preserved; MSB cancellation; MSB pass-through;
   Lipmaa-Moriai equal to an exhaustive count at n = 3), plus a README SCOPE section citing
   SPARKLE p.6/p.33, BLAKE3 Sec. 4.4 and FIPS 180-4 Sec. 6.2.2.
8. **R8 draft: certificate and letter, not sent (S-M).** Acceptance:
   * `WideTrail/Rijndael/Claims.lean` restates each claim of the letter under its own name, with
     axioms pinned.
   * `RIJNDAEL256_CERTIFICATE.md` has a sources table with hashes, the claims, a boundary
     section (the 7a non-goals) and reproduction steps for a tagged commit.
   * `submission/rijndael256/LETTER.md`: every factual sentence cites a name in `Claims.lean` or
     a dated source. The 2^-24 figure appears only as a coarse bound next to the known exact
     value.
   * The draft goes to the owner, who decides on sending (Q1-Q3).
9. **K0 and K1: Keccak constants, spec, runner and KATs (M).** Acceptance:
   * Constants computed and checked against FIPS 202 Table 2 and the XKCP RC list.
   * `keccakP_eq_exec` for every w.
   * KATs at XKCP 200/400/800/1600 and SHA3-256(""), plus two negative controls.
   * The FIPS 202 edition pinned to August 2015, with its hash.
10. **K2 to K4: chi, theta, row branch number 4 for every width, two-round corollaries (M).**
    Acceptance:
    * `XorBits 5` rows; `chiRow_uniform` (8) and `wRow_table`.
    * `lambda_rowBranch w` proved for all w ∈ {1, 2, 4, 8, 16, 32, 64} by a generic argument,
      not by enumeration, plus `lambda_rowBranch_tight`.
    * `keccak_two_round_weight` (2^-8) and `keccak_two_round_differential` (2^-6), argued from
      `activePattern_eq_of_diffCount_ne_zero` and `lambda_rowBranch`.
    * If the generic proof fails in the all-odd case, stop and report the failing case rather
      than weaken the statement.
11. **A0 and A1: Ascon S-box, Σi branch numbers and the two-round bound (S-M).** Acceptance:
    * `Ascon.sbox` from SP 800-232 Table 6, checked against eq. (7).
    * `Ascon.sbox_uniform` (8) and differential branch number 3.
    * `Ascon.sigma_bitBranch` for all five Σi by a structural argument, and `Ascon.pL_colBranch`.
    * `ascon_two_round_active` (4, matching Ascon v1.2 Table 12), `ascon_two_round_prob`
      (2^-8) and `ascon_two_round_differential` (2^-6).
    * Negative checks: 5 active S-boxes and exponent 9 fail.
    * Docstrings cite SP 800-232 with its hash and say that nothing is claimed for three or
      more rounds.
12. **L1: XOR cells and lightweight S-box facts (S).** Acceptance: `XorBits`/`Nibble`; SKINNY S4,
    Midori/CRAFT Sb0 and GIFT GS facts, including `GS_six_iff` and the BOGI identity property,
    all by decide. S8 is deferred to after the spike.
13. **R5a: the AES S-box Walsh bound (M).** Acceptance:
    * `AES.sbox_walsh_le` (|walsh| ≤ 32 for b ≠ 0), with a local `walsh` definition documented
      as provisional until target 3.
    * Proved by route (i), the trace form and Kloosterman sums, or route (ii), digit packing.
    * A go/no-go note after two days if neither route fits the default library.
14. **Z1: gadget algebra (S-M, after R2).** Acceptance: `hinted_inverse_sound`,
    `sbox_gadget_sound`, `pluto_invTable_eq`, `ttable_middleRound_eq` and `ttable_finalRound_eq`
    (tied to `Rijndael.cipher` at Nb = 4), `plookup_table_eq`, `sparse9_xor` with
    `sparse9_xor_fails_nine`. Each docstring cites the pinned gadget source and its hash and says
    that no deployed circuit is verified.
15. **L2: `Search/Automaton` soundness and superadditivity (M; not gated by the spike).**
    Acceptance:
    * `binaryMatrix_rel_sound` for every `AddCommGroup` with `∀ g, g + g = 0`, plus a check that
      the ZMod 3 counterexample violates the relation.
    * `path_of_trailKeyCount_ne_zero` and `minWeight_superadditive`.
    * `check_sound` with the ladder hypothesis (or a `check` that re-verifies its ladder).
    * A toy certificate that the kernel accepts; a deliberately wrong bound and an inflated
      `Bprev` must both be rejected.
16. **D1: `HadesDesign` facade (M, after target 1 is merged and no Poseidon2 work is open).**
    Acceptance:
    * The BN254 (8554/754), SP1 KoalaBear (989/209), SP1 BabyBear (906/198) and Pico KoalaBear
      (989/209) exponents are re-derived through `HadesDesign.certificate` with unchanged
      values.
    * The width-16 instances go through a wrapper of `Poseidon2.Plonky3.Diag`.
    * The middle term is a parameter.

---

## 6. Open questions for the project owner

1. **Whether to submit to NIST, under whose name, and when.** NIST posts comments with
   submitters' names and affiliations (SP 800-197 page). No FIPS 197 revision draft exists
   (2026-11-27). The options:
   * (a) send a short unsolicited comment now, aimed at the drafting stage (Rcon[11..14],
     vectors with intermediate values, precise statements in the trail model). The channels are:
     * `ciphermodes@nist.gov`, subject "Comments on Rijndael-256" (the SP 800-197 channel);
     * `cryptopubreviewboard@nist.gov` (the channel of the 2022 FIPS 197 update draft);
     * the ciphermodes-forum.
   * (b) wait for the draft and comment on its text. The precedents point both ways. The 2022
     editorial FIPS 197 update had a CSRC-only notice and 56 days, with no Federal Register
     notice found. The FIPS 203-205 drafts, which added algorithms, had a Federal Register notice
     and 90 days, as did the 2001 AES draft. A Rijndael-256 revision is technical, so the second
     pattern is likelier (inference).
   * (c) both.

   Should the letter carry the project name, a personal name or an affiliation?
2. **Scope of the letter.** Is it facts only, or does it also take a position on the key-schedule
   question that NSA, Ericsson and Avanzi et al. raised? If NIST changes the key schedule, R2-R4
   need rework; R0-R1 do not.
3. **The linear claims.** Should the first submission wait for target 3 and R5 (2^-75 per 4
   rounds), or should the linear claims follow as a second comment?
4. **The 3GPP/ETSI vectors (blocks the TS 35.236 data commit in task 4).**
   * The 3GPP archives carry a 3GPP copyright notice. The ETSI PDF says "No part may be
     reproduced or utilized in any form or by any means … except as authorized by written
     permission of ETSI" (ETSI TS 135 236 V19.0.0, pdf p.2).
   * May the TS 35.236 vectors be transcribed into an Apache-2.0 repository from either source?
   * The alternative is to keep only citations and hashes in the repository, with the check
     reproducible locally from the downloaded PDF.
   * Also: is the outside model's Nk = 4/6 regression data at Nb = 8 to be committed, labelled
     as unpublished?
5. **The trust tier.** Must everything stay kernel-only, or may a separately named library with a
   compiled checker (`native_decide`, excluded from the audit claims and the README headline) host
   large certificates (Keccak b ≥ 200, GIFT at 6-7 rounds, the SKINNY 40-round ladder)? Kernel-only
   caps 8b at small widths and symmetric trails. On the 2026-11-27 measurements it also puts the
   SKINNY 40-round ladder (at least about 26 h) out of reach.
6. **Resolved: `decide +kernel`.** It is already used in the default library
   (`Differential/Checks/Hull.lean:135`) and passes the axiom audit. Using it more needs only
   README wording.
7. **The circuit dependency.** Should `clean@v4.33.1` be used in a separate Lake package, or should
   a minimal in-house R1CS be built? Which deployed gadget comes first: Reclaim gnark, Crema/Pluto
   circom, Barretenberg AES-128 (which shares a repository with the Aztec BN254 work of target 1),
   or the TLSNotary Bristol circuits?
8. **New results.** Should the computed but unpublished SKINNY linear bounds for rounds 24-40 be
   stated and released as new kernel-checked results, or only used as cross-checks?
9. **Errata.** Should the project report what it finds to the authors? The findings are:
   * the three Keccak reference pdf pp.40-41 slips;
   * the TS 35.235 clause 11.5 and 11.7 errata, now confirmed in the published ETSI PDF (pdf
     pp.28 and 30) and reportable to 3GPP SA3 or ETSI;
   * the possible typo in Delaune et al. p.7;
   * the GIFT 2017 nine-round figures that conflict with later optima.
10. **Fetching the blocked sources.** Who fetches the ePrint, ToSC and Springer sources that were
    blocked on 2026-11-26, before any "as claimed by the designers" statement is encoded?
    * They include the SKINNY and GIFT full papers (2016/660, 2017/622; PDFs still HTTP 403 on
      2026-11-27, abstract pages reachable), the Poseidon2, Rescue-Prime, RPO, XHash, Tip5 and
      Monolith papers, the Xoodoo cookbook (2018/767), TurboSHAKE (2023/342), the ePrint
      2026/1035 SoK table, and the Rijndael book's appendix vectors.
    * Also blocked: the Keliher-Sui paper body (only its abstract was read), the ACVP Ascon
      vectors and the GitHub-hosted 7c facts (403 on 2026-11-27).
11. **Outreach to design authors.** Should the project contact a design author to pilot the design
    kit? Ashlar's posts (2026-08-06, 2026-08-17) name an artifact tag that was not fetched. In
    the documentation, should third-party designs be named only with citations?
12. **Data licences.** The XooTools trail lists have no licence file at the probed paths, and the
    giftcipher repository's licence is unverified. May they be vendored as test data?
13. **The order of the research tracks.** After the foundations, which comes first: the SKINNY
    automaton (7b), Keccak small-width certificates (8b) or the Ascon 3-round certificate (A2)?
    All depend on the spike; the last two share `Search/Tree`.
14. **The FIPS 202 update.** When NIST publishes its FIPS 202 update draft, should the Keccak
    sector move to it or stay pinned to the 2015 edition? The update is mainly editorial, but
    NIST will also consider technical changes from the comments (decision of 2025-03-12). No
    draft exists as of 2026-11-27.

---

### Appendix A: local research material

Research root:
`research/standards-and-designs/`.
Per-topic manifests:

* `research/standards-and-designs/nist-rijndael256/SHA256SUMS.downloads.txt`
* `research/standards-and-designs/skinny-gift/notes/SHA256SUMS.txt`
* `research/standards-and-designs/aes-zktls/manifest.sha256`
* `research/standards-and-designs/new-designs/SHA256SUMS.txt`
* `research/standards-and-designs/keccak/SHA256SUMS.txt`
* `research/standards-and-designs/adversarial-review/SHA256SUMS.downloads.txt`
  and `.../adversarial-review/SHA256SUMS.scripts-spike.txt`
* `research/standards-and-designs/revision/SHA256SUMS.downloads.txt`
  and `.../revision/SHA256SUMS.scripts-spike.txt`
* The re-verification log:
  `research/standards-and-designs/revision/notes/VERIFICATION.txt`.
  The plan before this revision is saved as `.../revision/notes/PLAN.before-revision.md` (sha256
  `2887e4c8b639fa1fcd6aa1a9d3d0d4a9f369efadd4ea540e6d2b432b2c5e6176`).

Downloaded material sits in each topic's `downloads/` directory. The research scripts and kernel
probes sit outside those directories. None of the downloaded code was executed. Python ran only
as `python3 -I`.

### Appendix B: Review notes

Every disputed point was re-checked against the repository or the primary source on 2026-11-27
before the text changed (log: `revision/notes/VERIFICATION.txt`).

**Accepted and applied:**

* Repository and commit facts: A1, A2 (so Q6 is resolved), A3, A4 (the `IsTrail` form) and all
  three A5 nits.
* NIST status facts: B1-B5.
* 3GPP/ETSI: C1, C2. I also reproduced all 8 vectors and 15 round keys with an independent model.
* Numbers from papers: D1-D6.
* Mathematics and scope: E1 (counterexample re-run: 6 pairs), E2, E3, E4.
* Effort and feasibility: F2, F3, F5 (probes re-run; numbers above), F6.
* Ordering and missing items: G2, G3, H2, H3, H4, and the I list.

**Rejected or modified:**

* **A4, the S-box argument.** The corrected signature put the AES bricklayer into `rijndaelSpec`.
  That field needs a support-preserving map, and `AES.sbox 0 = 0x63`. The library uses the `id`
  placeholder (`aesLinSpec`, `AESProb.lean:41-63`), and `IsTrail` reads only the linear layer.
  The plan uses `id`.
* **A1, two details.** "Tree clean at 03:34Z" was true then, but at 03:46Z the two Pico files had
  uncommitted edits again; the plan says so, and this strengthens G2. The nine unmerged commits
  are `cba2cf8` … `d6a3907`; in git range notation, `500a3f5..d6a3907` has eight.
* **B6.** The forum thread was reachable on 2026-11-27 (HTTP 200, sha256 `1d4d7b30…`), so the
  post is now cited as verified with its own quote. The distinction from SP 800-38D r1 comment 11
  was kept, and checked against the local text of those comments.
* **C3.** "All 8 in the default library" was accepted with two conditions. First, only after Q4
  (G1). Second, in one module: two vectors in one file peaked at 3.85 GB, and Lake builds
  modules in parallel. The measurement used a scratch List runner, so the spike re-measures with
  the committed runner.
* **E5, the 4-round figure.** The review wrote "4-round MEDP ≤ 2^-113.9". The Keliher-Sui abstract
  gives (53/2^34)^4 ≈ 1.881 × 2^-114 ≈ 2^-113.1. The plan uses the abstract's figure.
* **F1, the rebracketing.** Accepted as conditional. It is needed if T3 keeps the backward Aᵀ
  convention of `Transpose.lean:13-14`, and not with forward propagation through L⁻ᵀ. R5 itself
  moved to M as proposed.
* **F4.** Accepted on the component list. The cited aes-zktls estimate could not be checked: that
  note's text is not on disk.
* **G1, "store it as a hash".** A Lean theorem cannot carry a vector "as a hash" without SHA-256
  in Lean. This became: commit only the citation and the PDF's SHA-256, and keep the check local
  until Q4 is answered.
* **H1, the ranking.** "The most standards-relevant target in the 7b/8b family" was not adopted
  as stated. Keccak-f[1600] underlies FIPS 202 and, through it, FIPS 203-205. Ascon is the most
  standards-relevant addition on the lightweight side. Ascon was added (A0-A3) with the review's
  figures. They were re-read from Ascon v1.2 and recomputed from SP 800-232, which I downloaded
  for the S-box and Σi tables.
* **The review's own header.** The fetch window "03:08-04:10 UTC" does not match its files: they
  are timestamped 03:10-03:44 UTC, and the clock read 03:46 UTC when this revision began. No plan
  text depends on it.

**Changes beyond the critique, found while re-verifying:**

* `BitVec n` addition is modular, so 4-bit and 5-bit cells need an XOR wrapper (`XorBits`,
  Section 0, item 10). This affects SKINNY-64, Keccak rows and Ascon columns.
* The SP 800-197 announcement's own timing sentence ("over the next year") was added.
* The D1 instance table now has sources.
