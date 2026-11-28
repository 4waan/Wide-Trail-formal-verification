# Research material for the standards and new-designs plan

[`STANDARDS_AND_DESIGNS_PLAN.md`](../../STANDARDS_AND_DESIGNS_PLAN.md) was written from five
research notes (`nist-rijndael256`, `skinny-gift`, `aes-zktls`, `new-designs`, `keccak`), an
adversarial review (`adversarial-review`, `review`) and a re-verification (`revision`), all dated
2026-11-26 and 2026-11-27.

This directory holds only their SHA-256 manifests. Each manifest lists the files a note relied on,
with the hash of each, so that a reader can fetch a source again and check that it is the same
file. The sources themselves (NIST, ETSI/3GPP, IACR, Springer and other documents, and web-page
snapshots), their extracted text, and the scripts and kernel probes are not committed: several
sources may not be redistributed, and some scripts embed third-party test vectors. See Section 6
of the plan, questions Q4 and Q12.
