<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Operations, Backups & Offsite Mirror (`docs/operations.md`)

## 1. Master Research Archive Mirror
This repository is pinned as an immutable Git submodule (`repos/p-vs-np-frontier-lab`) and archived with frozen PDF SHA-256 digests inside [`0thernes/0thernes-research-archive`](https://github.com/0thernes/0thernes-research-archive) (`0TH-2026-013`).

## 2. Offline Git Bundle Backup
```bash
git bundle create p-vs-np-frontier-lab-$(cat VERSION).bundle --all
git bundle verify p-vs-np-frontier-lab-$(cat VERSION).bundle
sha256sum p-vs-np-frontier-lab-$(cat VERSION).bundle
```

## 3. Releases & Long-Term Archival
- Every `v*` tag triggers `.github/workflows/release.yml`, attaching `Donahue_2026_p_vs_np_barrier_anatomy.pdf`, `arxiv_submission.tar.gz`, `MANIFEST.sha256`, `SHA256SUMS`, and Sigstore SLSA build-provenance attestations (`actions/attest-build-provenance@v2`).
- Submit public release URLs to Software Heritage (`archive.softwareheritage.org/save/`) and Palomar Registry (`submit.palomar-registry.org`).
