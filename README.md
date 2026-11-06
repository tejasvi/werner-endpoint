# Equality cases and every-copy results for the Werner endpoint inequality

Programs and Lean 4 proofs for version 3 of the paper of this title. The paper and the full verification packages are
on Zenodo:

- version 3: https://doi.org/10.5281/zenodo.23992370
- all versions: https://doi.org/10.5281/zenodo.23718036

Each directory below is one package of that record, unpacked. The certificate files of `release_commonplane` (`*.pkl`)
are left out. Every other file is identical to the one in the archive, and each package's `SHA256SUMS` also lists the
files left out here.

| Directory | Package |
|---|---|
| `release_endpoint` | Equality cases and every-copy results for the Werner endpoint inequality: verification package |
| `release_commonplane` | Certificates: four copies, common-plane sector, every dimension |
| `release_lean_commonplane` | Lean 4 formalization: the four-copy endpoint property on the common-plane sector at d = 3 |

## How to check

`release_endpoint` and `release_lean_commonplane` are complete here. In `release_endpoint`, run `run_all.sh` as its
README describes. In `release_lean_commonplane`, build with `./build_sequential.sh` as `README_commonplane.md` describes;
it also gives the memory and time the build needs.

`release_commonplane` needs its certificate files, so check it from the archive. Download `release_commonplane.tar.gz`
from the [v3 release](https://github.com/tejasvi/werner-endpoint/releases/tag/v3) of this repository or from Zenodo,
compare its SHA-256 with the list in the release notes, unpack it and follow its README:

    sha256sum release_commonplane.tar.gz
    tar -xzf release_commonplane.tar.gz
    cd release_commonplane

## License

Every package is licensed under CC BY 4.0; see the `LICENSE` file in its directory.
