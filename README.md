# Merkle Trees in Plonky2

## Examples

The `examples` folder contains separate Plonky2 examples that explore how it can be used. They either contain a `main` function, or test functions in the file. In both cases, they can be run from your IDE clicking on `Run` or `Run test`.

## Notes

Plonky repo: https://github.com/mir-protocol/plonky2/tree/main.

`rust-toolchain` has been added, since plonky2 currently doesn't run on stable. 

## Merkle Mountain Ranges

Merkle Mountain Ranges have been implemented in `src/mmr`. The main implementation can be found in `merkle_mountain_ranges.rs`, which contains functionality to create and update an MMR, and generate and verify a proof for a leaf. Plonky2 verifiers for this can be found in `mmr_plonky2_verifier.rs` and `mmr_plonky2_verifier_1_recursion.rs` for a "normal" and a 1 layer recursive verifier respectively. In the recursive verifier the verification of the Merkle proof is embedded in the outer proof which verifies the hash of the peaks (see MMR explanation in `mmr/README.md`). 

Additionally, there is a "naive" implementation which requires more space to keep the MMR data. In the main implementation the MMR consists of an array of elements. The naive implementation holds more information and could be easier to follow in the beginning. Also for this version there are Plonky2 verifiers, with and without recursion.

### Run

Tests have been added to all `mmr` files, which can be run from within the file, using the play button in git pishan IDE.