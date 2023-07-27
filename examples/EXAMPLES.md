# Examples of using Plonky2

Practice with Plonky2.

The example files have either a `main` that can be run, or tests in the file itself that can be run. Click `Run` or `Run Test` in your IDE. 

## cube

Create proof for "I know xˆ3"

## pol  

Create proof for "I know xˆ3 - 2xˆ2 + 7x + 11"

This was created by learning from [this Polymerlabs tutorial](https://polymerlabs.medium.com/a-tutorial-on-writing-zk-proofs-with-plonky2-part-i-be5812f6b798). 

## merkle_proof_old

Creating a simple circuit builder and witness to test what the hash of 2 elements together is. 

## merkle_tiny_tree_proof

A small example of verifying a merkle tree proof for a Merkle Tree with 4 leaves. 
Naive and only works for 4 leaves and leaf index 0.

## merkle_proof_example1

Creates a circuit for verifying a merkle proof. No recursion. 

In the tests witness is created and together with the circuit, a proof is created and verified. 

## merkle_proof_example2

Example of how to make a recursive proof. This verifies the merkle proof in a recursive way: per layer in the merkle tree 1 proof, and for every consecutive step the previous proof is added to the circuit and verified, as well as the next step of verifying data. 

Check following reference examples for recursive proofs in Plonky2:
- https://github.com/polymerdao/plonky2-ed25519/blob/8fb5654b8bce6daff1145761a4db015183662838/src/main.rs
- https://github.com/morgana-proofs/plonky2-hashchain/blob/main/src/hashchain.rs 
- https://github.com/mir-protocol/plonky2/blob/main/plonky2/examples/bench_recursion.rs
