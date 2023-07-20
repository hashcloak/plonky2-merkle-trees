# Examples of using Plonky2

Practice with Plonky2.

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

## merkle_proof_recursive

WIP. Has to be reviewed. 

Exercise in using recursive proof to prove all leaves of a Merkle tree are leaves of the Merkle tree. 

Has been made using following examples:
- https://github.com/polymerdao/plonky2-ed25519/blob/8fb5654b8bce6daff1145761a4db015183662838/src/main.rs
- https://github.com/morgana-proofs/plonky2-hashchain/blob/main/src/hashchain.rs 