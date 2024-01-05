use std::collections::HashMap;

use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::hash::hash_types::HashOutTarget;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
// We want to prove the 0th leaf of the merkle tree with 4 leaves
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{PoseidonGoldilocksConfig, GenericConfig, Hasher};

use crate::simple_merkle_tree::simple_merkle_tree::MerkleTree;


pub fn verify_4leaves_merkle_tree() {
    // Construct the CircuitBuilder
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // Circuit Arithmetic
    // Add virtual targets
    let leaf_hash = builder.add_virtual_hash();

    // we need siblings (merkle proof to use the logic.)
    // we have 2 siblings since we have 4 leaves = log(4) = log(2^2) = 2
    // if we have 16 leaves -> we'are going to have siblings of 4 which is
    // log(16) = log(2^4) = 4
    let siblings: Vec<HashOutTarget> = builder.add_virtual_hashes(2);

    // aritmetic.
    // we have a generic hash H: AlgebraicHasher
    // we want to use PoseidonHash here.
    let level1_hash = builder.hash_or_noop::<PoseidonHash>([leaf_hash.elements.to_vec(), siblings[0].elements.to_vec()].concat());
    let expected_hash = builder.hash_or_noop::<PoseidonHash>([level1_hash.elements.to_vec(), siblings[1].elements.to_vec()].concat());


    // Register the Public Inputs
    builder.register_public_inputs(&leaf_hash.elements);
    builder.register_public_inputs(&siblings[0].elements);
    builder.register_public_inputs(&siblings[1].elements);
    builder.register_public_inputs(&expected_hash.elements);


    // PartialWitness, WitnessWrite
    // In this section we are going to use MerkleTree::build function
    let leaves = [
        F::from(GoldilocksField(1234245)),
        F::from(GoldilocksField(346345234)),
        F::from(GoldilocksField(132462346)),
        F::from(GoldilocksField(456745543))
    ].to_vec();

    let tree: MerkleTree = MerkleTree::build(leaves.clone(), 2);

    // we need a merkle proof for leaf
    let merkle_proof_leaf_0 = tree.clone().get_merkle_proof(0);
    println!("merkle proof_leaf_0 is: {:?}", merkle_proof_leaf_0);

    let hashed_leaf = PoseidonHash::hash_or_noop(&[leaves[0]]);

    let mut pw = PartialWitness::new();
    
    pw.set_hash_target(leaf_hash, hashed_leaf);
    pw.set_hash_target(siblings[0], merkle_proof_leaf_0[0]);
    pw.set_hash_target(siblings[1], merkle_proof_leaf_0[1]);
    pw.set_hash_target(expected_hash, tree.root);

    // let's make the proof wrong by changing the value of expected_hash
    //pw.set_hash_target(expected_hash, merkle_proof_leaf_0[0]);

    // Build the Circuit as a Data
    let data = builder.build::<C>();

    // Prove the data with witness
    let proof = data.prove(pw).unwrap();

    // Verify the proof
    data.verify(proof);
}