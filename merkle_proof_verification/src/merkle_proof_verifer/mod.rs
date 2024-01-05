use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::plonk::circuit_data;
use plonky2::hash::hash_types::HashOutTarget;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{PoseidonGoldilocksConfig, GenericConfig, Hasher};
use simple_merkle_tree::simple_merkle_tree::MerkleTree;

use crate::simple_merkle_tree;

pub fn verify_merkle_proof_leaf_0() {
    // Circuit Builder
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // Circuit arithmetic
    // Add targets (hash targets in our case?)
    let leaf = builder.add_virtual_hash();

    // if we have leaves of 4 in the merkle tree
    let siblings: Vec<HashOutTarget> = builder.add_virtual_hashes(2);

    // To ease of use, we will first write a verifier that proves the leaf 0
    // Burayı tekrar yapacağız.
    let level_0_hash = builder.hash_or_noop::<PoseidonHash>([leaf.elements.to_vec(), siblings[0].elements.to_vec()].concat());
    let expected_root = builder.hash_or_noop::<PoseidonHash>([level_0_hash.elements.to_vec(), siblings[1].elements.to_vec()].concat());

    // Register Targets
    builder.register_public_inputs(&leaf.elements);
    builder.register_public_inputs(&siblings[0].elements);
    builder.register_public_inputs(&siblings[1].elements);
    builder.register_public_inputs(&expected_root.elements); // Expected root da pw olarak girileceği için bunu kullanmamız gerekir.

    // Partial Witness
    // To have the Partial Witness, we need to construct a Merkle Proof with leaves.
    let leaves = [
      F::from(GoldilocksField(2890852870)), 
      F::from(GoldilocksField(156728478)), 
      F::from(GoldilocksField(2876514289)), 
      F::from(GoldilocksField(984286162))
      ].to_vec();

    let tree: MerkleTree  = MerkleTree::build(leaves.clone(), 2);

    // tree[0] has len 4: - - - -
    // tree[1] has len 2:  -   -
    // root is len 1:        -

    let merkle_proof_leaf0 = tree.clone().get_merkle_proof(0);
    //println!("{:?}", merkle_proof_leaf0);

    let mut pw =PartialWitness::new();
    //let circuit_data = builder.build::<C>();
    //let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();

    // Set first hash; the leaf we're trying to prove membership of
    let leaf_to_prove = PoseidonHash::hash_or_noop(&[leaves[0]]); // makes no operation for the goldilocks field.
    println!("leaf to prove is {:?}", leaf_to_prove);

    // Use partial witness to set witnesses.
    pw.set_hash_target(leaf, leaf_to_prove);
    pw.set_hash_target(siblings[0], merkle_proof_leaf0[0]);
    pw.set_hash_target(siblings[1], merkle_proof_leaf0[1]);
    //pw.set_hash_target(expected_root, tree.root);

    // build a wrong proof
    pw.set_hash_target(expected_root, tree.root);

    // Build the Circuit as Data
    let data = builder.build::<C>();

    // Prove the data with pw
    let proof = data.prove(pw).unwrap();

    // Verify the data
    data.verify(proof);
    
}