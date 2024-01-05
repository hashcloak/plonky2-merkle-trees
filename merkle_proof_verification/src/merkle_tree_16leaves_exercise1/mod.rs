// Implement a merkle proof verifier with 16 leaves for the leaf index 0.

use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::hash::hash_types::HashOutTarget;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::hash::poseidon_goldilocks;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{PoseidonGoldilocksConfig, GenericConfig, Hasher};

use crate::simple_merkle_tree::simple_merkle_tree::MerkleTree;

pub fn verify_merkle_proof_16leaves_exercise1(leaf_index: usize) {
    // Construct a builder using CircuitBuilder
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    // Circuit Arithmetic
    // add virtual targets
    let leaf_hash = builder.add_virtual_hash();

    //                -                  -> root
    //        -               -          -> level 3
    //    -       -       -       -      -> level 2
    //  -   -   -   -   -   -   -   -    -> level 1
    // - - - - - - - - - - - - - - - -   -> level 0

    // if we have time, we will change this.

    // since we are doing a verification for 16 elements, siblings will have log(16) = log(2^4) = 4
    let siblings: Vec<HashOutTarget> = builder.add_virtual_hashes(4); // If we want to do a generic impl we need to change it.

    // we're having leaf hash first since we will verify the correction of the first element.
    // If we want to have a verification at any location, we need to change this implementation

    // To make it for any location, we need to change the circuit arithmetic to compute the root.
    //let level1_hash = builder.hash_or_noop::<PoseidonHash>([leaf_hash.elements.to_vec(), siblings[0].elements.to_vec()].concat());
    //let level2_hash = builder.hash_or_noop::<PoseidonHash>([level1_hash.elements.to_vec(), siblings[1].elements.to_vec()].concat());
    //let level3_hash = builder.hash_or_noop::<PoseidonHash>([level2_hash.elements.to_vec(), siblings[2].elements.to_vec()].concat());
    //let expected_root = builder.hash_or_noop::<PoseidonHash>([level3_hash.elements.to_vec(), siblings[3].elements.to_vec()].concat());


    let mut position = leaf_index;
    let mut root = leaf_hash;

    for i in 0..4 {
        if position % 2 == 0 {
            root = builder.hash_or_noop::<PoseidonHash>([root.elements.to_vec(), siblings[i].elements.to_vec()].concat());
        }
        else {
            root = builder.hash_or_noop::<PoseidonHash>([siblings[i].elements.to_vec(), root.elements.to_vec()].concat());
        }
        position = position / 2;
    }
    // Register the public inputs
    let expected_root = root;
    

    builder.register_public_inputs(&leaf_hash.elements);
    builder.register_public_inputs(&siblings[0].elements);
    builder.register_public_inputs(&siblings[1].elements);
    builder.register_public_inputs(&siblings[2].elements);
    builder.register_public_inputs(&siblings[3].elements);
    builder.register_public_inputs(&expected_root.elements);
    

    // Create a PartialWitness as a proof input
    // Get merkle proof here
    // We need leaf_hash
    // We need merkle proof
    // We need a root to compare
    let leaves = [
        F::from(GoldilocksField(134534)),
        F::from(GoldilocksField(223542345)),
        F::from(GoldilocksField(33262346)),
        F::from(GoldilocksField(42342141)),
        F::from(GoldilocksField(36345)),
        F::from(GoldilocksField(2551)),
        F::from(GoldilocksField(54674643)),
        F::from(GoldilocksField(537456345)),
        F::from(GoldilocksField(1354235)),
        F::from(GoldilocksField(456456)),
        F::from(GoldilocksField(456456)),
        F::from(GoldilocksField(2345)),
        F::from(GoldilocksField(11111)),
        F::from(GoldilocksField(151235)),
        F::from(GoldilocksField(161222)),
        F::from(GoldilocksField(4563456)),
    ].to_vec();

    let tree: MerkleTree = MerkleTree::build(leaves.clone(), 4);

    let leaf_hash_at_index = PoseidonHash::hash_or_noop(&[leaves[leaf_index]]); // Leaf0_hash needs be changed
    println!("The leaf hash is : {:?}", leaf_hash);

    // We need a merkle proof to verify it
    // We need to change it if we implement for any location
    let merkle_proof_element0 = tree.clone().get_merkle_proof(leaf_index);

    // It needs be 4 elements
    println!("The siblings has {}", merkle_proof_element0.len());

    // We can use them as the inputs of proofs.
    let mut pw = PartialWitness::new();
    pw.set_hash_target(leaf_hash, leaf_hash_at_index);
    pw.set_hash_target(siblings[0], merkle_proof_element0[0]);
    pw.set_hash_target(siblings[1], merkle_proof_element0[1]);
    pw.set_hash_target(siblings[2], merkle_proof_element0[2]);
    pw.set_hash_target(siblings[3], merkle_proof_element0[3]);
    pw.set_hash_target(expected_root, tree.root);
    
    // Let's build a wrong proof
    //pw.set_hash_target(expected_root, merkle_proof_element0[0]);


    // Build the circuit as data
    let data = builder.build::<C>();

    // Prove the data with pw
    let proof = data.prove(pw).unwrap();

    // Verify the data
    data.verify(proof);
}