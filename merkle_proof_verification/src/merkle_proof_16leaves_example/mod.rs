use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::hash::hash_types::{HashOutTarget, HashOut};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{PoseidonGoldilocksConfig, GenericConfig, Hasher};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};

use crate::simple_merkle_tree::simple_merkle_tree::MerkleTree;


// Verify a merkle proof of the 0th index of 16 leaves merkle_tree
pub fn verify_16leaves_merkle_tree() {
    // CircuitBuilder
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // CircuitArithmetic
    // add_virtual targets
    let leaf_hash = builder.add_virtual_hash();

    let siblings: Vec<HashOutTarget> = builder.add_virtual_hashes(4);
    // size 4 since we have 16 leaves, which makes log(16) = log(2^4) = 4

    let level1_hash = builder.hash_or_noop::<PoseidonHash>([leaf_hash.elements.to_vec(), siblings[0].elements.to_vec()].concat());
    let level2_hash = builder.hash_or_noop::<PoseidonHash>([level1_hash.elements.to_vec(), siblings[1].elements.to_vec()].concat());
    let level3_hash = builder.hash_or_noop::<PoseidonHash>([level2_hash.elements.to_vec(), siblings[2].elements.to_vec()].concat());
    let expected_root = builder.hash_or_noop::<PoseidonHash>([level3_hash.elements.to_vec(), siblings[3].elements.to_vec()].concat());

    //                -
    //        -               -
    //    -       -       -       -
    //  -   -   -   -   -   -   -   -
    // - - - - - - - - - - - - - - - - 

    // Register public inputs
    builder.register_public_inputs(&leaf_hash.elements);
    builder.register_public_inputs(&siblings[0].elements);
    builder.register_public_inputs(&siblings[1].elements);
    builder.register_public_inputs(&siblings[2].elements);
    builder.register_public_inputs(&siblings[3].elements);
    builder.register_public_inputs(&expected_root.elements);


    // PartialWitness -> witness for proving
    // Before the use of PartialWitness, we should bring the test merkle tree elements
    let leaves = [
        F::from(GoldilocksField(38957345)),
        F::from(GoldilocksField(928323234)),
        F::from(GoldilocksField(398573451)),
        F::from(GoldilocksField(12342134)),
        F::from(GoldilocksField(34623456342)),
        F::from(GoldilocksField(2342356436)),
        F::from(GoldilocksField(1111111)),
        F::from(GoldilocksField(10101001)),
        F::from(GoldilocksField(234234)),
        F::from(GoldilocksField(45645)),
        F::from(GoldilocksField(39328573451)),
        F::from(GoldilocksField(3463456)),
        F::from(GoldilocksField(222222)),
        F::from(GoldilocksField(222)),
        F::from(GoldilocksField(223)),
        F::from(GoldilocksField(1)),
    ].to_vec();

    let tree: MerkleTree = MerkleTree::build(leaves.clone(), 4);

    // We need to have siblings
    let merkle_proof_element_0 = tree.clone().get_merkle_proof(0);

    println!("merkle proof element 0 has {} elements", merkle_proof_element_0.len());

    let mut pw = PartialWitness::new();

    let leaf_hash_witness = PoseidonHash::hash_or_noop(&[leaves[0]]);
    
    pw.set_hash_target(leaf_hash, leaf_hash_witness);
    pw.set_hash_target(siblings[0], merkle_proof_element_0[0]);
    pw.set_hash_target(siblings[1], merkle_proof_element_0[1]);
    pw.set_hash_target(siblings[2], merkle_proof_element_0[2]);
    pw.set_hash_target(siblings[3], merkle_proof_element_0[3]);
    pw.set_hash_target(expected_root, tree.root);

    println!("The actual root is : {:?}", tree.root);

    //let's create a wrong proof
    //pw.set_hash_target(expected_root, tree.tree[1][0]);
    
    // Build the circuit as a circuit data
    let data = builder.build::<C>();

    // Prove the data with witness
    let proof = data.prove(pw).unwrap();

    // Verify the proof
    data.verify(proof);
}


// Verify a merkle proof of the 0th index of 16 leaves merkle_tree
pub fn verify_16leaves_merkle_tree_any_location(leaf_index: usize) {
    // CircuitBuilder
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // CircuitArithmetic
    // add_virtual targets
    let leaf_hash = builder.add_virtual_hash();

    let siblings: Vec<HashOutTarget> = builder.add_virtual_hashes(4);
    // size 4 since we have 16 leaves, which makes log(16) = log(2^4) = 4

    //let level1_hash = builder.hash_or_noop::<PoseidonHash>([leaf_hash.elements.to_vec(), siblings[0].elements.to_vec()].concat());
    //let level2_hash = builder.hash_or_noop::<PoseidonHash>([level1_hash.elements.to_vec(), siblings[1].elements.to_vec()].concat());
    //let level3_hash = builder.hash_or_noop::<PoseidonHash>([level2_hash.elements.to_vec(), siblings[2].elements.to_vec()].concat());
    //let expected_root = builder.hash_or_noop::<PoseidonHash>([level3_hash.elements.to_vec(), siblings[3].elements.to_vec()].concat());

    let mut root: HashOutTarget = leaf_hash;
    let mut position = leaf_index;

    for i in 0..4 {
        println!("current position is: {}", position);
        if position % 2 == 0 {
            root = builder.hash_or_noop::<PoseidonHash>([root.elements.to_vec(), siblings[i].elements.to_vec()].concat());
        } else {
            root = builder.hash_or_noop::<PoseidonHash>([siblings[i].elements.to_vec(), root.elements.to_vec()].concat());
        }
        position = position / 2;
    }

    let expected_root = root;
    //                -
    //        -               -
    //    -       -       -       -
    //  -   -   -   -   -   -   -   -
    // - - - - - - - - - - - - - - - - 

    // Register public inputs
    builder.register_public_inputs(&leaf_hash.elements);
    builder.register_public_inputs(&siblings[0].elements);
    builder.register_public_inputs(&siblings[1].elements);
    builder.register_public_inputs(&siblings[2].elements);
    builder.register_public_inputs(&siblings[3].elements);
    builder.register_public_inputs(&expected_root.elements);


    // PartialWitness -> witness for proving
    // Before the use of PartialWitness, we should bring the test merkle tree elements
    let leaves = [
        F::from(GoldilocksField(38957345)),
        F::from(GoldilocksField(928323234)),
        F::from(GoldilocksField(398573451)),
        F::from(GoldilocksField(12342134)),
        F::from(GoldilocksField(34623456342)),
        F::from(GoldilocksField(2342356436)),
        F::from(GoldilocksField(1111111)),
        F::from(GoldilocksField(10101001)),
        F::from(GoldilocksField(234234)),
        F::from(GoldilocksField(45645)),
        F::from(GoldilocksField(39328573451)),
        F::from(GoldilocksField(3463456)),
        F::from(GoldilocksField(222222)),
        F::from(GoldilocksField(222)),
        F::from(GoldilocksField(223)),
        F::from(GoldilocksField(1)),
    ].to_vec();

    let tree: MerkleTree = MerkleTree::build(leaves.clone(), 4);

    // We need to have siblings
    let merkle_proof_element_0 = tree.clone().get_merkle_proof(leaf_index);
    println!("leaf_index is: {}", leaf_index);

    println!("merkle proof element 0 has {} elements", merkle_proof_element_0.len());

    let mut pw = PartialWitness::new();

    let leaf_hash_witness = PoseidonHash::hash_or_noop(&[leaves[leaf_index]]);
    // *** WE FIXED THE ABOVE FOR THE ANY LOCATION
    
    pw.set_hash_target(leaf_hash, leaf_hash_witness);
    pw.set_hash_target(siblings[0], merkle_proof_element_0[0]);
    pw.set_hash_target(siblings[1], merkle_proof_element_0[1]);
    pw.set_hash_target(siblings[2], merkle_proof_element_0[2]);
    pw.set_hash_target(siblings[3], merkle_proof_element_0[3]);
    pw.set_hash_target(expected_root, tree.root);

    println!("The actual root is : {:?}", tree.root);

    //let's create a wrong proof
    //pw.set_hash_target(expected_root, tree.tree[1][0]);
    
    // Build the circuit as a circuit data
    let data = builder.build::<C>();

    // Prove the data with witness
    let proof = data.prove(pw).unwrap();

    // Verify the proof
    data.verify(proof);
}