use anyhow::Result;
use plonky2::{plonk::{config::{PoseidonGoldilocksConfig, GenericConfig, Hasher}, circuit_builder::CircuitBuilder, circuit_data::{CircuitConfig, VerifierOnlyCircuitData, CommonCircuitData, CircuitData}, proof}, hash::{hash_types::{RichField, HashOut}, poseidon::PoseidonHash}, iop::witness::{WitnessWrite, PartialWitness}, field::{goldilocks_field::GoldilocksField, types::Field}};
use plonky2_merkle_trees::simple_merkle_tree::simple_merkle_tree::MerkleTree;

/**
 * This is a small example of verifying a merkle tree proof for a Merkle Tree with 4 leaves
 * Naive and only works for 4 leaves and leaf index 0
 * Leaving this here to have small and simple example code
 */

// NOTE this assumes a Merkle Tree of 4 leaf with the merkle proof element always on the left 
// (the leaf that is being proven has index 0)
// Returns the cricuit data for verifying the Merkle Proof
pub fn verify_merkle_proof_circuit() -> CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2> {
  const D: usize = 2;
  type C = PoseidonGoldilocksConfig;
  type F = <C as GenericConfig<D>>::F;

  let config = CircuitConfig::standard_recursion_config();
  let mut builder: CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2> = CircuitBuilder::<F, D>::new(config);

  // The leaf to prove is in the Merkle Tree
  let leaf_to_prove = builder.add_virtual_hash();
  // The elements of the proof
  let merkle_proof_elm_0 = builder.add_virtual_hash();
  let merkle_proof_elm_1 = builder.add_virtual_hash();

  let level1_hash: plonky2::hash::hash_types::HashOutTarget = builder.hash_or_noop::<PoseidonHash>([
    leaf_to_prove.elements.to_vec(), 
    merkle_proof_elm_0.elements.to_vec()
  ].concat());

  // This is how we set the constraint of the expected root wrt the computed value
  let expected_root = builder.hash_or_noop::<PoseidonHash>([
    level1_hash.elements.to_vec(),
    merkle_proof_elm_1.elements.to_vec()
  ].concat());

  // For now, making everything public inputs so we can set them outside of this function (don't know how to do that if they are simply "targets")
  // But logically, only the root and leaf_to_prove would be public input and the rest of the values witness inputs

  // Registering a hash target actually registers 4 target elements
  builder.register_public_inputs(&leaf_to_prove.elements);
  builder.register_public_inputs(&merkle_proof_elm_0.elements);
  builder.register_public_inputs(&merkle_proof_elm_1.elements);
  builder.register_public_inputs(&expected_root.elements);

  let data = builder.build::<C>();
  data
}

fn main() -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

      // Test tree, 4 leaves
    let leaves = [
      F::from_canonical_u64(2890852870), 
      F::from_canonical_u64(156728478), 
      F::from_canonical_u64(2876514289), 
      F::from_canonical_u64(984286162)
      ].to_vec();
    let tree: MerkleTree  = MerkleTree::build(leaves.clone());

    let merkle_proof_leaf0 = tree.clone().get_merkle_proof(0);
    println!("{:?}", merkle_proof_leaf0);
    // [
    // other leaf: HashOut { elements: [156728478, 0, 0, 0] }, 
    // other node: HashOut { elements: [6698018865469624861, 12486244005715193285, 11330639022572315007, 6059804404595156248] }
    // ]

    // The tree:
    //         R
    //    N0         N1    
    // L0   L1    L2    L3

    // PROOF for L0: (the elements in brackets)
    //    N0          [N1]    
    // L0   [L1]    L2    L3

    // Check proof L0:
    // H0 = Hash(L0||L1)
    // H1 = Hash(H0||N1)
    // CHECK Root = H1 equals R ? 

    let circuit_data = verify_merkle_proof_circuit();

    /* The witness needs the following inputs:
      - leaf_to_prove
      - merkle_proof_elm_0
      - merkle_proof_elm_1
      - expected_root

      builder.register_public_inputs(&leaf_to_prove.elements);
      builder.register_public_inputs(&merkle_proof_elm_0.elements);
      builder.register_public_inputs(&merkle_proof_elm_1.elements);
      builder.register_public_inputs(&expected_root.elements);
    */
    
    let mut pw = plonky2::iop::witness::PartialWitness::new();
    let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();

    // Set first hash; the leaf we're trying to prove membership of
    let leaf_to_prove = PoseidonHash::hash_or_noop(&[leaves[0]]);
    for i in 0..4 {
      pw.set_target(expected_public_inputs[i], leaf_to_prove.elements[i]);
    }

    // Set first elm of proof
    for i in 0..4 {
      pw.set_target(expected_public_inputs[i+4], merkle_proof_leaf0[0].elements[i]);
    }

    // Set second elm of proof
    for i in 0..4 {
      pw.set_target(expected_public_inputs[i+8], merkle_proof_leaf0[1].elements[i]);
    }

    // Set root
    for i in 0..4 {
      pw.set_target(expected_public_inputs[i+12], tree.root.elements[i]);
    }

    let proof = circuit_data.prove(pw)?;
    // uncomment to print proof
    // println!("{:?}", proof);

    // Verify proof
    circuit_data.verify(proof)
}