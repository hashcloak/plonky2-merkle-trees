use plonky2::{plonk::{config::{PoseidonGoldilocksConfig, GenericConfig, PoseidonHashConfig}, circuit_builder::CircuitBuilder, circuit_data::{CircuitConfig, VerifierOnlyCircuitData, CommonCircuitData, CircuitData}, proof}, hash::{hash_types::{RichField, HashOut, HashOutTarget}, poseidon::PoseidonHash}, iop::witness::{WitnessWrite, PartialWitness}, field::{goldilocks_field::GoldilocksField, types::Field}};

/**
 * zkp for veryfing merkle proof
 */

// Returns the cricuit data for verifying the Merkle Proof + the target for witness (non-public) input data
// the second part might not be necessary, but don't know how to set that data otherwise in the testing part
pub fn verify_merkle_proof_circuit(leaf_index: usize, nr_layers: usize) -> (CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>, Vec<HashOutTarget>) {
  const D: usize = 2;
  type C = PoseidonGoldilocksConfig;
  type F = <C as GenericConfig<D>>::F;

  let mut targets: Vec<HashOutTarget> = Vec::new();

  let config = CircuitConfig::standard_recursion_config();
  let mut builder: CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2> = CircuitBuilder::<F, D>::new(config);
  
  // The leaf to prove is in the Merkle Tree
  let leaf_to_prove = builder.add_virtual_hash();
  targets.push(leaf_to_prove);

  // The first hashing outside of the loop, since it uses the leaf_to_prove
  let merkle_proof_elm= builder.add_virtual_hash();
  targets.push(merkle_proof_elm);

  let mut next_hash: plonky2::hash::hash_types::HashOutTarget;
  if leaf_index % 2 == 0 {
    next_hash = builder.hash_or_noop::<PoseidonHashConfig, PoseidonHash>([
      leaf_to_prove.elements.to_vec(), 
      merkle_proof_elm.elements.to_vec()
    ].concat());
  } else {
    next_hash = builder.hash_or_noop::<PoseidonHashConfig, PoseidonHash>([
      merkle_proof_elm.elements.to_vec(),
      leaf_to_prove.elements.to_vec()
    ].concat());
  }

  let mut current_layer_index = leaf_index / 2;
  
  for _layer in 1..nr_layers {
    let merkle_proof_elm= builder.add_virtual_hash();
    targets.push(merkle_proof_elm);

    if current_layer_index % 2 == 0 {
      next_hash = builder.hash_or_noop::<PoseidonHashConfig, PoseidonHash>([
        next_hash.elements.to_vec(), 
        merkle_proof_elm.elements.to_vec()
      ].concat());
    } else {
      next_hash = builder.hash_or_noop::<PoseidonHashConfig, PoseidonHash>([
        merkle_proof_elm.elements.to_vec(),
        next_hash.elements.to_vec()
      ].concat());
    }
    current_layer_index = current_layer_index/2;
  }
  // This is the expected root value
  builder.register_public_inputs(&next_hash.elements);

  let data = builder.build::<C>();
  (data, targets)
}

#[cfg(test)]
mod tests {
  use anyhow::Result;
  use plonky2::{plonk::config::{PoseidonGoldilocksConfig, GenericConfig, Hasher}, hash::{poseidon::PoseidonHash, hash_types::RichField}, iop::witness::WitnessWrite, gates::poseidon::PoseidonGenerator};
use plonky2_field::{goldilocks_field::GoldilocksField, types::{Field, Sample}};
  use plonky2_merkle_trees::simple_merkle_tree::simple_merkle_tree::MerkleTree;
use rand::Rng;

  use crate::verify_merkle_proof_circuit;
  const GOLDILOCKS_FIELD_ORDER: u64 = 18446744069414584321;
  const D: usize = 2;
  type C = PoseidonGoldilocksConfig;
  type F = <C as GenericConfig<D>>::F;

  fn get_test_tree(nr_leaves: u64) -> MerkleTree { 
    let mut rng = rand::thread_rng();
    let mut leaves: Vec<GoldilocksField> = Vec::new();
    for i in 0..nr_leaves {
      leaves.push(F::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
    }
    let tree: MerkleTree  = MerkleTree::build(leaves.clone());
    tree
  }

  #[test]
  fn test_tree_4_leaves_index0() -> Result<()> {
      // Test tree, 4 leaves
      let tree: MerkleTree = get_test_tree(4);

      let merkle_proof_leaf0 = tree.clone().get_merkle_proof(0);
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

      let (circuit_data, targets) = verify_merkle_proof_circuit(0, 2);

      /* The witness needs the following inputs:
        - leaf_to_prove
        - proof elm 0
        - poof elm 1
        Public:
        - expected_root
      */
      
      let mut pw = plonky2::iop::witness::PartialWitness::new();
      // non-public inputs to witness: leaf and elements of merkle proof
      pw.set_hash_target(targets[0], tree.tree[0][0]); // leaf index 0
      pw.set_hash_target(targets[1], merkle_proof_leaf0[0]);
      pw.set_hash_target(targets[2], merkle_proof_leaf0[1]);

      // Public input: root
      let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();
      for i in 0..4 {
        pw.set_target(expected_public_inputs[i], tree.root.elements[i]);
      }

      let proof = circuit_data.prove(pw)?;
      // uncomment to print proof
      // println!("{:?}", proof);

      // Verify proof
      circuit_data.verify(proof)
  }

  #[test]
  fn test_tree_4_leaves_index3() -> Result<()> {
      let tree: MerkleTree = get_test_tree(4);
      let merkle_proof_leaf0 = tree.clone().get_merkle_proof(3);
      // println!("{:?}", merkle_proof_leaf0);

      // [HashOut { elements: [2876514289, 0, 0, 0] }, 
      // HashOut { elements: [6678006133445961348, 15827935749738443865, 6295652393730592048, 1546515167911236130] }]

      // The tree:
      //         R
      //    N0         N1    
      // L0   L1    L2    L3

      // PROOF for L0: (the elements in brackets)
      //    [N0]         N1    
      // L0   L1    [L2]    L3

      // Check proof L3:
      // H0 = Hash(L2||L3)
      // H1 = Hash(N0||H0)
      // CHECK Root = H1 equals R ? 

      let (circuit_data, targets) = verify_merkle_proof_circuit(3, 2);

      /* The witness needs the following inputs:
        - leaf_to_prove
        - proof elm 0
        - poof elm 1
        Public:
        - expected_root
      */
      
      let mut pw = plonky2::iop::witness::PartialWitness::new();
      // non-public inputs to witness: leaf and elements of merkle proof
      pw.set_hash_target(targets[0], tree.tree[0][3]); // leaf index 3

      pw.set_hash_target(targets[1], merkle_proof_leaf0[0]);
      pw.set_hash_target(targets[2], merkle_proof_leaf0[1]);

      // Public input: root
      let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();
      for i in 0..4 {
        pw.set_target(expected_public_inputs[i], tree.root.elements[i]);
      }

      let proof = circuit_data.prove(pw)?;
      // uncomment to print proof
      // println!("{:?}", proof);

      // Verify proof
      circuit_data.verify(proof)
  }

  #[test]
  fn test_tree_16_leaves_index_0() -> Result<()> {
      // Test tree, 16 leaves
      let tree: MerkleTree = get_test_tree(16);
      let merkle_proof_leaf0 = tree.clone().get_merkle_proof(0);
      println!("{:?}", merkle_proof_leaf0);

      let (circuit_data, targets) = verify_merkle_proof_circuit(0, 4);

      /* The witness needs the following inputs:
        - leaf_to_prove
        - merkle proof elm 0,1,2,3
        Public:
        - expected_root
      */
      
      let mut pw = plonky2::iop::witness::PartialWitness::new();
      // non-public inputs to witness: leaf and elements of merkle proof
      pw.set_hash_target(targets[0], tree.tree[0][0]); // leaf index 0

      pw.set_hash_target(targets[1], merkle_proof_leaf0[0]);
      pw.set_hash_target(targets[2], merkle_proof_leaf0[1]);
      pw.set_hash_target(targets[3], merkle_proof_leaf0[2]);
      pw.set_hash_target(targets[4], merkle_proof_leaf0[3]);

      // public input: root of merkle tree
      let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();
      for i in 0..4 {
        pw.set_target(expected_public_inputs[i], tree.root.elements[i]);
      }

      let proof = circuit_data.prove(pw)?;
      // uncomment to print proof
      // println!("{:?}", proof);

      // Verify proof
      circuit_data.verify(proof)
  }

  #[test]
  fn test_tree_16_leaves_index_7() -> Result<()> {
      // Test tree, 16 leaves
      let tree: MerkleTree = get_test_tree(16);
      let merkle_proof_leaf7 = tree.clone().get_merkle_proof(7);
      println!("{:?}", merkle_proof_leaf7);

      let (circuit_data, targets) = verify_merkle_proof_circuit(7, 4);

      /* The witness needs the following inputs:
        - leaf_to_prove
        - merkle proof elm 0,1,2,3
        Public: 
        - expected_root
      */
      
      let mut pw = plonky2::iop::witness::PartialWitness::new();
      // non-piblic input: leaf hash and merkle proof elements
      pw.set_hash_target(targets[0], tree.tree[0][7]);
      pw.set_hash_target(targets[1], merkle_proof_leaf7[0]);
      pw.set_hash_target(targets[2], merkle_proof_leaf7[1]);
      pw.set_hash_target(targets[3], merkle_proof_leaf7[2]);
      pw.set_hash_target(targets[4], merkle_proof_leaf7[3]);

      // Public input: root
      let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();
      for i in 0..4 {
        pw.set_target(expected_public_inputs[i], tree.root.elements[i]);
      }

      let proof = circuit_data.prove(pw)?;
      // uncomment to print proof
      // println!("{:?}", proof);

      // Verify proof
      circuit_data.verify(proof)
  }
 
}