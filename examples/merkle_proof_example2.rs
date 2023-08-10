use anyhow::Result;
use plonky2::{plonk::{config::{PoseidonGoldilocksConfig, GenericConfig, Hasher}, circuit_builder::CircuitBuilder, circuit_data::{CircuitConfig, VerifierOnlyCircuitData, CommonCircuitData, CircuitData, VerifierCircuitTarget}, proof::{self, ProofWithPublicInputsTarget, ProofWithPublicInputs}}, hash::{hash_types::{RichField, HashOut, HashOutTarget}, poseidon::PoseidonHash}, iop::{witness::{WitnessWrite, PartialWitness}, target::Target}, field::{goldilocks_field::GoldilocksField, types::Field}};

/**
 * Recursive zkp for verifying merkle proof.
 * This has practice/educational purpose: try see how a recursive proof in Plonky2 works
 * 
 * There is a proof for each layer of the merkle tree.
 * For each next layer, the proof for the previous layer is incorporated and proven. 
 * This repeatedly until getting to the root and ending up with 1 proof that verifies the complete merkle proof for a leaf. 
 * 
 */

 // Returns circuit for proving that 2 leave values hashed together result in the public input hash
 pub fn initial_proof_circuit() -> (CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>, Vec<HashOutTarget>) {
  // takes leaf and sibling as witness data
  // public input is next hash (the result)
  // "constraint": hashed leaf & sibling data, this should be equal to public data

  const D: usize = 2;
  type C = PoseidonGoldilocksConfig;
  type F = <C as GenericConfig<D>>::F;

  // targets that must be filled by witness
  let mut w_targets: Vec<HashOutTarget> = Vec::new();

  let config = CircuitConfig::standard_recursion_config();
  let mut builder: CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2> = CircuitBuilder::<F, D>::new(config);

  let left_hash_target = builder.add_virtual_hash();
  let right_hash_target = builder.add_virtual_hash();
  w_targets.push(left_hash_target);
  w_targets.push(right_hash_target);

  let merkle_digest_target = builder.hash_or_noop::<PoseidonHash>([
    left_hash_target.elements.to_vec(), 
    right_hash_target.elements.to_vec()
  ].concat());

  // Register the digest of the 2 leafs as public input
  builder.register_public_inputs(&merkle_digest_target.elements);

  (builder.build::<C>(), w_targets)
 }


 // Takes a previous proof + a new input value and returns a circuit for:
 // - verifying previous proof 
 // - "output" of previous proof (= the public input) hashed together with new input value should equal new public input
 pub fn recursive_step(
  previous_proof_circuit_data_common: CommonCircuitData<GoldilocksField, 2>, 
  sibling_right_side: bool)-> (CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>, ProofWithPublicInputsTarget<2>, VerifierCircuitTarget, Vec<HashOutTarget>) {
  // takes previous proof, previous output hash and sibling
  // public input is next hash
  // verifies previous proof
  // hashed prev output & sibling data, this should be equal to public data

  const D: usize = 2;
  type C = PoseidonGoldilocksConfig;
  type F = <C as GenericConfig<D>>::F;

  let config = CircuitConfig::standard_recursion_config();
  let mut builder: CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2> = CircuitBuilder::<F, D>::new(config);

  let input_hash = builder.add_virtual_hash();

  let prev_proof_target = 
    builder.add_virtual_proof_with_pis(&previous_proof_circuit_data_common);
    
  let prev_proof_verifier_data = 
    builder.add_virtual_verifier_data(previous_proof_circuit_data_common.config.fri_config.cap_height);

  // The public input of the previous proof (the "output" one might say), 
  //  is connected to one of the input for current proof
  input_hash.elements.iter()
  .zip(&prev_proof_target.public_inputs[0..4])
  .for_each(|(e1, e2)| {
    builder.connect(*e1, *e2);
  });

  builder.verify_proof::<PoseidonGoldilocksConfig>(
    &prev_proof_target, 
    &prev_proof_verifier_data, 
    &previous_proof_circuit_data_common);

  // targets that must be filled by witness
  let mut targets: Vec<HashOutTarget> = Vec::new();

  if sibling_right_side {
    // Add target for sibling hash (that's on the right)
    let right_hash_target = builder.add_virtual_hash();
    targets.push(right_hash_target);
    let merkle_digest_target = builder.hash_or_noop::<PoseidonHash>([
      input_hash.elements.to_vec(), 
      right_hash_target.elements.to_vec()
    ].concat());
    // Add target for merkle digest of this level to public inputs
    builder.register_public_inputs(&merkle_digest_target.elements);
  } else {
    // Add target for sibling hash (that's on the left)
    let left_hash_target = builder.add_virtual_hash();
    targets.push(left_hash_target);
    let merkle_digest_target = builder.hash_or_noop::<PoseidonHash>([
      left_hash_target.elements.to_vec(),
      input_hash.elements.to_vec()
    ].concat());
    // Add target for merkle digest of this level to public inputs
    builder.register_public_inputs(&merkle_digest_target.elements);
  }
  
  (builder.build::<C>(), prev_proof_target, prev_proof_verifier_data, targets)
}


// Returns circuitdata and proof verifying a merkleproof for 1 leaf recursively
// per layer in the merkle tree, we have 1 proof
// the proof of the previous layer is incorporated in the current layer, and so on continuously 
//    until ending up with a single proof for the count_level layers
// Input:
// - leaf_index; to determine the path that is taken and thus at which step what value is left and what value is right
// - leaf_value: the leaf we're verifying the merkle_proof of
// - merkle_proof
// - in_between_hashes: the resulting intermediate values. All intermediate proofs are verifying the validity of an intermediate step, hence the need for these intermediate values
pub fn verify_merkle_proof_circuit_and_proof(
  leaf_index: usize, 
  leaf_value: HashOut<GoldilocksField>,
  merkle_proof: Vec<HashOut<GoldilocksField>>,
  in_between_hashes: Vec<HashOut<GoldilocksField>>) -> (CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>, ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2>) {
  // first creates the initial proof
  let (initial_circuit_data, initial_targets) = 
    initial_proof_circuit();
  let initial_circuit_verifier_data = 
    initial_circuit_data.verifier_only.clone();

  let mut pw = plonky2::iop::witness::PartialWitness::new();
  let mut current_leaf_index = leaf_index;
  if current_leaf_index % 2 == 0 {
    pw.set_hash_target(initial_targets[0], leaf_value);
    pw.set_hash_target(initial_targets[1], merkle_proof[0]);
  } else {
    pw.set_hash_target(initial_targets[0], merkle_proof[0]);
    pw.set_hash_target(initial_targets[1], leaf_value);
  }

  current_leaf_index = current_leaf_index/2;
  let expected_public_inputs = initial_circuit_data.prover_only.public_inputs.clone();
  for i in 0..4 {
    pw.set_target(expected_public_inputs[i], in_between_hashes[0].elements[i]);
  }

  let mut prev_circuit_data_common = initial_circuit_data.common.clone();
  let mut prev_proof = initial_circuit_data.prove(pw).unwrap();
  let mut prev_verifier_data = initial_circuit_verifier_data;

  // This is the final data to return
  let mut final_circuit = initial_circuit_data; 

  // goes through the nr of layers of the merkle tree for the recursive steps until the root
  for i in 1..merkle_proof.len() {
    let mut current_pw = plonky2::iop::witness::PartialWitness::new();

    let siblings_right_side = current_leaf_index % 2 == 0;
    let (next_circuit_data, 
      prev_proof_target, 
      v_data_target, 
      new_targets) = recursive_step(prev_circuit_data_common, siblings_right_side);
    // Set the witness values (the proof must be created to be incorporated in recursive step)
    current_pw.set_hash_target(new_targets[0], merkle_proof[i]);
    current_pw.set_proof_with_pis_target(&prev_proof_target, &prev_proof);
    current_pw.set_verifier_data_target(
      &v_data_target,
      &prev_verifier_data,
    );

    // Public input for this step
    let expected_public_inputs = next_circuit_data.prover_only.public_inputs.clone();
    for j in 0..4 {
      current_pw.set_target(expected_public_inputs[j], in_between_hashes[i].elements[j]);
    }

    // Update values for next iteration
    prev_circuit_data_common = next_circuit_data.common.clone();
    prev_proof = next_circuit_data.prove(current_pw).unwrap(); // Current step gets proven to be incorporated in next step
    prev_verifier_data = next_circuit_data.verifier_only.clone();
    // Get ready for next layer
    current_leaf_index = current_leaf_index/2;

    final_circuit = next_circuit_data;
  }

  (final_circuit, prev_proof)
}

#[cfg(test)]
mod tests {
  use anyhow::Result;
  use plonky2::{plonk::config::{PoseidonGoldilocksConfig, GenericConfig, Hasher}, hash::{poseidon::PoseidonHash, hash_types::{RichField, HashOut}}, iop::witness::WitnessWrite, gates::poseidon::PoseidonGenerator};
use plonky2_field::{goldilocks_field::GoldilocksField, types::{Field, Sample}};
  use plonky2_merkle_trees::simple_merkle_tree::simple_merkle_tree::MerkleTree;
use rand::Rng;

  use crate::{initial_proof_circuit, recursive_step, verify_merkle_proof_circuit_and_proof};
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

    let (initial_circuit_data, targets) = initial_proof_circuit();
    let initial_circuit_verifier_data = &initial_circuit_data.verifier_only.clone();

    let mut pw = plonky2::iop::witness::PartialWitness::new();
    pw.set_hash_target(targets[0], tree.tree[0][0]); // leaf index 0
    pw.set_hash_target(targets[1], merkle_proof_leaf0[0]); // leaf index 1 (first elm of merkle proof)

    // // Test if level 1 works
    let proof = initial_circuit_data.prove(pw.clone())?;
    // initial_circuit_data.verify(proof)

    //////// RECURSIVE STEP ////////
    /// The proof for the first 2 leaves is folded into the circuit for the next step that checks the next level in the Merkle Proof
    let (recursive_step_circuit_data, 
      prev_proof_target,
      inner_data, 
      rec_targets) = 
      recursive_step(initial_circuit_data.common, true);

    let mut pw_new = plonky2::iop::witness::PartialWitness::new();
    
    // Set the next input hash (= next elm in merkle proof)
    pw_new.set_hash_target(rec_targets[0], merkle_proof_leaf0[1]);
    let rec_expected_public_inputs = recursive_step_circuit_data.prover_only.public_inputs.clone();

    // Set the expected next hash, in this case the root
    for i in 0..4 {
      pw_new.set_target(rec_expected_public_inputs[i], tree.root.elements[i]);
    }

    // Set the targets wrt to the previous proof
    pw_new.set_proof_with_pis_target(&prev_proof_target, &proof);
    pw_new.set_verifier_data_target(
      &inner_data,
      initial_circuit_verifier_data,
    );

    let proof = recursive_step_circuit_data.prove(pw_new)?;
    // uncomment to print proof
    // println!("{:?}", proof);

    // Verify proof
    recursive_step_circuit_data.verify(proof)
  }

  #[test]
  #[should_panic]
  fn test_wrong_pub_input_tree_4_leaves_index0() {
    // Sets wrong public input

    // Test tree, 4 leaves
    let tree: MerkleTree = get_test_tree(4);
    let merkle_proof_leaf0 = tree.clone().get_merkle_proof(0);

    let (initial_circuit_data, targets) = initial_proof_circuit();
    let initial_circuit_verifier_data = &initial_circuit_data.verifier_only.clone();

    let mut pw = plonky2::iop::witness::PartialWitness::new();
    pw.set_hash_target(targets[0], tree.tree[0][0]); // leaf index 0
    pw.set_hash_target(targets[1], merkle_proof_leaf0[0]); // leaf index 1 (first elm of merkle proof)

    let proof = initial_circuit_data.prove(pw.clone()).unwrap();

    //////// RECURSIVE STEP ////////
    /// The proof for the first 2 leaves is folded into the circuit for the next step that checks the next level in the Merkle Proof
    let (recursive_step_circuit_data, 
      prev_proof_target,
      inner_data, 
      rec_targets) = 
      recursive_step(initial_circuit_data.common, true);

    let mut pw_new = plonky2::iop::witness::PartialWitness::new();
    
    // Set the next input hash (= next elm in merkle proof)
    pw_new.set_hash_target(rec_targets[0], merkle_proof_leaf0[1]);
    let rec_expected_public_inputs = recursive_step_circuit_data.prover_only.public_inputs.clone();

    for i in 0..4 {
      // This is the wrong value; should be root value and is the initial leaf value. Thus proof must fail
      pw_new.set_target(rec_expected_public_inputs[i], tree.tree[0][0].elements[i]);
    }

    // Set the targets wrt to the previous proof
    pw_new.set_proof_with_pis_target(&prev_proof_target, &proof);
    pw_new.set_verifier_data_target(
      &inner_data,
      initial_circuit_verifier_data,
    );

    let proof = recursive_step_circuit_data.prove(pw_new).unwrap();

    // Verify proof
    recursive_step_circuit_data.verify(proof);
  }

  #[test]
  #[should_panic]
  fn test_wrong_sibling_side_tree_4_leaves_index0() {
    // Passes wrong information about which side the leaf is on
    // Test tree, 4 leaves
    let tree: MerkleTree = get_test_tree(4);

    let merkle_proof_leaf0 = tree.clone().get_merkle_proof(0);

    let (initial_circuit_data, targets) = initial_proof_circuit();
    let initial_circuit_verifier_data = &initial_circuit_data.verifier_only.clone();

    let mut pw = plonky2::iop::witness::PartialWitness::new();
    pw.set_hash_target(targets[0], tree.tree[0][0]); // leaf index 0
    pw.set_hash_target(targets[1], merkle_proof_leaf0[0]); // leaf index 1 (first elm of merkle proof)

    // // Test if level 1 works
    let proof = initial_circuit_data.prove(pw.clone()).unwrap();
    // initial_circuit_data.verify(proof)

    //////// RECURSIVE STEP ////////
    /// The proof for the first 2 leaves is folded into the circuit for the next step that checks the next level in the Merkle Proof
    let (recursive_step_circuit_data, 
      prev_proof_target,
      inner_data, 
      rec_targets) = 
      recursive_step(initial_circuit_data.common, false);

    let mut pw_new = plonky2::iop::witness::PartialWitness::new();
    
    // Set the next input hash (= next elm in merkle proof)
    pw_new.set_hash_target(rec_targets[0], merkle_proof_leaf0[1]);
    let rec_expected_public_inputs = recursive_step_circuit_data.prover_only.public_inputs.clone();

    // Set the expected next hash, in this case the root
    for i in 0..4 {
      pw_new.set_target(rec_expected_public_inputs[i], tree.root.elements[i]);
    }

    // Set the targets wrt to the previous proof
    pw_new.set_proof_with_pis_target(&prev_proof_target, &proof);
    pw_new.set_verifier_data_target(
      &inner_data,
      initial_circuit_verifier_data,
    );

    let proof = recursive_step_circuit_data.prove(pw_new).unwrap();
    // uncomment to print proof
    // println!("{:?}", proof);

    // Verify proof
    recursive_step_circuit_data.verify(proof);
  }

  #[test]
  #[should_panic]
  fn test_wrong_right_leaf_tree_4_leaves_index0() {
    // Wrong right leaf input

    // Test tree, 4 leaves
    let tree: MerkleTree = get_test_tree(4);

    let merkle_proof_leaf0 = tree.clone().get_merkle_proof(0);

    let (initial_circuit_data, targets) = initial_proof_circuit();
    let initial_circuit_verifier_data = &initial_circuit_data.verifier_only.clone();

    let mut pw = plonky2::iop::witness::PartialWitness::new();
    pw.set_hash_target(targets[0], tree.tree[0][0]); // leaf index 0
    pw.set_hash_target(targets[1],tree.tree[0][0]); // WRONG INFO: this is leaf index 0 again, while it should be the first elm of the Merkle proof

    // // Test if level 1 works
    let proof = initial_circuit_data.prove(pw.clone()).unwrap();
    // initial_circuit_data.verify(proof)

    //////// RECURSIVE STEP ////////
    /// The proof for the first 2 leaves is folded into the circuit for the next step that checks the next level in the Merkle Proof
    let (recursive_step_circuit_data, 
      prev_proof_target,
      inner_data, 
      rec_targets) = 
      recursive_step(initial_circuit_data.common, true);

    let mut pw_new = plonky2::iop::witness::PartialWitness::new();
    
    // Set the next input hash (= next elm in merkle proof)
    pw_new.set_hash_target(rec_targets[0], merkle_proof_leaf0[1]);
    let rec_expected_public_inputs = recursive_step_circuit_data.prover_only.public_inputs.clone();

    // Set the expected next hash, in this case the root
    for i in 0..4 {
      pw_new.set_target(rec_expected_public_inputs[i], tree.root.elements[i]);
    }

    // Set the targets wrt to the previous proof
    pw_new.set_proof_with_pis_target(&prev_proof_target, &proof);
    pw_new.set_verifier_data_target(
      &inner_data,
      initial_circuit_verifier_data,
    );

    let proof = recursive_step_circuit_data.prove(pw_new).unwrap();
    // uncomment to print proof
    // println!("{:?}", proof);

    // Verify proof
    recursive_step_circuit_data.verify(proof);
  }

  #[test]
  fn test_tree_4_leaves_index3() -> Result<()> {
    // Test tree, 4 leaves
    let tree: MerkleTree = get_test_tree(4);

    let merkle_proof_leaf0 = tree.clone().get_merkle_proof(3);

    let (initial_circuit_data, targets) = initial_proof_circuit();
    let initial_circuit_verifier_data = &initial_circuit_data.verifier_only.clone();

    let mut pw = plonky2::iop::witness::PartialWitness::new();
    // Leaf with index 3 is on the left side of the pair, so notice the order
    pw.set_hash_target(targets[0], merkle_proof_leaf0[0]); // leaf index 3
    pw.set_hash_target(targets[1], tree.tree[0][3]); // leaf index 1 (first elm of merkle proof)

    // // Test if level 1 works
    let proof = initial_circuit_data.prove(pw.clone())?;
    // initial_circuit_data.verify(proof)

    //////// RECURSIVE STEP ////////
    /// The proof for the first 2 leaves is folded into the circuit for the next step that checks the next level in the Merkle Proof
    let (recursive_step_circuit_data, 
      prev_proof_target,
      inner_data, 
      rec_targets) = 
      recursive_step(initial_circuit_data.common, false);

    let mut pw_new = plonky2::iop::witness::PartialWitness::new();
    
    // Set the next input hash (= next elm in merkle proof)
    pw_new.set_hash_target(rec_targets[0], merkle_proof_leaf0[1]);
    let rec_expected_public_inputs = recursive_step_circuit_data.prover_only.public_inputs.clone();

    // Set the expected next hash, in this case the root
    for i in 0..4 {
      pw_new.set_target(rec_expected_public_inputs[i], tree.root.elements[i]);
    }

    // Set the targets wrt to the previous proof
    pw_new.set_proof_with_pis_target(&prev_proof_target, &proof);
    pw_new.set_verifier_data_target(
      &inner_data,
      initial_circuit_verifier_data,
    );

    let proof = recursive_step_circuit_data.prove(pw_new)?;
    // uncomment to print proof
    // println!("{:?}", proof);

    // Verify proof
    recursive_step_circuit_data.verify(proof)
  }

  #[test]
  fn recursive_test_tree_4_leaves_index0() -> Result<()> {
    // Test tree, 4 leaves
    let tree: MerkleTree = get_test_tree(4);

    let merkle_proof_leaf0 = tree.clone().get_merkle_proof(0);

    //These are used for public input
    let in_between_hashes = tree.clone().get_in_between_hashes(0);

    let (circuit, recursive_proof) = 
      verify_merkle_proof_circuit_and_proof(
        0, 
        tree.clone().tree[0][0], 
        merkle_proof_leaf0, 
        in_between_hashes);
    circuit.verify(recursive_proof)
  }

  #[test]
  #[should_panic]
  fn recursive_test_wrong_proof_tree_4_leaves_index0() {
    // Passes wrong merkle_proof
    // Test tree, 4 leaves
    let tree: MerkleTree = get_test_tree(4);
    println!("{:?}", tree);

    let merkle_proof_leaf0 = tree.clone().get_merkle_proof(0);
    println!("{:?}", merkle_proof_leaf0);
    //These are used for public input
    let in_between_hashes = tree.clone().get_in_between_hashes(0);

    // The merkle proof is for leaf 0, but the leaf value passed in is index 1
    let (circuit, recursive_proof) = 
      verify_merkle_proof_circuit_and_proof(1, tree.tree[0][1], merkle_proof_leaf0, in_between_hashes);
    circuit.verify(recursive_proof);
  }

  #[test]
  #[should_panic]
  fn recursive_test_wrong_index_tree_4_leaves_index0() {
    // Passes wrong leaf index
    // Test tree, 4 leaves
    let tree: MerkleTree = get_test_tree(4);
    println!("{:?}", tree);

    let merkle_proof_leaf0 = tree.clone().get_merkle_proof(0);
    println!("{:?}", merkle_proof_leaf0);
    //These are used for public input
    let in_between_hashes = tree.clone().get_in_between_hashes(0);

    // The merkle proof is for leaf 0, but the leaf index is 1
    let (circuit, recursive_proof) = 
      verify_merkle_proof_circuit_and_proof(1, tree.tree[0][0], merkle_proof_leaf0, in_between_hashes);
    circuit.verify(recursive_proof);
  }

  #[test]
  fn recursive_test_tree_4_leaves_index1() -> Result<()> {
    // Test tree, 4 leaves
    let tree: MerkleTree = get_test_tree(4);

    let merkle_proof_leaf1 = tree.clone().get_merkle_proof(1);
    //These are used for public input
    let in_between_hashes = tree.clone().get_in_between_hashes(1);

    let (circuit, recursive_proof) = 
      verify_merkle_proof_circuit_and_proof(1, tree.tree[0][1], merkle_proof_leaf1, in_between_hashes);
    circuit.verify(recursive_proof)
  }

  #[test]
  fn recursive_test_tree_16_leaves_index0() -> Result<()> {
    // Test tree, 16 leaves
    let tree: MerkleTree = get_test_tree(16);

    let merkle_proof_leaf0 = tree.clone().get_merkle_proof(0);
    //These are used for public input
    let in_between_hashes = tree.clone().get_in_between_hashes(0);

    let (circuit, recursive_proof) = 
      verify_merkle_proof_circuit_and_proof(0, tree.tree[0][0], merkle_proof_leaf0, in_between_hashes);
    circuit.verify(recursive_proof)
  }

  #[test]
  #[should_panic]
  fn recursive_test_wrong_proof_tree_16_leaves_index0() {
    // Passes wrong merkle_proof
    // Test tree, 16 leaves
    let tree: MerkleTree = get_test_tree(16);
    let merkle_proof_leaf1 = tree.clone().get_merkle_proof(1);
    //These are used for public input
    let in_between_hashes = tree.clone().get_in_between_hashes(1);

    // The merkle proof is for leaf 0, but the proof passed is for leaf 1
    let (circuit, recursive_proof) = 
      verify_merkle_proof_circuit_and_proof(0, tree.tree[0][0], merkle_proof_leaf1, in_between_hashes);
    circuit.verify(recursive_proof);
  }

  #[test]
  fn recursive_test_tree_16_leaves_index13() -> Result<()> {
    // Test tree, 16 leaves
    let tree: MerkleTree = get_test_tree(16);

    let merkle_proof_leaf13 = tree.clone().get_merkle_proof(13);
    //These are used for public input
    let in_between_hashes = tree.clone().get_in_between_hashes(13);

    let (circuit, recursive_proof) = 
      verify_merkle_proof_circuit_and_proof(13, tree.tree[0][13], merkle_proof_leaf13, in_between_hashes);
    circuit.verify(recursive_proof)
  }

  #[test]
  #[should_panic]
  fn recursive_test_wrong_index_16_leaves_index13() {
    // Passes wrong merkle_proof
    // Test tree, 16 leaves
    let tree: MerkleTree = get_test_tree(16);
    let merkle_proof_leaf13 = tree.clone().get_merkle_proof(13);
    //These are used for public input
    let in_between_hashes = tree.clone().get_in_between_hashes(13);

    // The merkle proof is for leaf 13, but the index passed is 0
    let (circuit, recursive_proof) = 
      verify_merkle_proof_circuit_and_proof(0, tree.tree[0][13], merkle_proof_leaf13, in_between_hashes);
    circuit.verify(recursive_proof);
  }

  #[test]
  fn recursive_test_tree_32_leaves_index13() -> Result<()> {
    // Test tree, 32 leaves
    let tree: MerkleTree = get_test_tree(32);

    let merkle_proof_leaf13 = tree.clone().get_merkle_proof(13);
    //These are used for public input
    let in_between_hashes = tree.clone().get_in_between_hashes(13);

    let (circuit, recursive_proof) = 
      verify_merkle_proof_circuit_and_proof(13, tree.tree[0][13], merkle_proof_leaf13, in_between_hashes);
    circuit.verify(recursive_proof)
  }

  #[test]
  fn recursive_test_tree_128_leaves_index111() -> Result<()> {
    // Test tree, 128 leaves
    let tree: MerkleTree = get_test_tree(128);

    let merkle_proof_leaf111 = tree.clone().get_merkle_proof(111);
    //These are used for public input
    let in_between_hashes = tree.clone().get_in_between_hashes(111);

    let (circuit, recursive_proof) = 
      verify_merkle_proof_circuit_and_proof(111, tree.tree[0][111], merkle_proof_leaf111, in_between_hashes);
    circuit.verify(recursive_proof)
  }

  #[test]
  #[should_panic]
  fn recursive_test_wrong_proof_128_leaves_index80() {
    // Passes wrong merkle_proof
    // Test tree, 128 leaves
    let tree: MerkleTree = get_test_tree(128);
    let merkle_proof_leaf80 = tree.clone().get_merkle_proof(80);
    //These are used for public input
    let in_between_hashes = tree.clone().get_in_between_hashes(80);

    // The merkle proof is for leaf 80, but the index and leaf value passed are for 79
    let (circuit, recursive_proof) = 
      verify_merkle_proof_circuit_and_proof(79, tree.tree[0][79], merkle_proof_leaf80, in_between_hashes);
    circuit.verify(recursive_proof);
  }
}