use itertools::Itertools;
use num::ToPrimitive;
use plonky2::{plonk::{config::{PoseidonGoldilocksConfig, GenericConfig}, circuit_data::{CircuitData, CircuitConfig, CommonCircuitData, VerifierCircuitTarget}, circuit_builder::CircuitBuilder, proof::ProofWithPublicInputsTarget}, hash::{poseidon::PoseidonHash, hash_types::HashOutTarget}, iop::target::BoolTarget};
use plonky2_field::goldilocks_field::GoldilocksField;

use crate::mmr::{naive_merkle_mountain_ranges::get_standard_index, common::{equal, or_list}};

/** 
 * An mmr proof consists of 2 parts:
 * (1) inner Merkle proof, that proves a leaf is part of that subtree
 * (2) root check (hashing all peaks of mmr together)
 * 
 * To add recursion within this verification the proof of step 1 can be embedded in the circuit of step 2.
 * That is the strategy used here.
*/

/** Returns a circuit for the (inner) Merkle proof and the accompanying targets that have to be set by the witness
 *    Public input: root of subtree
 *    Inputs: leaf_to_prove (hashed), all elements of Merkle proof (count = nr_proof_elms) 
 */
pub fn verify_inner_merkle_proof_circuit(
  relative_leaf_index: usize, // index of leaf within subtree. This is an MMR index
  nr_proof_elms: usize // nr of layers within subtree
) -> (CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>, Vec<HashOutTarget>) {
  const D: usize = 2;
  type C = PoseidonGoldilocksConfig;
  type F = <C as GenericConfig<D>>::F;

  // targets that must be filled by witness
  let mut targets: Vec<HashOutTarget> = Vec::new();

  let config = CircuitConfig::standard_recursion_config();
  let mut builder: CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2> = CircuitBuilder::<F, D>::new(config);
  // The leaf to prove is in the MMR
  let leaf_to_prove = builder.add_virtual_hash();
  targets.push(leaf_to_prove);
  // The first hashing outside of the loop, since it uses the leaf_to_prove
  let merkle_proof_elm = builder.add_virtual_hash();
  targets.push(merkle_proof_elm);
  let mut next_hash: plonky2::hash::hash_types::HashOutTarget;

  let nr_leaves_subtree = 2i32.pow(nr_proof_elms.to_u32().unwrap()).to_usize().unwrap();
  let standardized_index = get_standard_index(relative_leaf_index, nr_leaves_subtree);

  if standardized_index % 2 == 0 {
    next_hash = builder.hash_or_noop::<PoseidonHash>([
      leaf_to_prove.elements.to_vec(), 
      merkle_proof_elm.elements.to_vec()
    ].concat());
  } else {
    next_hash = builder.hash_or_noop::<PoseidonHash>([
      merkle_proof_elm.elements.to_vec(),
      leaf_to_prove.elements.to_vec()
    ].concat());
  }
  let mut current_layer_index = standardized_index / 2;
  for _layer in 1..nr_proof_elms {
    let merkle_proof_elm= builder.add_virtual_hash();
    targets.push(merkle_proof_elm);

    if current_layer_index % 2 == 0 {
      next_hash = builder.hash_or_noop::<PoseidonHash>([
        next_hash.elements.to_vec(), 
        merkle_proof_elm.elements.to_vec()
      ].concat());
    } else {
      next_hash = builder.hash_or_noop::<PoseidonHash>([
        merkle_proof_elm.elements.to_vec(),
        next_hash.elements.to_vec()
      ].concat());
    }
    current_layer_index = current_layer_index/2;
  }

  // The proof is complete by checking the result equals the root of the subtree
  builder.register_public_inputs(&next_hash.elements);

  let data = builder.build::<C>();
  (data, targets)
}

// This is the same as for the non-naive impl
/**
 * Returns a circuit for the outer proof, which does the following:
 * - verifies inner proof
 * - checks that the resulting hash of the inner proof is part of the peaks
 * - checks the root is correct
 */
pub fn complete_verification_circuit_with_inner_proof(
  inner_proof_circuit_data_common: CommonCircuitData<GoldilocksField, 2>, 
  nr_peaks: usize
) -> (CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>, ProofWithPublicInputsTarget<2>, VerifierCircuitTarget, Vec<HashOutTarget>) {
  const D: usize = 2;
  type C = PoseidonGoldilocksConfig;
  type F = <C as GenericConfig<D>>::F;

  let config = CircuitConfig::standard_recursion_config();
  let mut builder: CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2> = CircuitBuilder::<F, D>::new(config);

  let prev_proof_target = 
    builder.add_virtual_proof_with_pis(&inner_proof_circuit_data_common);
  
  let prev_proof_verifier_data = 
    builder.add_virtual_verifier_data(inner_proof_circuit_data_common.config.fri_config.cap_height);

  builder.verify_proof::<PoseidonGoldilocksConfig>(
    &prev_proof_target, 
    &prev_proof_verifier_data, 
    &inner_proof_circuit_data_common);
  
  let mut targets: Vec<HashOutTarget> = Vec::new();

  // Hash all peaks together
  let mut peaks: Vec<HashOutTarget> = Vec::new();
  let mut equals: Vec<BoolTarget> = Vec::new();
  let prev_hash = HashOutTarget::from_vec(prev_proof_target.public_inputs[0..4].to_vec());
  for _peaks in 0..nr_peaks {
    let peak = builder.add_virtual_hash();
    peaks.push(peak);
    targets.push(peak);
    let equals_peak: BoolTarget = equal(&mut builder, peak, prev_hash);
    equals.push(equals_peak);
  }
  // Check that the resulting hash of the merkle proof appears in the given peaks
  let hash_in_peaks = or_list(&mut builder, equals);
  // check that its "true"
  let one: plonky2::iop::target::Target = builder.one();
  builder.connect(one, hash_in_peaks.target); 

  if peaks.len() > 1 {
    let root = builder.hash_n_to_hash_no_pad::<PoseidonHash>(peaks.into_iter().flat_map(|x| x.elements).collect_vec());
    // This is the expected root value (bagged MMR)
    builder.register_public_inputs(&root.elements);
  } else {
    // If there's only 1 peak, the root will be equal to that peak
    builder.register_public_inputs(&peaks[0].elements);
  }

  // Returns:
  // - Current circuit
  // - target where previous proof has to be added in witness
  // - target where previous verifier data has to be added in witness
  // - targets to set for this circuit wrt other checks that will be done
  (builder.build::<C>(), prev_proof_target, prev_proof_verifier_data, targets)
}

#[cfg(test)]
mod tests {
  use anyhow::Result;
  use plonky2::{plonk::config::PoseidonGoldilocksConfig, iop::witness::WitnessWrite};
  use plonky2_field::{goldilocks_field::GoldilocksField, types::Field};
  use rand::Rng;

  use crate::mmr::naive_merkle_mountain_ranges::naive_MMR;

  use super::{verify_inner_merkle_proof_circuit, complete_verification_circuit_with_inner_proof};
  const GOLDILOCKS_FIELD_ORDER: u64 = 18446744069414584321;

  pub fn do_test_verify_inner_proof(nr_leaves: usize, leaf_index: usize) -> Result<()> {
    let mut rng = rand::thread_rng();
    let leaf0 = GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER));
    let mut mmr = naive_MMR::new(leaf0);
    for _ in 0..(nr_leaves-1) {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    // This returns
    // (merkle proof for leaf within subtree, peaks in mmr (before bagging the peaks), leaf index within the subtree)
    // Note that the merkle proof also contains the root of the subtree; we need this to chop the verification up in 2 parts 
    let pr = mmr.clone().get_proof_with_extended_merkleproof(leaf_index);

    let (circuit_data, targets) = verify_inner_merkle_proof_circuit(
      pr.2,
      pr.0.len()-1
    );

    let mut pw = plonky2::iop::witness::PartialWitness::new();
    pw.set_hash_target(targets[0], mmr.elements[leaf_index]); // hashed leaf to prove
    // Add the proof elements (do not add the root)
    for i in 0..pr.0.len()-1 {
      pw.set_hash_target(targets[1 + i], pr.0[i]);
    }
    
    let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();
    // The public input is the root of this subtree
    let subtree_root = pr.0[pr.0.len()-1];
    for i in 0..4 {
      pw.set_target(expected_public_inputs[i], subtree_root.elements[i]);
    }
    let proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      circuit_data.prove(pw)?;

    circuit_data.verify(proof)

  }

  #[test]
  fn verify_inner_proof_2_leaves_index1() -> Result<()> {
    do_test_verify_inner_proof(2, 0)
  }

  #[test]
  fn verify_inner_proof_12_leaves_index16() -> Result<()> {
    do_test_verify_inner_proof(12, 16)
  }

  pub fn test_complete_verification_circuit_with_inner_proof(nr_leaves: usize, leaf_index: usize) -> Result<()> {
    let mut rng = rand::thread_rng();
    let leaf0 = GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER));
    let mut mmr = naive_MMR::new(leaf0);
    for _ in 0..(nr_leaves-1) {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    // This returns
    // (merkle proof for leaf within subtree, peaks in mmr (before bagging the peaks), leaf index within the subtree)
    // Note that the merkle proof also contains the root of the subtree; we need this to chop the verification up in 2 parts 
    let pr = mmr.clone().get_proof_with_extended_merkleproof(leaf_index);

    let (inner_circuit_data, targets) = verify_inner_merkle_proof_circuit(
      pr.2,
      pr.0.len()-1
    );

    let mut pw1 = plonky2::iop::witness::PartialWitness::new();
    pw1.set_hash_target(targets[0], mmr.elements[leaf_index]); // hashed leaf to prove
    // Add the proof elements (do not add the root)
    for i in 0..pr.0.len()-1 {
      pw1.set_hash_target(targets[1 + i], pr.0[i]);
    }
    
    let expected_public_inputs = inner_circuit_data.prover_only.public_inputs.clone();
    // The public input is the root of this subtree
    let subtree_root = pr.0[pr.0.len()-1];
    for i in 0..4 {
      pw1.set_target(expected_public_inputs[i], subtree_root.elements[i]);
    }
    let inner_proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      inner_circuit_data.prove(pw1).unwrap();

    let (main_circuit_data, inner_proof_target, inner_verifier_data_target, targets) = 
      complete_verification_circuit_with_inner_proof(inner_circuit_data.common, mmr.peaks.len());

    let mut pw2 = plonky2::iop::witness::PartialWitness::new();
    pw2.set_proof_with_pis_target(&inner_proof_target, &inner_proof);
    pw2.set_verifier_data_target(&inner_verifier_data_target, &inner_circuit_data.verifier_only);

    // Add all peaks to witness
    for i in 0..pr.1.len() {
      pw2.set_hash_target(targets[i], pr.1[i]);
    }

    let mmr_bagged = mmr.clone().bagging_the_peaks();

    // The public input is the root of mmr_bagged
    let expected_public_inputs_main = main_circuit_data.prover_only.public_inputs.clone();
    for i in 0..4 {
      pw2.set_target(expected_public_inputs_main[i], mmr_bagged.root.elements[i]);
    }
    let final_proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      main_circuit_data.prove(pw2)?;

    main_circuit_data.verify(final_proof)
  }

  #[test]
  fn verify_full_proof_2_leaves_index0() -> Result<()> {
    test_complete_verification_circuit_with_inner_proof(2, 0)
  }

  #[test]
  fn verify_full_proof_32_leaves_index0() -> Result<()> {
    test_complete_verification_circuit_with_inner_proof(32, 0)
  }

  #[test]
  fn verify_proof_32_leaves_index56() -> Result<()> {
    test_complete_verification_circuit_with_inner_proof(32, 56)
  }

  #[test]
  fn verify_proof_12_leaves_index16() -> Result<()> {
    test_complete_verification_circuit_with_inner_proof(12, 16)
  }
  
  #[test]
  fn verify_proof_1001_leaves_index56() -> Result<()> {
    test_complete_verification_circuit_with_inner_proof(10101, 56)
  }

  #[test]
  #[should_panic]
  fn test_complete_verification_circuit_with_wrong_inner_proof() {
    let nr_leaves = 16;
    let leaf_index = 0;
    let mut rng = rand::thread_rng();
    let leaf0 = GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER));
    let mut mmr = naive_MMR::new(leaf0);
    for _ in 0..(nr_leaves-1) {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    // Inner proof is for leaf 0
    let pr = mmr.clone().get_proof_with_extended_merkleproof(leaf_index);

    let (inner_circuit_data, targets) = verify_inner_merkle_proof_circuit(
      pr.2,
      pr.0.len()-1
    );

    let mut pw1 = plonky2::iop::witness::PartialWitness::new();
    pw1.set_hash_target(targets[0], mmr.elements[leaf_index+1]); // wrong leaf, so this should fail!!
    // Add the proof elements (do not add the root)
    for i in 0..pr.0.len()-1 {
      pw1.set_hash_target(targets[1 + i], pr.0[i]);
    }
    
    let expected_public_inputs = inner_circuit_data.prover_only.public_inputs.clone();
    // The public input is the root of this subtree
    let subtree_root = pr.0[pr.0.len()-1];
    for i in 0..4 {
      pw1.set_target(expected_public_inputs[i], subtree_root.elements[i]);
    }
    let inner_proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      inner_circuit_data.prove(pw1).unwrap();

    let (main_circuit_data, inner_proof_target, inner_verifier_data_target, targets) = 
      complete_verification_circuit_with_inner_proof(inner_circuit_data.common, mmr.peaks.len());

    // Outer proof is for leaf 3
    let mut pw2 = plonky2::iop::witness::PartialWitness::new();
    pw2.set_proof_with_pis_target(&inner_proof_target, &inner_proof);
    pw2.set_verifier_data_target(&inner_verifier_data_target, &inner_circuit_data.verifier_only);

    // Add all peaks to witness
    for i in 0..pr.1.len() {
      pw2.set_hash_target(targets[i], pr.1[i]);
    }

    let mmr_bagged = mmr.clone().bagging_the_peaks();

    // The public input is the root of mmr_bagged
    let expected_public_inputs_main = main_circuit_data.prover_only.public_inputs.clone();
    for i in 0..4 {
      pw2.set_target(expected_public_inputs_main[i], mmr_bagged.root.elements[i]);
    }
    let _: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      main_circuit_data.prove(pw2).unwrap();
  }

  #[test]
  #[should_panic]
  fn test_complete_verification_circuit_with_wrong_outer_proof() {
    let nr_leaves = 16;
    let leaf_index = 0;
    let mut rng = rand::thread_rng();
    let leaf0 = GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER));
    let mut mmr = naive_MMR::new(leaf0);
    for _ in 0..(nr_leaves-1) {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    let pr = mmr.clone().get_proof_with_extended_merkleproof(leaf_index);

    let (inner_circuit_data, targets) = verify_inner_merkle_proof_circuit(
      pr.2,
      pr.0.len()-1
    );

    let mut pw1 = plonky2::iop::witness::PartialWitness::new();
    pw1.set_hash_target(targets[0], mmr.elements[leaf_index]);
    // Add the proof elements (do not add the root)
    for i in 0..pr.0.len()-1 {
      pw1.set_hash_target(targets[1 + i], pr.0[i]);
    }
    
    let expected_public_inputs = inner_circuit_data.prover_only.public_inputs.clone();
    // The public input is the root of this subtree
    let subtree_root = pr.0[pr.0.len()-1];
    for i in 0..4 {
      pw1.set_target(expected_public_inputs[i], subtree_root.elements[i]);
    }
    let inner_proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      inner_circuit_data.prove(pw1).unwrap();

    let (main_circuit_data, inner_proof_target, inner_verifier_data_target, targets) = 
      complete_verification_circuit_with_inner_proof(inner_circuit_data.common, mmr.peaks.len());

    let mut pw2 = plonky2::iop::witness::PartialWitness::new();
    pw2.set_proof_with_pis_target(&inner_proof_target, &inner_proof);
    pw2.set_verifier_data_target(&inner_verifier_data_target, &inner_circuit_data.verifier_only);

    // Add all peaks to witness
    for i in 0..pr.1.len() {
      pw2.set_hash_target(targets[i], pr.1[i]);
    }

    let mmr_bagged = mmr.clone().bagging_the_peaks();

    // The expected public input is the root of mmr_bagged
    let expected_public_inputs_main = main_circuit_data.prover_only.public_inputs.clone();
    for i in 0..4 {
      // Setting root to the first leaf of the tree, so this should fail!
      pw2.set_target(expected_public_inputs_main[i], mmr_bagged.mmr.elements[0].elements[i]);
    }
    let _: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      main_circuit_data.prove(pw2).unwrap();

  }


  #[test]
  #[should_panic]
  fn test_complete_verification_circuit_proofs_hash_not_in_peaks() {
    let nr_leaves = 15;
    let leaf_index = 0;
    let mut rng = rand::thread_rng();
    let leaf0 = GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER));
    let mut mmr = naive_MMR::new(leaf0);
    for _ in 0..(nr_leaves-1) {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    let pr = mmr.clone().get_proof_with_extended_merkleproof(leaf_index);

    let (inner_circuit_data, targets) = verify_inner_merkle_proof_circuit(
      pr.2,
      pr.0.len()-1
    );

    let mut pw1 = plonky2::iop::witness::PartialWitness::new();
    pw1.set_hash_target(targets[0], mmr.elements[leaf_index]);
    // Add the proof elements (do not add the root)
    for i in 0..pr.0.len()-1 {
      pw1.set_hash_target(targets[1 + i], pr.0[i]);
    }
    
    let expected_public_inputs = inner_circuit_data.prover_only.public_inputs.clone();
    // The public input is the root of this subtree
    let subtree_root = pr.0[pr.0.len()-1];
    for i in 0..4 {
      pw1.set_target(expected_public_inputs[i], subtree_root.elements[i]);
    }
    let inner_proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      inner_circuit_data.prove(pw1).unwrap();

    let (main_circuit_data, inner_proof_target, inner_verifier_data_target, targets) = 
      complete_verification_circuit_with_inner_proof(inner_circuit_data.common, mmr.peaks.len());

    let mut pw2 = plonky2::iop::witness::PartialWitness::new();
    pw2.set_proof_with_pis_target(&inner_proof_target, &inner_proof);
    pw2.set_verifier_data_target(&inner_verifier_data_target, &inner_circuit_data.verifier_only);

    // Add all peaks to witness
    for i in 0..pr.1.len() {
      pw2.set_hash_target(targets[i], pr.1[i]);
    }

    // Adding 1 more leaf changes the peaks and should cause a mismatch between inner and outer proof
    mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    let mmr_bagged = mmr.clone().bagging_the_peaks();

    // The expected public input is the root of mmr_bagged
    let expected_public_inputs_main = main_circuit_data.prover_only.public_inputs.clone();
    for i in 0..4 {
      // Setting root to the first leaf of the tree, so this should fail!
      pw2.set_target(expected_public_inputs_main[i], mmr_bagged.root.elements[i]);
    }
    let _: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      main_circuit_data.prove(pw2).unwrap();

  }
}