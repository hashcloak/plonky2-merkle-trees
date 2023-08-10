use itertools::Itertools;
use plonky2::{hash::{poseidon::PoseidonHash, hash_types::HashOutTarget}, plonk::{config::{PoseidonGoldilocksConfig, GenericConfig}, circuit_data::{CircuitData, CircuitConfig, CommonCircuitData, VerifierCircuitTarget}, circuit_builder::CircuitBuilder, proof::ProofWithPublicInputsTarget}, iop::target::{BoolTarget, Target}};
use plonky2_field::goldilocks_field::GoldilocksField;
use crate::mmr::common::{pick_hash, equal, or_list};

/** 
 * An mmr proof consists of 2 parts:
 * (1) inner Merkle proof, that proves a leaf is part of that subtree
 * (2) root check (hashing all peaks of mmr together)
 * 
 * To add recursion within this verification the proof of step 1 can be embedded in the circuit of step 2.
 * That is the strategy used here.
*/

// Returns a circuit that verifies a Merkle proof. The final check will be that the resulting root is present in a list of peaks
// Also returns targets that need to be set in the witness: (in order)
// - Target: to set the leaf for which the proof is
// - Vec<(HashOutTarget, BoolTarget)>: to set the merkle proof elements with indication whether that hash is on the left
// Public input is the resulting root
pub fn verify_inner_merkle_proof_circuit(nr_merkle_proof_elms: usize, nr_peaks: usize) 
  -> (CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>, Target, Vec<(HashOutTarget, BoolTarget)>) {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    
    let mut proof_targets: Vec<(HashOutTarget, BoolTarget)> = Vec::new();

    let config = CircuitConfig::standard_recursion_config();
    let mut builder: CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2> = CircuitBuilder::<F, D>::new(config);
    // The leaf to prove is in the MMR
    let leaf_to_prove = builder.add_virtual_target();
    let hashed_leaf = builder.hash_or_noop::<PoseidonHash>([leaf_to_prove].to_vec());
      
    // The first hashing outside of the loop, since it uses the leaf_to_prove
    let mut next_hash: plonky2::hash::hash_types::HashOutTarget = hashed_leaf;

    let mut proof_elm_index = 0;
    while proof_elm_index < nr_merkle_proof_elms {
      let merkle_proof_elm = builder.add_virtual_hash();
      let elm_on_left = builder.add_virtual_bool_target_safe();
      proof_targets.push((merkle_proof_elm, elm_on_left));
      // Create the 2 options and then chose the correct one
      // Option 1: sibling on the left
      let option1 = builder.hash_or_noop::<PoseidonHash>([
        merkle_proof_elm.elements.to_vec(),
        next_hash.elements.to_vec()
      ].concat());
      // Option 2: sibling on the right
      let option2 = builder.hash_or_noop::<PoseidonHash>([
        next_hash.elements.to_vec(),
        merkle_proof_elm.elements.to_vec()
      ].concat());
  
      // Pick the right next hash according to the bool that has been given with this element
      next_hash = pick_hash(&mut builder, option1, option2, elm_on_left);
      proof_elm_index += 1;
    }

    let mut equals: Vec<BoolTarget> = Vec::new();
    for _ in 0..nr_peaks {
      let peak = builder.add_virtual_hash();
      peak.elements.map(|elm| builder.register_public_input(elm));
      let equals_peak: BoolTarget = equal(&mut builder, peak, next_hash);
      equals.push(equals_peak);
    }

    // Now check that the resulting "next_hash" appears in the given peaks
    let hash_in_peaks = or_list(&mut builder, equals);
    // check that its "true"
    let one: plonky2::iop::target::Target = builder.one();
    builder.connect(one, hash_in_peaks.target); 
    
    let data = builder.build::<C>();
    (data, leaf_to_prove, proof_targets)
}

// This is the same as for the naive impl
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
  use crate::mmr::{common::GOLDILOCKS_FIELD_ORDER, merkle_mountain_ranges::{MMR, get_mmr_index}};
  use super::{complete_verification_circuit_with_inner_proof, verify_inner_merkle_proof_circuit};

  pub fn test_complete_verification_circuit_with_inner_proof(nr_leaves: usize, normal_leaf_index: usize) -> Result<()> {
    let mut rng = rand::thread_rng();
    let mmr_leaf_index = get_mmr_index(normal_leaf_index);
    let mut mmr = MMR::new();
    let mut leaves = Vec::new();
    for i in 0..nr_leaves {
      leaves.push(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
      mmr.add_leaf(leaves[i]);
    }
    // This returns
    // (merkle proof for leaf within subtree, peaks in mmr (before bagging the peaks), leaf index within the subtree)
    // Note that the merkle proof also contains the root of the subtree; we need this to chop the verification up in 2 parts 
    let pr = mmr.clone().get_proof(mmr_leaf_index);

    let (inner_circuit_data, leaf_target, proof_targets) = verify_inner_merkle_proof_circuit(
      pr.merkle_proof.len(), pr.peaks.len()
    );

    let mut pw1 = plonky2::iop::witness::PartialWitness::new();
    pw1.set_target(leaf_target, leaves[normal_leaf_index]); // leaf to prove

    // Add the proof elements; for each element we add the hash and a bool whether this hash is on the left
    for i in 0..pr.merkle_proof.len() {
      pw1.set_hash_target(proof_targets[i].0, pr.merkle_proof[i].0);
      pw1.set_bool_target(proof_targets[i].1, pr.merkle_proof[i].1);
    }
    
    let expected_public_inputs = inner_circuit_data.prover_only.public_inputs.clone();
    // The public inputs are the peaks, since the root must be among them
    let mut i = 0;
    for peak in &pr.peaks {
      // pw1.set_target(expected_public_inputs[i], subtree_root.elements[i]);
      pw1.set_target(expected_public_inputs[i], peak.elements[0]);
      pw1.set_target(expected_public_inputs[i+1], peak.elements[1]);
      pw1.set_target(expected_public_inputs[i+2], peak.elements[2]);
      pw1.set_target(expected_public_inputs[i+3], peak.elements[3]);
      i+=4;
    }

    let inner_proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      inner_circuit_data.prove(pw1).unwrap();
      
      // Optional check the inner proof verifies
    // inner_circuit_data.verify(inner_proof)
    
    
    let (main_circuit_data, inner_proof_target, inner_verifier_data_target, targets) = 
      complete_verification_circuit_with_inner_proof(inner_circuit_data.common, pr.peaks.len());

    let mut pw2 = plonky2::iop::witness::PartialWitness::new();
    pw2.set_proof_with_pis_target(&inner_proof_target, &inner_proof);
    pw2.set_verifier_data_target(&inner_verifier_data_target, &inner_circuit_data.verifier_only);

    // Add all peaks to witness
    for i in 0..pr.peaks.len() {
      pw2.set_hash_target(targets[i], pr.peaks[i]);
    }

    let root = mmr.clone().bagging_the_peaks();

    // The public input is the root ofthe mmr
    let expected_public_inputs_main = main_circuit_data.prover_only.public_inputs.clone();
    for i in 0..4 {
      pw2.set_target(expected_public_inputs_main[i], root.elements[i]);
    }
    let final_proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      main_circuit_data.prove(pw2)?;

    main_circuit_data.verify(final_proof)
  }

  #[test]
  fn test_mmr_verifier_2leaves() -> Result<()> {
    let nr_leaves: usize = 2;
    test_complete_verification_circuit_with_inner_proof(nr_leaves, 0)
  }
  
    #[test]
  fn test_mmr_verifier_7leaves_multiple() -> Result<()> {
    let nr_leaves: usize = 7;
    for i in 0..nr_leaves {
      _ = test_complete_verification_circuit_with_inner_proof(nr_leaves, i);
    }
    Ok(())
  }

  #[test]
  fn test_mmr_verifier_8leaves_multiple() -> Result<()> {
    let nr_leaves: usize = 8;
    for i in 0..nr_leaves {
      _ = test_complete_verification_circuit_with_inner_proof(nr_leaves, i);
    }
    Ok(())
  }

  #[test]
  fn test_mmr_verifier_31leaves() -> Result<()> {
    let nr_leaves: usize = 31;
    test_complete_verification_circuit_with_inner_proof(nr_leaves, 8)
  }

  #[test]
  fn test_mmr_verifier_1031leaves() -> Result<()> {
    let nr_leaves: usize = 1031;
    test_complete_verification_circuit_with_inner_proof(nr_leaves, 100)
  }
}