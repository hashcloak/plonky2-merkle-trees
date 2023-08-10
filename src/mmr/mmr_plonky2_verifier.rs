use itertools::Itertools;
use plonky2::{hash::{poseidon::PoseidonHash, hash_types::HashOutTarget}, plonk::{config::{PoseidonGoldilocksConfig, GenericConfig}, circuit_data::{CircuitData, CircuitConfig}, circuit_builder::CircuitBuilder}, iop::target::{BoolTarget, Target}};
use plonky2_field::goldilocks_field::GoldilocksField;
use crate::mmr::common::{equal, or_list, pick_hash};

// Returns a circuit that verifies an MMR proof that has:
// - [nr_merkle_proof_elms] hashes that make up the Merkle proof of the subtree that the leaf is part of
// - [nr_peaks] peaks that have to be hashed together to get to the root
// Also returns targets that need to be set in the witness: (in order)
// - Target: to set the leaf for which the proof is
// - Vec<(HashOutTarget, BoolTarget)>: to set the merkle proof elements with indication whether that hash is on the left
// - Vec<HashOutTarget>: to set the peaks
pub fn verify_mmr_proof_circuit(
  nr_merkle_proof_elms: usize,
  nr_peaks: usize
  // Returns circuit data, targets for leaf, targets for proof elements (hashes), targets for peaks
) -> (CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>, Target, Vec<(HashOutTarget, BoolTarget)>, Vec<HashOutTarget>) {
  const D: usize = 2;
  type C = PoseidonGoldilocksConfig;
  type F = <C as GenericConfig<D>>::F;
  // Verifying proof does the following:
  // 1. Hashes its way through the (public input) merkle proof elements
  // 2. Check result of (1) is amongst peaks
  //     (for this, compare it to all peaks and check that the OR of these comparisons together true)
  // 3. Hash peaks and compare to public input root

  let mut proof_targets: Vec<(HashOutTarget, BoolTarget)> = Vec::new();
  let mut peak_targets: Vec<HashOutTarget> = Vec::new();

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

  // Hash all peaks together
  let mut peaks: Vec<HashOutTarget> = Vec::new();
  let mut equals: Vec<BoolTarget> = Vec::new();
  for _peaks in 0..nr_peaks {
    let peak = builder.add_virtual_hash();
    peaks.push(peak);
    peak_targets.push(peak);
    let equals_peak: BoolTarget = equal(&mut builder, peak, next_hash);
    equals.push(equals_peak);
  }

  // Now check that the resulting "next_hash" appears in the given peaks
  let hash_in_peaks = or_list(&mut builder, equals);
  // check that its "true"
  let one: plonky2::iop::target::Target = builder.one();
  builder.connect(one, hash_in_peaks.target); 
  // for some reason this below doesn't work
  // builder.assert_bool(hash_in_peaks);

  if peaks.len() > 1 {
    let root = builder.hash_n_to_hash_no_pad::<PoseidonHash>(peaks.into_iter().flat_map(|x| x.elements).collect_vec());
    // This is the expected root value (bagged MMR)
    builder.register_public_inputs(&root.elements);
  } else {
    // If there's only 1 peak, the root will be equal to that peak
    builder.register_public_inputs(&peaks[0].elements);
  }

  let data = builder.build::<C>();
  (data, leaf_to_prove, proof_targets, peak_targets)
}

#[cfg(test)]
mod tests {
  use anyhow::Result;
  use plonky2::{iop::witness::WitnessWrite, plonk::config::PoseidonGoldilocksConfig};
  use plonky2_field::{goldilocks_field::GoldilocksField, types::Field};
  use rand::Rng;

  use crate::mmr::{merkle_mountain_ranges::{MMR, get_mmr_index}, mmr_plonky2_verifier::verify_mmr_proof_circuit, common::GOLDILOCKS_FIELD_ORDER};

  fn test_mmr_verifier(nr_leaves: usize, leaf_normal_index: usize) -> Result<()> {
    let leaf_mmr_index: usize = get_mmr_index(leaf_normal_index);
    
    let mut rng = rand::thread_rng();
    let mut leaves = Vec::new();
    
    let mut mmr = MMR::new();
    for i in 0..nr_leaves {
      leaves.push(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
      mmr.add_leaf(leaves[i]);  
    }
    let pr = mmr.clone().get_proof(leaf_mmr_index);

    // Checking that the proof is valid
    let root = mmr.bagging_the_peaks();
    assert!(pr.clone().verify(leaves[leaf_normal_index], root));

    let (circuit_data, 
      leaf_target, 
      proof_elms_targets, 
      peak_targets) =
      verify_mmr_proof_circuit(pr.clone().merkle_proof.len(), pr.clone().peaks.len());

    // Create witness
    let mut pw = plonky2::iop::witness::PartialWitness::new();

    // Leaf to be proved
    pw.set_target(leaf_target, leaves[leaf_normal_index]);
    
    // Merkle proof hashes, along with the indication whether the hash is on the left
    for i in 0..pr.merkle_proof.len() {
      pw.set_hash_target(proof_elms_targets[i].0, pr.merkle_proof[i].0);
      pw.set_bool_target(proof_elms_targets[i].1, pr.merkle_proof[i].1);
    }

    // Add all peaks
    for i in 0..pr.peaks.len() {
      pw.set_hash_target(peak_targets[i], pr.peaks[i]);
    }
    
    // Set the public inputs; leaf and root
    let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();
    for i in 0..4 {
      pw.set_target(expected_public_inputs[i], root.elements[i]);
    }
    let proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      circuit_data.prove(pw).unwrap();

    circuit_data.verify(proof)
  }

  #[test]
  fn test_mmr_verifier_3leaves() -> Result<()> {
    let nr_leaves: usize = 3;
    for i in 0..nr_leaves {
      _ = test_mmr_verifier(nr_leaves,i);  
    }
    Ok(())
  }
  
  #[test]
  fn test_mmr_verifier_7leaves() -> Result<()> {
    let nr_leaves: usize = 7;
    for i in 0..nr_leaves {
      _ = test_mmr_verifier(nr_leaves,i);  
    }
    Ok(())
  }
    
  #[test]
  fn test_mmr_verifier_70leaves() -> Result<()> {
    let nr_leaves: usize = 70;
    for i in 0..nr_leaves {
      _ = test_mmr_verifier(nr_leaves,i);  
    }
    Ok(())
  }
    
  #[test]
  fn test_mmr_verifier_31leaves() -> Result<()> {
    let nr_leaves: usize = 31;
    for i in 0..nr_leaves {
      _ = test_mmr_verifier(nr_leaves,i);  
    }
    Ok(())
  }

  #[test]
  fn test_mmr_verifier_multiple_sizes_1() -> Result<()> {
    for nr_leaves in 6..16 {
      for i in 0..nr_leaves {
        _ = test_mmr_verifier(nr_leaves,i);  
      }
    }
    
    Ok(())
  }
  
    #[test]
  fn test_mmr_verifier_multiple_sizes_2() -> Result<()> {
    for nr_leaves in 0..40 {
      for i in 0..nr_leaves {
        _ = test_mmr_verifier(nr_leaves,i);  
      }
    }
    
    Ok(())
  }
}