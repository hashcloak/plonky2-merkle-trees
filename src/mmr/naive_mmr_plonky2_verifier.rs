use itertools::Itertools;
use num::ToPrimitive;
use plonky2::{plonk::{config::{PoseidonGoldilocksConfig, GenericConfig}, circuit_data::{CircuitData, CircuitConfig}, circuit_builder::CircuitBuilder}, hash::{poseidon::PoseidonHash, hash_types::HashOutTarget}, iop::target::BoolTarget};
use plonky2_field::goldilocks_field::GoldilocksField;

use crate::mmr::{naive_merkle_mountain_ranges::get_standard_index, common::{equal, or_list}};

// Returns a circuit that verifies an mmr proof, and the targets that need to be set in the witness
pub fn verify_naive_mmr_proof_circuit(
  relative_leaf_index: usize, // index of leaf within subtree. This is an MMR index
  nr_proof_elms: usize, // nr of layers within subtree
  nr_peaks: usize // peaks in MMR
) -> (CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>, Vec<HashOutTarget>) {
  // 1. Hashes its way through the (public input) merkle proof elements
  // 2. Check result of (1) is amongst peaks
  //     (for this, compare it to all peaks and check that the OR of these comparisons together true)
  // 3. Hash peaks and compare to public input root

  const D: usize = 2;
  type C = PoseidonGoldilocksConfig;
  type F = <C as GenericConfig<D>>::F;

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

  // Hash all peaks together
  let mut peaks: Vec<HashOutTarget> = Vec::new();
  let mut equals: Vec<BoolTarget> = Vec::new();
  for _peaks in 0..nr_peaks {
    let peak = builder.add_virtual_hash();
    peaks.push(peak);
    targets.push(peak);
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
  (data, targets)
}

#[cfg(test)]
mod tests {
  use anyhow::Result;
  use plonky2_field::{goldilocks_field::GoldilocksField, types::Field};
  use plonky2::{iop::witness::WitnessWrite, plonk::config::PoseidonGoldilocksConfig};
  use rand::Rng;

  use crate::mmr::naive_merkle_mountain_ranges::naive_MMR;

  use super::verify_naive_mmr_proof_circuit;
  const GOLDILOCKS_FIELD_ORDER: u64 = 18446744069414584321;


  pub fn do_test_verify_proof(nr_leaves: usize, leaf_index: usize) -> Result<()> {
    let mut rng = rand::thread_rng();
    let leaf0 = GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER));
    let mut mmr = naive_MMR::new(leaf0);
    for _ in 0..(nr_leaves-1) {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    let mmr_bagged = mmr.clone().bagging_the_peaks();
    let pr = mmr.clone().get_proof(leaf_index);

    let (circuit_data, targets) = verify_naive_mmr_proof_circuit(
      pr.2,
      pr.0.len(),
      pr.1.len()
    );

    let mut pw = plonky2::iop::witness::PartialWitness::new();
    pw.set_hash_target(targets[0], mmr.elements[leaf_index]); // hashed leaf to prove
    // Add all proof elements
    for i in 0..pr.0.len() {
      pw.set_hash_target(targets[1 + i], pr.0[i]);
    }
    // Add all peaks
    for i in 0..pr.1.len() {
      pw.set_hash_target(targets[pr.0.len() + 1 + i], pr.1[i]);
    }
    
    let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();
    for i in 0..4 {
      pw.set_target(expected_public_inputs[i], mmr_bagged.root.elements[i]);
    }
    let proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      circuit_data.prove(pw)?;

    circuit_data.verify(proof)

  }

  #[test]
  fn verify_proof_2_leaves_index1() -> Result<()> {
    do_test_verify_proof(2, 1)
  }

  #[test]
  fn verify_proof_4_leaves_index0() -> Result<()> {
    do_test_verify_proof(4, 0)
  }

  #[test]
  fn verify_proof_4_leaves_index1() -> Result<()> {
    do_test_verify_proof(4, 1)
  }
  
  #[test]
  fn verify_proof_4_leaves_index3() -> Result<()> {
    do_test_verify_proof(4, 3)
  }

  #[test]
  fn verify_proof_4_leaves_index4() -> Result<()> {
    do_test_verify_proof(4, 4)
  }

  #[test]
  fn verify_proof_5_leaves_index3() -> Result<()> {
    do_test_verify_proof(5, 3)
  }

  #[test]
  fn verify_proof_6_leaves_index3() -> Result<()> {
    do_test_verify_proof(6, 3)
  }

  #[test]
  fn verify_proof_10_leaves_index15() -> Result<()> {
    do_test_verify_proof(10, 15)
  }

  #[test]
  fn verify_proof_12_leaves_index16() -> Result<()> {
    do_test_verify_proof(12, 16)
  }

  #[test]
  fn verify_proof_16_leaves_index3() -> Result<()> {
    do_test_verify_proof(16, 3)
  }

  #[test]
  fn verify_proof_16_leaves_index8() -> Result<()> {
    do_test_verify_proof(16, 8)
  }

  #[test]
  fn verify_proof_16_leaves_index25() -> Result<()> {
    do_test_verify_proof(16, 25)
  }

  #[test]
  fn verify_proof_101_leaves_index25() -> Result<()> {
    do_test_verify_proof(101, 25)
  }

  #[test]
  fn verify_proof_1001_leaves_index25() -> Result<()> {
    do_test_verify_proof(1001, 25)
  }

  #[test]
  fn verify_proof_32_leaves_index56() -> Result<()> {
    do_test_verify_proof(32, 56)
  }
  
  #[test]
  fn verify_proof_1001_leaves_index56() -> Result<()> {
    do_test_verify_proof(10101, 56)
  }

  fn test_wrong_proof(nr_leaves: usize, leaf_index: usize, wrong_leaf: usize) {
    // let nr_leaves: usize = 1001;
    // let leaf_index: usize = 25;

    let mut rng = rand::thread_rng();
    let leaf0 = GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER));
    let mut mmr = naive_MMR::new(leaf0);
    for _ in 0..(nr_leaves-1) {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    let mmr_bagged = mmr.clone().bagging_the_peaks();
    let pr = mmr.clone().get_proof(leaf_index);

    let (circuit_data, targets) = verify_naive_mmr_proof_circuit(
      pr.2,
      pr.0.len(),
      pr.1.len()
    );

    let mut pw = plonky2::iop::witness::PartialWitness::new();
    // WRONG LEAF
    pw.set_hash_target(targets[0], mmr.elements[wrong_leaf]);
    // Add all proof elements
    for i in 0..pr.0.len() {
      pw.set_hash_target(targets[1 + i], pr.0[i]);
    }
    // Add all peaks
    for i in 0..pr.1.len() {
      pw.set_hash_target(targets[pr.0.len() + 1 + i], pr.1[i]);
    }
    
    let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();
    for i in 0..4 {
      pw.set_target(expected_public_inputs[i], mmr_bagged.root.elements[i]);
    }
    let proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      circuit_data.prove(pw).unwrap();

    circuit_data.verify(proof);
  }

  #[test]
  #[should_panic]
  fn test_wrong_proof1() {
    test_wrong_proof(1001,25, 1);
  }

  #[test]
  #[should_panic]
  fn test_wrong_proof2() {
    test_wrong_proof(16,10, 11);
  }

  #[test]
  #[should_panic]
  fn test_wrong_proof3() {
    test_wrong_proof(32,25, 23);
  }

  #[test]
  #[should_panic]
  fn test_wrong_proof4() {
    test_wrong_proof(100100,1, 0);
  }

  #[test]
  #[should_panic]
  fn test_wrong_root() {
    let nr_leaves: usize = 32;
    let leaf_index: usize = 0;

    let mut rng = rand::thread_rng();
    let leaf0 = GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER));
    let mut mmr = naive_MMR::new(leaf0);
    for _ in 0..(nr_leaves-1) {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    let mmr_bagged = mmr.clone().bagging_the_peaks();
    let pr = mmr.clone().get_proof(leaf_index);

    let (circuit_data, targets) = verify_naive_mmr_proof_circuit(
      pr.2,
      pr.0.len(),
      pr.1.len()
    );

    let mut pw = plonky2::iop::witness::PartialWitness::new();
    
    pw.set_hash_target(targets[0], mmr.elements[0]);
    // Add all proof elements
    for i in 0..pr.0.len() {
      pw.set_hash_target(targets[1 + i], pr.0[i]);
    }
    // Add all peaks
    for i in 0..pr.1.len() {
      pw.set_hash_target(targets[pr.0.len() + 1 + i], pr.1[i]);
    }
    
    let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();
    for i in 0..4 {
      // WRONG ROOT 
      pw.set_target(expected_public_inputs[i], mmr_bagged.root.elements[0]);
    }
    let proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      circuit_data.prove(pw).unwrap();

    circuit_data.verify(proof);

  }

  #[test]
  #[should_panic]
  fn test_wrong_peaks() {
    let nr_leaves: usize = 10101;
    let leaf_index: usize = 0;

    let mut rng = rand::thread_rng();
    let leaf0 = GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER));
    let mut mmr = naive_MMR::new(leaf0);
    for _ in 0..(nr_leaves-1) {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    let mmr_bagged = mmr.clone().bagging_the_peaks();
    let pr = mmr.clone().get_proof(leaf_index);

    let (circuit_data, targets) = verify_naive_mmr_proof_circuit(
      pr.2,
      pr.0.len(),
      pr.1.len()
    );

    let mut pw = plonky2::iop::witness::PartialWitness::new();
    
    pw.set_hash_target(targets[0], mmr.elements[0]);
    // Add all proof elements
    for i in 0..pr.0.len() {
      pw.set_hash_target(targets[1 + i], pr.0[i]);
    }
    // Add all peaks
    for i in 0..pr.1.len() {
      pw.set_hash_target(targets[pr.0.len() + 1 + i], pr.1[0]);
    }
    
    let expected_public_inputs = circuit_data.prover_only.public_inputs.clone();
    for i in 0..4 {
      pw.set_target(expected_public_inputs[i], mmr_bagged.root.elements[i]);
    }
    let proof: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
      circuit_data.prove(pw).unwrap();

    circuit_data.verify(proof);

  }
}