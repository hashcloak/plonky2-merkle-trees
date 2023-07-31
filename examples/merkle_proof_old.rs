use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig, Hasher};
use plonky2_merkle_trees::simple_merkle_tree::simple_merkle_tree::MerkleTree;


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
    // For tree with 4 leaves and thus 2 levels, the proof consists of 2 elements

    let res_leaf_2 = tree.clone().get_merkle_proof(2);
    // Input into circuit is hashed leaf (H_2) we're proving is part of the tree
    // Step 1: hash H_2 with H_3. H_3 is the first hash in the proof (res_leaf_2)
    // Input into circuit
    let leaf_hashed = PoseidonHash::hash_or_noop(&[leaves.clone()[2]]);

    let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    let start_hash_target = builder.add_virtual_hash();
    let hash0 = builder.add_virtual_hash();

    builder.hash_or_noop::<PoseidonHash>([start_hash_target.elements.to_vec(), hash0.elements.to_vec()].concat());

    let mut pw = PartialWitness::new();
    pw.set_hash_target(start_hash_target, leaf_hashed);
    pw.set_hash_target(hash0, res_leaf_2[0]);

    let data = builder.build::<C>();
    let proof = data.prove(pw).unwrap();
    println!("done");

    data.verify(proof)
}
