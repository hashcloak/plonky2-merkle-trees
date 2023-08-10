use plonky2::{plonk::circuit_builder::CircuitBuilder, iop::target::BoolTarget, hash::hash_types::HashOutTarget};

pub const GOLDILOCKS_FIELD_ORDER: u64 = 18446744069414584321;

pub fn equal(
  builder: &mut CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2>,
  first: HashOutTarget, 
  second: HashOutTarget) -> BoolTarget {
  let elm0 = builder.is_equal(first.elements[0], second.elements[0]);
  let elm1 = builder.is_equal(first.elements[1], second.elements[1]);
  let elm2 = builder.is_equal(first.elements[2], second.elements[2]);
  let elm3 = builder.is_equal(first.elements[3], second.elements[3]);
  let elm0_or_elm1 = builder.or(elm0, elm1);
  let elm2_or_elm3 = builder.or(elm2, elm3);
  builder.or(elm0_or_elm1, elm2_or_elm3)
}

pub fn or_list(
  builder: &mut CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2>,
  ins: Vec<BoolTarget>) -> BoolTarget {
    assert!(ins.len() > 0 );
    if ins.len() == 1 {
      return ins[0];
    } else if ins.len() == 2 {
      return builder.or(ins[0], ins[1]); 
    } else {
      let mut pairs: Vec<BoolTarget> = Vec::new();
      for pair in ins.chunks(2) {
        if pair.len() > 1 {
          pairs.push(builder.or(pair[0], pair[1]));
        } else {
          pairs.push(pair[0]);
        }
        
      }
      return or_list(builder, pairs);
    }
}

// Returns a HashOutTarget that equals option1 if pick_left is true and returns option2 otherwise
// if pick_left: option1 else option2
pub fn pick_hash(
  builder: &mut CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2>,
  option1: HashOutTarget, 
  option2: HashOutTarget, 
  pick_left: BoolTarget) -> HashOutTarget {
    let opposite = builder.not(pick_left);

    let t0 = builder.mul(option2.elements[0], opposite.target);
    let t1 = builder.mul(option2.elements[1], opposite.target);
    let t2 = builder.mul(option2.elements[2], opposite.target);
    let t3 = builder.mul(option2.elements[3], opposite.target);
    let hash_elm0 = builder.mul_add(option1.elements[0], pick_left.target,  t0);
    let hash_elm1 = builder.mul_add(option1.elements[1], pick_left.target, t1);
    let hash_elm2 = builder.mul_add(option1.elements[2], pick_left.target, t2);
    let hash_elm3 = builder.mul_add(option1.elements[3], pick_left.target, t3);
    HashOutTarget { elements: [hash_elm0, hash_elm1, hash_elm2, hash_elm3] }
}

#[cfg(test)]
mod tests {
  use anyhow::Result;
  use plonky2::{plonk::{config::{PoseidonGoldilocksConfig, GenericConfig}, circuit_data::CircuitConfig, circuit_builder::CircuitBuilder}, iop::witness::WitnessWrite};
  use plonky2_field::goldilocks_field::GoldilocksField;

  use crate::mmr::common::or_list;

  #[test]
  fn test_or_list_result_true() -> Result<()> {
    
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder: CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2> = CircuitBuilder::<F, D>::new(config);
    let b0 = builder.add_virtual_bool_target_safe();
    let b1 = builder.add_virtual_bool_target_safe();
    let b2 = builder.add_virtual_bool_target_safe();
    let b3 = or_list(&mut builder, [b0,b1,b2].to_vec());

    
    let one: plonky2::iop::target::Target = builder.one();
    builder.connect(one, b3.target); // this is how we can test for true /false. Somehow assert_bool doesn't work
    let circuit_data = builder.build();

    // false true false
    let mut pw1 = plonky2::iop::witness::PartialWitness::new();
    pw1.set_bool_target(b0, false);
    pw1.set_bool_target(b1, true);
    pw1.set_bool_target(b2, false);

    let proof1: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
    circuit_data.prove(pw1)?;

    circuit_data.verify(proof1);

    // true true true
    let mut pw2 = plonky2::iop::witness::PartialWitness::new();
    pw2.set_bool_target(b0, true);
    pw2.set_bool_target(b1, true);
    pw2.set_bool_target(b2, true);

    let proof2: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
    circuit_data.prove(pw2)?;

    circuit_data.verify(proof2)
  }  

  #[test]
  fn test_or_list_result_false() -> Result<()> {
    
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder: CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2> = CircuitBuilder::<F, D>::new(config);
    let b0 = builder.add_virtual_bool_target_safe();
    let b1 = builder.add_virtual_bool_target_safe();
    let b2 = builder.add_virtual_bool_target_safe();
    let b3 = builder.add_virtual_bool_target_safe();
    let b4 = or_list(&mut builder, [b0,b1,b2,b3].to_vec());
    
    let zero: plonky2::iop::target::Target = builder.zero();
    builder.connect(zero, b4.target); // this is how we can test for true /false. Somehow assert_bool doesn't work
    let circuit_data = builder.build();

    // false false false false
    let mut pw1 = plonky2::iop::witness::PartialWitness::new();
    pw1.set_bool_target(b0, false);
    pw1.set_bool_target(b1, false);
    pw1.set_bool_target(b2, false);
    pw1.set_bool_target(b3, false);

    let proof1: plonky2::plonk::proof::ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2> = 
    circuit_data.prove(pw1)?;

    circuit_data.verify(proof1)
  }

}