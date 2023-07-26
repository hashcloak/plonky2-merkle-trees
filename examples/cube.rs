#![allow(clippy::upper_case_acronyms)]

use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

fn main() -> Result<()> {
  const D: usize = 2;
  type C = PoseidonGoldilocksConfig;
  type F = <C as GenericConfig<D>>::F;

  let config = CircuitConfig::standard_recursion_config();
  let mut builder: CircuitBuilder<plonky2::field::goldilocks_field::GoldilocksField, 2> = CircuitBuilder::<F, D>::new(config);

  // The virtual target later will be added as public input
  let x = builder.add_virtual_target();
  let cube = builder.cube(x);

  builder.register_public_input(x);
  builder.register_public_input(cube);

  let mut pw = PartialWitness::new();
  pw.set_target(x, F::from_canonical_u32(3));
  pw.set_target(cube, F::from_canonical_u32(27));

  let data = builder.build::<C>();
  let proof = data.prove(pw)?;

  println!("{}'s cube is {}", proof.public_inputs[0], proof.public_inputs[1]);
  data.verify(proof)
}