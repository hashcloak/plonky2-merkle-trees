use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{PoseidonGoldilocksConfig, GenericConfig};

// This functions writes a plonky2 circuit
//   that verifies x is a solution for the
//   polynomial x^3 - 5x^2 + 8x + 10

// for x = 1 -> 1 - 5 + 8 + 10 = 14
// for x = 2 -> 8 - 20 + 16 + 10 = 14
// for x = 3 -> 27 - 45 + 24 + 10 = 61 - 45 = 16

pub fn verify_the_polynomial() {
    // Construct the CircuitBuilder
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // Circuit Arithmetic
    // add_virtual_targets
    let x = builder.add_virtual_target();
    let x_square = builder.square(x);
    let x_square_mul_5 = builder.mul_const(GoldilocksField(5), x_square);
    let x_square_mul_f_neg = builder.neg(x_square_mul_5);
    let x_mul_8 = builder.mul_const(GoldilocksField(8), x);
    let x_cube = builder.cube(x);
    let mut result = builder.add(x_cube, x_mul_8);
    result = builder.add(result, x_square_mul_f_neg);
    result = builder.add_const(result, GoldilocksField(10));

    // Register the Public Inputs
    builder.register_public_input(x);
    builder.register_public_input(result);

    // Create a PartialWitness
    // set_target using pw
    let mut pw = PartialWitness::new();
    pw.set_target(x, F::from(GoldilocksField(1)));
    pw.set_target(result, F::from(GoldilocksField(14)));

    // Build the circuit as data
    let data = builder.build::<C>();

    // Prove the data
    let proof = data.prove(pw).unwrap();

    // Verify the data
    data.verify(proof);
}


pub fn verify_the_polynomial_incorrect() {
    // Construct the CircuitBuilder
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // Circuit Arithmetic
    // add_virtual_targets
    let x = builder.add_virtual_target();
    let x_square = builder.square(x);
    let x_square_mul_5 = builder.mul_const(GoldilocksField(5), x_square);
    let x_square_mul_f_neg = builder.neg(x_square_mul_5);
    let x_mul_8 = builder.mul_const(GoldilocksField(8), x);
    let x_cube = builder.cube(x);
    let mut result = builder.add(x_cube, x_mul_8);
    result = builder.add(result, x_square_mul_f_neg);
    result = builder.add_const(result, GoldilocksField(10));

    // Register the Public Inputs
    builder.register_public_input(x);
    builder.register_public_input(result);

    // Create a PartialWitness
    // set_target using pw
    let mut pw = PartialWitness::new();
    pw.set_target(x, F::from(GoldilocksField(3)));
    pw.set_target(result, F::from(GoldilocksField(14)));

    // Build the circuit as data
    let data = builder.build::<C>();

    // Prove the data
    let proof = data.prove(pw).unwrap();

    // Verify the data
    data.verify(proof);
}