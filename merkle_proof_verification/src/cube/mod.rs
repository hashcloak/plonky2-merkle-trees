use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{PoseidonGoldilocksConfig, GenericConfig};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::field::goldilocks_field::GoldilocksField;


pub fn verify_cube() {
   println!("The verification is started!"); 

   const D: usize = 2;
   type C = PoseidonGoldilocksConfig;
   type F = <C as GenericConfig<D>>::F;

   let config = CircuitConfig::standard_recursion_config();
   let mut builder = CircuitBuilder::<F, D>::new(config);

   // add_virtual_target ne yapıyor
   // Target -> türünden döndürüyor. Gerçek wire değil,
   
   // Here is the circuit arithmetic
   let x = builder.add_virtual_target();
   let cube = builder.cube(x);

   // register the Target's as Public Inputs?? Amaç
   builder.register_public_input(x);
   builder.register_public_input(cube);

   let mut pw = PartialWitness::new();
   pw.set_target(x, F::from(GoldilocksField(3)));
   pw.set_target(cube, F::from(GoldilocksField(27)));

   let data = builder.build::<C>();
   let proof = data.prove(pw).unwrap();

   let _ = data.verify(proof);

   // since it is result, let's unwrap it

}

pub fn verify_cube_wrong_proof() {
    // Construct the Circuit Builder
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // Circuit arithmetic 
    let x = builder.add_virtual_target();
    let cube = builder.cube(x);

    
    // Register inputs
    builder.register_public_input(x);
    builder.register_public_input(cube);

    // Construct PartialWitness for proof add witness values for GoldilocksField
    // Use incorrect witnesses
    let mut pw = PartialWitness::new();
    pw.set_target(x, F::from(GoldilocksField(3)));
    pw.set_target(cube, F::from(GoldilocksField(28)));

    // Build the circuit as data
    let data = builder.build::<C>();

    // Prove the data using partial witness
    let proof = data.prove(pw).unwrap();

    // Verify the data
    data.verify(proof);
}