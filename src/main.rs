// use plonky2::hash::hash_types::HashOutTarget;
// use plonky2::iop::target::Target;
use plonky2::{hash::hash_types::RichField, plonk::config::Hasher};
use plonky2::{plonk::config::{GenericConfig, PoseidonGoldilocksConfig}, field::{goldilocks_field::GoldilocksField, types::Field}};
// use plonky2::plonk::config::AlgebraicHasher;
// use plonky2::field::extension::Extendable;
// use plonky2::plonk::circuit_builder::CircuitBuilder;
// use anyhow::Result;
// use plonky2::plonk::circuit_data::CircuitConfig;
// use plonky2::iop::witness::PartialWitness;
use plonky2::hash::poseidon::PoseidonHash;
use std::iter;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IncrementalTree<F: RichField, H: Hasher<F>> {
    root: H::Hash,
    zeros: Vec<H::Hash>,
    nodes: Vec<Vec<H::Hash>>,
    depth: usize,
    position: usize,

}

impl<F: RichField, H: Hasher<F>> IncrementalTree<F, H> {

    pub fn new(zero_value: H::Hash, depth: usize) -> Self {
        if depth > 32 {panic!("Max depth exceeded!")}

        let zeroes: Vec<H::Hash> = {
            iter::empty()
            .chain(Some(zero_value))
            .chain(
                (0..depth).scan(zero_value, |zero, _level| {
                    *zero = H::two_to_one(*zero, *zero);
                    Some(*zero)
                })
            )
            .collect()
        };

        assert_eq!(zeroes.len(), depth + 1);

        IncrementalTree { root: *zeroes.last().unwrap(), zeros: zeroes, nodes: vec![Vec::new(); depth], depth: depth, position: 0 }
    }
}

// fn random_data<F: Field>(n: usize, k: usize) -> Vec<Vec<F>> {
//     (0..n).map(|_| F::rand_vec(k)).collect()
// }

fn main() {

    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    // let config = CircuitConfig::standard_recursion_config();
    // let mut pw: PartialWitness<_> = PartialWitness::<F>::new();
    // let mut builder = CircuitBuilder::<F, D>::new(config);

    // let log_n = 8;
    // let n = 1 << log_n;
    let cap_height = 3;
    // let leaves = random_data::<F>(n, 7);
    let zero = vec![GoldilocksField::from_canonical_u64(0)];
    let zero_hash = PoseidonHash::hash_or_noop(&zero);
    let tree = IncrementalTree::<F, <C as GenericConfig<D>>::Hasher>::new(zero_hash, cap_height);
    println!("{:?}", tree);
    println!("Hello, world!");
}
