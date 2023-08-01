use plonky2::hash::hash_types::HashOutTarget;
// use plonky2::iop::target::Target;
use plonky2::{hash::hash_types::RichField, plonk::config::Hasher};
use plonky2::{plonk::config::{GenericConfig, PoseidonGoldilocksConfig}, field::{goldilocks_field::GoldilocksField, types::Field}};
// use plonky2::plonk::config::AlgebraicHasher;
use plonky2::field::extension::Extendable;
use plonky2::plonk::circuit_builder::CircuitBuilder;
// use anyhow::Result;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::iop::witness::PartialWitness;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::AlgebraicHasher;
use plonky2::iop::target::BoolTarget;
use plonky2::iop::witness::WitnessWrite;
use std::iter;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IncrementalTree<F: RichField, H: Hasher<F>> {
    root: H::Hash,
    zeroes: Vec<H::Hash>,
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

        IncrementalTree { root: *zeroes.last().unwrap(), zeroes: zeroes, nodes: vec![Vec::new(); depth], depth: depth, position: 0 }
    }

    pub fn insert(&mut self, leaf: H::Hash) {

        if leaf == self.zeroes[0] {
            panic!("leaf cannot be zero");
        }

        if self.nodes.len() >= usize::pow(2, self.depth.try_into().unwrap()) {
            panic!("Tree is full");
        }

        let IncrementalTree {root, zeroes, nodes, depth, position} = self;

        let mut append_leaf = |node, level, index| {
            let level = level as usize;

            if nodes[level].len() > index { 
                nodes[level][index] = node; 
            } else {
                nodes[level].push(node);
            }

            if (index % 2) == 1 {
                H::two_to_one(nodes[level][index - 1], node)
            } else {
                H::two_to_one(node, zeroes[level])
            }

        };

        let mut node = leaf;
        let mut index = *position;

        for level in 0..*depth {
            node = append_leaf(node, level, index);
            index = (index as f64 / 2 as f64).floor() as usize;
        }

        *position += 1;
        *root = node;

        ()

    }

    pub fn witness(&mut self, leaf: H::Hash) -> (Vec<H::Hash>, Vec<bool>) {
        let IncrementalTree {zeroes, nodes, depth, .. } = self;

        let index = nodes[0].iter().position(|&el| el == leaf);
        // println!("{:?}", index);
        if index.is_none() {
            panic!("no such leaf");
        }

        let mut index = index.unwrap();
        let mut siblings = vec![zeroes[0];depth.clone()];
        let mut pos = vec![false; depth.clone()];

        let mut sibling_path = |level, index| {
            let level = level as usize;

            if index % 2 == 1 {
                siblings[level] = nodes[level][index - 1];
                pos[level] = true;
            } else {
                siblings[level] = zeroes[level];
            }
        };

        for level in 0..*depth {
            sibling_path(level, index);
            index = (index as f64 / 2 as f64).floor() as usize;
        }

        (siblings, pos)
    }

    pub fn check_proof(&self, leaf: H::Hash, siblings: Vec<H::Hash>, pos: Vec<bool>) -> bool {
        let mut node = leaf;
        for (sibling, p) in siblings.iter().zip(pos.iter()) {
            if *p {
                node = H::two_to_one(*sibling, node);
            } else {
                node = H::two_to_one(node, *sibling);

            }
        }

        node == self.root
    }

    pub fn root(&self) -> H::Hash {
        self.root
    }

    pub fn depth(&self) -> usize {
        self.depth
    }

}


fn main() {

    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    let config = CircuitConfig::standard_recursion_config();
    let mut pw: PartialWitness<_> = PartialWitness::<F>::new();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let cap_height = 3;
    let zero = vec![GoldilocksField::from_canonical_u64(0)];
    let one = vec![GoldilocksField::from_canonical_u64(1)];
    let two = vec![GoldilocksField::from_canonical_u64(2)];
    let three = vec![GoldilocksField::from_canonical_u64(3)];
    let four = vec![GoldilocksField::from_canonical_u64(4)];
    let five = vec![GoldilocksField::from_canonical_u64(5)];

    let zero_hash = PoseidonHash::hash_or_noop(&zero);
    let one_hash = PoseidonHash::hash_or_noop(&one);
    let two_hash = PoseidonHash::hash_or_noop(&two);
    let three_hash = PoseidonHash::hash_or_noop(&three);
    let four_hash = PoseidonHash::hash_or_noop(&four);
    let five_hash = PoseidonHash::hash_or_noop(&five);


    let mut tree = IncrementalTree::<F, <C as GenericConfig<D>>::Hasher>::new(zero_hash, cap_height);

    tree.insert(one_hash);
    tree.insert(two_hash);
    tree.insert(three_hash);
    tree.insert(four_hash);
    tree.insert(five_hash);

    let (siblings, pos) = tree.witness(five_hash);
    println!("{:?}", tree.check_proof(five_hash, siblings.clone(), pos.clone()));

    let mut targets: Vec<HashOutTarget> = Vec::new();

    let node = builder.add_virtual_hash();
    targets.push(node);

    let root = builder.add_virtual_hash();
    targets.push(root);

    let siblings_t = builder.add_virtual_hashes(siblings.clone().len());

    let mut next_hash: plonky2::hash::hash_types::HashOutTarget;

    for (&p, &sibling) in pos.iter().zip(&siblings_t) {   

        if p {
                    next_hash = builder.hash_or_noop::<PoseidonHash>([
                        sibling.elements.to_vec(),
                        node.elements.to_vec()
                      ].concat());
                } else {
                    next_hash = builder.hash_or_noop::<PoseidonHash>([
                        node.elements.to_vec(),
                        sibling.elements.to_vec()
                        ].concat());
    
                }
    }
    
    
    
    // pw.set_hash_target(leaf, five_hash);

    let root_t = builder.add_virtual_hash();
    pw.set_hash_target(root_t, tree.root);

    let siblings_t = builder.add_virtual_hashes(siblings.clone().len());

    for i in 0..siblings.clone().len() {
        pw.set_hash_target(siblings_t[i], siblings[i]);
    }




}


pub fn verify<F: RichField + Extendable<D>, H: AlgebraicHasher<F>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    pos: Vec<bool>,
    siblings: Vec<HashOutTarget>,
    root: HashOutTarget,
    leaf: HashOutTarget,
) {

    let initial = builder.add_virtual_target();

    let mut node = leaf;
    for (&p, &sibling) in pos.iter().zip(&siblings) {   

        //  if p {
        //         node = builder.hash_or_noop([
        //             siblings.to_vec(),
        //             vec![node]
        //           ].concat());
        //     } else {
        //         node = H::two_to_one(node, *sibling);

        //     }
        }

    }