use plonky2::{

    hash::{
        hash_types::{RichField, HashOutTarget},
        poseidon::PoseidonHash
    }, 

    plonk::{
        config::{GenericConfig, PoseidonGoldilocksConfig, AlgebraicHasher, Hasher},
        circuit_builder::CircuitBuilder, 
        circuit_data::CircuitConfig
    }, 

    field::{
        goldilocks_field::GoldilocksField, 
        extension::Extendable, 
        types::Field
    },

    iop::witness::{
        PartialWitness, 
        WitnessWrite
    }
};
use std::iter;
use anyhow::Result;

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

        if self.nodes.get(0).unwrap().len() >= usize::pow(2, self.depth.try_into().unwrap()) {
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


//verification circuit
pub fn verify<F: RichField + Extendable<D>, H: AlgebraicHasher<F>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    pos: Vec<bool>,
    siblings: &Vec<HashOutTarget>,
    root: &HashOutTarget,
    leaf: &HashOutTarget,
) {

    let mut node = *leaf;
    for (&p, sibling) in pos.iter().zip(siblings) {   

        if p {
            node = builder.hash_or_noop::<PoseidonHash>([
                sibling.elements.to_vec(),
                node.elements.to_vec()
              ].concat());
        } else {
            node = builder.hash_or_noop::<PoseidonHash>([
                node.elements.to_vec(),
                sibling.elements.to_vec()
                ].concat());

        }

    }

    for i in 0..4 {
        builder.connect(root.elements[i], node.elements[i]);
    }
}

#[cfg(test)]

mod tests {
    use crate::GoldilocksField;
    use crate::Field;
    use crate::PoseidonHash;
    use crate::Hasher;
    use crate::IncrementalTree;
    use crate::PoseidonGoldilocksConfig;
    use crate::GenericConfig;
    use crate::CircuitConfig;
    use crate::PartialWitness;
    use crate::CircuitBuilder;
    use crate::verify;
    use crate::WitnessWrite;
    use crate::Result;

    #[test]
    fn create_tree_test(){
        let zero = vec![GoldilocksField::from_canonical_u64(0)];
        let zero_hash = PoseidonHash::hash_or_noop(&zero);
        let cap_height = 3;

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let tree = IncrementalTree::<F, <C as GenericConfig<D>>::Hasher>::new(zero_hash, cap_height);

        println!("Empty tree of height {:?} created", cap_height);
        println!("{:?}", tree);

    }

    #[test]
    fn append_leaf_test() {
        let zero = vec![GoldilocksField::from_canonical_u64(0)];
        let zero_hash = PoseidonHash::hash_or_noop(&zero);
        let cap_height = 3;

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let mut tree = IncrementalTree::<F, <C as GenericConfig<D>>::Hasher>::new(zero_hash, cap_height);

        for i in 0..5 {
            tree.insert(PoseidonHash::hash_or_noop(&vec![GoldilocksField::from_canonical_u64(i + i*i + 2)]));
        }

        println!("Tree after leaves inserted:");
        println!("{:?}", tree);
    }

    #[test]
    fn merkle_proof_verify_test() {
        let zero_hash = PoseidonHash::hash_or_noop(
            &vec![GoldilocksField::from_canonical_u64(0)]
        );

        let cap_height = 3;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let mut tree = IncrementalTree::<F, <C as GenericConfig<D>>::Hasher>::new(zero_hash, cap_height);

        for i in 0..5 {
            tree.insert(PoseidonHash::hash_or_noop(&vec![GoldilocksField::from_canonical_u64(i + i*i + 2)]));
        }

        let i = 4;
        let leaf = PoseidonHash::hash_or_noop(&vec![GoldilocksField::from_canonical_u64(i + i*i + 2)]);

        let (siblings, pos) = tree.witness(leaf);
        assert_eq!(tree.check_proof( leaf, siblings, pos), true);
    }

    #[test]
    fn generate_and_verify_circuit_test() -> Result<()>{
        let zero_hash = PoseidonHash::hash_or_noop(
            &vec![GoldilocksField::from_canonical_u64(0)]
        );

        let cap_height = 3;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let mut tree = IncrementalTree::<F, <C as GenericConfig<D>>::Hasher>::new(zero_hash, cap_height);

        for i in 0..5 {
            tree.insert(PoseidonHash::hash_or_noop(&vec![GoldilocksField::from_canonical_u64(i + i*i + 2)]));
        }

        let i = 4;
        let leaf = PoseidonHash::hash_or_noop(&vec![GoldilocksField::from_canonical_u64(i + i*i + 2)]);

        let (siblings, pos) = tree.witness(leaf);
        assert_eq!(tree.check_proof( leaf, siblings.clone(), pos.clone()), true);


        let config = CircuitConfig::standard_recursion_config();

        let mut builder = CircuitBuilder::<F,D>::new(config);

        let leaf_t = builder.add_virtual_hash();
        let siblings_t = builder.add_virtual_hashes(siblings.clone().len());
        let root_t = builder.add_virtual_hash();

        //verification circuit
        verify::<GoldilocksField, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher, 2>(&mut builder, pos, &siblings_t, &root_t, &leaf_t);



        let mut pw: PartialWitness<_> = PartialWitness::<F>::new();
        pw.set_hash_target(leaf_t, leaf);
        for i in 0..siblings.clone().len() {
            pw.set_hash_target(siblings_t[i], *siblings.get(i).unwrap());
        }
        pw.set_hash_target(root_t, tree.root());

        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        
        data.verify(proof)
    }
}