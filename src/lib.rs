#![no_std]
#![no_main]
// #![cfg_attr(not(test), no_std)]
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
    }, util::timing::TimingTree
};
use plonky2::plonk::proof::ProofWithPublicInputs;
use plonky2::plonk::circuit_data::VerifierOnlyCircuitData;
use plonky2::plonk::circuit_data::CommonCircuitData;
use log::Level;
use plonky2::plonk::prover::prove;
use core::iter;
use anyhow::{Result, Ok};

#[macro_use]
extern crate alloc;
use alloc::vec::Vec;

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

type ProofTuple<F, C, const D: usize> = (
    ProofWithPublicInputs<F, C, D>,
    VerifierOnlyCircuitData<C, D>,
    CommonCircuitData<F, D>,
);

pub fn recursive_proof< F: RichField + Extendable<D> , C: GenericConfig<D, F = F>, InnerC: GenericConfig<D, F = F>, const D: usize>(
inner: &ProofTuple<F, InnerC, D>,
config: &CircuitConfig,
) -> Result<ProofTuple<F, C, D>> where <InnerC as GenericConfig<D>>::Hasher: AlgebraicHasher<F>, {

    let (inner_proof, inner_vd, inner_cd ) = inner;
    let mut builder = CircuitBuilder::<F,D>::new(config.clone());
    let pt = builder.add_virtual_proof_with_pis(inner_cd);
    let inner_data = builder.add_virtual_verifier_data(inner_cd.config.fri_config.cap_height);
    builder.verify_proof::<InnerC>(&pt, &inner_data, &inner_cd);

    let data = builder.build();

    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target(&pt, inner_proof);
    pw.set_verifier_data_target(&inner_data, inner_vd);

    let mut timing = TimingTree::new("prove", Level::Debug);

    let proof = prove::<F, C, D>(&data.prover_only, &data.common, pw, &mut timing)?;
    timing.print();

    // data.verify(proof.clone())
    Ok((proof, data.verifier_only, data.common))
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
    use plonky2::plonk::circuit_data::VerifierCircuitTarget;
    use crate::recursive_proof;
    use crate::ProofWithPublicInputs;

    #[test]
    fn create_tree_test(){
        let zero = vec![GoldilocksField::from_canonical_u64(0)];
        let zero_hash = PoseidonHash::hash_or_noop(&zero);
        let cap_height = 3;

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let tree = IncrementalTree::<F, <C as GenericConfig<D>>::Hasher>::new(zero_hash, cap_height);

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

        builder.register_public_inputs(&root_t.elements);

        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        
        data.verify(proof.clone())

    }

    // #[test]
    // fn recursive_test() -> Result<()>{
    //     let zero_hash = PoseidonHash::hash_or_noop(
    //         &vec![GoldilocksField::from_canonical_u64(0)]
    //     );

    //     let cap_height = 3;
    //     const D: usize = 2;
    //     type C = PoseidonGoldilocksConfig;
    //     type F = <C as GenericConfig<D>>::F;

    //     let mut tree = IncrementalTree::<F, <C as GenericConfig<D>>::Hasher>::new(zero_hash, cap_height);

    //     for i in 0..4 {
    //         tree.insert(PoseidonHash::hash_or_noop(&vec![GoldilocksField::from_canonical_u64(i + i*i + 2)]));
    //     }

    //     //first leaf proof
    //     let i = 3;
    //     let leaf = PoseidonHash::hash_or_noop(&vec![GoldilocksField::from_canonical_u64(i + i*i + 2)]);

    //     let (siblings, pos) = tree.witness(leaf);
    //     assert_eq!(tree.check_proof( leaf, siblings.clone(), pos.clone()), true);


    //     let config = CircuitConfig::standard_recursion_config();

    //     let mut builder = CircuitBuilder::<F,D>::new(config);

    //     let leaf_t = builder.add_virtual_hash();
    //     let siblings_t = builder.add_virtual_hashes(siblings.clone().len());
    //     let root_t = builder.add_virtual_hash();

    //     //verification circuit
    //     verify::<GoldilocksField, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher, 2>(&mut builder, pos, &siblings_t, &root_t, &leaf_t);



    //     let mut pw: PartialWitness<_> = PartialWitness::<F>::new();
    //     pw.set_hash_target(leaf_t, leaf);
    //     for i in 0..siblings.clone().len() {
    //         pw.set_hash_target(siblings_t[i], *siblings.get(i).unwrap());
    //     }
    //     pw.set_hash_target(root_t, tree.root());

    //     builder.register_public_inputs(&root_t.elements);

    //     let data = builder.build::<C>();
    //     let proof = data.prove(pw)?;


    //     let _ = data.verify(proof.clone());
    //     //second leaf proof
    //     let i = 4;
    //     let leaf2 = PoseidonHash::hash_or_noop(&vec![GoldilocksField::from_canonical_u64(i + i*i + 2)]);
    //     tree.insert(leaf2);
    //     let (siblings2, pos2) = tree.witness(leaf2);
    //     assert_eq!(tree.check_proof( leaf2, siblings2.clone(), pos2.clone()), true);

    //     let config2 = CircuitConfig::standard_recursion_config();

    //     let mut builder2 = CircuitBuilder::<F,D>::new(config2);

    //     let leaf_t2 = builder2.add_virtual_hash();
    //     let siblings_t2 = builder2.add_virtual_hashes(siblings2.clone().len());
    //     let root_t2 = builder2.add_virtual_hash();

    //     //verification circuit
    //     verify::<GoldilocksField, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher, 2>(&mut builder2, pos2, &siblings_t2, &root_t2, &leaf_t2);


    //     let mut pw2: PartialWitness<_> = PartialWitness::<F>::new();
    //     pw2.set_hash_target(leaf_t2, leaf2);
    //     for i in 0..siblings2.clone().len() {
    //         pw2.set_hash_target(siblings_t2[i], *siblings2.get(i).unwrap());
    //     }
    //     pw2.set_hash_target(root_t2, tree.root());

    //     builder2.register_public_inputs(&root_t2.elements);

    //     let data2 = builder2.build::<C>();
    //     let proof2 = data2.prove(pw2)?;
        
    //     let config3 = CircuitConfig::standard_recursion_config();

    //     let inner = (proof, data.verifier_only.clone(), data.common.clone());
    //     let inner2 = (proof2.clone(), data2.verifier_only.clone(), data2.common.clone());

    //     let middle = recursive_proof::<F, C, C, D>(&inner, &config3)?;
    //     let (_, _, common_data) = &middle;
    //     let middle2 = recursive_proof::<F, C, C, D>(&inner2, &config3)?;
    //     let (_, _, common_data2) = &middle2;

    //     let outer = recursive_proof::<F, C, C, D>(&middle2.clone(), &config3);
    //     let (proof3, vd3, common_data3) = &outer?;

        
    //     data2.verify(proof2.clone())
    // }

    
    // #[test]
    // fn recursive_test2() -> Result<()>{
    //     let zero_hash = PoseidonHash::hash_or_noop(
    //         &vec![GoldilocksField::from_canonical_u64(0)]
    //     );

    //     let cap_height = 3;
    //     const D: usize = 2;
    //     type C = PoseidonGoldilocksConfig;
    //     type F = <C as GenericConfig<D>>::F;

    //     let mut tree = IncrementalTree::<F, <C as GenericConfig<D>>::Hasher>::new(zero_hash, cap_height);

    //     for i in 0..4 {
    //         tree.insert(PoseidonHash::hash_or_noop(&vec![GoldilocksField::from_canonical_u64(i + i*i + 2)]));
    //     }

    //     //first leaf proof
    //     let i = 3;
    //     let leaf = PoseidonHash::hash_or_noop(&vec![GoldilocksField::from_canonical_u64(i + i*i + 2)]);

    //     let (siblings, pos) = tree.witness(leaf);
    //     assert_eq!(tree.check_proof( leaf, siblings.clone(), pos.clone()), true);

    //     let root = tree.root();
    //     let config = CircuitConfig::standard_recursion_config();

    //     let mut builder = CircuitBuilder::<F,D>::new(config);

    //     let leaf_t = builder.add_virtual_hash();
    //     let siblings_t = builder.add_virtual_hashes(siblings.clone().len());
    //     let root_t = builder.add_virtual_hash();

    //     //verification circuit
    //     verify::<GoldilocksField, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher, 2>(&mut builder, pos, &siblings_t, &root_t, &leaf_t);



    //     let mut pw: PartialWitness<_> = PartialWitness::<F>::new();
    //     pw.set_hash_target(leaf_t, leaf);
    //     for i in 0..siblings.clone().len() {
    //         pw.set_hash_target(siblings_t[i], *siblings.get(i).unwrap());
    //     }
    //     pw.set_hash_target(root_t, tree.root());

    //     builder.register_public_inputs(&root_t.elements);

    //     let data = builder.build::<C>();
    //     let proof = data.prove(pw)?;
        

    //     let _ = data.verify(proof.clone());

    //     //second leaf proof
    //     let i = 4;
    //     let leaf2 = PoseidonHash::hash_or_noop(&vec![GoldilocksField::from_canonical_u64(i + i*i + 2)]);
    //     tree.insert(leaf2);
    //     let (siblings2, pos2) = tree.witness(leaf2);
    //     assert_eq!(tree.check_proof( leaf2, siblings2.clone(), pos2.clone()), true);
    //     let root2 = tree.root();
    //     let config2 = CircuitConfig::standard_recursion_config();

    //     let mut builder2 = CircuitBuilder::<F,D>::new(config2);

    //     let leaf_t2 = builder2.add_virtual_hash();
    //     let siblings_t2 = builder2.add_virtual_hashes(siblings2.clone().len());
    //     let root_t2 = builder2.add_virtual_hash();

    //     //verification circuit
    //     verify::<GoldilocksField, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher, 2>(&mut builder2, pos2, &siblings_t2, &root_t2, &leaf_t2);


    //     let mut pw2: PartialWitness<_> = PartialWitness::<F>::new();
    //     pw2.set_hash_target(leaf_t2, leaf2);
    //     for i in 0..siblings2.clone().len() {
    //         pw2.set_hash_target(siblings_t2[i], *siblings2.get(i).unwrap());
    //     }
    //     pw2.set_hash_target(root_t2, tree.root());

    //     builder2.register_public_inputs(&root_t2.elements);

    //     let data2 = builder2.build::<C>();
    //     let proof2 = data2.prove(pw2)?;

    //     let config3 = CircuitConfig::standard_recursion_zk_config();
    //     let mut builder3 = CircuitBuilder::new(config3);
    //     let mut pw3 = PartialWitness::new();

    //     let proof_target0 = builder3.add_virtual_proof_with_pis(&data.common);
    //     pw3.set_proof_with_pis_target(&proof_target0, &ProofWithPublicInputs {proof: proof.proof.clone(), public_inputs: root.elements.to_vec()});

    //     let proof_target1 = builder3.add_virtual_proof_with_pis(&data2.common);
    //     pw3.set_proof_with_pis_target(&proof_target1, &ProofWithPublicInputs {proof: proof2.proof.clone(), public_inputs: root2.elements.to_vec()});


    //     let vd_target: VerifierCircuitTarget = VerifierCircuitTarget {
    //         constants_sigmas_cap: builder3.add_virtual_cap(data.common.config.fri_config.cap_height),
    //         circuit_digest: root_t,
    //     };

    //     builder3.verify_proof::<C>(&proof_target0, &vd_target, &data.common);
    //     builder3.verify_proof::<C>(&proof_target1, &vd_target, &data2.common);

    //     let data4 = builder3.build::<C>();
    //     let recursive_proof = data4.prove(pw3).unwrap();

    //     data4.verify(recursive_proof.clone())

    //     // data2.verify(proof2.clone())
    // }
}