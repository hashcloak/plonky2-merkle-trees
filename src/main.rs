// The following implementation is taken into reference https://github.com/skletsun/merkle-simple
// This is just for practicing and understanding plonky2 and not to be used in production at all

use plonky2::{hash::hash_types::RichField, plonk::config::Hasher};
use plonky2::{plonk::config::{GenericConfig, PoseidonGoldilocksConfig}, field::{goldilocks_field::GoldilocksField, types::Field}};

// use proof::{PathItem, Proof};
use std::collections::VecDeque;
// use treeelement::TreeElement;
// use utils::{Hashable, Hasher};

#[derive(Clone, Debug, Eq, PartialEq)]
/// Common type for leafs and internal nodes.
/// In order to store custom struct it should implement the Hashable trait.
pub enum TreeElement<F: RichField, H: Hasher<F>> {

    /// Leafs contain data.
    Leaf {
        /// Value to store withing the tree
        value: Vec<F>,
        /// Hash of the stored value
        hash: H::Hash,
    },
    /// Represents the internal node that can have children
    Node {
        /// Reference to the left subtree
        left: Box<TreeElement<F, H>>,
        /// Reference to the right subtree
        right: Box<TreeElement<F, H>>,
        /// Combined hash of child subtrees
        hash: H::Hash,
    },
}

impl<F: RichField, H: Hasher<F>> TreeElement<F, H> {
    /// Returns hash according to a node type
    pub fn hash(&self) -> H::Hash {
        match *self {
            TreeElement::Leaf { ref hash, .. } => *hash,
            TreeElement::Node { ref hash, .. } => *hash,
        }
    }

    /// Produces new leaf node from data
    pub fn new_leaf(value: Vec<F>) -> TreeElement<F,H> {
        TreeElement::Leaf {
            hash: H::hash_or_noop(&value),
            value: value,
        }
    }
    /// Produces new internal node from children elements
    pub fn new_node(left: TreeElement<F,H>, right: TreeElement<F,H>) -> TreeElement<F,H> {
        TreeElement::Node {
            hash: H::two_to_one(left.hash(), right.hash()),
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MerkleTree<F: RichField, H: Hasher<F>> {
    root: TreeElement<F, H>,

    /// The amount of elements
    count: usize,

    /// The height of the tree
    height: usize,
}

impl<F: RichField, H: Hasher<F>> MerkleTree<F, H> {

    /// Total amount of elements in tree
    pub fn count(&self) -> usize {
        self.count
    }

    /// Whether the tree empty or not
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// The height (number of layers) in tree
    pub fn height(&self) -> usize {
        self.height
    }

    /// Reference to the root element in tree
    pub fn root_hash(&self) -> H::Hash {
        self.root.hash()
    }

    /// Produces tree from the vector of Hashable
    pub fn from_vector(data: Vec<Vec<F>>) -> Option<Self> {
    
        let count = data.len();

        match count {
            0 => None,
            _ => {
                let mut height = 0;
                let mut src = VecDeque::with_capacity(count);

                // create first layer of leaves
                for val in data {
                    src.push_back(TreeElement::new_leaf(val));
                }

                // build tree without recursion, layer by layer
                while src.len() > 1 {
                    let mut new_layer: VecDeque<TreeElement<F,H>> =
                        VecDeque::with_capacity(src.len() / 2);

                    while !src.is_empty() {
                        // check for a case when we have the one element only - it will be the Leaf
                        if src.len() == 1 {
                            // it's a leaf - push it to the next turn of processing
                            new_layer.push_back(src.pop_front().unwrap());
                        } else {
                            // we take two elements and produce the Node
                            let left_node = src.pop_front().unwrap();
                            let right_node = src.pop_front().unwrap();
                            let node = TreeElement::new_node(left_node, right_node);
                            // and push it for further processing
                            new_layer.push_back(node);
                        }
                    }
                    // we've just processed the new layer of our tree
                    // increase the height of tree
                    height += 1;
                    // pass our prepared queue to the next iteration if any
                    src = new_layer;
                }
                // we ended up with only one element - this is the root node
                let root = src.pop_back().unwrap();

                // return the resulting tree
                Some(MerkleTree {
                    root: root,
                    count: count,
                    height: height,
                })
            }
        }
    }

    /// Generates the proof of inclusion
    pub fn get_proof(&self, value: Vec<F>) -> Option<Proof<F,H>>
    {
        // calculate hash of data
        let calculated_hash = H::hash_or_noop(&value);
        // and get the value of the root hash
        let root_hash = self.root_hash();

        // create a path first and feed it to Proof's construtor
        PathItem::create_path(&self.root, calculated_hash).map(
            |path| {
                Proof::new(value, root_hash, path)
            },
        )
    }
}



#[derive(Debug)]
/// Implements verification for inclusion of data into treeEleTreeElement
pub struct Proof<F: RichField, H: Hasher<F>> {
    /// Value to verify
    value: Vec<F>,

    /// Root hash of the treeEleTreeElement
    root_hash: H::Hash,

    /// Starting point of proof-path
    path: PathItem<F,H>,
}

#[derive(Debug, Clone)]
/// Data structure that the inclusion proof path consist of. Holds the information about
/// (1) hash values of this and sibling nodes and (2) a reference to the sub-item.
pub struct PathItem<F: RichField, H: Hasher<F>> {
    /// Hash of current node
    hash: H::Hash,

    /// Hash of sibling if any. Leaf element doesn't have any siblings so we wrap it with Option.
    sibling_hash: Option<Position<F,H>>,

    /// Reference to the child node in the direction from root to leafs
    sub_item: Option<Box<PathItem<F,H>>>,
}

#[derive(Debug, Clone)]
/// Encapsulates positioning of sibling node in the inclusion path
enum Position<F: RichField, H: Hasher<F>> {
    /// For the left sibling
    Left(H::Hash),

    /// For the right sibling
    Right(H::Hash),
}


impl <F: RichField, H: Hasher<F>>PathItem<F,H> {
    /// Recursively creates path according to the exact type of nodes until element is found.
    /// Returns None in case element hasn't been found in the tree.
    pub fn create_path(
        node: &TreeElement<F,H>,
        hash_to_find: H::Hash,
    ) -> Option<PathItem<F,H>> {
        match *node {
            TreeElement::Node {
                ref left,
                ref right,
                ref hash,
            } => PathItem::new_node_proof(*hash, hash_to_find, left, right),
            TreeElement::Leaf { ref hash, .. } => PathItem::new_leaf_proof(*hash, hash_to_find),
        }
    }

    fn new_leaf_proof(hash: H::Hash, hash_to_find: H::Hash) -> Option<PathItem<F,H>> {
        if hash == hash_to_find {
            Some(PathItem {
                hash: hash,
                sibling_hash: None,
                sub_item: None,
            })
        } else {
            None
        }
    }

    /// Creates an item in the inclusion proof path for an internal node (not leaf)
    fn new_node_proof(
        hash: H::Hash,
        hash_to_find: H::Hash,
        left: &TreeElement<F,H>,
        right: &TreeElement<F,H>,
    ) -> Option<PathItem<F,H>> {
    // Recusively go to the left node
    PathItem::create_path(left, hash_to_find)
        .map(|item| {
            (item, Some(Position::Right(right.hash().clone())))
        }).or_else(|| {
            let child_item = PathItem::create_path(right, hash_to_find);
            child_item.map(|item| {
                (item, Some(Position::Left(left.hash().clone())))
            })
        }).map(|(path_item, sibl_hash)| {
            // And finally construct the path item
            PathItem {
                hash: hash,
                sibling_hash: sibl_hash,
                sub_item: Some(Box::new(path_item)),
            }
        })
    }
}

impl <F: RichField, H: Hasher<F>> Proof<F, H> {
    /// Produces new Proof structure
    pub fn new(value: Vec<F>, root_hash: H::Hash, path_item: PathItem<F,H>) -> Self {
        Proof {
            value: value,
            root_hash: root_hash,
            path: path_item,
        }
    }

    /// Validates the path
    pub fn validate(&self, root_hash: H::Hash) -> bool {
        // Check for the obvious things first
        if root_hash != self.root_hash || self.path.hash != root_hash {
            return false;
        }

        // recursive check the path
        self.validate_recursive(&self.path)
    }

    fn validate_recursive(&self, path_item: &PathItem<F,H>) -> bool {
        match path_item.sub_item {
            Some(ref child) => {
                match path_item.sibling_hash {
                    Some(Position::Left(ref hash)) => {
                        // calculating node hash taking into account that sibling's hash should be
                        // the first parameter of hash_node_data() since it is positioned left
                        let calculated_hash = H::two_to_one(*hash, child.hash);
                        // it should match the node's hash
                        (calculated_hash == path_item.hash) && self.validate_recursive(child)
                    }
                    Some(Position::Right(ref hash)) => {
                        // calculating node hash taking into account that sibling's hash should be
                        // the second parameter of hash_node_data() since it is positioned right
                        let calculated_hash = H::two_to_one(child.hash, *hash);
                        // it should match the node's hash
                        (calculated_hash == path_item.hash) && self.validate_recursive(child)
                    }
                    None => false,
                }
            }
            None => path_item.sibling_hash.is_none() && path_item.hash == H::hash_or_noop(&self.value),
        }
    }
}

// fn random_data<F: RichField>(n: usize, k: usize) -> Vec<Vec<F>> {
//     (0..n).map(|_| F::rand_vec(k)).collect()
// }
fn main() {
    println!("Hello, world!");
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    // // The cloning of leaves doesnt work because clone is not implemented for Vec<GoldilocksField>
    // // Therefore hardcoding the values
    // let leaves = random_data::<F>(4, 100);
    // println!("{:?}",leaves);

    let leaves = vec![
    vec![GoldilocksField::from_canonical_u64(2890852870)],
    vec![GoldilocksField::from_canonical_u64(156728478)], 
    vec![GoldilocksField::from_canonical_u64(2876514289)], 
    vec![GoldilocksField::from_canonical_u64(984286162)]
    ];


    let tree: MerkleTree<_, _> = MerkleTree::<F, <C as GenericConfig<D>>::Hasher>::from_vector(leaves.clone()).unwrap();

    // println!("{:?}", tree);


    let proof = tree.get_proof(vec![GoldilocksField::from_canonical_u64(2890852870)]);
    // assert!(proof.is_some());
    // println!("{:?}", proof.unwrap());

    let result = proof.unwrap().validate(tree.root_hash());
    assert!(result);
    println!("{:?}", result);

}
