use plonky2::{hash::hash_types::RichField, plonk::config::Hasher};

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
fn main() {
    println!("Hello, world!");
}
