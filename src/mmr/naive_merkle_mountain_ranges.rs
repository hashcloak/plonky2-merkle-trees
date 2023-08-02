use std::cmp::max;

use itertools::Itertools;
use num::{ToPrimitive, Integer};
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::hash::hash_types::HashOut;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;

/**
 * Functionality:
 * - add leaf
 * - get proof for leaf
 * - verify proof
 * 
 * This is a naive implementation to get familiar with the workings of mmr
 * Does not focus on efficiency, both in computation and memory space 
*/

#[derive(Debug, Clone)]
pub struct naive_MMR { // Merkle Mountain Ranges
  // holds values of all elements in mmr
  pub elements: Vec<HashOut<GoldilocksField>>, 
  // holds height for all elements in tree (0 is leaf). Indices line up with the elements vector
  pub heights: Vec<u32>, 
  // total leaves in all mountains together
  pub nr_leaves: u64,
  // max_height that occurs amongst peaks
  pub max_height: u32,
  // all peaks in the MMR, if it is a perfect Merkle tree, this is 1 elements
  pub peaks: Vec<HashOut<GoldilocksField>>
}

// After bagging the peaks - in this form the MMR will have a single root 
pub struct MMR_bagged {
  pub mmr: naive_MMR,
  pub root: HashOut<GoldilocksField>
}

impl naive_MMR {
  pub fn new(leaf: GoldilocksField) -> Self {
    let leaf_hash = PoseidonHash::hash_or_noop(&[leaf]);

    naive_MMR {
      elements: [leaf_hash].to_vec(),
      heights: [0].to_vec(),
      nr_leaves: 1,
      max_height: 0,
      peaks: [].to_vec(),
    }
  }

  pub fn add_leaf(&mut self, leaf: GoldilocksField) {
    let leaf_hash = PoseidonHash::hash_or_noop(&[leaf]);
    // First we add the leaf to the tree
    self.elements.push(leaf_hash);
    self.heights.push(0);
    self.nr_leaves += 1;
    self.peaks.push(leaf_hash);

    // Next we check whether this requires adding any further elements

    // If previous element was a leaf we need to add a node
    if self.heights[self.heights.len() - 2] == 0 {
      let node_1 = PoseidonHash::two_to_one(self.elements[self.elements.len() - 2], leaf_hash);
      self.elements.push(node_1);
      self.heights.push(1);
      // If this was the beginning of the tree, make sure the height is adjusted
      if self.max_height == 0 {
        self.max_height = 1;
      }
      // Remove previous leaves from peaks and replace with this new node
      self.peaks.pop();
      self.peaks.pop();
      self.peaks.push(node_1);
    }
    
    // Possibly add more nodes on higher levels
    // For each layer the question is whether this leaf_nr is a multiple of the merkle tree leaf amount corresponding to the layer
    // Layer 1: Merkle tree of 2^1 leaves (This layer we already did above)
    // Layer 2: Merkle tree of 2^2 leaves
    // Layer 3: Merkle tree of 2^3 leaves
    let base: i32 = 2;
    for i in 2..(self.max_height + 2) {
      let nr_leaves: u64 = base.pow(i.try_into().unwrap()).try_into().unwrap();
      // Check whether the leaf we inserted is a multiple of the nr_leaves (Whether it "completes" a next merkle tree)
      //  if that's the case, we need to merge peaks and add a new node
      if self.nr_leaves % nr_leaves == 0 {
        // The other peak is nr_leaves-1 steps back from the peak we're looking at
        let prev_peak = self.elements[self.elements.len() - 1 - (nr_leaves.to_usize().unwrap() - 1)];
        let next_node = PoseidonHash::two_to_one(prev_peak, self.elements[self.elements.len() - 1]);
        self.elements.push(next_node);
        self.heights.push(i.try_into().unwrap());
        self.max_height = max(self.max_height, i);

        // These two previous peaks get replaced by the new one
        self.peaks.pop();
        self.peaks.pop();
        self.peaks.push(next_node);
      } else {
        // Once the "chain" gets broken we can stop because further updating won't be necessary
        break;
      }
    }

  }

  // Creating a root for the MMR: this means hashing all peaks together from left to right
  // in case the MMR is already a perfect binary tree, the root equals the only peak that exists
  pub fn bagging_the_peaks(self) -> MMR_bagged {
    let peaks_elm = self.peaks.iter().flat_map(|x| x.elements).collect_vec();
    let root = PoseidonHash::hash_or_noop(&peaks_elm);
    MMR_bagged {
      mmr: self,
      root: root
    }
  }

  // Return MMR proof, which consists of:
  // - (standard) Merkle proof for the subtree of which the leaf is part of
  // - all the peaks
  // - index of leaf within the subtree
  pub fn get_proof(self, index: usize) -> (Vec<HashOut<GoldilocksField>>, Vec<HashOut<GoldilocksField>>, usize) {
    // 1. Determine subtree information that the leaf is part of
    let (highest_peak_subtree, index_highest_peak, start) = get_info_subtree_leaf_index(&self, index);
    let subtree = &self.elements[start..index_highest_peak];
    let subtree_heights = &self.heights[start..index_highest_peak];

    // 2. Get the Merkle proof for the subtree
    let relative_index = index - start;
    let merkle_proof = get_merkle_proof(subtree.to_vec(), subtree_heights.to_vec(), relative_index, highest_peak_subtree);

    // 3. Return merkle proof, peaks and leaf index within subtree
    (merkle_proof, self.peaks, relative_index)
  }

  // Return MMR proof with an extended Merkle proof, consisting of:
  // - Merkle proof for the subtree of which the leaf is part of WITH ROOT. 
  //     In a standard Merkle proof the root is not included, but this is useful for the recursive step, and included here
  // - all the peaks of the MMR
  // - index of leaf within the subtree
  pub fn get_proof_with_extended_merkleproof(self, index: usize) -> (Vec<HashOut<GoldilocksField>>, Vec<HashOut<GoldilocksField>>, usize) {
    // 1. Determine subtree information that the leaf is part of
    let (highest_peak_subtree, index_highest_peak, start) = get_info_subtree_leaf_index(&self, index);
    let subtree = &self.elements[start..=index_highest_peak];
    let subtree_heights = &self.heights[start..index_highest_peak];

    // 2. Get the Merkle proof for the subtree, including the root at the end - which is normally the value the final hash is compared to
    let relative_index = index - start;
    let mut merkle_proof = get_merkle_proof(subtree.to_vec(), subtree_heights.to_vec(), relative_index, highest_peak_subtree);
    
    // Additionally, add the root of the subtree to the proof 
    merkle_proof.push(*subtree.last().unwrap());

    // 3. Return merkle proof, peaks and leaf index within subtree
    (merkle_proof, self.peaks, relative_index)
  }

  // Verify proof for leaf in MMR. Checks 3 things:
  // - the standard Merkle tree proof for the subtree the leaf is part of
  // - resulting peak of Merkle tree proof must be in MMR peaks
  // - MMR root after bagging the peaks must be equal to hashed peaks
  pub fn verify_proof(
    relative_leaf_index: usize, // This is the index within the smaller subtree the leaf is in
    leaf: GoldilocksField,
    merkle_proof_subtree: Vec<HashOut<GoldilocksField>>, 
    peaks: Vec<HashOut<GoldilocksField>>,
    root_check: HashOut<GoldilocksField>) -> bool {

    let nr_leaves_subtree = 2i32.pow(merkle_proof_subtree.len().to_u32().unwrap()).to_usize().unwrap();
    // This is calculated to know at what side the sibling from the proof should be hashed
    let standardized_index = get_standard_index(relative_leaf_index, nr_leaves_subtree);

    let leaf_hash = PoseidonHash::hash_or_noop(&[leaf]);

    let mut next_hash;
    if standardized_index.is_even() {
      next_hash = PoseidonHash::two_to_one(leaf_hash, merkle_proof_subtree[0]);
    } else {
      next_hash= PoseidonHash::two_to_one(merkle_proof_subtree[0], leaf_hash);
    }
    let mut updated_index = standardized_index/2;

    for i in 1..merkle_proof_subtree.len() {
      if updated_index.is_even() {
        next_hash = PoseidonHash::two_to_one(next_hash, merkle_proof_subtree[i]);
      } else {
        next_hash = PoseidonHash::two_to_one(merkle_proof_subtree[i], next_hash);
      }
      updated_index = updated_index/2;
    }

    // Now, next_hash should be amongst the peaks. Check this
    assert!(peaks.contains(&next_hash));

    // Hash all peaks together to get to root
    let peaks_elm = peaks.iter().flat_map(|x| x.elements).collect_vec();
    let calc_root = PoseidonHash::hash_or_noop(&peaks_elm);
    calc_root == root_check
  }

  // TODO improve this terrible drawing xD
  pub fn paint(self) {
    for height in (2..=self.max_height).rev() {
      
      // count the nr of occurrences of this height in the height list
      let count = self.heights.iter().filter(|&&h| h == height.to_u32().unwrap_or(0)).count();

      for _c in 0..count {
        print!(" ");
        print!("/\\");
        print!(" ");
      }

      for _j in 0..height {
        print!("\n");
      }
    }

    for i in 0..self.nr_leaves {
      if i % 2 == 0 {
        print!("/");
      } else {
        print!("\\");
      }
      
    }
  }
  
}

// Every leaf in an MMR is also part of a perfect Merkle tree, which is a subtree of the MMR
// For the given leaf_index, return:
// - height of subtree that leaf is part of
// - index of that peak (in the MMR)
// - index of start subtree (in the MMR)
pub fn get_info_subtree_leaf_index(mmr: &naive_MMR, leaf_index: usize) -> (u32, usize, usize) {
  // From the index, go to the right and decide where the highest peak is 
  //   (keep in mind that we know the height of highest peaks)
  let mut highest_peak_subtree: u32 = 0;
  let mut index_highest_peak= 0;
  for i in leaf_index..mmr.elements.len() {
    if mmr.heights[i] > highest_peak_subtree {
      highest_peak_subtree = mmr.heights[i];
      index_highest_peak = i;
      if highest_peak_subtree == mmr.max_height {
        break;
      }
    }
  }

  // From that peak, we know how many elements make up the sub-tree
  // 2^h * 2 -1
  let len_subtree: usize = (2u32.pow(highest_peak_subtree)*2-2).to_usize().unwrap();

  let start = index_highest_peak - len_subtree;
  (highest_peak_subtree, index_highest_peak, start)
}


// Return a (standard) Merkle proof for the given subtree
fn get_merkle_proof(
      subtree: Vec<HashOut<GoldilocksField>>, 
      subtree_heights: Vec<u32>, 
      leaf_index: usize, // this is an mmr index
      max_height: u32) -> Vec<HashOut<GoldilocksField>> {
  assert!(subtree_heights[leaf_index] == 0); // check that the given index actually belongs to a leaf
  let mut proof_hashes = Vec::new();
  let mut updated_index;

  // First, get the other leaf
  let leaf_right = leaf_index + 1 < subtree_heights.len() && subtree_heights[leaf_index + 1] == 0;
  if leaf_right {
    proof_hashes.push(subtree[leaf_index + 1]);
    updated_index = leaf_index + 1;
  } else {
    proof_hashes.push(subtree[leaf_index - 1]);
    updated_index = leaf_index - 1;
  }

  updated_index = max(updated_index, leaf_index) + 1; // the node that we've arrived at after considering the 2 leaves

  // Now, for all levels of the subtree, get the hashes on the "other side" that make the proof
  for h in 1..max_height {
    let diff: usize = (2i32.pow(h+1) -1).to_usize().unwrap();

    // Because of how the tree was built, only the sibling that is exactly at 2^(h+1) - 1 distance is needed for the next step
    // So check this elements (1) exists and (2) has the same height
    if updated_index + diff < subtree.len() && subtree_heights[updated_index + diff] == h {
      proof_hashes.push(subtree[updated_index + diff]);
      updated_index = updated_index + diff;
    } else {
      proof_hashes.push(subtree[updated_index - diff]); //otherwise it must be the other side
      updated_index = updated_index;
    }
  
    // This moves to the node we just got the other input for
    updated_index += 1;
  }

  proof_hashes
}

// return 2^h * 2 -1
pub fn get_nr_elms(nr_leaves: usize) -> usize {
  let h = nr_leaves.ilog2();
  (2i32.pow(h)*2-1).to_usize().unwrap()
}

// Transform a leaf_index of a MMR to the corresponding leaf_index of a "normal" Merkle tree.
pub fn get_standard_index(leaf_index: usize, nr_leaves: usize) -> usize {
  // Base case
  if nr_leaves == 4 || nr_leaves == 2 {
    if leaf_index == 0 || leaf_index == 1 {
      return leaf_index;
    } else {
      return leaf_index -1;
    }
  }

  // Recursive step
  // If we're on the right side of the tree, add 1+ ((nr_leaves-2) / 2).
  // in the recursive step correct for the nr_leaves
  //    otherwise add nothing, and the recursive step also doesn't need to correct
  let nr_elms = get_nr_elms(nr_leaves);

  if leaf_index >= (nr_elms/2) {
     // add 1+ ((nr_leaves-2) / 2) for the level
    return 1 + ((nr_leaves-2) / 2) + get_standard_index(leaf_index - (nr_leaves-1), nr_leaves/2);
  } else {
    return get_standard_index(leaf_index, nr_leaves/2);
  }

}

#[cfg(test)]
mod tests {
  use anyhow::Result;
  use itertools::Itertools;
  use rand::Rng;
  use plonky2::{field::{goldilocks_field::GoldilocksField, types::Field}, hash::poseidon::PoseidonHash, plonk::config::Hasher};
  use crate::mmr::naive_merkle_mountain_ranges::{naive_MMR, get_merkle_proof, get_standard_index};
  const GOLDILOCKS_FIELD_ORDER: u64 = 18446744069414584321;

  #[test]
  fn test_tree_7_leaves() -> Result<()> {
    let mut rng = rand::thread_rng();
    let mut mmr = naive_MMR::new(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
    for _i in 0..6 {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    // Uncomment this for checking what the mmr looks like. Note that the paint function is terrible
    // println!("{:#?}", mmr.heights);
    // println!("{:#?}", mmr.nr_leaves);
    // println!("{:#?}", mmr.peaks);
    // mmr.paint();

    Ok(())
  }

  #[test]
  fn test_bagging_peaks_4_leaves() -> Result<()> {
    let mut rng = rand::thread_rng();
    let mut mmr = naive_MMR::new(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
    for _i in 0..3 {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }

    // In this case the mmr is already a perfect merkle tree, so bagging the tree results in a root equal to the only peak that exists
    let mmr_bagged = mmr.bagging_the_peaks();
    assert!(mmr_bagged.mmr.peaks[0] == mmr_bagged.root);
    
    Ok(())
  }

  #[test]
  fn test_bagging_peaks_7_leaves() -> Result<()> {
    let mut rng = rand::thread_rng();
    let mut mmr = naive_MMR::new(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
    for _i in 0..6 {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    
    // Should hash together elms 6, 9,10
    let expected_peaks = [mmr.elements[6], mmr.elements[9], mmr.elements[10]];
    let peaks_elm = expected_peaks.iter().flat_map(|x| x.elements).collect_vec();
    let root = PoseidonHash::hash_or_noop(&peaks_elm);
    let mmr_bagged = mmr.bagging_the_peaks();
    
    assert!(root == mmr_bagged.root);
    Ok(())
  }

  #[test]
  fn test_bagging_peaks_30_leaves() -> Result<()> {
    let mut rng = rand::thread_rng();
    let mut mmr = naive_MMR::new(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
    for _i in 0..30 {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    
    // Should hash together elms 6, 9,10
    let expected_peaks = [mmr.elements[30], mmr.elements[45], mmr.elements[52], mmr.elements[55], mmr.elements[56]];
    let peaks_elm = expected_peaks.iter().flat_map(|x| x.elements).collect_vec();
    let root = PoseidonHash::hash_or_noop(&peaks_elm);
    let mmr_bagged = mmr.bagging_the_peaks();
    assert!(root == mmr_bagged.root);
    Ok(())
  }

  #[test]
  fn test_merkle_proof_subtree_index0() -> Result<()> {
    let mut rng = rand::thread_rng();
    let mut mmr = naive_MMR::new(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
    for _i in 0..7 {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    let subtree = mmr.elements.clone();
    let pr = get_merkle_proof(subtree, mmr.heights.clone(), 0, mmr.max_height);
    // Proof for leaf 0 should return elms 1, 5, 13
    assert!(pr[0] == mmr.elements[1]);
    assert!(pr[1] == mmr.elements[5]);
    assert!(pr[2] == mmr.elements[13]);
    Ok(())
  }

  #[test]
  fn test_merkle_proof_subtree_index8() -> Result<()> {
    let mut rng = rand::thread_rng();
    let mut mmr = naive_MMR::new(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
    for _i in 0..7 {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    let subtree = mmr.elements.clone();
    let pr = get_merkle_proof(subtree, mmr.heights.clone(), 8, mmr.max_height);
    // Proof for leaf 8 should return elms 7, 12, 6
    assert!(pr[0] == mmr.elements[7]);
    assert!(pr[1] == mmr.elements[12]);
    assert!(pr[2] == mmr.elements[6]);
    Ok(())
  }

  #[test]
  fn test_mmr_proof_tree_8_leaves() -> Result<()> {
    let mut rng = rand::thread_rng();
    let leaf0 = GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER));
    let mut mmr = naive_MMR::new(leaf0);
    for _i in 0..7 {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    let mmr_bagged = mmr.clone().bagging_the_peaks();
    let pr = mmr.clone().get_proof(0);

    let verified = naive_MMR::verify_proof(0, leaf0, pr.0, pr.1, mmr_bagged.root);
    assert!(verified);
    Ok(())
  }

  #[test]
  fn test_get_original_index_tree4() -> Result<()> {
    let res0 = get_standard_index(0, 4);
    let res1 = get_standard_index(1, 4);
    let res2 = get_standard_index(3, 4);
    let res3 = get_standard_index(4, 4);
    assert!([res0, res1, res2, res3] == [0,1,2,3]); 
    Ok(())
  }

  #[test]
  fn test_get_original_index_tree8() -> Result<()> {
    let nr_leaves = 8;
    let res0 = get_standard_index(0, nr_leaves);
    let res1 = get_standard_index(1, nr_leaves);
    let res2 = get_standard_index(3, nr_leaves);
    let res3 = get_standard_index(4, nr_leaves);

    let res4 = get_standard_index(7, nr_leaves);
    let res5 = get_standard_index(8, nr_leaves);
    let res6 = get_standard_index(10, nr_leaves);
    let res7 = get_standard_index(11, nr_leaves);

    assert!([res0, res1, res2, res3, res4, res5, res6, res7] == [0,1,2,3,4,5,6,7]); 

    Ok(())
  }

  #[test]
  fn test_get_original_index_tree16() -> Result<()> {
    let nr_leaves = 16;
    let res0 = get_standard_index(0, nr_leaves);
    let res1 = get_standard_index(1, nr_leaves);
    let res2 = get_standard_index(3, nr_leaves);
    let res3 = get_standard_index(4, nr_leaves);

    let res4 = get_standard_index(7, nr_leaves);
    let res5 = get_standard_index(8, nr_leaves);
    let res6 = get_standard_index(10, nr_leaves);
    let res7 = get_standard_index(11, nr_leaves);

    let res8 = get_standard_index(15, nr_leaves);
    let res9 = get_standard_index(16, nr_leaves);
    let res10 = get_standard_index(18, nr_leaves);
    let res11 =  get_standard_index(19, nr_leaves);

    let res12 = get_standard_index(22, nr_leaves);
    let res13 = get_standard_index(23, nr_leaves);
    let res14 = get_standard_index(25, nr_leaves);
    let res15 = get_standard_index(26, nr_leaves);

    assert!([res0, res1, res2, res3, res4, res5, res6, res7] == [0,1,2,3,4,5,6,7]); 
    assert!([res8, res9, res10, res11, res12, res13, res14, res15] == [8,9,10,11,12,13,14,15]); 
    Ok(())
  }

  #[test]
  fn test_get_original_index_tree32() -> Result<()> {
    let nr_leaves = 32;
    let res0 = get_standard_index(0, nr_leaves);
    let res1 = get_standard_index(1, nr_leaves);
    let res2 = get_standard_index(3, nr_leaves);
    let res3 = get_standard_index(4, nr_leaves);

    let res4 = get_standard_index(7, nr_leaves);
    let res5 = get_standard_index(8, nr_leaves);
    let res6 = get_standard_index(10, nr_leaves);
    let res7 = get_standard_index(11, nr_leaves);

    let res8 = get_standard_index(15, nr_leaves);
    let res9 = get_standard_index(16, nr_leaves);
    let res10 = get_standard_index(18, nr_leaves);
    let res11 =  get_standard_index(19, nr_leaves);

    let res12 = get_standard_index(22, nr_leaves);
    let res13 = get_standard_index(23, nr_leaves);
    let res14 = get_standard_index(25, nr_leaves);
    let res15 = get_standard_index(26, nr_leaves);

    let res16 = get_standard_index(31, nr_leaves);
    let res17 = get_standard_index(32, nr_leaves);
    let res18 = get_standard_index(34, nr_leaves);
    let res19= get_standard_index(35, nr_leaves);

    let res20 = get_standard_index(38, nr_leaves);
    let res21 = get_standard_index(39, nr_leaves);
    let res22 = get_standard_index(41, nr_leaves);
    let res23= get_standard_index(42, nr_leaves);
    
    assert!([res0, res1, res2, res3, res4, res5, res6, res7] == [0,1,2,3,4,5,6,7]); 
    assert!([res8, res9, res10, res11, res12, res13, res14, res15] == [8,9,10,11,12,13,14,15]); 
    assert!([res16, res17, res18, res19, res20, res21, res22, res23] == [16,17,18,19,20,21,22,23]); 
    Ok(())
  }


  #[test]
  fn test_mmr_proof_tree_8_leaves_all_indices() -> Result<()> {
    let mut leaves = Vec::new();
    let mut rng = rand::thread_rng();
    for _i in 0..8 {
      leaves.push(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
    }
    let mut mmr = naive_MMR::new(leaves[0]);
    for i in 1..8 {
      mmr.add_leaf(leaves[i]);  
    }
    
    let mmr_bagged = mmr.clone().bagging_the_peaks();

    let pr1 = mmr.clone().get_proof(1);
    let verified1 = naive_MMR::verify_proof(1, leaves[1], pr1.0, pr1.1, mmr_bagged.root);

    let pr2 = mmr.clone().get_proof(3);
    // Leaf index 3 in the MMR corresponds to the third leaf that was inserted
    let verified2 = naive_MMR::verify_proof(3, leaves[2], pr2.0, pr2.1, mmr_bagged.root);

    let pr3 = mmr.clone().get_proof(4);
    // Leaf index 4 in the MMR corresponds to the fourth leaf that was inserted
    let verified3 = naive_MMR::verify_proof(4, leaves[3], pr3.0, pr3.1, mmr_bagged.root);

    let pr4 = mmr.clone().get_proof(7);
    // Leaf index 7 in the MMR corresponds to the fifth leaf that was inserted
    let verified4 = naive_MMR::verify_proof(7, leaves[4], pr4.0, pr4.1, mmr_bagged.root);

    let pr5 = mmr.clone().get_proof(8);
    // Leaf index 8 in the MMR corresponds to the sixth leaf that was inserted
    let verified5 = naive_MMR::verify_proof(8, leaves[5], pr5.0, pr5.1, mmr_bagged.root);

    let pr6 = mmr.clone().get_proof(10);
    // Leaf index 10 in the MMR corresponds to the seventh leaf that was inserted
    let verified6 = naive_MMR::verify_proof(10, leaves[6], pr6.0, pr6.1, mmr_bagged.root);

    let pr7 = mmr.clone().get_proof(11);
    // Leaf index 11 in the MMR corresponds to the fifth leaf that was inserted
    let verified7 = naive_MMR::verify_proof(11, leaves[7], pr7.0, pr7.1, mmr_bagged.root);

    assert!(verified1 && verified2 && verified3 && verified4 && verified5 && verified6 && verified7);
    Ok(())
  }

  #[test]
  fn test_mmr_proof_tree_16_leaves_all_indices() -> Result<()> {
    let mut leaves = Vec::new();
    let mut rng = rand::thread_rng();
    for _i in 0..16 {
      leaves.push(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
    }
    let mut mmr = naive_MMR::new(leaves[0]);
    for i in 1..16 {
      mmr.add_leaf(leaves[i]);  
    }
    
    let mmr_bagged = mmr.clone().bagging_the_peaks();

    let pr0 = mmr.clone().get_proof(0);
    let verified0 = naive_MMR::verify_proof(0, leaves[0], pr0.0, pr0.1, mmr_bagged.root);

    let pr1 = mmr.clone().get_proof(1);
    let verified1 = naive_MMR::verify_proof(1, leaves[1], pr1.0, pr1.1, mmr_bagged.root);

    let pr2 = mmr.clone().get_proof(3);
    // Leaf index 3 in the MMR corresponds to the third leaf that was inserted
    let verified2 = naive_MMR::verify_proof(3, leaves[2], pr2.0, pr2.1, mmr_bagged.root);

    let pr3 = mmr.clone().get_proof(4);
    // Leaf index 4 in the MMR corresponds to the fourth leaf that was inserted
    let verified3 = naive_MMR::verify_proof(4, leaves[3], pr3.0, pr3.1, mmr_bagged.root);

    let pr4 = mmr.clone().get_proof(7);
    // Leaf index 7 in the MMR corresponds to the fifth leaf that was inserted
    let verified4 = naive_MMR::verify_proof(7, leaves[4], pr4.0, pr4.1, mmr_bagged.root);

    let pr5 = mmr.clone().get_proof(8);
    // Leaf index 8 in the MMR corresponds to the sixth leaf that was inserted
    let verified5 = naive_MMR::verify_proof(8, leaves[5], pr5.0, pr5.1, mmr_bagged.root);

    let pr6 = mmr.clone().get_proof(10);
    // Leaf index 10 in the MMR corresponds to the seventh leaf that was inserted
    let verified6 = naive_MMR::verify_proof(10, leaves[6], pr6.0, pr6.1, mmr_bagged.root);

    let pr7 = mmr.clone().get_proof(11);
    // Leaf index 11 in the MMR corresponds to the fifth leaf that was inserted
    let verified7 = naive_MMR::verify_proof(11, leaves[7], pr7.0, pr7.1, mmr_bagged.root);

    let pr8 = mmr.clone().get_proof(15);
    let verified8 = naive_MMR::verify_proof(15, leaves[8], pr8.0, pr8.1, mmr_bagged.root);

    let pr9 = mmr.clone().get_proof(16);
    let verified9 = naive_MMR::verify_proof(16, leaves[9], pr9.0, pr9.1, mmr_bagged.root);

    let pr10 = mmr.clone().get_proof(18);
    let verified10 = naive_MMR::verify_proof(18, leaves[10], pr10.0, pr10.1, mmr_bagged.root);

    let pr11 = mmr.clone().get_proof(19);
    let verified11 = naive_MMR::verify_proof(19, leaves[11], pr11.0, pr11.1, mmr_bagged.root);

    let pr12 = mmr.clone().get_proof(22);
    let verified12 = naive_MMR::verify_proof(22, leaves[12], pr12.0, pr12.1, mmr_bagged.root);

    let pr13 = mmr.clone().get_proof(23);
    let verified13 = naive_MMR::verify_proof(23, leaves[13], pr13.0, pr13.1, mmr_bagged.root);

    let pr14 = mmr.clone().get_proof(25);
    let verified14 = naive_MMR::verify_proof(25, leaves[14], pr14.0, pr14.1, mmr_bagged.root);

    let pr15 = mmr.clone().get_proof(26);
    let verified15 = naive_MMR::verify_proof(26, leaves[15], pr15.0, pr15.1, mmr_bagged.root);

    assert!(verified0 && verified1 && verified2 && verified3 && verified4 && verified5 && verified6 && verified7);
    assert!(verified8 && verified9 && verified10 && verified11 && verified12 && verified13 && verified14 && verified15);
    Ok(())
  }

  #[test]
  fn test_mmr_proof_tree_18_leaves_all_indices() -> Result<()> {
    let mut leaves = Vec::new();
    let mut rng = rand::thread_rng();
    for _i in 0..18 {
      leaves.push(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
    }
    let mut mmr = naive_MMR::new(leaves[0]);
    for i in 1..18 {
      mmr.add_leaf(leaves[i]);  
    }
    
    let mmr_bagged = mmr.clone().bagging_the_peaks();

    let pr0 = mmr.clone().get_proof(0);
    let verified0 = naive_MMR::verify_proof(0, leaves[0], pr0.0, pr0.1, mmr_bagged.root);

    let pr1 = mmr.clone().get_proof(1);
    let verified1 = naive_MMR::verify_proof(1, leaves[1], pr1.0, pr1.1, mmr_bagged.root);

    let pr2 = mmr.clone().get_proof(3);
    let verified2 = naive_MMR::verify_proof(3, leaves[2], pr2.0, pr2.1, mmr_bagged.root);

    let pr3 = mmr.clone().get_proof(4);
    let verified3 = naive_MMR::verify_proof(4, leaves[3], pr3.0, pr3.1, mmr_bagged.root);

    let pr4 = mmr.clone().get_proof(7);
    let verified4 = naive_MMR::verify_proof(7, leaves[4], pr4.0, pr4.1, mmr_bagged.root);

    let pr5 = mmr.clone().get_proof(8);
    let verified5 = naive_MMR::verify_proof(8, leaves[5], pr5.0, pr5.1, mmr_bagged.root);

    let pr6 = mmr.clone().get_proof(10);
    let verified6 = naive_MMR::verify_proof(10, leaves[6], pr6.0, pr6.1, mmr_bagged.root);

    let pr7 = mmr.clone().get_proof(11);
    let verified7 = naive_MMR::verify_proof(11, leaves[7], pr7.0, pr7.1, mmr_bagged.root);

    let pr8 = mmr.clone().get_proof(15);
    let verified8 = naive_MMR::verify_proof(15, leaves[8], pr8.0, pr8.1, mmr_bagged.root);

    let pr9 = mmr.clone().get_proof(16);
    let verified9 = naive_MMR::verify_proof(16, leaves[9], pr9.0, pr9.1, mmr_bagged.root);

    let pr10 = mmr.clone().get_proof(18);
    let verified10 = naive_MMR::verify_proof(18, leaves[10], pr10.0, pr10.1, mmr_bagged.root);

    let pr11 = mmr.clone().get_proof(19);
    let verified11 = naive_MMR::verify_proof(19, leaves[11], pr11.0, pr11.1, mmr_bagged.root);

    let pr12 = mmr.clone().get_proof(22);
    let verified12 = naive_MMR::verify_proof(22, leaves[12], pr12.0, pr12.1, mmr_bagged.root);

    let pr13 = mmr.clone().get_proof(23);
    let verified13 = naive_MMR::verify_proof(23, leaves[13], pr13.0, pr13.1, mmr_bagged.root);

    let pr14 = mmr.clone().get_proof(25);
    let verified14 = naive_MMR::verify_proof(25, leaves[14], pr14.0, pr14.1, mmr_bagged.root);

    let pr15 = mmr.clone().get_proof(26);
    let verified15 = naive_MMR::verify_proof(26, leaves[15], pr15.0, pr15.1, mmr_bagged.root);

    let pr16: (Vec<plonky2::hash::hash_types::HashOut<GoldilocksField>>, Vec<plonky2::hash::hash_types::HashOut<GoldilocksField>>, usize) = mmr.clone().get_proof(31);
    let verified16 = naive_MMR::verify_proof(pr16.2, leaves[16], pr16.0, pr16.1, mmr_bagged.root);

    assert!(verified0 && verified1 && verified2 && verified3 && verified4 && verified5 && verified6 && verified7);
    assert!(verified8 && verified9 && verified10 && verified11 && verified12 && verified13 && verified14 && verified15);
    assert!(verified16);
    Ok(())
  }

  #[test]
  fn test_mmr_proof_tree_21_leaves_all_indices() -> Result<()> {
    let mut leaves = Vec::new();
    let mut rng = rand::thread_rng();
    for _i in 0..22 {
      leaves.push(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));
    }
    let mut mmr = naive_MMR::new(leaves[0]);
    for i in 1..22 {
      mmr.add_leaf(leaves[i]);  
    }
    
    let mmr_bagged = mmr.clone().bagging_the_peaks();

    let pr0 = mmr.clone().get_proof(0);
    let verified0 = naive_MMR::verify_proof(0, leaves[0], pr0.clone().0, pr0.clone().1, mmr_bagged.root);

    let pr1 = mmr.clone().get_proof(1);
    let verified1 = naive_MMR::verify_proof(1, leaves[1], pr1.0, pr1.1, mmr_bagged.root);

    let pr2 = mmr.clone().get_proof(3);
    let verified2 = naive_MMR::verify_proof(3, leaves[2], pr2.0, pr2.1, mmr_bagged.root);

    let pr3 = mmr.clone().get_proof(4);
    let verified3 = naive_MMR::verify_proof(4, leaves[3], pr3.0, pr3.1, mmr_bagged.root);

    let pr4 = mmr.clone().get_proof(7);
    let verified4 = naive_MMR::verify_proof(7, leaves[4], pr4.0, pr4.1, mmr_bagged.root);

    let pr5 = mmr.clone().get_proof(8);
    let verified5 = naive_MMR::verify_proof(8, leaves[5], pr5.0, pr5.1, mmr_bagged.root);

    let pr6 = mmr.clone().get_proof(10);
    let verified6 = naive_MMR::verify_proof(10, leaves[6], pr6.0, pr6.1, mmr_bagged.root);

    let pr7 = mmr.clone().get_proof(11);
    let verified7 = naive_MMR::verify_proof(11, leaves[7], pr7.0, pr7.1, mmr_bagged.root);

    let pr8 = mmr.clone().get_proof(15);
    let verified8 = naive_MMR::verify_proof(15, leaves[8], pr8.0, pr8.1, mmr_bagged.root);

    let pr9 = mmr.clone().get_proof(16);
    let verified9 = naive_MMR::verify_proof(16, leaves[9], pr9.0, pr9.1, mmr_bagged.root);

    let pr10 = mmr.clone().get_proof(18);
    let verified10 = naive_MMR::verify_proof(18, leaves[10], pr10.0, pr10.1, mmr_bagged.root);

    let pr11 = mmr.clone().get_proof(19);
    let verified11 = naive_MMR::verify_proof(19, leaves[11], pr11.0, pr11.1, mmr_bagged.root);

    let pr12 = mmr.clone().get_proof(22);
    let verified12 = naive_MMR::verify_proof(22, leaves[12], pr12.0, pr12.1, mmr_bagged.root);

    let pr13 = mmr.clone().get_proof(23);
    let verified13 = naive_MMR::verify_proof(23, leaves[13], pr13.0, pr13.1, mmr_bagged.root);

    let pr14 = mmr.clone().get_proof(25);
    let verified14 = naive_MMR::verify_proof(25, leaves[14], pr14.0, pr14.1, mmr_bagged.root);

    let pr15 = mmr.clone().get_proof(26);
    let verified15 = naive_MMR::verify_proof(26, leaves[15], pr15.0, pr15.1, mmr_bagged.root);

    let pr16 = mmr.clone().get_proof(31);
    let verified16 = naive_MMR::verify_proof(pr16.2, leaves[16], pr16.0, pr16.1, mmr_bagged.root);
 
    let pr17 = mmr.clone().get_proof(32);
    let verified17 = naive_MMR::verify_proof(pr17.2, leaves[17], pr17.0, pr17.1, mmr_bagged.root);
  
    let pr18 = mmr.clone().get_proof(34);
    let verified18 = naive_MMR::verify_proof(pr18.2, leaves[18], pr18.0, pr18.1, mmr_bagged.root);
   
    let pr19 = mmr.clone().get_proof(35);
    let verified19 = naive_MMR::verify_proof(pr19.2, leaves[19], pr19.0, pr19.1, mmr_bagged.root);

    let pr20 = mmr.clone().get_proof(38);
    let verified20 = naive_MMR::verify_proof(pr20.2, leaves[20], pr20.0, pr20.1, mmr_bagged.root);
 
    assert!(verified0 && verified1 && verified2 && verified3 && verified4 && verified5 && verified6 && verified7);
    assert!(verified8 && verified9 && verified10 && verified11 && verified12 && verified13 && verified14 && verified15);
    assert!(verified16 && verified17 && verified18 && verified19 && verified20);
    Ok(())
  }

}