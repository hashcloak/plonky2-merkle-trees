use itertools::Itertools;
use num::{PrimInt, ToPrimitive};
use plonky2::{hash::{hash_types::HashOut, poseidon::PoseidonHash}, plonk::config::Hasher};
use plonky2_field::goldilocks_field::GoldilocksField;

// Merkle Mountain Ranges see introduction here: https://github.com/opentimestamps/opentimestamps-server/blob/master/doc/merkle-mountain-range.md
#[derive(Clone)]
pub struct MMR {
    // holds values of all elements in mmr
    // new leaves can be added, leaves cannot be changed
    pub elements: Vec<HashOut<GoldilocksField>>
}

#[derive(Debug, Clone)]
pub struct MMR_proof {
  // MMR size at the moment of generating proof
  pub mmr_size: usize,
  // Merkle proof for subtree that the leaf is part of
  // Holds per sibling: (hash, whether sibling is on the left)
  pub merkle_proof: Vec<(HashOut<GoldilocksField>, bool)>,
  // Peaks of mountains in MMR at moment of generating proof
  pub peaks: Vec<HashOut<GoldilocksField>>
}


// Return a number whose bits represent at what heights there are peaks + the height of the next element to be added
// There is always at most 1 peak at each height, because if there are multiple, they get hashed together to a new peak
// A bit set in a position means there is a peak there. Counting starts from the right at height 0.
// Examples:
// In: 1. Out: 1: peaks at height 1
// In: 4. Out: 101 : peaks at height 2 and 0
// In: 11. Out: 111 : peaks at heights 2,1 and 0
// In: 25. Out: 1110 : peaks at heights 3,2 and 1
pub fn get_heights_bitmap_for_mmr_size(mmr_size: usize) -> (u64, usize) {
  if mmr_size == 0 {
    return (0,0);
  }
  // The max that we can get for this size is all ones in the space that this length takes up
  let all_peaks_set = std::usize::MAX >> mmr_size.leading_zeros();

  // Now, iterate over each peak (bit) to see whether it's set or not
  // To decide if a peak is included, we check how many elements "fit" in the mmr_size
  // Example mmr_size 25. Then 31, 15, 7 and 3 are the size of the subtrees of heights 4,3,2 and 1 resp.
  // 25 >= 31 NO
  // 25 >= 15 YES set bit 1000
  // 10 >= 7 YES set bit 100
  // 3 >= 3 YES set bit 10
  // 0
  // Result 1110

  // For each peak holds:
  // If peak is at height x, the nr of elements of that subtree is 2^{x+1}-1 = 2ˆx+2ˆ{x-1}+..+2ˆ1+1 This equals a number with x+1 bits set to 1
  // For example, if peak is at height 4:
  // 2^5-1=31 (equals 2^4+2^3+2^2+2ˆ1+1=31) In bits 11111

  // Initially, we have the largest possible subtree size
  let mut subtree_size = all_peaks_set;
  // The mmr_size will be updated throughout the loop
  let mut updated_mmr_size = mmr_size;
  // In this number we'll be setting the bits where there are peaks
  let mut peaks: u64 = 0;

  while subtree_size > 0 {
    peaks <<= 1;
    // We include the peak at this position if the subtree fits within the mmr_size
    if updated_mmr_size >= subtree_size {
      // Add peak
      peaks |= 1;
      updated_mmr_size -= subtree_size;
    }
    // For next subtree size, we do a shift right
    subtree_size >>= 1;
  }

  (peaks, updated_mmr_size)
}

impl MMR {
  pub fn new() -> Self {
    MMR { elements: Vec::new() }
  }

  // Adds a leaf to the MMR and any further nodes that might be necessary
  pub fn add_leaf(&mut self, leaf: GoldilocksField) {
    if self.elements.is_empty() {
      self.elements.push(PoseidonHash::hash_or_noop(&[leaf]));
      return;
    }

    // Add leaf
    let mut next_hash = PoseidonHash::hash_or_noop(&[leaf]);

    // Add new peaks as long as needed:
    //   Reading from right to left; add a new peak if there was a peak at the position
    //   Once there's a gap of peaks we stop, because it means next up is a separate previous subtree 
    // Get inital peaks map based on mmr_size before adding new leaf
    let (mut peaks, pos) = get_heights_bitmap_for_mmr_size(self.elements.len());
    let mut current_pos = self.elements.len();
    self.elements.push(next_hash);
    let mut height = 1;
    while peaks > 0 {
      if peaks & 1 == 1 {
        // prev sibling is mmr_size of height away from the last element in the tree
        let prev_peak_index: usize = current_pos - (2.pow(height) - 1);
        let prev_peak = self.elements[prev_peak_index];
        next_hash = PoseidonHash::two_to_one(prev_peak, next_hash);
        self.elements.push(next_hash);
      } else {
        break;
      }
      peaks >>= 1;
      height += 1;
      current_pos += 1;
    }
  }

  pub fn bagging_the_peaks(self) -> HashOut<GoldilocksField> {
    let peaks = self.get_peaks();
    let peaks_elm: Vec<GoldilocksField> = peaks.iter().flat_map(|h| h.elements).collect_vec();
    let root = PoseidonHash::hash_or_noop(&peaks_elm);
    root
  }

  fn add_right_elm(
    curr_index: usize,
    height: u32,
    mmr: &MMR,
    proof_elms: &mut Vec<(HashOut<GoldilocksField>, bool)>,
    curr_index_mut: &mut usize,
    intree_mut: &mut bool,
  ) {
    let next_elm_index = curr_index + (2.pow(height + 1) - 1);
    if next_elm_index < mmr.elements.len() - 1 {
        proof_elms.push((mmr.elements[next_elm_index], false));
        *curr_index_mut = next_elm_index + 1;
    } else {
        *intree_mut = false;
    }
  }

  // Return the merkle proof for leaf at mmr_index, which is the Merkle proof of the Merkle tree the leaf is part of
  pub fn get_subtree_proof_elm(mmr: MMR, mmr_index: usize) -> Vec<(HashOut<GoldilocksField>, bool)> {
    // Walk up from the leaf, until the next sibling hash would fall outside the mmr. In that case the subtree top has been reached and the proof is done

    // Left sibling: index-(2^(h+1)-1). 16 - (2^1-1) = 15, 20 - (2^2-1) = 17 
    // Right sibling: index + (2^(h+1)-1)
    let mut proof_elms = Vec::new();

    let mut curr_index = mmr_index;
    let mut intree = true;
    let mut height = 0;
    while intree {
      if curr_index >= (2.pow(height+1)-1) {
        // Check if previous elm is at same height  
        let prev_elm_index = curr_index - (2.pow(height+1)-1);
        if get_heights_bitmap_for_mmr_size(prev_elm_index).1 == height.try_into().unwrap() {
          // Add left hash to proof
          proof_elms.push((mmr.elements[prev_elm_index], true));
          curr_index += 1;
        } else {
          // Add right hash to proof
          Self::add_right_elm(curr_index, height, &mmr, &mut proof_elms, &mut curr_index, &mut intree);
        }
      } else {
        // Add right hash to proof
        Self::add_right_elm(curr_index, height, &mmr, &mut proof_elms, &mut curr_index, &mut intree);
      }
      height += 1;
    }
    proof_elms
  }

  // Return peaks of this MMR
  pub fn get_peaks(self) -> Vec<HashOut<GoldilocksField>> {
    let mut peaks: Vec<HashOut<GoldilocksField>> = Vec::new();
    let mmr_len = self.elements.len();

    // Try to fit in peaks until we get to the current position
    let mut max_tree_size:usize = (u32::MAX >> mmr_len.to_u32().unwrap().leading_zeros()).to_usize().unwrap();
    let mut current_index = mmr_len;
    let mut peak_pos = 0;
    
    while max_tree_size > 0 {
      if current_index >= max_tree_size {
        peak_pos += max_tree_size;

        peaks.push(self.elements[peak_pos-1]);
        current_index-=max_tree_size;
      }

      max_tree_size >>= 1;
        
    }
    peaks
  }
  
  // Returns "MMR proof" for leaf at given (normal) index
  pub fn get_proof_normal_index(self, normal_index: usize) -> MMR_proof {
    self.get_proof(get_mmr_index(normal_index))
  }

  // Returns "MMR proof" for leaf at given (mmr) index
  //  this consists of a Merkle proof for the leaf in the subtree accompanied by all the peaks of the MMR
  pub fn get_proof(self, mmr_index: usize) -> MMR_proof {
    let mmr_len = self.elements.len();

    // 1. Get the Merkle proof
    let path = Self::get_subtree_proof_elm(self.clone(), mmr_index);
    
    // 2. Get the peaks
    let peaks = self.get_peaks();

    MMR_proof {
      mmr_size: mmr_len,
      merkle_proof: path,
      peaks: peaks
    }
  }
}

impl MMR_proof {
  // Returns whether the proof verifies for the given leaf and root
  // Checks:
  // - Merkle proof for leaf checks out
  // - the root of subtree is among peaks
  // - hashing all roots together should give the root
  pub fn verify(self, leaf: GoldilocksField, root: HashOut<GoldilocksField>) -> bool {
    let leaf_hash = PoseidonHash::hash_or_noop(&[leaf]);
    // 1. Check Merkle proof of subtree
    let mut next_hash = leaf_hash;
    for (sibling, sibling_on_left) in self.merkle_proof {
      if sibling_on_left {
        next_hash = PoseidonHash::two_to_one(sibling, next_hash);
      } else {
        next_hash = PoseidonHash::two_to_one(next_hash, sibling);
      }
    }

    // Check this hash is among the peaks
    assert!(self.peaks.contains(&next_hash));

    // 2. Hash all peaks together
    let peaks_elm: Vec<GoldilocksField> = self.peaks.iter().flat_map(|p| p.elements).collect_vec();
    let calc_root = PoseidonHash::hash_or_noop(&peaks_elm);
    
    calc_root == root
  }
}

// Returns the "MMR index" of the given "normal index"
//  For example, the 4th leaf would have "normal index" 5, and mmr index 8
pub fn get_mmr_index(leaf_normal_index: usize) -> usize {
// Observation: The normal index represents the peaks bitmap with 1 difference
let mut index = leaf_normal_index;
  let mut height = 1;
  let mut res = 0;
  while index > 0 {
    if index & 1 == 1 {
      res += 2i32.pow(height) -1; 
    }
    height += 1;
    index >>= 1;
  }
  res.to_usize().unwrap()
}

#[cfg(test)]
mod tests {
  use plonky2_field::{goldilocks_field::GoldilocksField, types::Field};
  use rand::Rng;
  use crate::mmr::{merkle_mountain_ranges::{MMR, get_heights_bitmap_for_mmr_size, get_mmr_index}, common::GOLDILOCKS_FIELD_ORDER};

  #[test]
  fn test_heights_bitmap() {
    let test_values = [
      (1,1),
      (3,2),
      (4,3),
      (7,4),
      (10,6),
      (15,8),
      (22,12),
      (25,14),
      (26,15),
      (31,16),
      (32,17),
      (34,18),
      (35,19),
      (38,20),
      (41,22),
      (42,23)
    ];
    for (leaf_index, mmr_size) in test_values {
      assert!(get_heights_bitmap_for_mmr_size(leaf_index).0 == mmr_size);
      assert!(get_heights_bitmap_for_mmr_size(leaf_index).1 == 0);
    }
    println!("{:#?}", get_heights_bitmap_for_mmr_size(30));
  }

  #[test]
  fn test_get_mmr_index() {
    let test_values = [
      (0,0),
      (1,1),
      (2,3),
      (3,4),
      (4,7),
      (5,8),
      (6,10),
      (7,11),
      (8,15),
      (9,16),
      (10,18),
      (11,19),
      (12,22),
      (13,23),
      (14,25),
      (15,26)
    ];
    for pair in test_values {
      assert!(get_mmr_index(pair.0) == pair.1);
    }
  }

  #[test]
  fn test_mmr_add_leaf() {
    let nr_leaves = 100;
    let mut rng = rand::thread_rng();
    let mut mmr = MMR::new();
    for _i in 0..nr_leaves {
      mmr.add_leaf(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    // println!("{:#?}", mmr.elements);
    println!("{:#?}", mmr.elements.len());
  }

  #[test]
  fn test_get_proof() {
    let nr_leaves = 16;
    let mut rng = rand::thread_rng();
    let mut mmr = MMR::new();
    let mut leaves = Vec::new();

    for _i in 0..nr_leaves {
      leaves.push(GoldilocksField::from_canonical_u64(rng.gen_range(0..GOLDILOCKS_FIELD_ORDER)));  
    }
    
    for i in 0..nr_leaves {
      mmr.add_leaf(leaves[i]);  
    }

    // Test 1
    // let standard_index = 8;
    // let leaf_index = 15; 
    // Test 2
    let standard_index = 4;
    let leaf_index = 7;
    // Test 3
    // let standard_index = 0;
    // let leaf_index = 0;

    let proof = mmr.clone().get_proof(leaf_index);
    println!("{:#?}", proof);

    let root = mmr.clone().bagging_the_peaks();
    let verified = proof.verify(leaves[standard_index], root);
    println!("{}", verified);
    
  }
}