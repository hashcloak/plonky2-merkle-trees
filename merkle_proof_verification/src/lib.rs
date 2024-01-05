mod cube;
mod polynomial;
mod merkle_proof_verifer;
mod simple_merkle_tree;
mod merkle_proof_4leaves_example;
mod merkle_proof_16leaves_example;
mod merkle_tree_16leaves_exercise1;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}

#[test]
fn test_verify_cube() {
    cube::verify_cube();
}

#[test]
fn test_verify_wrong_proof() {
    cube::verify_cube_wrong_proof();
}

#[test]
fn test_verify_polynomial_correct() {
    polynomial::verify_the_polynomial();
}

#[test]
fn test_verify_polynomial_incorrect() {
    polynomial::verify_the_polynomial_incorrect();
}

#[test]
fn test_verify_simple_merkle_proof() {
    merkle_proof_verifer::verify_merkle_proof_leaf_0();
}

#[test]
fn test_verify_4_leaves() {
    merkle_proof_4leaves_example::verify_4leaves_merkle_tree();
}

#[test]
fn test_verify_16_leaves() {
    merkle_proof_16leaves_example::verify_16leaves_merkle_tree();
    merkle_proof_16leaves_example::verify_16leaves_merkle_tree_any_location(1);
}

#[test]
fn test_verify_16_leaves_exercise_1() {
    merkle_tree_16leaves_exercise1::verify_merkle_proof_16leaves_exercise1(5);
}