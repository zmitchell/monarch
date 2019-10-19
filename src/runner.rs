#[cfg(test)]
use proptest::collection;
#[cfg(test)]
use proptest::prelude::*;
use std::fmt::Debug;
use std::panic;

#[derive(Debug, Clone, PartialEq)]
pub struct Reason {
    msg: String,
}

impl Reason {
    fn message(&self) -> String {
        self.msg.clone()
    }
}

/// An error that may be encountered while running metamorphic tests.
#[derive(Debug, PartialEq, Clone)]
pub enum MonarchError {
    /// The test configuration is invalid
    Invalid(Reason),

    /// The test failed
    TestFailure(Reason),
}

/// The struct responsible for running the metamorphic test suite.
pub struct MetamorphicTestRunner<IN: Clone + Debug, OUT: panic::UnwindSafe> {
    input: Option<IN>,
    operation: Option<Box<dyn Fn(&IN) -> OUT>>,
    transformations: Vec<Box<dyn Fn(&mut IN) -> IN>>,
    relation: Option<Box<dyn Fn(&OUT, &OUT) -> bool>>,
}

impl<IN: Clone + Debug, OUT: panic::UnwindSafe> Default for MetamorphicTestRunner<IN, OUT> {
    fn default() -> Self {
        Self::new()
    }
}

impl<IN: Clone + Debug, OUT: panic::UnwindSafe> MetamorphicTestRunner<IN, OUT> {
    /// Construct a new test runner.
    pub fn new() -> Self {
        MetamorphicTestRunner {
            input: None,
            operation: None,
            transformations: Vec::new(),
            relation: None,
        }
    }

    /// Supply an additional way of transforming an input.
    pub fn add_transformation(&mut self, f: impl Fn(&mut IN) -> IN + 'static) {
        self.transformations.push(Box::new(f));
    }

    /// Set the initial input.
    ///
    /// This initial input along with the operation will be used to compute an output against which
    /// all other outputs will be compared using the supplied metamorphic relation.
    pub fn set_input(&mut self, input: IN) {
        self.input = Some(input);
    }

    /// Set the operation which will be used to compute an output for each input.
    pub fn set_operation(&mut self, f: impl Fn(&IN) -> OUT + 'static) {
        self.operation = Some(Box::new(f));
    }

    /// Set the metamorphic relation which determines whether two outputs pass the test.
    pub fn set_relation(&mut self, f: impl Fn(&OUT, &OUT) -> bool + 'static) {
        self.relation = Some(Box::new(f));
    }

    /// Run the metamorphic test.
    // TODO: At some point it would probably be a good idea to cache the combinations so they aren't
    //       computed every time a new input is set.
    pub fn run(&mut self) -> Result<(), MonarchError> {
        if self.input.is_none() {
            return Err(MonarchError::Invalid(Reason {
                msg: String::from("No input was provided"),
            }));
        }
        if self.operation.is_none() {
            return Err(MonarchError::Invalid(Reason {
                msg: String::from("No operation was provided"),
            }));
        }
        if self.relation.is_none() {
            return Err(MonarchError::Invalid(Reason {
                msg: String::from("No relation was provided"),
            }));
        }
        if self.transformations.is_empty() {
            return Err(MonarchError::Invalid(Reason {
                msg: String::from("No transformations were provided"),
            }));
        }
        let op = self.operation.take().unwrap();
        let input = self.input.take().unwrap();
        let relation = self.relation.take().unwrap();
        let src_output = op(&input);
        let mut trans_combinations = Vec::new();
        for i in 1..self.transformations.len() {
            let combs = combinations(self.transformations.len(), i)?;
            trans_combinations.extend_from_slice(combs.as_slice());
        }
        for comb in trans_combinations.iter() {
            let mut trans_input = input.clone();
            for i in comb.iter() {
                trans_input = self.transformations[*i](&mut trans_input);
            }
            let trans_output = op(&trans_input);
            let test_result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                assert!(relation(&src_output, &trans_output));
            }));
            if test_result.is_err() {
                return Err(MonarchError::TestFailure(Reason {
                    msg: format!(
                        "Test failed with original input {:?} and transformed input {:?}",
                        input.clone(),
                        trans_input
                    ),
                }));
            }
        }
        Ok(())
    }
}

/// Return all combinations (without replacement) of size `k` from a list of `n` items.
///
/// This will return n! / k! (n - k)! combinations.
fn combinations(n: usize, k: usize) -> Result<Vec<Vec<usize>>, MonarchError> {
    if n == 0 {
        return Err(MonarchError::Invalid(Reason {
            msg: String::from("Invalid number of combinations"),
        }));
    }
    if k > n {
        return Err(MonarchError::Invalid(Reason {
            msg: String::from("Invalid number of combinations"),
        }));
    }
    if k == 0 {
        return Err(MonarchError::Invalid(Reason {
            msg: String::from("Invalid number of combinations"),
        }));
    }
    if k == 1 {
        return Ok(each_index_separately(n));
    }
    let last_index = k - 1;
    let start_of_last_k_elements = n - k;
    let mut current_indices: Vec<usize> = (0..k).collect();
    let mut items: Vec<Vec<usize>> = Vec::new();
    items.push(current_indices.clone());
    loop {
        if indices_are_in_final_positions(current_indices.as_slice(), n, k) {
            return Ok(items);
        }
        while current_indices[last_index] < (start_of_last_k_elements + last_index) {
            current_indices[last_index] += 1;
            items.push(current_indices.clone());
        }
        pack_indices_leftward(&mut current_indices, n, k);
        items.push(current_indices.clone());
    }
}

/// Returns each element in its own vector.
///
/// This is useful when the combination size is 1, as this avoids all the other machinery.
fn each_index_separately(n: usize) -> Vec<Vec<usize>> {
    let mut items: Vec<Vec<usize>> = Vec::with_capacity(n);
    for i in 0..n {
        items.push(Vec::with_capacity(1));
        items[i].push(i);
    }
    items
}

/// Returns true if the indices point to the last `k` elements of a collection with length `n`
/// in order.
///
/// For a list of length 5 and a list of indices of length 3, the final positions would
/// be (2, 3, 4).
fn indices_are_in_final_positions(indices: &[usize], n: usize, k: usize) -> bool {
    let start_of_last_k_elements = n - k;
    (0..k)
        .map(|i| indices[i] == (start_of_last_k_elements + i))
        .all(|x| x)
}

/// Find the rightmost index that is not in its final position and pack all indices that follow
/// immediately following this index.
///
/// Given a list of items with length 10 and the indices (0, 2, 8, 9), the last two indices are in
/// their final positions. The rightmost index not in its final position is the index with value 2.
/// The last two indices will be packed to the left so that the result is (0, 2, 3, 4).
fn pack_indices_leftward(indices: &mut Vec<usize>, n: usize, k: usize) {
    let start_of_last_k_elements = n - k;
    // Find the rightmost index that isn't in its final position and increment it.
    for i in (0..=(k - 2)).rev() {
        if indices[i] != (start_of_last_k_elements + i) {
            indices[i] += 1;
            // Pack the indices that follow `i` to the left so that `i`, `i+1`, ... are
            // all one after another.
            for (x, j) in (i + 1..k).enumerate() {
                indices[j] = indices[i] + x + 1; // enumerate starts at 0
            }
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Returns the number of combinations given the length of the list and the number of items in
    /// each combination.
    fn num_combinations(n: usize, k: usize) -> Result<usize, MonarchError> {
        let numerator = ((k + 1)..=n).rev().fold(Some(1usize), |acc, x| match acc {
            Some(acc) => acc.checked_mul(x),
            None => None,
        });
        let bottom = factorial(n - k)?;
        match numerator {
            Some(top) => Ok(top / bottom),
            None => {
                return Err(MonarchError::Invalid(Reason {
                    msg: String::from("Number of combinations too large"),
                }));
            }
        }
    }

    /// Returns the factorial of `n`
    fn factorial(n: usize) -> Result<usize, MonarchError> {
        if n > 20 {
            return Err(MonarchError::Invalid(Reason {
                msg: String::from("Invalid number of combinations"),
            }));
        }
        if n == 0 {
            return Ok(1);
        }
        Ok((1..=n).product())
    }

    /// A strategy to produce a vector of indices into a vector of items.
    ///
    /// The return value is a tuple (indices_vec, items_vec). The `indices_vec` is guaranteed to be
    /// no longer than the `items_vec`. The contents of `indices_vec` have very few constraints. The
    /// maximum value of any index is the final index of `items_vec`, but the indices are in no
    /// particular order and may not even be unique.
    fn indices_and_items() -> impl Strategy<Value = (Vec<usize>, Vec<usize>)> {
        collection::vec(any::<usize>(), 1..100usize)
            .prop_flat_map(|v| (collection::vec(0..v.len(), 1..=v.len()), Just(v)))
    }

    /// A strategy to produce a vector of indices into an imaginary vector of items with length `n`.
    ///
    /// The return value is a tuple (indices_vec, n). The `indices_vec` is guaranteed to be
    /// no longer than the `n` indices. The indices are guaranteed to be unique and in the final
    /// state i.e. for an `items_vec` of length `n` and `indices_vec` of length `k`, the indices in
    /// the `indices_vec` will point to the last `k` items in `items_vec` with the indices in
    /// ascending order.
    ///
    /// This strategy is simpler and faster when you only care about the ordering of the indices and
    /// don't actually need the contents of the `items_vec`.
    fn indices_and_items_length_final() -> impl Strategy<Value = (Vec<usize>, usize)> {
        (1..100usize).prop_flat_map(|n| {
            (
                (1..=n).prop_map(move |k| {
                    let start_of_last_k_items = n - k;
                    let mut ind_vec = Vec::with_capacity(k);
                    for i in 0..k {
                        ind_vec.push(start_of_last_k_items + i);
                    }
                    ind_vec
                }),
                Just(n),
            )
        })
    }

    /// A strategy producing two usizes where one is less than the other.
    fn valid_n_and_k(lim: usize) -> impl Strategy<Value = (usize, usize)> {
        (1usize..=lim).prop_flat_map(|n| (Just(n), 1..=n))
    }

    /// A strategy producing two usizes where one is less than the other.
    fn valid_n_and_too_large_k(lim: usize) -> impl Strategy<Value = (usize, usize)> {
        (2usize..=lim).prop_flat_map(|k: usize| (1..k, Just(k)))
    }

    #[test]
    fn it_errors_when_operation_is_missing() {
        let mut runner: MetamorphicTestRunner<i32, i32> = MetamorphicTestRunner::new();
        runner.set_input(0);
        runner.set_relation(|&x, &y| x == y);
        runner.add_transformation(|&mut x| x);
        match runner.run() {
            Err(err) => {
                let dummy_error = MonarchError::Invalid(Reason { msg: String::new() });
                assert_eq!(
                    std::mem::discriminant(&err),
                    std::mem::discriminant(&dummy_error)
                );
            }
            _ => panic!(),
        }
    }

    #[test]
    fn it_errors_when_relation_is_missing() {
        let mut runner: MetamorphicTestRunner<i32, i32> = MetamorphicTestRunner::new();
        runner.set_input(0);
        runner.set_operation(|&x| x);
        runner.add_transformation(|&mut x| x);
        match runner.run() {
            Err(err) => {
                let dummy_error = MonarchError::Invalid(Reason { msg: String::new() });
                assert_eq!(
                    std::mem::discriminant(&err),
                    std::mem::discriminant(&dummy_error)
                );
            }
            _ => panic!(),
        }
    }

    #[test]
    fn it_errors_when_input_is_missing() {
        let mut runner: MetamorphicTestRunner<i32, i32> = MetamorphicTestRunner::new();
        runner.set_relation(|&x, &y| x == y);
        runner.set_operation(|&x| x);
        runner.add_transformation(|&mut x| x);
        match runner.run() {
            Err(err) => {
                let dummy_error = MonarchError::Invalid(Reason { msg: String::new() });
                assert_eq!(
                    std::mem::discriminant(&err),
                    std::mem::discriminant(&dummy_error)
                );
            }
            _ => panic!(),
        }
    }

    #[test]
    fn it_errors_when_transformations_are_missing() {
        let mut runner: MetamorphicTestRunner<i32, i32> = MetamorphicTestRunner::new();
        runner.set_relation(|&x, &y| x == y);
        runner.set_operation(|&x| x);
        runner.set_input(0);
        match runner.run() {
            Err(err) => {
                let dummy_error = MonarchError::Invalid(Reason { msg: String::new() });
                assert_eq!(
                    std::mem::discriminant(&err),
                    std::mem::discriminant(&dummy_error)
                );
            }
            _ => panic!(),
        }
    }

    #[test]
    fn it_completes_basic_test() {
        let mut runner: MetamorphicTestRunner<(i32, i32), i32> = MetamorphicTestRunner::new();
        runner.set_input((2, 2));
        runner.set_relation(|&z1, &z2| z1.signum() == z2.signum());
        runner.set_operation(|&(x, y)| x + y);
        runner.add_transformation(|&mut (x, y)| (2 * x, 2 * y));
        runner.add_transformation(|&mut (x, y)| (y, x));
        runner.run().unwrap();
    }

    #[test]
    fn error_when_k_is_zero() {
        let res = combinations(5usize, 0usize);
        match res {
            Err(e) => {
                let dummy_error = MonarchError::Invalid(Reason { msg: String::new() });
                assert_eq!(
                    std::mem::discriminant(&e),
                    std::mem::discriminant(&dummy_error)
                );
            }
            _ => assert!(false),
        }
    }

    #[test]
    #[should_panic]
    fn combinations_are_applied() {
        // This is a check to make sure that combinations of different sizes are being applied.
        // The two ends of the spectrum are one transformation at a time and combinations that
        // are the same size as the number of transformations. With three transformations the
        // middle case is two transformations. You can differentiate this case by incrementing a
        // starting value and looking for a value with the correct parity.
        let mut runner: MetamorphicTestRunner<u32, u32> = MetamorphicTestRunner::new();
        runner.set_input(0);
        runner.set_relation(|&orig, &trans| {
            if (trans == 1) || (trans == 3) {
                return true;
            } else if trans == 2 {
                return false;
            } else {
                return true;
            }
        });
        runner.set_operation(|&x| x);
        runner.add_transformation(|&mut x| x + 1);
        runner.add_transformation(|&mut x| x + 1);
        runner.add_transformation(|&mut x| x + 1);
        runner.run().unwrap();
    }

    #[test]
    #[should_panic]
    fn catches_test_failure() {
        let mut runner: MetamorphicTestRunner<i32, i32> = MetamorphicTestRunner::new();
        runner.set_input(0);
        runner.set_relation(|&orig, &trans| orig > trans);
        runner.set_operation(|&x| x);
        runner.add_transformation(|&mut x| x + 1);
        runner.add_transformation(|&mut x| x - 1);
        runner.run().unwrap();
    }

    proptest! {
        #[test]
        fn correctly_identifies_final_index_positions(
            (indices, n) in indices_and_items_length_final()
        ) {
            prop_assert!(indices_are_in_final_positions(indices.as_ref(), n, indices.len()));
        }

        #[test]
        fn correctly_identifies_nonfinal_index_positions(
            (indices, items) in indices_and_items()
        ) {
            let n = items.len();
            let k = indices.len();
            let is_final = (0..k)
                .map(|i| {
                    indices[k - 1 - i] == n - 1 - i
                })
                .all(|x| x);
            prop_assume!(!is_final);
            prop_assert!(!indices_are_in_final_positions(indices.as_ref(), n, k));
        }

        #[test]
        fn error_when_k_too_large(
            (n, k) in valid_n_and_too_large_k(100)
        ) {
            let res = combinations(n, k);
            match res {
                Err(e) => {
                    let dummy_error = MonarchError::Invalid(Reason { msg: String::new() });
                    prop_assert_eq!(std::mem::discriminant(&e), std::mem::discriminant(&dummy_error));
                },
                Ok(_) => prop_assert!(false),
            }
        }

        #[test]
        fn error_when_list_is_empty(k: usize) {
            prop_assume!(k > 0);
            let res = combinations(0usize, k);
            match res {
                Err(e) => {
                    let dummy_error = MonarchError::Invalid(Reason { msg: String::new() });
                    prop_assert_eq!(std::mem::discriminant(&e), std::mem::discriminant(&dummy_error));
                },
                _ => prop_assert!(false),
            }
        }

        #[test]
        fn correct_num_combinations_produced(
            (n, k) in valid_n_and_k(20)
        ) {
            let expected_num = num_combinations(n, k).unwrap();
            let mut combs = combinations(n, k).unwrap();
            let num_combs = combs.len();
            combs.sort_unstable();
            combs.dedup();
            let unique_combs = combs.len();
            prop_assert_eq!(num_combs, unique_combs);
            prop_assert_eq!(expected_num, unique_combs);
        }

    }
}
