use std::fmt::Debug;

#[derive(Debug, PartialEq)]
pub enum MonarchError {
    NoInput,
    NoTransformations,
    NoRelation,
    NoOperation,
}

pub struct MetamorphicTestRunner<IN: Clone + Debug, OUT> {
    input: Option<IN>,
    operation: Option<Box<dyn Fn(&IN) -> OUT>>,
    transformations: Vec<Box<dyn Fn(&mut IN) -> IN>>,
    relation: Option<Box<dyn Fn(&OUT, &OUT) -> bool>>,
}

impl<IN: Clone + Debug, OUT> MetamorphicTestRunner<IN, OUT> {
    pub fn new() -> Self {
        MetamorphicTestRunner {
            input: None,
            operation: None,
            transformations: Vec::new(),
            relation: None,
        }
    }

    pub fn add_transformation(&mut self, f: impl Fn(&mut IN) -> IN + 'static) {
        self.transformations.push(Box::new(f));
    }

    pub fn set_input(&mut self, input: IN) {
        self.input = Some(input);
    }

    pub fn set_operation(&mut self, f: impl Fn(&IN) -> OUT + 'static) {
        self.operation = Some(Box::new(f));
    }

    pub fn set_relation(&mut self, f: impl Fn(&OUT, &OUT) -> bool + 'static) {
        self.relation = Some(Box::new(f));
    }

    pub fn run(&mut self) -> Result<(), MonarchError> {
        if self.input.is_none() {
            return Err(MonarchError::NoInput);
        }
        if self.operation.is_none() {
            return Err(MonarchError::NoOperation);
        }
        if self.relation.is_none() {
            return Err(MonarchError::NoRelation);
        }
        if self.transformations.is_empty() {
            return Err(MonarchError::NoTransformations);
        }
        let op = self.operation.take().unwrap();
        let input = self.input.take().unwrap();
        let relation = self.relation.take().unwrap();
        let src_result = op(&input);
        for transform in self.transformations.iter_mut() {
            let mut fup_input = input.clone();
            fup_input = transform(&mut fup_input);
            let fup_result = op(&fup_input);
            if !relation(&src_result, &fup_result) {
                panic!("Relation not satisfied with input: {:?}", fup_input);
            }
        }
        Ok(())
    }
}

// `list` should really be U: Index + IntoIterator<T> where T: Clone
// TODO: Add documentation string
fn combinations<T: Clone>(list: Vec<T>, k: usize) -> Vec<Vec<T>> {
    let n = list.len();
    let last_index = k - 1;
    let start_of_last_k_elements = n - k;
    let mut current_indices: Vec<usize> = (0..k).collect();
    current_indices[last_index] -= 1; // prepare for first loop iteration
    let mut items: Vec<Vec<T>> = Vec::new();
    loop {
        if indices_in_final_position(&current_indices, n, k) {
            return items;
        }
        while current_indices[last_index] < (start_of_last_k_elements + last_index) {
            current_indices[last_index] += 1;
            store_item_from_indices(&list, &current_indices, &mut items);
        }
        pack_indices_leftward(&mut current_indices, n, k);
        store_item_from_indices(&list, &current_indices, &mut items);
    }
}

fn indices_in_final_position(indices: &[usize], n: usize, k: usize) -> bool {
    let start_of_last_k_elements = n - k;
    (0..k)
        .map(|i| indices[i] == (start_of_last_k_elements + i))
        .all(|x| x)
}

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

fn store_item_from_indices<T: Clone>(
    item_list: &[T],
    indices: &[usize],
    comb_list: &mut Vec<Vec<T>>,
) {
    let mut comb = Vec::new();
    for i in indices.iter() {
        comb.push(item_list[*i].clone());
    }
    comb_list.push(comb);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_errors_when_operation_is_missing() {
        let mut runner: MetamorphicTestRunner<i32, i32> = MetamorphicTestRunner::new();
        runner.set_input(0);
        runner.set_relation(|&x, &y| x == y);
        runner.add_transformation(|&mut x| x);
        match runner.run() {
            Err(err) => {
                assert!(err == MonarchError::NoOperation);
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
                assert!(err == MonarchError::NoRelation);
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
                assert!(err == MonarchError::NoInput);
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
                assert!(err == MonarchError::NoTransformations);
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

}
