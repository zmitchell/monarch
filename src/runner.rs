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
        if self.transformations.len() == 0 {
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
            },
            _ => panic!()
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
            },
            _ => panic!()
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
            },
            _ => panic!()
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
            },
            _ => panic!()
        }
    }

    #[test]
    fn it_completes_basic_test() {
        let mut runner: MetamorphicTestRunner<(i32, i32), i32> = MetamorphicTestRunner::new();
        runner.set_input((2, 2));
        runner.set_relation(|&z1, &z2| {
            z1.signum() == z2.signum()
        });
        runner.set_operation(|&(x, y)| {
            x + y
        });
        runner.add_transformation(|&mut (x, y)| {
            (2*x, 2*y)
        });
        runner.add_transformation(|&mut (x, y)| {
            (y, x)
        });
        runner.run().unwrap();
    }
}