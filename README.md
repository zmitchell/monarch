# Monarch

Monarch is a barebones utility for metamorphic testing in Rust. For an overview of metamorphic testing and some examples, there is an excellent blog post by Hillel Wayne:
- [Metamorphic Testing - Hillel Wayne](https://hillelwayne.com/post/metamorphic-testing/)

Monarch is currently still in the experimental stage, so the API is subject to my whims at this point.

## Metamorphic tests

With a basic test you're checking that a specific input produces a specific, expected output. 
```rust
fn double(x: i32) -> i32 {
    2 * x
}

#[test]
fn test_double() {
    let doubled = double(5);
    assert_eq!(doubled, 10);  // We already know what "doubled" should be!
}
```

These tests can be quick and easy to write, but they don't always provide good test coverage because the responsibility falls on the developer to predict which inputs will uncover bugs.
Futhermore, you can end up with lots of duplicated code between tests that perform the same operation with slightly different inputs.

A metamorphic test works differently. When you write a metamorphic test you supply a few pieces of information:
- An input to start out with
- Ways to transform that input
- An operation that turns an input into an output
- A relationship that should be satisfied between the output of the original input and the transformed input

First an output is computed from the original input. Next you compute a new, transformed input for every possible combination of transformations and produce an output for each of those. Finally, you check that your relation holds between the "original" output and each "transformed" output.

That might sound complicated, but the transformations and relations can be extremely simple. On top of that, the more transformations you supply, the wider variety of inputs you'll generate, and the better coverage you'll get from this one test.

Let's do a quick example.

## Example
Let's say I'm working on a web app that returns some search results in response to a user's query.
For my relation I'm going to require that I should get the same number of search results as the original input.

```rust
#[test]
fn test_search_results() {
    let mut runner: MetamorphicTestRunner<MyHTTPRequest, Vec<SearchResult>> = MetamorphicTestRunner::new();
    //                                    ^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^
    //                                    input type     output type
    let original_input = MyHTTPRequest::new();
    runner.set_input(original_input.clone());
    runner.set_relation(|&original_output, &transformed_output| {
        original_output.len() == transformed_output.len()
    });
}
```

The next order of business is coming up with ways to tweak the input that shouldn't affect how many total search results I get back.
A few examples are changing the sort order of the results, changing the number of results per page, etc.
```rust
runner.add_transformation(|&mut request| {
    request.sort_order = ... // Sort by some parameter
});
runner.add_transformation(|&mut request| {
    request.page_results = ... // Some number of results per page
});
```

The last thing to do is to tell the test runner what operation to perform with each request in order to produce an output (e.g. send it to the server), and run the test.
```rust
runner.set_operation(|&request| {
    // send the request
});
runner.run().unwrap();
```

The test runner will run the input through all combinations of the supplied transformations, and panic if the relation isn't satisfied.

## Error Reporting

The final format of the error reporting is still up in the air. Currently the test runner will identify which test case failed (which transformed input caused the failure), but this is returned as a `MonarchError::TestFailure(Reason)`, where `Reason` has a method `message` which will return a `String` explaining the failure.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.

## FAQ
- Why "monarch"?
    - Metamorphic testing -> metamorphosis -> butterflies -> monarch
- Should I use this?
    - One day, but not today
- Are you looking for contributors?
    - Contributions would be great once I get things up and running!
