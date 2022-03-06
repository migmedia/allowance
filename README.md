# Allowance 

Math representation of the physically needed permissible deviation of measures in rust avoiding floating point 
inaccuracy.  

Based of type `Measure` with a accuracy of 1/10th my-meter (= 0.1μ).

### Exaxmple
```rust
use allowance::AllowanceValue;

fn main() {
    let width1 = AllowanceValue::new(100.0, 0.05, -0.2);
    let width2 = AllowanceValue::with_sym(50.0, 0.05);

    // Adding two `AllowancesValue`s is strait-forth.
    assert_eq!(width1 + width2, AllowanceValue::new(150.0, 0.1, -0.25));

    // `!` inverts the direction of tolerance to /subtract/ measures.
    assert_eq!(!width1, AllowanceValue::new(-100.0, 0.2, -0.05));

    // Adding an inverted `AllowanceValue` wides the tolerance.
    assert_eq!(width1 + !width1, AllowanceValue::new(0.0, 0.25, -0.25));
}
```
