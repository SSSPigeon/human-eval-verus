/*
### ID
HumanEval/97
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;
use vstd::arithmetic::mul::lemma_mul_left_inequality;

verus! {

spec fn unit(a: int) -> int {
    if a > 0 {
        a%10
    } else {
        (-a)%10
    }
}

proof fn equal_unit_of_min (a: int)
    requires a == i32::MIN as int,
    ensures (-a)%10 == 10-a % 10,
{

}

spec fn mul_unit(a: int, b: int) -> int {
    let a_unit = unit(a);
    let b_unit = unit(b);
    a*b
}

fn abs_mod(a: i32) -> (ret: i32)
    ensures
        0 <= ret < 10,
        ret == unit(a as int),
{
    if a >= 0 {
        a % 10
    } else if a == i32::MIN {
        // Use residue normalization: r = ((a % 10) + 10) % 10
        let r = 10 - a % 10;
        proof {
            equal_unit_of_min(a as int);
        }
        
        assert(r == unit(a as int));
        r
    } else {
        // a < 0 and a != MIN, so -a is well-defined and nonnegative
        let t = (-a) % 10;
        assert(0 <= t < 10);
        t
    }
}

// proof fn mutiplication_is_monotone
fn multiply(a: i32, b: i32) -> (ret: i32) 
    ensures
        ret == mul_unit(a as int, b as int),
{
    let a_unit = abs_mod(a);
    let b_unit = abs_mod(b);
    if (a_unit == 0){
        return 0;
    }
    assert(0 < a_unit < 10 );
    assert(0 <= b_unit < 10 );
    assert(a_unit * b_unit < a_unit * 10 ) by {
        lemma_mul_left_inequality(a_unit as int, b_unit as int, 10);
    }
    assert(0 <= a_unit * b_unit < 100);
    a_unit * b_unit
    
}
} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def multiply(a, b):
    """Complete the function that takes two integers and returns
    the product of their unit digits.
    Assume the input is always valid.
    Examples:
    multiply(148, 412) should return 16.
    multiply(19, 28) should return 72.
    multiply(2020, 1851) should return 0.
    multiply(14,-15) should return 20.
    """

*/

/*
### ENTRY POINT
multiply
*/

/*
### CANONICAL SOLUTION
    return abs(a % 10) * abs(b % 10)

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate(148, 412) == 16, "First test error: " + str(candidate(148, 412))
    assert candidate(19, 28) == 72, "Second test error: " + str(candidate(19, 28))
    assert candidate(2020, 1851) == 0, "Third test error: " + str(candidate(2020, 1851))
    assert candidate(14,-15) == 20, "Fourth test error: " + str(candidate(14,-15))
    assert candidate(76, 67) == 42, "Fifth test error: " + str(candidate(76, 67))
    assert candidate(17, 27) == 49, "Sixth test error: " + str(candidate(17, 27))


    # Check some edge cases that are easy to work out by hand.
    assert candidate(0, 1) == 0, "1st edge test error: " + str(candidate(0, 1))
    assert candidate(0, 0) == 0, "2nd edge test error: " + str(candidate(0, 0))


*/
