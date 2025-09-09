/*
### ID
HumanEval/90
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

use vstd::prelude::*;

verus! {
fn two_smallest(s: &Vec<i32>) -> (result: Vec<usize>)
    ensures
        result.len() == 0 <==> s.len() == 0,
        result.len() == 0 || result.len() == 2,
        result.len() > 0 ==>
            0 <= result@[0] < s.len() && 0 <= result@[1] < s.len(),
        result.len() > 0 ==> 
            forall |i: int| #![trigger s[i]] 0 <= i < s.len() ==>
                s[i] == s[result@[0] as int] || s[i] >= s[result@[1] as int],
        result.len() > 0 ==> 
            result@[0] == result@[1] ==> 
                forall |i: int| #![trigger s[i]] 0 <= i < s.len() ==>
                    s[i] == s[0],
        result.len() > 0 ==> 
            result@[0] != result@[1] ==> 
                s[result@[0] as int] < s[result@[1] as int],
        
{
    let mut result = Vec::new();
    if s.len() == 0 {
        return result;
    }

    let mut min1 = 0;
    let mut min2 = 0;

    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= min1 < s.len(),
            0 <= min2 < s.len(),
            min1 != min2 ==> s[min1 as int] < s[min2 as int],
            s[min1 as int] == s[min2 as int] ==> 
                forall |j: int| 0 <= j < i ==> s[j] == s[min1 as int],
            forall |j: int| 0 <= j < i ==> 
                s[j] == s[min1 as int] || s[j] >= s[min2 as int],
            exists |j: int| 0 <= j < i ==> s[j] == s[min1 as int],
        decreases (s.len() - i),
    {
        let x = s[i];

        if s[min2] == s[min1] {
            if x > s[min1] {
                min2 = i;
            } else if x < s[min1] {
                assert(forall |j: int| 0 <= j < i ==> s[j] >= s[min2 as int]);
                min2 = min1;
                min1 = i;
            } 
        } else {
            if x < s[min1] {
                min2 = min1;
                min1 = i;
            } else if s[min1] < x && x < s[min2] {
                min2 = i;
            }
        }

        i += 1;
    }

    result.push(min1);
    result.push(min2);
    result
}

// A helper predicate describing "v is the minimum among values strictly 
// greater than the global minimum"
spec fn is_next_smallest_value(s: Seq<i32>, v: i32) -> bool {
    exists |m_i: int| #![trigger s[m_i]] 
        0 <= m_i < s.len() && forall |j:int| 0 <= j < s.len() ==> 
            s[m_i] <= s[j] && v > s[m_i]
            && forall |j:int| #![trigger s[j]] 
                0 <= j < s.len() && s[j] > s[m_i] ==> s[j] >= v
}

fn next_smallest(s: &Vec<i32>) -> (ret: Option<i32>)
    ensures
        // None iff empty or all elements equal
        ret.is_none() <==> s.len()==0 ||
            (s.len() > 0 && 
            forall |i: int| #![trigger s[i]] 0 <= i < s.len() ==> s[i]==s[0]),
        // Some(v) iff there exists a value strictly greater than the global 
        // minimum and v is the least such value
        ret.is_some() ==> is_next_smallest_value(s@, ret.unwrap())
{
    let two = two_smallest(s);
    if two.len() == 0 {
        return None;
    }

    let i0 = two[0];
    let i1 = two[1];

    if i0 == i1 {
        return None;
    } else {
        return Some(s[i1]);
    }
}
} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def next_smallest(lst):
    """
    You are given a list of integers.
    Write a function next_smallest() that returns the 2nd smallest element of the list.
    Return None if there is no such element.

    next_smallest([1, 2, 3, 4, 5]) == 2
    next_smallest([5, 1, 4, 3, 2]) == 2
    next_smallest([]) == None
    next_smallest([1, 1]) == None
    """

*/

/*
### ENTRY POINT
next_smallest
*/

/*
### CANONICAL SOLUTION
    lst = sorted(set(lst))
    return None if len(lst) < 2 else lst[1]

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([1, 2, 3, 4, 5]) == 2
    assert candidate([5, 1, 4, 3, 2]) == 2
    assert candidate([]) == None
    assert candidate([1, 1]) == None
    assert candidate([1,1,1,1,0]) == 1
    assert candidate([1, 0**0]) == None
    assert candidate([-35, 34, 12, -45]) == -35

    # Check some edge cases that are easy to work out by hand.
    assert True


*/
