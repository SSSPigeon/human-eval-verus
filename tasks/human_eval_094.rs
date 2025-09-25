use vstd::prelude::*;

verus! {

pub open spec fn is_prime(n: nat) -> bool {
    (n > 1) && forall|i| 1 < i < n ==> #[trigger] (n % i) != 0
}

pub closed spec fn is_prime_so_far(n: nat, k: nat) -> bool
    recommends
        n >= k > 1,
{
    forall|i| 1 < i < k ==> #[trigger] (n % i) != 0
}

fn is_prime_impl(n: u8) -> (res: bool)
    ensures
        res == is_prime(n as nat),
{
    if n < 2 {
        return false;
    }
    let mut k = 2;
    let mut res = true;

    while (k < n)
        invariant
            2 <= k <= n,
            res == is_prime_so_far(n as nat, k as nat),
        decreases n - k,
    {
        assert((is_prime_so_far(n as nat, k as nat) && (n as nat) % (k as nat) != 0)
            == is_prime_so_far(n as nat, (k + 1) as nat));

        res = res && n % k != 0;
        k = k + 1;
    }
    return res;
}


fn max_prime(lst: Vec<u8>) -> (ret: u8) 
    ensures
        lst.len() == 0 ==> ret == 0,
        (forall|k| #![trigger lst[k]]
                0 <= k < lst.len() ==> !is_prime(lst[k] as nat)) ==> ret == 0,
        ret == 0 ==> 
            lst.len() == 0 || 
            forall|k| #![trigger lst[k]]
                0 <= k < lst.len() ==> !is_prime(lst[k] as nat),
        ret != 0 ==>
            forall|k| #![trigger lst[k]] 
                0 <= k < lst.len() && is_prime(lst[k] as nat) ==> lst[k] <= ret
            && is_prime(ret as nat)
            && exists|k| 0 <= k < lst.len() && lst[k] == ret,
{
    if lst.len() == 0 {
        return 0;
    }
    let mut max_prime_idx = 0;
    let mut found_prime = false;

    let mut i = 0;
    
    
    while i < lst.len() 
        invariant
            lst.len() > 0 ==> 0 <= max_prime_idx < lst.len(),
            !found_prime <==> 
                forall|k| #![trigger lst[k]]
                    0 <= k < i ==> !is_prime(lst[k] as nat),
            found_prime ==> 
                is_prime(lst[max_prime_idx as int] as nat) &&
                (forall|k| #![trigger lst[k]]
                    0 <= k < i && is_prime(lst[k] as nat) 
                        ==> lst[k] <= lst[max_prime_idx as int]),
        decreases
            lst.len() - i,
    {
        let x = i;
        
        if is_prime_impl(lst[x]) {
            assert(max_prime_idx < lst.len() && max_prime_idx >= 0);
            if !found_prime || lst[x] > lst[max_prime_idx] {
                max_prime_idx = x;
                found_prime = true;
                assert(is_prime(lst[max_prime_idx as int] as nat));
            }
        }
        i += 1;
        if !found_prime {
            assert(forall|k| #![trigger lst[k]]
                0 <= k < i ==> !is_prime(lst[k] as nat));
        }
    }
    
    
    if found_prime {
        assert(max_prime_idx < lst.len() && max_prime_idx >= 0);
        assert(is_prime(lst[max_prime_idx as int] as nat));
        lst[max_prime_idx]
    } else {
        assert(forall|k| #![trigger lst[k]]
                0 <= k < lst.len() ==> !is_prime(lst[k] as nat));
        0
    }
}


} // verus!