use super::*;
use stdlib::hash::Hash;

extern crate scc2;

extern crate once_cell;
use self::once_cell::sync::Lazy;

static HASHER: ahash::RandomState = ahash::RandomState::with_seeds(0x623a10fd7ac95b24, 0x498b1bbf2d2b6458, 0x157bef2607065c7e, 0x3bb0ea0b6ab52a76);

static CACHE: Lazy<scc2::HashIndex<Key, BigDecimal>> = Lazy::new(Default::default);

#[derive(Clone, PartialEq, Eq, Hash)]
// V = "value of hasher output"
pub enum Key<V=u64> {
    Pow(V, V),
    Div(V, V),
    Ln(V),
    Exp(V),
}

impl Key<u64> {
    pub fn pow(x: &BigDecimal, y: &BigDecimal) -> Self {
                               // discarding .ctx to make sure cached result apply to any context.
        let x = HASHER.hash_one(x.as_bigint_and_scale());
        let y = HASHER.hash_one(y.as_bigint_and_scale());
        Self::Pow(x, y)
    }
    pub fn div(x: &BigDecimal, y: &BigDecimal) -> Self {
        let x = HASHER.hash_one(x);
                               // only discarding y.ctx due to it has no effect.
        let y = HASHER.hash_one(y.as_bigint_and_scale());

        Self::Div(x, y)
    }

    // for ln (include log), and exp:
    //
    // x.ctx is always kept for hashing.
    // so a higher precision does not overrided by other low precision results.

    pub fn ln(x: &BigDecimal) -> Self {
        let x = HASHER.hash_one(x);
        Self::Ln(x)
    }
    pub fn exp(x: &BigDecimal) -> Self {
        let x = HASHER.hash_one(x);
        Self::Exp(x)
    }
}

pub fn has(k: &Key) -> bool {
    CACHE.contains(k)
}

pub fn get(k: &Key) -> Option<BigDecimal> {
    let g = scc2::ebr::Guard::new();
    CACHE.peek(k, &g).cloned()
}

pub fn put(k: Key, v: BigDecimal) -> bool {
    CACHE.insert(k, v).is_ok()
}
