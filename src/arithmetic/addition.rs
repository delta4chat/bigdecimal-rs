//! addition routines
//!

use crate::*;


pub(crate) fn add_bigdecimals(
    mut a: BigDecimal,
    mut b: BigDecimal,
) -> BigDecimal {
    if b.is_zero() {
        a.extend_scale_to(b.scale);
        return a;
    }

    if a.is_zero() {
        b.extend_scale_to(a.scale);
        return b;
    }

    let (a, b) = match a.scale.cmp(&b.scale) {
        Ordering::Equal => (a, b),
        Ordering::Less => (a.take_and_scale(b.scale), b),
        Ordering::Greater => (b.take_and_scale(a.scale), a),
    };

    add_aligned_bigdecimals(a, b)
}

fn add_aligned_bigdecimals(
    mut a: BigDecimal,
    mut b: BigDecimal,
) -> BigDecimal {
    debug_assert_eq!(a.scale, b.scale);
    if a.int_val.bits() >= b.int_val.bits() {
        a.int_val += b.int_val;
        a
    } else {
        b.int_val += a.int_val;
        b
    }
}


pub(crate) fn add_bigdecimal_refs<'a, 'b, Lhs, Rhs>(
    lhs: Lhs,
    rhs: Rhs,
    ctx: Option<&Context>,
) -> BigDecimal
where
    Rhs: Into<BigDecimalRef<'a>>,
    Lhs: Into<BigDecimalRef<'b>>,
{
    use stdlib::cmp::Ordering::*;

    let lhs = lhs.into();
    let rhs = rhs.into();
    if rhs.is_zero() {
        if lhs.scale < rhs.scale {
            let digits = lhs.digits * ten_to_the_uint((rhs.scale - lhs.scale) as u64);
            return BigDecimal::new(BigInt::from_biguint(lhs.sign, digits), rhs.scale);
        }
        return lhs.to_owned();
    }
    if lhs.is_zero() {
        if rhs.scale < lhs.scale {
            let digits = rhs.digits * ten_to_the_uint((lhs.scale - rhs.scale) as u64);
            return BigDecimal::new(BigInt::from_biguint(rhs.sign, digits), lhs.scale);
        }
        return rhs.to_owned();
    }

    match lhs.scale.cmp(&rhs.scale) {
        Equal => {
            add_aligned_bigdecimal_ref_ref(lhs, rhs)
        }
        Greater => {
            add_unaligned_bigdecimal_ref_ref(lhs, rhs, (lhs.scale - rhs.scale) as u64, ctx)
        }
        Less => {
            add_unaligned_bigdecimal_ref_ref(rhs, lhs, (rhs.scale - lhs.scale) as u64, ctx)
        }
    }
}


pub(crate) fn addassign_bigdecimals(
    lhs: &mut BigDecimal,
    rhs: BigDecimal,
) {
    if rhs.is_zero() {
        return;
    }
    if lhs.is_zero() {
        *lhs = rhs;
        return;
    }
    lhs.add_assign(rhs.to_ref());
}


pub(crate) fn addassign_bigdecimal_ref<'a, T: Into<BigDecimalRef<'a>>>(
    lhs: &mut BigDecimal,
    rhs: T,
) {
    // TODO: Replace to_owned() with efficient addition algorithm
    let rhs = rhs.into().to_owned();
    match lhs.scale.cmp(&rhs.scale) {
        Ordering::Less => {
            let scaled = lhs.with_scale(rhs.scale);
            lhs.int_val = scaled.int_val + &rhs.int_val;
            lhs.scale = rhs.scale;
        }
        Ordering::Greater => {
            let scaled = rhs.with_scale(lhs.scale);
            lhs.int_val += scaled.int_val;
        }
        Ordering::Equal => {
            lhs.int_val += &rhs.int_val;
        }
    }
}

/// Add BigDecimal references which have the same scale (integer addition)
fn add_aligned_bigdecimal_ref_ref<'a, 'b>(
    lhs: BigDecimalRef<'a>, rhs: BigDecimalRef<'b>
) -> BigDecimal {
    debug_assert!(!lhs.is_zero() && !rhs.is_zero());
    debug_assert_eq!(lhs.scale, rhs.scale);

    if lhs.digits.bits() >= rhs.digits.bits() {
        lhs.to_owned() + rhs
    } else {
        rhs.to_owned() + lhs
    }
}

fn add_unaligned_bigdecimal_ref_ref<'a, 'b>(
    lhs: BigDecimalRef<'a>, rhs: BigDecimalRef<'b>, scale_diff: u64, ctx: Option<&Context>,
) -> BigDecimal {
    debug_assert!(!lhs.is_zero() && !rhs.is_zero());
    debug_assert_eq!(lhs.scale, rhs.scale + scale_diff as i64);

    let shifted_rhs_digits = rhs.digits * ten_to_the_uint(scale_diff);
    let shifted_rhs_int = BigInt::from_biguint(rhs.sign, shifted_rhs_digits).into();
    let shifted_rhs = BigDecimal::new(shifted_rhs_int, lhs.scale);

    shifted_rhs + lhs
}


#[cfg(test)]
mod test {
    use super::*;

    include!("addition.tests.rs");
}
