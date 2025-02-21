//! Code for implementing From/To BigDecimals

use crate::*;

use crate::stdlib::convert::TryFrom;

use num_bigint::BigInt;


macro_rules! impl_from_int_primitive {
    ($($t:ty)*) => {$(
        impl From<$t> for BigDecimal {
            fn from(n: $t) -> Self {
                BigDecimal {
                    int_val: n.into(),
                    scale: 0,
                    ctx: Context::default(),
                }
            }
        }

        impl From<&$t> for BigDecimal {
            fn from(n: &$t) -> Self {
                BigDecimal {
                    int_val: (*n).into(),
                    scale: 0,
                    ctx: Context::default(),
                }
            }
        }
    )*};
}

impl_from_int_primitive! {
    u8 u16 u32 u64 u128
    i8 i16 i32 i64 i128
    isize usize
}

impl TryFrom<f32> for BigDecimal {
    type Error = super::ParseBigDecimalError;

    #[inline]
    fn try_from(n: f32) -> Result<Self, Self::Error> {
        crate::parsing::try_parse_from_f32(n)
    }
}

impl TryFrom<f64> for BigDecimal {
    type Error = super::ParseBigDecimalError;

    #[inline]
    fn try_from(n: f64) -> Result<Self, Self::Error> {
        crate::parsing::try_parse_from_f64(n)
    }
}


impl From<BigInt> for BigDecimal {
    fn from(int_val: BigInt) -> Self {
        BigDecimal {
            int_val: int_val,
            scale: 0,
            ctx: Context::default(),
        }
    }
}

// Anything that may be a big-integer paired with a scale
// parameter may be a bigdecimal
impl<T: Into<BigInt>> From<(T, i64)> for BigDecimal {
    fn from((int_val, scale): (T, i64)) -> Self {
        Self {
            int_val: int_val.into(),
            scale: scale,
            ctx: Context::default(),
        }
    }
}
