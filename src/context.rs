//! Define arithmetical context
//!

use crate::*;
use stdlib::num::NonZeroU64;

use arithmetic::store_carry;


// const DEFAULT_PRECISION: u64 = ${RUST_BIGDECIMAL_DEFAULT_PRECISION} or 100;
include!(concat!(env!("OUT_DIR"), "/default_precision.rs"));


/// Mathematical Context
///
/// Stores rules for numerical operations, such as how to round and
/// number of digits to keep.
///
/// Defaults are defined at compile time, determined by environment
/// variables:
///
/// | Variable                                |   Descripiton   | default  |
/// |-----------------------------------------|-----------------|----------|
/// | `RUST_BIGDECIMAL_DEFAULT_PRECISION`     | digit precision | 100      |
/// | `RUST_BIGDECIMAL_DEFAULT_ROUNDING_MODE` | rounding-mode   | HalfEven |
///
/// It is recommended that the user set explicit values of a Context and *not*
/// rely on compile time constants, but the option is there if necessary.
///
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Context {
    /// total number of digits
    pub(crate) precision: NonZeroU64,
    /// how to round
    rounding: RoundingMode,
}

impl Context {
    /// Create context with precision and rounding mode
    pub fn new(precision: NonZeroU64, rounding: RoundingMode) -> Self {
        Context {
            precision: precision,
            rounding: rounding,
        }
    }

    /// Copy context with new precision value
    pub fn with_precision(&self, precision: NonZeroU64) -> Self {
        Self {
            precision: precision,
            ..*self
        }
    }

    /// Copy context with new precision value
    pub fn with_prec<T: ToPrimitive>(&self, precision: T) -> Option<Self> {
        precision
            .to_u64()
            .and_then(NonZeroU64::new)
            .map(|prec| {
                Self {
                    precision: prec,
                    ..*self
                }
            })
    }

    /// Copy context with new rounding mode
    pub fn with_rounding_mode(&self, mode: RoundingMode) -> Self {
        Self {
            rounding: mode,
            ..*self
        }
    }

    /// Return maximum precision
    pub fn precision(&self) -> NonZeroU64 {
        self.precision
    }

    /// Return rounding mode
    pub fn rounding_mode(&self) -> RoundingMode {
        self.rounding
    }

    /// Round decimal to precision in this context, using rounding-mode
    pub fn round_decimal(&self, n: BigDecimal) -> BigDecimal {
        n.with_precision_round(self.precision(), self.rounding_mode())
    }

    /// Round digits x and y with the rounding mode
    #[allow(dead_code)]
    pub(crate) fn round_pair(&self, sign: Sign, x: u8, y: u8, trailing_zeros: bool) -> u8 {
        self.rounding.round_pair(sign, (x, y), trailing_zeros)
    }

    /// Round digits x and y with the rounding mode
    #[allow(dead_code)]
    pub(crate) fn round_pair_with_carry(
        &self,
        sign: Sign,
        x: u8,
        y: u8,
        trailing_zeros: bool,
        carry: &mut u8,
    ) -> u8 {
        self.rounding.round_pair_with_carry(sign, (x, y), trailing_zeros, carry)
    }
}

impl stdlib::default::Default for Context {
    fn default() -> Self {
        Self {
            precision: NonZeroU64::new(DEFAULT_PRECISION).unwrap(),
            rounding: RoundingMode::default(),
        }
    }
}

#[cfg(test)]
mod test_context {
    use super::*;

    #[test]
    fn contstructor_and_setters() {
        let ctx = Context::default();
        let c = ctx.with_prec(44).unwrap();
        assert_eq!(c.precision.get(), 44);
        assert_eq!(c.rounding, RoundingMode::HalfEven);

        let c = c.with_rounding_mode(RoundingMode::Down);
        assert_eq!(c.precision.get(), 44);
        assert_eq!(c.rounding, RoundingMode::Down);
    }

    mod round_decimal {
        use super::*;

        #[test]
        fn case_bigint_1234567_prec3() {
            let ctx = Context::default().with_prec(3).unwrap();
            let i = BigDecimal::from(1234567);
            let d = ctx.round_decimal(i);
            assert_eq!(d.int_val, 123.into());
            assert_eq!(d.scale, -4);
        }

        #[test]
        fn case_bigint_1234500_prec4_halfup() {
            let ctx = Context::default()
                              .with_prec(4).unwrap()
                              .with_rounding_mode(RoundingMode::HalfUp);
            let i = BigDecimal::from(1234500);
            let d = ctx.round_decimal(i);
            assert_eq!(d.int_val, 1235.into());
            assert_eq!(d.scale, -3);
        }

        #[test]
        fn case_bigint_1234500_prec4_halfeven() {
            let ctx = Context::default()
                              .with_prec(4).unwrap()
                              .with_rounding_mode(RoundingMode::HalfEven);
            let i = BigDecimal::from(1234500);
            let d = ctx.round_decimal(i);
            assert_eq!(d.int_val, 1234.into());
            assert_eq!(d.scale, -3);
        }

        #[test]
        fn case_bigint_1234567_prec10() {
            let ctx = Context::default().with_prec(10).unwrap();
            let i = BigDecimal::from(1234567);
            let d = ctx.round_decimal(i);
            assert_eq!(d.int_val, 1234567000.into());
            assert_eq!(d.scale, 3);
        }
    }
}
