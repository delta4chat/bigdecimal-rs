//! Power operator trait implementation
//!

use super::*;
//use crate::stdlib::mem::swap;

/// [Exponentiation by squaring](https://en.wikipedia.org/wiki/Exponentiation_by_squaring) algorithm for power operation (`x ** y`)
impl<'a> Pow<&'a BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn pow(mut self, rhs: &'a BigDecimal) -> BigDecimal {
        if ! rhs.is_integer() {
            if self.sign() != Sign::Plus { // self <= 0
                unimplemented!("power with fractional exponents for non-positive base are not supported right now");
            }

            return self.ln().unwrap().mul(rhs).exp();
        }

        if rhs.is_zero() {
            BigDecimal::one()
        } else if self.is_zero() {
            self
        } else if self.is_one() || rhs.is_one() {
            self
        } else {
            if rhs.sign() == Sign::Minus {
                self = BigDecimal::one() / &self;
                let rhs = rhs.abs();
                return self.pow(&rhs);
            }

            let zero = BigDecimal::zero();
            let zero = &zero;

            let one = BigDecimal::one();
            let one = &one;

            let two: BigDecimal = 2u8.into();
            let two = &two;

            let mut exp = rhs.clone();
            while &((&exp) % two) == zero {
                self = (&self) * (&self);
                exp = ((&exp) / two).with_scale_round(0, RoundingMode::Down);
            }

            if (&exp) == one {
                return self;
            }

            let mut base = self.clone();
            while (&exp) > one {
                exp = ((&exp) / two).with_scale_round(0, RoundingMode::Down);

                base = (&base) * (&base);
                if &((&exp) % two) == one {
                    self *= &base;
                }
            }

            self
        }
    }
}

impl Pow<BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn pow(self, rhs: BigDecimal) -> BigDecimal {
        self.pow(&rhs)
    }
}

impl Pow<BigDecimal> for &BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn pow(self, rhs: BigDecimal) -> BigDecimal {
        self.clone().pow(rhs)
    }
}

impl Pow<&BigDecimal> for &BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn pow(self, rhs: &BigDecimal) -> BigDecimal {
        self.clone().pow(rhs)
    }
}

impl Pow<BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn pow(self, rhs: BigInt) -> BigDecimal {
        self.pow(BigDecimal::from(rhs))
    }
}

impl Pow<&BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn pow(self, rhs: &BigInt) -> BigDecimal {
        self.pow(BigDecimal::from(rhs.clone()))
    }
}

impl Pow<BigInt> for &BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn pow(self, rhs: BigInt) -> BigDecimal {
        self.clone().pow(rhs)
    }
}

impl Pow<&BigInt> for &BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn pow(self, rhs: &BigInt) -> BigDecimal {
        self.clone().pow(rhs)
    }
}

impl Pow<BigDecimal> for BigInt {
    type Output = BigDecimal;

    #[inline]
    fn pow(self, rhs: BigDecimal) -> BigDecimal {
        BigDecimal::from(self).pow(rhs)
    }
}

impl Pow<BigDecimal> for &BigInt {
    type Output = BigDecimal;

    #[inline]
    fn pow(self, rhs: BigDecimal) -> BigDecimal {
        BigDecimal::from(self.clone()).pow(rhs)
    }
}

impl Pow<&BigDecimal> for &BigInt {
    type Output = BigDecimal;

    #[inline]
    fn pow(self, rhs: &BigDecimal) -> BigDecimal {
        BigDecimal::from(self.clone()).pow(rhs)
    }
}

impl Pow<&BigDecimal> for BigInt {
    type Output = BigDecimal;

    #[inline]
    fn pow(self, rhs: &BigDecimal) -> BigDecimal {
        BigDecimal::from(self).pow(rhs)
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod bigdecimal_pow_tests {
    use super::*;
    use num_traits::{ToPrimitive, FromPrimitive, Signed, Zero, One};
    use num_bigint;
    use paste::paste;

    macro_rules! impl_test {
        ($name:ident; $a:literal ** $b:literal => $expected:literal) => {
            #[test]
            fn $name() {
                let mut a: BigDecimal = $a.parse().unwrap();
                let b: BigDecimal = $b.parse().unwrap();
                let expected = $expected.parse().unwrap();

                let prod = a.clone().pow(b.clone());
                assert_eq!(prod, expected);
                assert_eq!(prod.scale, expected.scale);

                assert_eq!(a.clone().pow(&b), expected);
                assert_eq!((&a).pow(b.clone()), expected);
                assert_eq!((&a).pow(&b), expected);

                a = a.pow(b);
                assert_eq!(a, expected);
                assert_eq!(a.scale, expected.scale);
            }
        };
        ($name:ident; $bigt:ty; $a:literal ** $b:literal => $expected:literal) => {
            #[test]
            fn $name() {
                let a: BigDecimal = $a.parse().unwrap();
                let b: $bigt = $b.parse().unwrap();
                let c = $expected.parse().unwrap();

                let prod = a.clone().pow(b.clone());
                assert_eq!(prod, c);
                assert_eq!(prod.scale, c.scale);

                assert_eq!(a.clone().pow(&b), c);
                assert_eq!((&a).pow(b.clone()), c);
                assert_eq!((&a).pow(&b), c);
            }
        };
    }

    impl_test!(case_2_1; "2" ** "1" => "2");
    impl_test!(case_2e1_1; "2e1" ** "1" => "2e1");
    impl_test!(case_3_d333333; ".333333" ** "3" => "0.037036925926037037");
    impl_test!(case_2_2094; "2" ** "2094" => "2274107132820098583779534975770791402012647532175266505405399807105458701191019394675150175292882139237271587493107433537116798498657010457777276858152709809741143100298761961509534347091252462477419592066507808656639093225182549843617203788688882182495749718546022156925042947832003308567809767060989871010566864129593611960047557683230792190733951242982940572506645920649551458071383747981955017708251048940167206874499934925198162252638772990548151887959002734210169155811976479016639052191814699528032527778068299117926371991933443521489604057319138783330322834288172792932116931299127217031352612769118035471853689120787267584");
    impl_test!(case_1ed450_295; "1e-450" ** "295" => "1e-132750");
    impl_test!(case_n995052931ddd_5; "-995052931372975485719.533153137" ** "5" => "-975508184016430539672554182849644522470828743238564592279295695181757004746080435889990982000102239896318.397157127812978479174123289552727264747889457");
    impl_test!(case_1d129374865661_100; "1.129374865661" ** "100" => "192225.865312076284460257922583243142164238696637955176303392515346381318674135207869159296595985693555795992125807751373976272973612741855037995797784185802503421513587316962325052221186272093580692486379495164413125303359410007423907208707370070704294768872705214357966016856972415814111337424967490575243018381900298796749792793431520487961592076334467789467632179281289958468416586708832080992047855174341667073532665444890122140875567935548381678027619559242359084539163891258176483131330766205670379593628962785051822594417945843797057085261130175283826284232050718157244115387046663650833575738953983978828266883054687592907200900847678026900924634840427295252306860578211806251442772393361975976460875043260237984347353593560257649618826809956118627655157690758198889964712491796654164128980261587949506656270360597942219345375593609313046994563536845268072960830324921527264649668038875896693177738101599508159629059204118180227418052567718297621472201059948799651530296755373675409264201467274796257349004579709230115141474998239900187287555719711540795635788871912541191929756821396692905822649616709776589702631239567004734776246946481004872452318479447132655246605907469584667916354188073986001");
    impl_test!(case_n8d37664968_0; "-8.37664968" ** "0" => "1");
    impl_test!(case_8d37664968_0; "8.37664968" ** "0" => "1");
    impl_test!(case_9_0; "9" ** "0" => "1");
    impl_test!(case_n9_0; "-9" ** "0" => "1");

    // Test multiplication between big decimal and big integer
    impl_test!(case_5674_32; BigInt; "5674" ** "32" => "1331860094597820211515162622378052490313515153496740780838372202636437393829892572581549624234457763163034779478734667776");
    impl_test!(case_0d000000001_3; BigInt; "0.000000001" ** "3" => "0.000000000000000000000000001");
    impl_test!(case_n1d1_577; BigInt; "-1.1" ** "577" => "-764855398369519271683712.8763306293516792622237740785687223058179294885670676497458620645796895863305723840588933792686671614721304196450610588668939203485434469560756858695460655813370099943891981420541349938449973129694712671848036451891457611782600296527220285934444865687137105927728456720992366409555239875938923924350865837758724103497161827958184137981492215083398081355041336624666063930146774835563120602307443585895906077959711377955647425781422343416486578189236830282032621039019663109026381829997190630452194436467891088896226552524016542226114388937401771809369279101069395150089375023371");
}
